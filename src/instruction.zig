const std = @import("std");
const native_endian = @import("builtin").target.cpu.arch.endian();
const expect = std.testing.expect;
const CPU = @import("cpu.zig").CPU;
const Trap = @import("cpu.zig").Trap;
const RegistersName = @import("cpu.zig").RegistersName;
const Ram = @import("memory.zig").Ram;
const Rom = @import("memory.zig").Rom;

pub const Mode = enum(u1) { REGISTER_IMM16 = 0, OFFSET_INDEXED };

pub const Opcode = enum(u4) {
    FREE = 0,
    B,
    LD, // LD -(SP), Rs => PUSH ; LD Rd, (SP)+ POP ; LDM (Load Multiple Rn bytecode.fl=1)
    ST,
    ADD, // ADC
    SUB, // SBC
    MUL, // MULX
    DIV, // DIVX
    AND,
    OR,
    XOR,
    ROL,
    ROR,
    LSL,
    LSR, // ASR
    SWI,
};

pub const Condition = enum(u4) {
    EQ = 0, // EQ (EQUAL : Z = 1),
    NE, // NE (NOT EQUAL : Z = 0)
    CS, // CS/HS (CARRY SET : C = 1)
    CC, // CC/LO (CARRY CLEAR : C = 0)
    MI, // MI (MINUS / NEGATIVE : N = 1)
    PL, // PL (PLUS / POSITIVE OR ZERO : N = 0)
    VS, // VS (OVERFLOW SET : V = 1)
    VC, // VC (OVERFLOW CLEAR : V = 0)
    HI, // HI (HIGHER : UNSIGNED > : C = 1 AND Z = 0)
    LS, // LS (LOWER OR SAME : UNSIGNED <= : C = 0 OR Z = 1)
    GE, // GE (GREATER OR EQUAL : SIGNED >= : N == V)
    LT, // LT (LESS THAN : SIGNED < : N != V)
    GT, // GT (GREATER THAN : SIGNED > : Z = 0 AND N == V)
    LE, // LE (LESS OR EQUAL : SIGNED <= : Z = 1 OR N != V)
    PR, // PR (PREBRANCH) => TST
    A, // A  (ALWAYS) => JMP, JSR, BA (SP)+ => RTS
};

// Condition alias
pub const HS = Condition.CS;
pub const LO = Condition.CC;

// Define the bytecode layout based on endianness
const BytecodeLayout = switch (native_endian) {
    .big => packed struct(u32) {
        arch: u1,
        opcode: u4,
        mode: u1,
        size: u1,
        rd: u4,
        rs: u4,
        fl: u1,
        imm16: u16,
    },
    .little => packed struct(u32) {
        imm16: u16,
        fl: u1,
        rs: u4,
        rd: u4,
        size: u1,
        mode: u1,
        opcode: u4,
        arch: u1,
    },
};

pub const Instruction = packed union {
    raw: u32,
    bytecode: BytecodeLayout,

    pub fn pack(arch: u1, opcode: Opcode, mode: Mode, size: u1, rd: RegistersName, rs: RegistersName, fl: u1, imm16: u16) Instruction {
        return Instruction{ .bytecode = .{
            .arch = arch,
            .opcode = @intFromEnum(opcode),
            .mode = @intFromEnum(mode),
            .size = size,
            .rd = @intFromEnum(rd),
            .rs = @intFromEnum(rs),
            .fl = fl,
            .imm16 = imm16,
        } };
    }

    pub fn unpack(bytecode: u32) Instruction {
        return Instruction{ .raw = bytecode };
    }

    pub fn displayPacked(bytecode: u32) void {
        const instruction = Instruction.unpack(bytecode);
        std.debug.print("Packed bytecode: 0x{X:0>8}\n", .{bytecode});
        std.debug.print("  Binary: {b:0>32}\n", .{bytecode});
        std.debug.print("  Unpacked fields:\n", .{});
        instruction.displayUnpacked();
    }

    pub fn displayUnpacked(self: Instruction) void {
        const bc = self.bytecode;
        std.debug.print("    arch:   {d}\n", .{bc.arch});
        std.debug.print("    opcode: {d} ({s})\n", .{ bc.opcode, @tagName(@as(Opcode, @enumFromInt(bc.opcode))) });
        std.debug.print("    mode:   {d} ({s})\n", .{ bc.mode, @tagName(@as(Mode, @enumFromInt(bc.mode))) });
        std.debug.print("    size:   {d} ({s})\n", .{ bc.size, if (bc.size == 0) "BYTE" else "WORD" });
        std.debug.print("    rd:     {d} ({s})\n", .{ bc.rd, @tagName(@as(RegistersName, @enumFromInt(bc.rd))) });
        std.debug.print("    rs:     {d} ({s})\n", .{ bc.rs, @tagName(@as(RegistersName, @enumFromInt(bc.rs))) });
        std.debug.print("    fl:     {d}\n", .{bc.fl});
        std.debug.print("    imm16:  0x{X:0>4} ({d})\n", .{ bc.imm16, bc.imm16 });
    }

    pub fn execute(self: Instruction, cpu: *CPU) !void {
        switch (self.bytecode.opcode) {
            @intFromEnum(Opcode.FREE) => try VOID(cpu, self),
            @intFromEnum(Opcode.B) => try B(cpu, self),
            @intFromEnum(Opcode.LD) => try LD(cpu, self),
            @intFromEnum(Opcode.ST) => try ST(cpu, self),
            @intFromEnum(Opcode.ADD) => try ADD(cpu, self),
            @intFromEnum(Opcode.SUB) => try SUB(cpu, self),
            @intFromEnum(Opcode.MUL) => try MUL(cpu, self),
            @intFromEnum(Opcode.DIV) => try DIV(cpu, self),
            @intFromEnum(Opcode.AND) => try AND(cpu, self),
            @intFromEnum(Opcode.OR) => try OR(cpu, self),
            @intFromEnum(Opcode.XOR) => try XOR(cpu, self),
            @intFromEnum(Opcode.ROL) => try ROL(cpu, self),
            @intFromEnum(Opcode.ROR) => try ROR(cpu, self),
            @intFromEnum(Opcode.LSL) => try LSL(cpu, self),
            @intFromEnum(Opcode.LSR) => try LSR(cpu, self),
            @intFromEnum(Opcode.SWI) => try SWI(cpu, self),
        }
    }

    fn VOID(cpu: *CPU, instruction: Instruction) !void {
        _ = cpu;
        _ = instruction;
        return;
    }

    fn B(cpu: *CPU, instruction: Instruction) !void {
        // PC RELATIVE
        // When bitecode.fl bit is set save PC before jump (Link and Branch). Bxx.L => -(SP)=PC and Branch
        // Rd store Condition.

        // Accepted syntax.
        // BNE label        => Instruction.pack(0, .B, .REGISTER_IMM16, 0, Condition.NE, .R0, 0, PC - label);
        // BMI IMM16        => Instruction.pack(0, .B, .REGISTER_IMM16, 0, Condition.MI, .R0, 0, IMM16);

        // BGT label(Rs)    => Instruction.pack(0, .B, .OFFSET_INDEXED, 0, Condition.GT, .Rs, 0, PC - label;
        // BGE.L label(Rs)  => Instruction.pack(0, .B, .OFFSET_INDEXED, 0, Condition.GE, .Rs, 1, PC - label;

        // BPR Rs, Rn       => Instruction.pack(0, .B, .OFFSET_INDEXED, 0, Condition.PR, .Rs, 0, (Rn << 12));   => Rs - Rn ; Set flags NZCV discard result.
        // BPR Rs, IMM16    => Instruction.pack(0, .B, .REGISTER_IMM16, 0, Condition.PR, .Rs, 0, IMM16);        => Rs - IMM16 ; Set flags NZCV discard result.

        // BPR.B Rs, Rn       => Instruction.pack(0, .B, .OFFSET_INDEXED, 0, Condition.PR, .Rs, 1, (Rn << 12));   => Rs & Rn ; Set flags NZCV discard result.
        // BPR.B Rs, IMM16    => Instruction.pack(0, .B, .REGISTER_IMM16, 0, Condition.PR, .Rs, 1, IMM16);        => Rs & IMM16 ; Set flags NZCV discard result.

        const condition = @as(Condition, @enumFromInt(instruction.bytecode.rd));
        const rs = instruction.bytecode.rs;
        const imm = instruction.bytecode.imm16;
        const is_link = instruction.bytecode.fl == 1;

        // Determine if branch condition is met
        const condition_met = switch (condition) {
            .EQ => cpu.registers.SR.getFlag(.Z),
            .NE => !cpu.registers.SR.getFlag(.Z),
            .CS => cpu.registers.SR.getFlag(.C),
            .CC => !cpu.registers.SR.getFlag(.C),
            .MI => cpu.registers.SR.getFlag(.N),
            .PL => !cpu.registers.SR.getFlag(.N),
            .VS => cpu.registers.SR.getFlag(.V),
            .VC => !cpu.registers.SR.getFlag(.V),
            .HI => cpu.registers.SR.getFlag(.C) and !cpu.registers.SR.getFlag(.Z),
            .LS => !cpu.registers.SR.getFlag(.C) or cpu.registers.SR.getFlag(.Z),
            .GE => cpu.registers.SR.getFlag(.N) == cpu.registers.SR.getFlag(.V),
            .LT => cpu.registers.SR.getFlag(.N) != cpu.registers.SR.getFlag(.V),
            .GT => !cpu.registers.SR.getFlag(.Z) and (cpu.registers.SR.getFlag(.N) == cpu.registers.SR.getFlag(.V)),
            .LE => cpu.registers.SR.getFlag(.Z) or (cpu.registers.SR.getFlag(.N) != cpu.registers.SR.getFlag(.V)),
            .PR => false, // PR
            .A => true, // Always branch
        };

        // Handle PR (PreBranch)
        if (condition == .PR) {
            // BPR: Compare Rs with Rn or IMM16, set flags but don't branch
            const first_operand: u16 = cpu.registers.readRegister(rs);
            const second_operand = if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED))
                cpu.registers.readRegister(@truncate((instruction.bytecode.imm16 >> 12) & 0xF))
            else
                instruction.bytecode.imm16;

            if (is_link) {
                // BIT test: Rs & second_operand
                const result = first_operand & second_operand;
                cpu.registers.SR.updateFlag(.N, (result & 0x8000) != 0);
                cpu.registers.SR.updateFlag(.Z, result == 0);
                cpu.registers.SR.clearFlag(.C);
                cpu.registers.SR.clearFlag(.V);
            } else {
                // Normal compare: Rs - second_operand
                const result = @subWithOverflow(first_operand, second_operand);
                cpu.registers.SR.updateFlag(.N, (result[0] & 0x8000) != 0);
                cpu.registers.SR.updateFlag(.Z, result[0] == 0);
                cpu.registers.SR.updateFlag(.C, result[1] != 0);

                // Overflow: check if signs differ and result sign differs from first
                const first_negative = (first_operand & 0x8000) != 0;
                const second_negative = (second_operand & 0x8000) != 0;
                const result_negative = (result[0] & 0x8000) != 0;
                cpu.registers.SR.updateFlag(.V, (first_negative != second_negative) and (first_negative != result_negative));
            }
            return;
        }

        // If condition is not met, don't branch
        if (!condition_met) {
            return;
        }

        // Save PC to stack if link bit is set
        if (is_link) {
            cpu.registers.SP -%= 2;
            cpu.ram.write16(cpu.registers.SP, cpu.registers.PC);
        }

        // Calculate target address
        const target_address: u16 = if (instruction.bytecode.mode == @intFromEnum(Mode.REGISTER_IMM16)) blk: {
            // REGISTER_IMM16: offset is imm16 (sign-extended as PC-relative)
            const offset = @as(i16, @bitCast(imm));
            break :blk cpu.registers.PC +% @as(u16, @bitCast(offset));
        } else blk: {
            // OFFSET_INDEXED: address is imm16(rs) = base + offset
            const offset = @as(i16, @bitCast(imm));
            const base = cpu.registers.readRegister(rs);
            const computed_offset = @as(u16, @bitCast(offset));
            break :blk base +% computed_offset;
        };

        cpu.registers.PC = target_address;
    }

    fn LD(cpu: *CPU, instruction: Instruction) !void {
        const rd = instruction.bytecode.rd;
        const rs = instruction.bytecode.rs;
        const imm = instruction.bytecode.imm16;
        const sp_index = @intFromEnum(RegistersName.R14);
        const pc_index = @intFromEnum(RegistersName.R15);

        // LDM (bytecode.fl = 1) can pop/push multiple registers at the same time.
        // Syntax:
        // LDM -(SP), {R1,R2,R6} ; Order is no matter (Register is sorted)
        // LDM {R6,R2,R1}, (SP)+ ; Order is no matter (Register is sorted)
        // {R6,R2,R1} encoded into IMM16 as bit 0b0000_0000_0100_0110

        // Handle LDM (Load Multiple) - fl = 1
        if (instruction.bytecode.fl == 1) {
            // LDM only works with SP (R14)
            // PUSH Multiple: LDM -(SP), {register_list} => rd = SP, rs = 0, imm16 = register bitmask
            // POP Multiple:  LDM {register_list}, (SP)+ => rd = 0, rs = SP, imm16 = register bitmask

            const register_mask = imm;

            if (rd == sp_index and rs == 0) {
                // PUSH Multiple: LDM -(SP), {register_list}
                // Push registers in reverse order (R15 down to R0) so they pop in correct order
                var reg_index: u5 = 15;
                while (true) : (reg_index -%= 1) {
                    if ((register_mask & (@as(u16, 1) << @as(u4, @intCast(reg_index)))) != 0) {
                        const value = cpu.registers.readRegister(@as(u4, @intCast(reg_index)));
                        cpu.registers.SP -%= 2;
                        cpu.ram.write16(cpu.registers.SP, value);
                    }
                    if (reg_index == 0) break;
                }
                return;
            } else if (rd == 0 and rs == sp_index) {
                // POP Multiple: LDM {register_list}, (SP)+
                // Pop registers in forward order (R0 to R15)
                var reg_index: u5 = 0;
                while (reg_index <= 15) : (reg_index += 1) {
                    if ((register_mask & (@as(u16, 1) << @as(u4, @intCast(reg_index)))) != 0) {
                        const value = cpu.ram.read16(cpu.registers.SP);
                        cpu.registers.SP +%= 2;
                        cpu.registers.writeRegister(@as(u4, @intCast(reg_index)), value);
                    }
                }
                return;
            } else {
                // Illegal: LDM must use SP
                cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
                cpu.registers.SR.setFlag(.T);
                return;
            }
        }

        // Illegal: LD PC, Rs|IMM16
        if (rd == pc_index) {
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        if (instruction.bytecode.mode == @intFromEnum(Mode.REGISTER_IMM16)) {
            // Handle SP special cases
            if (rd == sp_index) {
                // Illegal: LD SP, SP
                if (rs == sp_index) {
                    cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
                    cpu.registers.SR.setFlag(.T);
                    return;
                }
                // PUSH: LD -(SP), Rs or LD -(SP), IMM16
                const value = if (imm != 0) imm else cpu.registers.readRegister(rs);
                cpu.registers.SP -%= 2;
                cpu.ram.write16(cpu.registers.SP, value);
                return;
            }

            // POP: LD Rd, (SP)+
            if (rs == sp_index) {
                const value = cpu.ram.read16(cpu.registers.SP);
                cpu.registers.SP +%= 2;
                cpu.registers.writeRegister(rd, value);
                return;
            }

            // Check for illegal instruction: LD Rd, Rs, IMM16 where all three differ
            // Only illegal when: rd != rs AND rs != 0 AND imm != 0
            if (rd != rs and rs != 0 and imm != 0) {
                cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
                cpu.registers.SR.setFlag(.T);
                return;
            }

            // LD Rd, IMM16 (rs == 0, imm != 0)
            if (rs == 0) {
                cpu.registers.writeRegister(rd, imm);
                return;
            }

            // LD Rd, Rs (imm == 0, rs != 0)
            const value = cpu.registers.readRegister(rs);
            cpu.registers.writeRegister(rd, value);
        } else {
            // OFFSET_INDEXED: LD Rd, IMM16(Rs)
            const address = cpu.registers.readRegister(rs) +% imm;
            const value = cpu.ram.read16(address);
            cpu.registers.writeRegister(rd, value);
        }
    }

    fn ST(cpu: *CPU, instruction: Instruction) !void {
        const rd = instruction.bytecode.rd;
        const rs = instruction.bytecode.rs;
        const imm = instruction.bytecode.imm16;
        const pc_index = @intFromEnum(RegistersName.R15);

        // REGISTER_IMM16 mode is illegal for ST
        if (instruction.bytecode.mode == @intFromEnum(Mode.REGISTER_IMM16)) {
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        // Illegal: ST PC, Rs|IMM16 (storing to PC as dest is illegal)
        if (rd == pc_index) {
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        // OFFSET_INDEXED: ST IMM16(Rd), Rs
        // [IMM16 + Rd] = Rs
        const address = cpu.registers.readRegister(rd) +% imm;
        const value = cpu.registers.readRegister(rs);
        cpu.ram.write16(address, value);
    }

    fn SWI(cpu: *CPU, instruction: Instruction) !void {
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            // SR = Trap ERROR.
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }
        return;
    }

    fn ADD(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            // SR = Trap ERROR.
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        // ADD Rd               => Rd = Rd + 1
        // ADD Rd, IMM16        => Rd = Rd + IMM16
        // ADD Rd, Rs           => Rd = Rd + Rs
        // ADD Rd, Rs, IMM16    => Rd = Rs + IMM16
        // ADD Rd, Rs, 0        => Defined behavior, but unexpected result! (Maybe better to reject parser side!?)

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        // Check if ADC (Add with Carry)
        if (instruction.bytecode.fl == 1) {
            // ADC: Add with carry
            const carry_in: u16 = if (cpu.registers.SR.getFlag(.C)) 1 else 0;

            // First addition: first_operand + second_operand
            const temp_result = @addWithOverflow(first_operand, second_operand);

            // Second addition: temp_result + carry
            const final_result = @addWithOverflow(temp_result[0], carry_in);

            // Carry out = carry from first add OR carry from second add
            const carry_out = (temp_result[1] != 0) or (final_result[1] != 0);

            // Update flags
            cpu.registers.SR.updateFlag(.N, (final_result[0] & 0x8000) != 0);
            cpu.registers.SR.updateFlag(.Z, final_result[0] == 0);
            cpu.registers.SR.updateFlag(.C, carry_out);

            // Overflow: check if signs of operands are same and result sign differs
            const first_negative = (first_operand & 0x8000) != 0;
            const second_negative = (second_operand & 0x8000) != 0;
            const result_negative = (final_result[0] & 0x8000) != 0;
            cpu.registers.SR.updateFlag(.V, (first_negative == second_negative) and (first_negative != result_negative));

            cpu.registers.writeRegister(instruction.bytecode.rd, final_result[0]);
        } else {
            // Normal ADD
            const result = @addWithOverflow(first_operand, second_operand);

            // Update flags
            cpu.registers.SR.updateFlag(.N, (result[0] & 0x8000) != 0);
            cpu.registers.SR.updateFlag(.Z, result[0] == 0);
            cpu.registers.SR.updateFlag(.C, result[1] != 0);

            // a + b ; (a + b) < a ; (sign(a)==sign(b)) and (sign(r)!=sign(a))
            const first_negative = (first_operand & 0x8000) != 0;
            const second_negative = (second_operand & 0x8000) != 0;
            const result_negative = (result[0] & 0x8000) != 0;
            cpu.registers.SR.updateFlag(.V, (first_negative == second_negative) and (first_negative != result_negative));

            cpu.registers.writeRegister(instruction.bytecode.rd, result[0]);
        }
    }

    fn SUB(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            // SR = Trap ERROR.
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        // SUB Rd               => Rd = Rd - 1
        // SUB Rd, IMM16        => Rd = Rd - IMM16
        // SUB Rd, Rs           => Rd = Rd - Rs
        // SUB Rd, Rs, IMM16    => Rd = Rs - IMM16
        // SUB Rd, Rs, 0        => Defined behavior, but unexpected result! (Maybe better to reject parser side!?)

        // When bytecode.fl is set SUB behave like SBC

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        // Check if SBC (Subtract with Borrow)
        if (instruction.bytecode.fl == 1) {
            // SBC: Subtract with borrow
            const borrow_in: u16 = if (cpu.registers.SR.getFlag(.C)) 1 else 0;

            // First subtraction: first_operand - second_operand
            const temp_result = @subWithOverflow(first_operand, second_operand);

            // Second subtraction: temp_result - borrow
            const final_result = @subWithOverflow(temp_result[0], borrow_in);

            // Borrow out = borrow from first sub OR borrow from second sub
            const borrow_out = (temp_result[1] != 0) or (final_result[1] != 0);

            // Update flags
            cpu.registers.SR.updateFlag(.N, (final_result[0] & 0x8000) != 0);
            cpu.registers.SR.updateFlag(.Z, final_result[0] == 0);
            cpu.registers.SR.updateFlag(.C, borrow_out);

            // Overflow: check if signs of operands differ and result sign differs from first operand
            const first_negative = (first_operand & 0x8000) != 0;
            const second_negative = (second_operand & 0x8000) != 0;
            const result_negative = (final_result[0] & 0x8000) != 0;
            cpu.registers.SR.updateFlag(.V, (first_negative != second_negative) and (first_negative != result_negative));

            cpu.registers.writeRegister(instruction.bytecode.rd, final_result[0]);
        } else {
            // Normal SUB
            const result = @subWithOverflow(first_operand, second_operand);

            // Update flags
            cpu.registers.SR.updateFlag(.N, (result[0] & 0x8000) != 0);
            cpu.registers.SR.updateFlag(.Z, result[0] == 0);
            cpu.registers.SR.updateFlag(.C, (result[1] != 0));

            // a - b ; a < b ; (sign(a)!=sign(b)) and (sign(r)!=sign(a))
            const first_negative = (first_operand & 0x8000) != 0;
            const second_negative = (second_operand & 0x8000) != 0;
            const result_negative = (result[0] & 0x8000) != 0;
            cpu.registers.SR.updateFlag(.V, (first_negative != second_negative) and (first_negative != result_negative));

            cpu.registers.writeRegister(instruction.bytecode.rd, result[0]);
        }
    }

    fn MUL(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            // SR = Trap ERROR.
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        // MUL Rd, IMM16        => Rd = Rd * IMM16
        // MUL Rd, Rs           => Rd = Rd * Rs
        // MUL Rd, Rs, IMM16    => Rd = Rs * IMM16
        // MUL Rd, Rs, 0        => Defined behavior, but unexpected result! (Maybe better to reject parser side!?)

        // MULX Rd, Rs          => Rd = Rd * Rs     => Rd:HI Rs:LO ; 32-bit operation
        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        // MUL Rd, Rs, imm16 → Rd = Rs * imm16

        // Check for MULX instruction
        if (instruction.bytecode.fl == 0) {
            const product: u32 = @as(u32, first_operand) * @as(u32, second_operand);
            const result: u16 = @truncate(product);

            // Update flags (N, Z, V)
            cpu.registers.SR.updateFlag(.N, (result & 0x8000) != 0);
            cpu.registers.SR.updateFlag(.Z, result == 0);
            cpu.registers.SR.updateFlag(.V, product > 0xFFFF);
            cpu.registers.SR.updateFlag(.C, product > 0xFFFF);
            if (instruction.bytecode.rd != 0) {
                cpu.registers.writeRegister(instruction.bytecode.rd, result);
            }
        } else {
            // MULX: Multiplication 16×16 → 32 bits
            const product_32: u32 = @as(u32, first_operand) * @as(u32, second_operand);
            const result_lo: u16 = @truncate(product_32); // 16 bits inférieurs
            const result_hi: u16 = @truncate(product_32 >> 16); // 16 bits supérieurs

            // Flags basés sur le résultat 32 bits complet
            cpu.registers.SR.updateFlag(.N, (product_32 & 0x80000000) != 0);
            cpu.registers.SR.updateFlag(.Z, product_32 == 0);
            cpu.registers.SR.updateFlag(.V, result_hi != 0); // Overflow si partie haute non-nulle
            cpu.registers.SR.updateFlag(.C, result_hi != 0);

            // Write result to Rd:Rs (Rd=high, Rs=low)
            if (instruction.bytecode.rd != 0) {
                cpu.registers.writeRegister(instruction.bytecode.rd, result_hi);
                cpu.registers.writeRegister(instruction.bytecode.rs, result_lo);
            }
        }
    }

    fn DIV(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            // SR = Trap ERROR.
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        // DIV Rd, IMM16        => Rd = Rd / IMM16
        // DIV Rd, Rs           => Rd = Rd / Rs
        // DIV Rd, Rs, IMM16    => Rd = Rs / IMM16
        // DIV Rd, Rs, 0        => Defined behavior, but unexpected result! (Maybe better to reject parser side!?)

        // DIVX Rd, Rs          => Rd = Rd / Rs     => Rd:Quotient Rs=Remainder
        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        // Check for division by zero
        if (second_operand == 0) {
            cpu.registers.SR.raw = @intFromEnum(Trap.Division_by_zero);
            cpu.registers.SR.setFlag(.T); // Set trap flag
            return;
        }

        const quotient: u32 = first_operand / second_operand;
        const result: u16 = @truncate(quotient);

        // Update flags (N, Z, V)
        cpu.registers.SR.updateFlag(.N, (result & 0x8000) != 0);
        cpu.registers.SR.updateFlag(.Z, result == 0);
        cpu.registers.SR.clearFlag(.C);
        cpu.registers.SR.clearFlag(.V);

        if (instruction.bytecode.rd != 0) {
            cpu.registers.writeRegister(instruction.bytecode.rd, result);
            if (instruction.bytecode.fl == 1) {
                const remainder: u16 = first_operand % second_operand;
                cpu.registers.writeRegister(instruction.bytecode.rs, remainder);
            }
        }
    }

    fn AND(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            // SR = Trap ERROR.
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        // AND Rd, Rs, imm16 → Rd = Rs & imm16
        const result: u16 = first_operand & second_operand;

        // Update flags (N, Z) and clear C, V
        cpu.registers.SR.updateFlag(.N, (result & 0x8000) != 0);
        cpu.registers.SR.updateFlag(.Z, result == 0);
        cpu.registers.SR.clearFlag(.C);
        cpu.registers.SR.clearFlag(.V);

        // Write result to Rd (unless Rd is R0, which is always zero)
        if (instruction.bytecode.rd != 0) {
            cpu.registers.writeRegister(instruction.bytecode.rd, result);
        }
    }

    fn OR(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            // SR = Trap ERROR.
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        // OR Rd, Rs, imm16 → Rd = Rs | imm16
        const result: u16 = first_operand | second_operand;

        // Update flags (N, Z) and clear C, V
        cpu.registers.SR.updateFlag(.N, (result & 0x8000) != 0);
        cpu.registers.SR.updateFlag(.Z, result == 0);
        cpu.registers.SR.clearFlag(.C);
        cpu.registers.SR.clearFlag(.V);

        // Write result to Rd (unless Rd is R0, which is always zero)
        if (instruction.bytecode.rd != 0) {
            cpu.registers.writeRegister(instruction.bytecode.rd, result);
        }
    }

    fn XOR(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            // SR = Trap ERROR.
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        const result: u16 = first_operand ^ second_operand;

        // Update flags (N, Z) and clear C, V
        cpu.registers.SR.updateFlag(.N, (result & 0x8000) != 0);
        cpu.registers.SR.updateFlag(.Z, result == 0);
        cpu.registers.SR.clearFlag(.C);
        cpu.registers.SR.clearFlag(.V);

        // Write result to Rd (unless Rd is R0, which is always zero)
        if (instruction.bytecode.rd != 0) {
            cpu.registers.writeRegister(instruction.bytecode.rd, result);
        }
    }

    fn ROL(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            // SR = Trap ERROR.
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        // ROL Rd, Rs (0x0F MASKED) => Rd is rotated by the ammount of Rs...
        // ROL Rd, IMM16 (0x0F MASKED) => Rd is rotated by the ammount of IMM16
        // ROL Rd, Rs, IMM16 (0x0F MASKED) => Rs is rotated by the ammount of IMM16

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        // Mask the shift amount to 0x0F (0-15)
        const shift_amount: u5 = @truncate(second_operand & 0x0F);

        // Rotate left: take bits from the left, wrap them to the right
        const result: u16 = std.math.rotl(u16, first_operand, shift_amount);

        // Carry flag gets the last bit rotated out (bit 15 before rotation if shift > 0)
        const carry: bool = if (shift_amount > 0) ((first_operand >> @as(u4, @intCast(16 - shift_amount))) & 1) != 0 else cpu.registers.SR.getFlag(.C); // Update flags (N, Z, C) and clear V
        cpu.registers.SR.updateFlag(.N, (result & 0x8000) != 0);
        cpu.registers.SR.updateFlag(.Z, result == 0);
        cpu.registers.SR.updateFlag(.C, carry);
        cpu.registers.SR.clearFlag(.V);

        // Write result to Rd (unless Rd is R0, which is always zero)
        if (instruction.bytecode.rd != 0) {
            cpu.registers.writeRegister(instruction.bytecode.rd, result);
        }
    }

    fn ROR(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            // SR = Trap ERROR.
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        // ROR Rd, Rs (0x0F MASKED) => Rd is rotated by the ammount of Rs...
        // ROR Rd, IMM16 (0x0F MASKED) => Rd is rotated by the ammount of IMM16
        // ROR Rd, Rs, IMM16 (0x0F MASKED) => Rs is rotated by the ammount of IMM16

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        // Mask the shift amount to 0x0F (0-15)
        const shift_amount: u5 = @truncate(second_operand & 0x0F);

        // Rotate right: take bits from the right, wrap them to the left
        const result: u16 = std.math.rotr(u16, first_operand, shift_amount);

        // Carry flag gets the last bit rotated out (bit 0 before rotation if shift > 0)
        const carry: bool = if (shift_amount > 0) ((first_operand >> @as(u4, @intCast(shift_amount - 1))) & 1) != 0 else cpu.registers.SR.getFlag(.C); // Update flags (N, Z, C) and clear V
        cpu.registers.SR.updateFlag(.N, (result & 0x8000) != 0);
        cpu.registers.SR.updateFlag(.Z, result == 0);
        cpu.registers.SR.updateFlag(.C, carry);
        cpu.registers.SR.clearFlag(.V);

        // Write result to Rd (unless Rd is R0, which is always zero)
        if (instruction.bytecode.rd != 0) {
            cpu.registers.writeRegister(instruction.bytecode.rd, result);
        }
    }

    fn LSL(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            // SR = Trap ERROR.
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        // LSL Rd, Rs (0x0F MASKED) => Rd is shifted left by the amount of Rs...
        // LSL Rd, IMM16 (0x0F MASKED) => Rd is shifted left by the amount of IMM16
        // LSL Rd, Rs, IMM16 (0x0F MASKED) => Rs is shifted left by the amount of IMM16

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        // Mask the shift amount to 0x0F (0-15)
        const shift_amount: u5 = @truncate(second_operand & 0x0F);

        // Logical shift left: shift bits left, fill with zeros on the right
        const result: u16 = std.math.shl(u16, first_operand, shift_amount);

        // Carry flag gets the last bit shifted out (bit 15 - shift_amount + 1 if shift > 0)
        const carry: bool = if (shift_amount > 0) ((first_operand >> @as(u4, @intCast(16 - shift_amount))) & 1) != 0 else cpu.registers.SR.getFlag(.C); // Update flags (N, Z, C) and clear V
        cpu.registers.SR.updateFlag(.N, (result & 0x8000) != 0);
        cpu.registers.SR.updateFlag(.Z, result == 0);
        cpu.registers.SR.updateFlag(.C, carry);
        cpu.registers.SR.clearFlag(.V);

        // Write result to Rd (unless Rd is R0, which is always zero)
        if (instruction.bytecode.rd != 0) {
            cpu.registers.writeRegister(instruction.bytecode.rd, result);
        }
    }

    fn LSR(cpu: *CPU, instruction: Instruction) !void {
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            // SR = Trap ERROR.
            cpu.registers.SR.raw = @intFromEnum(Trap.Illegal_instruction);
            cpu.registers.SR.setFlag(.T);
            return;
        }

        // LSR Rd, Rs (0x0F MASKED) => Rd is shifted right by the amount of Rs...
        // LSR Rd, IMM16 (0x0F MASKED) => Rd is shifted right by the amount of IMM16
        // LSR Rd, Rs, IMM16 (0x0F MASKED) => Rs is shifted right by the amount of IMM16

        // ASR if bytecode.fl is set, LSR behave like ASR.

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        // Mask the shift amount to 0x0F (0-15)
        const shift_amount: u5 = @truncate(second_operand & 0x0F);

        // Check if ASR (Arithmetic Shift Right)
        const result: u16 = if (instruction.bytecode.fl == 1) blk: {
            // ASR: Arithmetic shift right - preserve sign bit
            const signed_operand: i16 = @bitCast(first_operand);
            const shifted: i16 = std.math.shr(i16, signed_operand, shift_amount);
            break :blk @bitCast(shifted);
        } else blk: {
            // LSR: Logical shift right - fill with zeros
            break :blk std.math.shr(u16, first_operand, shift_amount);
        };

        // Carry flag gets the last bit shifted out (bit shift_amount - 1 if shift > 0)
        const carry: bool = if (shift_amount > 0) ((first_operand >> @as(u4, @intCast(shift_amount - 1))) & 1) != 0 else cpu.registers.SR.getFlag(.C); // Update flags (N, Z, C) and clear V
        cpu.registers.SR.updateFlag(.N, (result & 0x8000) != 0);
        cpu.registers.SR.updateFlag(.Z, result == 0);
        cpu.registers.SR.updateFlag(.C, carry);
        cpu.registers.SR.clearFlag(.V);

        // Write result to Rd (unless Rd is R0, which is always zero)
        if (instruction.bytecode.rd != 0) {
            cpu.registers.writeRegister(instruction.bytecode.rd, result);
        }
    }
};

// Tests for human errors...
test "Instruction size is 32 bits" {
    try expect(@sizeOf(Instruction) == 4);
}

test "Opcode enum values" {
    try expect(@intFromEnum(Opcode.FREE) == 0);
    try expect(@intFromEnum(Opcode.B) == 1);
    try expect(@intFromEnum(Opcode.LD) == 2);
    try expect(@intFromEnum(Opcode.ST) == 3);
    try expect(@intFromEnum(Opcode.ADD) == 4);
    try expect(@intFromEnum(Opcode.SUB) == 5);
    try expect(@intFromEnum(Opcode.MUL) == 6);
    try expect(@intFromEnum(Opcode.DIV) == 7);
    try expect(@intFromEnum(Opcode.AND) == 8);
    try expect(@intFromEnum(Opcode.OR) == 9);
    try expect(@intFromEnum(Opcode.XOR) == 10);
    try expect(@intFromEnum(Opcode.ROL) == 11);
    try expect(@intFromEnum(Opcode.ROR) == 12);
    try expect(@intFromEnum(Opcode.LSL) == 13);
    try expect(@intFromEnum(Opcode.LSR) == 14);
    try expect(@intFromEnum(Opcode.SWI) == 15);
}

test "Condition enum values" {
    try expect(@intFromEnum(Condition.EQ) == 0);
    try expect(@intFromEnum(Condition.NE) == 1);
    try expect(@intFromEnum(Condition.CS) == 2);
    try expect(@intFromEnum(Condition.CC) == 3);
    try expect(@intFromEnum(Condition.MI) == 4);
    try expect(@intFromEnum(Condition.PL) == 5);
    try expect(@intFromEnum(Condition.VS) == 6);
    try expect(@intFromEnum(Condition.VC) == 7);
    try expect(@intFromEnum(Condition.HI) == 8);
    try expect(@intFromEnum(Condition.LS) == 9);
    try expect(@intFromEnum(Condition.GE) == 10);
    try expect(@intFromEnum(Condition.LT) == 11);
    try expect(@intFromEnum(Condition.GT) == 12);
    try expect(@intFromEnum(Condition.LE) == 13);
    try expect(@intFromEnum(Condition.PR) == 14);
    try expect(@intFromEnum(Condition.A) == 15);
}

test "Mode enum values" {
    try expect(@intFromEnum(Mode.REGISTER_IMM16) == 0);
    try expect(@intFromEnum(Mode.OFFSET_INDEXED) == 1);
}

test "Build an instruction" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);
    // Roundstrip encoding
    const op1 = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R0, 0, 0x1234);
    try expect(op1.raw == 0x20201234);
    cpu.reset(false);
    try expect(Instruction.unpack(0x20201234).raw == Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R0, 0, 0x1234).raw);
}

test "ADD - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // ADD R1 => R1 = R1 + 1
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 1);
    const add_sugar = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R1, 0, 0x0001);
    try Instruction.ADD(&cpu, add_sugar);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 2);

    // ADD R1, R2 => R1 = R1 + R2
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 256);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 256);
    const add_register = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.ADD(&cpu, add_register);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 512);

    // ADD R1, 12 => R1 = R1 + 12
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 256);
    const add_immediate = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R1, 0, 12);
    try Instruction.ADD(&cpu, add_immediate);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == (256 + 12));

    // ADD R1, R2, 12 => R1 = R1 + 12
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 256);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 128);
    const add_registerImmediate = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R1, 0, 12);
    try Instruction.ADD(&cpu, add_registerImmediate);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == (128 + 12));
}

test "ADD - Flag Z (Zero)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0);

    const add_zero = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0000);
    try Instruction.ADD(&cpu, add_zero);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);
}

test "ADD - Flag N (Negative)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x8000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0);

    const add_zero = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0000);
    try Instruction.ADD(&cpu, add_zero);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x8000);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);
}

test "ADD - Flag C (Carry)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x8000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x8001);

    const add_zero = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0000);
    try Instruction.ADD(&cpu, add_zero);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0001);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.C == true);
    try expect(cpu.registers.SR.flags.V == true);
}

test "ADD - Flag V (Overflow)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x4000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x4000);

    const add_zero = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0000);
    try Instruction.ADD(&cpu, add_zero);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x8000);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == true);
}

test "ADD - R0 destination" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // ADD R0, Rs, imm → R0 stays 0, but flags are still updated
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    const add_r0 = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R0, .R1, 0, 0x0001);
    try Instruction.ADD(&cpu, add_r0);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R0)) == 0x0000); // R0 always 0
    try expect(cpu.registers.SR.flags.C == true); // But flags updated
    try expect(cpu.registers.SR.flags.Z == true); // Result would be 0
}

test "ADD - Edge cases" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test: Maximum values
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    const add_max = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R2, .R1, 0, 0xFFFF);
    try Instruction.ADD(&cpu, add_max);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xFFFE); // 0x1FFFE truncated
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.C == true);
    try expect(cpu.registers.SR.flags.V == false);

    // Test: Rs = Rd (self-add)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x0005);
    const add_self = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R3, .R3, 0, 0x0000);
    try Instruction.ADD(&cpu, add_self);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x000A); // Rd = Rd + Rd
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);
}

test "ADC - Basic (ADC behaviour)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Set carry in
    cpu.registers.SR.setFlag(.C);

    // 1 + 1 + carry(1) = 3
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0001);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const addx_basic = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.ADD(&cpu, addx_basic);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0003);
}

test "ADC - Flags N C Z V" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Case A: carry out
    cpu.reset(false);

    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const addx_carry = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.ADD(&cpu, addx_carry);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.C == true);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.V == false);

    // Case B: signed overflow
    cpu.reset(false);
    // Set X flag
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x4000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x4000);
    const addx_of = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.ADD(&cpu, addx_of);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x8000);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.V == true);

    // Case C: overflow with carry-in affecting V
    cpu.reset(false);
    cpu.registers.SR.setFlag(.C);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x7FFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const addx_carryin_of = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.ADD(&cpu, addx_carryin_of);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x8001);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.V == true);
}

test "ADD - Illegal_instruction" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    const add_illegal = Instruction.pack(0, .ADD, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0010);
    try Instruction.ADD(&cpu, add_illegal);
    const check = @as(u16, @intFromEnum(Trap.Illegal_instruction)) |
        @as(u16, @intFromBool(cpu.registers.SR.flags.T)) << 15;
    try expect(cpu.registers.SR.raw == check);
}

test "SUB - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // SUB R4 => SUB R4, R4, 1
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x0010);
    const sub_dec = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R4, .R4, 0, 0x0001);
    try Instruction.SUB(&cpu, sub_dec);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R4)) == 0x000F);

    // SUB R1, R2
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0050);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0020);
    const sub_reg = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.SUB(&cpu, sub_reg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0030);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);

    // SUB R3, 0x1234
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x1234);
    const sub_imm = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R3, .R3, 0, 0x0234);
    try Instruction.SUB(&cpu, sub_imm);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x1000);

    // SUB R5, R6, 0x10
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x0100);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R6), 0x0050);
    const sub_both = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R5, .R6, 0, 0x0010);
    try Instruction.SUB(&cpu, sub_both);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R5)) == 0x0040); // 0x100 - 0x50 - 0x10
}

test "SUB - Flag Z (Zero)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: 0x10 - 0x10 = 0 → Z=1
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0010);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0010);
    const sub_zero = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.SUB(&cpu, sub_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);
}

test "SUB - Flag N (Negative)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: 0x0001 - 0x0002 = 0xFFFF → N=1 (bit 15 set)
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0001);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0002);
    const sub_neg = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.SUB(&cpu, sub_neg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0xFFFF);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.C == true);
    try expect(cpu.registers.SR.flags.V == false);
}

test "SUB - Flag C (Borrow) - ARM style" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: 0x0001 - 0x0002
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0001);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0002);
    const sub_borrow = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.SUB(&cpu, sub_borrow);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0xFFFF);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.C == true);
    try expect(cpu.registers.SR.flags.V == false);

    // Test: 0x0000 - 0x0001
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x0000);
    const sub_borrow2 = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R3, .R3, 0, 0x0001);
    try Instruction.SUB(&cpu, sub_borrow2);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0xFFFF);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.C == true);
    try expect(cpu.registers.SR.flags.V == false);

    // Test: 0x8000 - 0x0001 = 0x7FFF
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x8000);
    const sub_no_borrow = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R5, .R5, 0, 0x0001);
    try Instruction.SUB(&cpu, sub_no_borrow);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R5)) == 0x7FFF);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == true);

    // Test: Equal values
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R6), 0x1234);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R7), 0x1234);
    const sub_equal = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R6, .R7, 0, 0x0000);
    try Instruction.SUB(&cpu, sub_equal);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R6)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);
}

test "SUB - Flag V (Overflow)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: Positive - Negative = overflow → V=1
    // 0x7FFF (32767) - 0xFFFF (-1) = 0x8000 (-32768) → signed overflow!
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x7FFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0xFFFF);
    const sub_overflow1 = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.SUB(&cpu, sub_overflow1);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x8000);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.C == true);
    try expect(cpu.registers.SR.flags.V == true);

    // Test: Negative - Positive = overflow → V=1
    // 0x8000 (-32768) - 0x0001 (1) = 0x7FFF (32767) → signed overflow!
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x8000);
    const sub_overflow2 = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R3, .R3, 0, 0x0001);
    try Instruction.SUB(&cpu, sub_overflow2);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x7FFF);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == true);

    // Test: Positive - Positive = No overflow → V=0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x7FFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R6), 0x1000);
    const sub_no_overflow = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R5, .R6, 0, 0x0000);
    try Instruction.SUB(&cpu, sub_no_overflow);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R5)) == 0x6FFF);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);

    // Test: Negative - Negative = No overflow → V=0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R7), 0x8000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R8), 0xFFFF);
    const sub_no_overflow2 = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R7, .R8, 0, 0x0000);
    try Instruction.SUB(&cpu, sub_no_overflow2);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R7)) == 0x8001);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.C == true);
    try expect(cpu.registers.SR.flags.V == false);
}

test "SUB - R0 destination (void write)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // SUB R0, Rs, imm → R0 stays 0, but flags are still updated
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0010);
    const sub_r0 = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R0, .R1, 0, 0x0005);
    try Instruction.SUB(&cpu, sub_r0);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R0)) == 0x0000); // R0 always 0
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);
}

test "SUB - Edge cases" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test: Subtract from zero
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0000);
    const sub_from_zero = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R1, 0, 0x0001);
    try Instruction.SUB(&cpu, sub_from_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0xFFFF);
    try expect(cpu.registers.SR.flags.C == true);

    // Test: Maximum underflow
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xFFFF);
    const sub_max = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R2, .R3, 0, 0x0000);
    try Instruction.SUB(&cpu, sub_max);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0001);
    try expect(cpu.registers.SR.flags.C == true);

    // Test: Self-subtract → result = 0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0xABCD);
    const sub_self = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R4, .R4, 0, 0x0000);
    try Instruction.SUB(&cpu, sub_self);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R4)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.C == false); // No borrow (equal values)
}

test "SUB - Illegal mode" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    const add_illegal = Instruction.pack(0, .SUB, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0010);
    try Instruction.ADD(&cpu, add_illegal);
    const check = @as(u16, @intFromEnum(Trap.Illegal_instruction)) |
        @as(u16, @intFromBool(cpu.registers.SR.flags.T)) << 15;
    try expect(cpu.registers.SR.raw == check);
}

test "SBC - Basic (SBC behaviour)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    cpu.registers.SR.setFlag(.C);

    // Assume SBC subtracts carry-in as extra 1: 2 - 1 - 1 = 0
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0002);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const subx_basic = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.SUB(&cpu, subx_basic);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000);
}

test "SBC - Flags N C Z V" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Case A: borrow occurs -> 0 - 1 - 1 = 0xFFFE
    cpu.reset(false);
    cpu.registers.SR.setFlag(.C);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const subx_borrow = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.SUB(&cpu, subx_borrow);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0xFFFE);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.C == true);
    try expect(cpu.registers.SR.flags.V == false);

    // Case B: result zero -> 2 - 1 - 1 = 0
    cpu.reset(false);
    cpu.registers.SR.setFlag(.C);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0002);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const subx_zero = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.SUB(&cpu, subx_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);

    // Case C: signed overflow example -> 0x8000 - 1 - 1 = 0x7FFE (overflow)
    cpu.reset(false);
    cpu.registers.SR.setFlag(.C);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x8000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const subx_of = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.SUB(&cpu, subx_of);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x7FFE);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == true);
}

test "MUL - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test 1: MUL Rd, Rs, imm16 → Rd = Rs * imm16
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0010);
    const mul_imm = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0003);
    try Instruction.MUL(&cpu, mul_imm);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0030);

    // Test 2: MUL Rd, imm (Rs=R0) → Rd = 0 * imm = 0
    cpu.reset(false);
    const mul_zero = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R3, .R3, 0, 0x1234);
    try Instruction.MUL(&cpu, mul_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x0000);

    // Test 3: Simple multiplication
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x000A); // 10
    const mul_simple = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R5, .R4, 0, 0x0005); // 10 * 5
    try Instruction.MUL(&cpu, mul_simple);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R5)) == 0x0032); // 50
}

test "MUL - Flag Z (Zero)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: 0 * anything = 0 → Z=1
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0000);
    const mul_zero1 = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R2, .R1, 0, 0xFFFF);
    try Instruction.MUL(&cpu, mul_zero1);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);

    // Test: anything * 0 = 0 → Z=1
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xFFFF);
    const mul_zero2 = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x0000);
    try Instruction.MUL(&cpu, mul_zero2);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R4)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
}

test "MUL - Flag N (Negative)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: Result with bit 15 set → N=1
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x4000); // 16384
    const mul_neg = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0002);
    try Instruction.MUL(&cpu, mul_neg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x8000); // 32768, bit 15 set
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.Z == false);
}

test "MUL - Flag V (Overflow)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: Result > 0xFFFF → V=1 (overflow)
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0100); // 256
    const mul_overflow1 = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0100); // 256 * 256 = 65536
    try Instruction.MUL(&cpu, mul_overflow1);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000); // Truncated to 16 bits
    try expect(cpu.registers.SR.flags.V == true);
    try expect(cpu.registers.SR.flags.Z == true); // Result is 0 after truncation

    // Test: Large multiplication with overflow
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xFFFF); // 65535
    const mul_overflow2 = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x0002); // 65535 * 2 = 131070
    try Instruction.MUL(&cpu, mul_overflow2);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R4)) == 0xFFFE); // 131070 & 0xFFFF
    try expect(cpu.registers.SR.flags.V == true);

    // Test: Just at the edge (no overflow)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x00FF); // 255
    const mul_no_overflow = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R6, .R5, 0, 0x00FF); // 255 * 255 = 65025
    try Instruction.MUL(&cpu, mul_no_overflow);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R6)) == 0xFE01); // 65025
    try expect(cpu.registers.SR.flags.V == false); // Fits in 16 bits
}

test "MUL - R0 destination (void write)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // MUL R0, Rs, imm → R0 stays 0, but flags are still updated
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0100);
    const mul_r0 = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R0, .R1, 0, 0x0100);
    try Instruction.MUL(&cpu, mul_r0);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R0)) == 0x0000); // R0 always 0
    try expect(cpu.registers.SR.flags.V == true); // But flags updated (overflow)
}

test "MUL - Edge cases" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test: Multiply by 1 (identity)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xABCD);
    const mul_one = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0001);
    try Instruction.MUL(&cpu, mul_one);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xABCD);
    try expect(cpu.registers.SR.flags.V == false);

    // Test: Maximum value * 1 (no overflow)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xFFFF);
    const mul_max = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x0001);
    try Instruction.MUL(&cpu, mul_max);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R4)) == 0xFFFF);
    try expect(cpu.registers.SR.flags.V == false);

    // Test: Small values
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x0002);
    const mul_small = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R6, .R5, 0, 0x0003);
    try Instruction.MUL(&cpu, mul_small);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R6)) == 0x0006);
}

test "MUL - Illegal mode" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // MUL doesn't support OFFSET_INDEXED mode
    const mul_illegal = Instruction.pack(0, .MUL, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0010);
    try Instruction.MUL(&cpu, mul_illegal);
    try expect(cpu.registers.SR.flags.T == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));
}

test "MULX - (32-bit result)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Example: 0xFFFF * 0x0002 = 0x0001_FFFE
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0002);
    const mul_with_x = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.MUL(&cpu, mul_with_x);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0001); // MSB
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xFFFE); // LSB
}

test "MULX - Flags Z N C V" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Case 1: Zero result -> Z=1, N=0, V=0, C=0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x1234);
    const mulx_zero = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.MUL(&cpu, mulx_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.V == false);
    try expect(cpu.registers.SR.flags.C == false);

    // Case 2: Small product (no overflow) -> Z=0, N=0, V=0, C=0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x1234);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0002);
    const mulx_small = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.MUL(&cpu, mulx_small);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000); // hi
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x2468); // lo
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.V == false);
    try expect(cpu.registers.SR.flags.C == false);

    // Case 3: Overflow but not MSB of 32-bit -> V=1, C=1, N=0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0002);
    const mulx_of = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.MUL(&cpu, mulx_of);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0001);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xFFFE);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.V == true);
    try expect(cpu.registers.SR.flags.C == true);

    // Case 4: Large product with MSB set -> N=1, V=1, C=1
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0xFFFF);
    const mulx_big = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.MUL(&cpu, mulx_big);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0xFFFE);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0001);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.V == true);
    try expect(cpu.registers.SR.flags.C == true);
}

test "DIV - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test 1: DIV Rd, Rs → Rd = Rd / Rs
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0064); // 100
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x000A); // 10
    const div_reg = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.DIV(&cpu, div_reg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x000A); // 100 / 10 = 10

    // Test 2: DIV Rd, imm (Rs=R0) → Rd = Rd / imm
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x0078); // 120
    const div_imm = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R3, .R3, 0, 0x000C); // 120 / 12
    try Instruction.DIV(&cpu, div_imm);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x000A); // 10

    // Test 3: DIV with remainder discarded
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x000A); // 10
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x0003); // 3
    const div_remainder = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R4, .R5, 0, 0x0000);
    try Instruction.DIV(&cpu, div_remainder);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R4)) == 0x0003); // 10 / 3 = 3 (remainder 1 discarded)

}

test "DIV - Flag Z (Zero)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: 0 / anything = 0 → Z=1
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x000A);
    const div_zero = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.DIV(&cpu, div_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);

    // Test: Dividend < Divisor → quotient = 0 → Z=1
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x0005); // 5
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x000A); // 10
    const div_small = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R3, .R4, 0, 0x0000); // 5 / 10 = 0
    try Instruction.DIV(&cpu, div_small);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
}

test "DIV - Flag N (Negative)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: Result with bit 15 set → N=1
    // 0xFFFF (65535) / 0x0001 (1) = 0xFFFF (bit 15 set)
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    const div_neg = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R1, 0, 0x0001);
    try Instruction.DIV(&cpu, div_neg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0xFFFF);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.Z == false);

    // Test: 0x8000 / 0x0001 = 0x8000 → N=1
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x8000);
    const div_neg2 = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R2, .R2, 0, 0x0001);
    try Instruction.DIV(&cpu, div_neg2);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x8000);
    try expect(cpu.registers.SR.flags.N == true);
}

test "DIV - Division by zero" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: Divide by zero → error + V=1 + T=1
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0064);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0000);
    const div_by_zero = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.DIV(&cpu, div_by_zero);
    try expect(cpu.registers.SR.flags.T == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Division_by_zero));
}

test "DIV - R0 destination (void write)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // DIV R0, Rs, imm → R0 stays 0, but flags are still updated
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x000A);
    const div_r0 = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R0, .R1, 0, 0x0000);
    try Instruction.DIV(&cpu, div_r0);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R0)) == 0x0000); // R0 always 0
    try expect(cpu.registers.SR.flags.Z == true); // But flags updated (0 / 10 = 0)
}

test "DIVX - Store remainder" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Example: 100 / 30 = 3 remainder 10
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0064); // 100
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x001E); // 30
    const div_with_x = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.DIV(&cpu, div_with_x);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0003); // quotient
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x000A); // remainder (100 - 3*30 = 10)
}

test "DIVX - Flags Z N C V" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Case 1: Zero dividend -> Z=1, N=0, V=0, C=0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x1234);
    const divx_zero = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.DIV(&cpu, divx_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.V == false);
    try expect(cpu.registers.SR.flags.C == false);

    // Case 2: 100 / 30 -> quotient 3, remainder 10 -> Z=0, N=0, V=0, C=0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0064);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x001E);
    const divx_small = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.DIV(&cpu, divx_small);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0003);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x000A);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.V == false);
    try expect(cpu.registers.SR.flags.C == false);

    // Case 3: MSB set in quotient -> N=1
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x8000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const divx_msb = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.DIV(&cpu, divx_msb);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x8000);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.V == false);
    try expect(cpu.registers.SR.flags.C == false);

    // Case 4: Dividend equals divisor -> quotient 1, remainder 0 -> Z=0, N=0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0xFFFF);
    const divx_eq = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.DIV(&cpu, divx_eq);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0001);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.V == false);
    try expect(cpu.registers.SR.flags.C == false);
}

test "DIV - Edge cases" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test: Divide by 1 (identity)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xABCD);
    const div_one = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R1, 0, 0x0001);
    try Instruction.DIV(&cpu, div_one);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0xABCD);

    // Test: Self-divide → result = 1
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0042);
    const div_self = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R2, .R2, 0, 0x0000);
    try Instruction.DIV(&cpu, div_self);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0001); // 0x42 / 0x42 = 1

    // Test: Maximum value / 2
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xFFFF);
    const div_max = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R3, .R3, 0, 0x0002);
    try Instruction.DIV(&cpu, div_max);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x7FFF); // 65535 / 2 = 32767

    // Test: Large dividend, large divisor
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0xFFFF); // 65535
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0xFFFF); // 65535
    const div_equal = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R4, .R5, 0, 0x0000);
    try Instruction.DIV(&cpu, div_equal);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R4)) == 0x0001); // 65535 / 65535 = 1
}

test "DIV - Illegal mode" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // DIV doesn't support OFFSET_INDEXED mode
    const div_illegal = Instruction.pack(0, .DIV, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0010);
    try Instruction.DIV(&cpu, div_illegal);
    try expect(cpu.registers.SR.flags.T == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));
}

test "AND - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test 1: AND Rd, Rs, imm16 → Rd = Rs & imm16
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0xFF0F);
    const and_imm = Instruction.pack(0, .AND, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x00FF);
    try Instruction.AND(&cpu, and_imm);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x000F);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.C == false); // Cleared
    try expect(cpu.registers.SR.flags.V == false); // Cleared

    // Test 2: AND with all bits set
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xABCD);
    const and_all = Instruction.pack(0, .AND, .REGISTER_IMM16, 0, .R4, .R3, 0, 0xFFFF);
    try Instruction.AND(&cpu, and_all);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R4)) == 0xABCD);

    // Test 3: Mask operation
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x1234);
    const and_mask = Instruction.pack(0, .AND, .REGISTER_IMM16, 0, .R6, .R5, 0, 0x0F0F);
    try Instruction.AND(&cpu, and_mask);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R6)) == 0x0204);
}

test "AND - Flag Z (Zero)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: No common bits → Z=1
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFF00);
    const and_zero = Instruction.pack(0, .AND, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x00FF);
    try Instruction.AND(&cpu, and_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);
}

test "AND - Flag N (Negative)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: Result with bit 15 set → N=1
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    const and_neg = Instruction.pack(0, .AND, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x8000);
    try Instruction.AND(&cpu, and_neg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x8000);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.Z == false);
}

test "AND - R0 destination and illegal mode" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // AND R0, Rs, imm → R0 stays 0, but flags updated
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    const and_r0 = Instruction.pack(0, .AND, .REGISTER_IMM16, 0, .R0, .R1, 0, 0xFFFF);
    try Instruction.AND(&cpu, and_r0);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R0)) == 0x0000);
    try expect(cpu.registers.SR.flags.N == true); // Flags still updated

    // Illegal mode
    cpu.reset(false);
    const and_illegal = Instruction.pack(0, .AND, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0010);
    try Instruction.AND(&cpu, and_illegal);
    try expect(cpu.registers.SR.flags.T == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));
}

test "OR - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test 1: OR Rd, Rs, imm16 → Rd = Rs | imm16
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x00F0);
    const or_imm = Instruction.pack(0, .OR, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0F00);
    try Instruction.OR(&cpu, or_imm);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0FF0);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.C == false); // Cleared
    try expect(cpu.registers.SR.flags.V == false); // Cleared

    // Test 2: OR with zero (identity)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xABCD);
    const or_zero = Instruction.pack(0, .OR, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x0000);
    try Instruction.OR(&cpu, or_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R4)) == 0xABCD);

    // Test 3: Set bits
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x1200);
    const or_set = Instruction.pack(0, .OR, .REGISTER_IMM16, 0, .R6, .R5, 0, 0x0034);
    try Instruction.OR(&cpu, or_set);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R6)) == 0x1234);
}

test "OR - Flag Z (Zero)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: 0 | 0 = 0 → Z=1
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0000);
    const or_zero = Instruction.pack(0, .OR, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0000);
    try Instruction.OR(&cpu, or_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);
}

test "OR - Flag N (Negative)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: Result with bit 15 set → N=1
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x7000);
    const or_neg = Instruction.pack(0, .OR, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x8000);
    try Instruction.OR(&cpu, or_neg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xF000);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.Z == false);
}

test "OR - R0 destination and illegal mode" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // OR R0, Rs, imm → R0 stays 0, but flags updated
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x8000);
    const or_r0 = Instruction.pack(0, .OR, .REGISTER_IMM16, 0, .R0, .R1, 0, 0x0001);
    try Instruction.OR(&cpu, or_r0);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R0)) == 0x0000);
    try expect(cpu.registers.SR.flags.N == true); // Flags still updated

    // Illegal mode
    cpu.reset(false);
    const or_illegal = Instruction.pack(0, .OR, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0010);
    try Instruction.OR(&cpu, or_illegal);
    try expect(cpu.registers.SR.flags.T == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));
}

test "XOR - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test 1: XOR Rd, Rs, imm16 → Rd = Rs ^ imm16
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0xFFFF);
    const xor_imm = Instruction.pack(0, .XOR, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x00FF);
    try Instruction.XOR(&cpu, xor_imm);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0xFF00);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == true); // Bit 15 set
    try expect(cpu.registers.SR.flags.C == false); // Cleared
    try expect(cpu.registers.SR.flags.V == false); // Cleared

    // Test 2: XOR with zero (identity)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xABCD);
    const xor_zero = Instruction.pack(0, .XOR, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x0000);
    try Instruction.XOR(&cpu, xor_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R4)) == 0xABCD);

    // Test 3: Toggle bits
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x1234);
    const xor_toggle = Instruction.pack(0, .XOR, .REGISTER_IMM16, 0, .R6, .R5, 0, 0xFFFF);
    try Instruction.XOR(&cpu, xor_toggle);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R6)) == 0xEDCB); // Inverted
}

test "XOR - Flag Z (Zero)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: Same value XOR → Z=1 (self-cancel)
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x1234);
    const xor_zero = Instruction.pack(0, .XOR, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x1234);
    try Instruction.XOR(&cpu, xor_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);
}

test "XOR - Flag N (Negative)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Test: Result with bit 15 set → N=1
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x7FFF);
    const xor_neg = Instruction.pack(0, .XOR, .REGISTER_IMM16, 0, .R2, .R1, 0, 0xFFFF);
    try Instruction.XOR(&cpu, xor_neg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x8000);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.Z == false);
}

test "XOR - R0 destination and illegal mode" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // XOR R0, Rs, imm → R0 stays 0, but flags updated
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    const xor_r0 = Instruction.pack(0, .XOR, .REGISTER_IMM16, 0, .R0, .R1, 0, 0x7FFF);
    try Instruction.XOR(&cpu, xor_r0);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R0)) == 0x0000);
    try expect(cpu.registers.SR.flags.N == true); // Flags still updated (result would be 0x8000)

    // Illegal mode
    cpu.reset(false);
    const xor_illegal = Instruction.pack(0, .XOR, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0010);
    try Instruction.XOR(&cpu, xor_illegal);
    try expect(cpu.registers.SR.flags.T == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));
}

test "ROL - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // ROL R1, R2 => R1 = R1 rotated left by R2
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0b1010_0000_0000_0001);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 4);
    const rol_reg = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.ROL(&cpu, rol_reg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0b0000_0000_0001_1010); // 4 bits rotated left

    // ROL R3, R4, 8 => R3 = R4 rotated left by 8
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x1234);
    const rol_imm = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R3, .R4, 0, 8);
    try Instruction.ROL(&cpu, rol_imm);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x3412); // Swap bytes
}

test "ROL - Flag NZCV" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test N flag (negative result)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x4000);
    const rol_n = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R1, .R1, 0, 1);
    try Instruction.ROL(&cpu, rol_n);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x8000);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);

    // Test Z flag (zero result)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0000);
    const rol_z = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R2, .R2, 0, 5);
    try Instruction.ROL(&cpu, rol_z);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);

    // Test C flag (carry from rotation)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x8000);
    const rol_c = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R3, .R3, 0, 1);
    try Instruction.ROL(&cpu, rol_c);
    try expect(cpu.registers.SR.flags.C == true); // Bit 15 rotated out
}

test "ROL - Edge Case" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Rotate by 0 (no change) - when imm16=0, uses Rs as shift amount
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x1234);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0); // R2 contains 0
    const rol_zero = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R1, .R2, 0, 0);
    try Instruction.ROL(&cpu, rol_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x1234);

    // Rotate by 16 (full rotation, masked to 0)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x5678);
    const rol_16 = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R2, .R2, 0, 16);
    try Instruction.ROL(&cpu, rol_16);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x5678); // Same value

    // Rotate with value > 15 (masked to 0x0F)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xFF00);
    const rol_masked = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R3, .R3, 0, 0x1F); // 31 masked to 15
    try Instruction.ROL(&cpu, rol_masked);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x7F80);
}

test "ROL - R0 as destination and Illegal Mode" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // R0 destination should remain 0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    const rol_r0 = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R0, .R1, 0, 8);
    try Instruction.ROL(&cpu, rol_r0);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R0)) == 0x0000);

    // Illegal mode should set trap
    cpu.reset(false);
    const rol_illegal = Instruction.pack(0, .ROL, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0);
    try Instruction.ROL(&cpu, rol_illegal);
    try expect(cpu.registers.SR.flags.T == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));
}

test "ROR - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // ROR R1, R2 => R1 = R1 rotated right by R2
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0b1010_0000_0000_0001);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 4);
    const ror_reg = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.ROR(&cpu, ror_reg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0b0001_1010_0000_0000); // 4 bits rotated right

    // ROR R3, R4, 8 => R3 = R4 rotated right by 8
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x1234);
    const ror_imm = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R3, .R4, 0, 8);
    try Instruction.ROR(&cpu, ror_imm);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x3412); // Swap bytes
}

test "ROR - Flag NZCV" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test N flag (negative result)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0001);
    const ror_n = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R1, .R1, 0, 1);
    try Instruction.ROR(&cpu, ror_n);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x8000);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.C == true); // Bit 0 rotated out
    try expect(cpu.registers.SR.flags.V == false);

    // Test Z flag (zero result)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0000);
    const ror_z = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R2, .R2, 0, 5);
    try Instruction.ROR(&cpu, ror_z);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);

    // Test C flag (carry from rotation)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x000F);
    const ror_c = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R3, .R3, 0, 1);
    try Instruction.ROR(&cpu, ror_c);
    try expect(cpu.registers.SR.flags.C == true); // Bit 0 rotated out
}

test "ROR - Edge Case" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Rotate by 0 (no change) - when imm16=0, uses Rs as shift amount
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x1234);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0); // R2 contains 0
    const ror_zero = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R1, .R2, 0, 0);
    try Instruction.ROR(&cpu, ror_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x1234);

    // Rotate by 16 (full rotation, masked to 0)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x5678);
    const ror_16 = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R2, .R2, 0, 16);
    try Instruction.ROR(&cpu, ror_16);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x5678); // Same value

    // Rotate with value > 15 (masked to 0x0F)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x00FF);
    const ror_masked = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R3, .R3, 0, 0x1F); // 31 masked to 15
    try Instruction.ROR(&cpu, ror_masked);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x01FE); // 0x00FF rotated right 15 = 0x01FE
}

test "ROR - R0 as destination and Illegal Mode" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // R0 destination should remain 0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    const ror_r0 = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R0, .R1, 0, 8);
    try Instruction.ROR(&cpu, ror_r0);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R0)) == 0x0000);

    // Illegal mode should set trap
    cpu.reset(false);
    const ror_illegal = Instruction.pack(0, .ROR, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0);
    try Instruction.ROR(&cpu, ror_illegal);
    try expect(cpu.registers.SR.flags.T == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));
}

test "LSL - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // LSL R1, R2 => R1 = R1 shifted left by R2
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0b0000_0000_0000_1111);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 4);
    const lsl_reg = Instruction.pack(0, .LSL, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.LSL(&cpu, lsl_reg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0b0000_0000_1111_0000); // Shifted left 4

    // LSL R3, R4, 8 => R3 = R4 shifted left by 8
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x0012);
    const lsl_imm = Instruction.pack(0, .LSL, .REGISTER_IMM16, 0, .R3, .R4, 0, 8);
    try Instruction.LSL(&cpu, lsl_imm);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x1200);
}

test "LSL - Flag NZCV" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test N flag (negative result)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x4000);
    const lsl_n = Instruction.pack(0, .LSL, .REGISTER_IMM16, 0, .R1, .R1, 0, 1);
    try Instruction.LSL(&cpu, lsl_n);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x8000);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);

    // Test Z flag (zero result from shift out)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const lsl_z = Instruction.pack(0, .LSL, .REGISTER_IMM16, 0, .R2, .R2, 0, 15);
    try Instruction.LSL(&cpu, lsl_z);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x8000);
    try expect(cpu.registers.SR.flags.N == true);

    // Test C flag (carry from shift)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x8000);
    const lsl_c = Instruction.pack(0, .LSL, .REGISTER_IMM16, 0, .R3, .R3, 0, 1);
    try Instruction.LSL(&cpu, lsl_c);
    try expect(cpu.registers.SR.flags.C == true); // Bit 15 shifted out
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
}

test "LSL - Edge Case" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Shift by 0 (no change) - when imm16=0, uses Rs as shift amount
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x1234);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0); // R2 contains 0
    const lsl_zero = Instruction.pack(0, .LSL, .REGISTER_IMM16, 0, .R1, .R2, 0, 0);
    try Instruction.LSL(&cpu, lsl_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x1234);

    // Shift by 16 (masked to 0, no change)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x5678);
    const lsl_16 = Instruction.pack(0, .LSL, .REGISTER_IMM16, 0, .R2, .R2, 0, 16);
    try Instruction.LSL(&cpu, lsl_16);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x5678);

    // Shift all bits out
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xFFFF);
    const lsl_all = Instruction.pack(0, .LSL, .REGISTER_IMM16, 0, .R3, .R3, 0, 15);
    try Instruction.LSL(&cpu, lsl_all);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x8000);
}

test "LSL - R0 as destination and Illegal Mode" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // R0 destination should remain 0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    const lsl_r0 = Instruction.pack(0, .LSL, .REGISTER_IMM16, 0, .R0, .R1, 0, 4);
    try Instruction.LSL(&cpu, lsl_r0);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R0)) == 0x0000);

    // Illegal mode should set trap
    cpu.reset(false);
    const lsl_illegal = Instruction.pack(0, .LSL, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0);
    try Instruction.LSL(&cpu, lsl_illegal);
    try expect(cpu.registers.SR.flags.T == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));
}

test "LSR - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // LSR R1, R2 => R1 = R1 shifted right by R2
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0b1111_0000_0000_0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 4);
    const lsr_reg = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.LSR(&cpu, lsr_reg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0b0000_1111_0000_0000); // Shifted right 4

    // LSR R3, R4, 8 => R3 = R4 shifted right by 8
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x1200);
    const lsr_imm = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R3, .R4, 0, 8);
    try Instruction.LSR(&cpu, lsr_imm);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x0012);
}

test "LSR - Flag NZCV" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test N flag (should not be set for logical shift)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x8000);
    const lsr_n = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R1, .R1, 0, 1);
    try Instruction.LSR(&cpu, lsr_n);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x4000);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);

    // Test Z flag (zero result)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const lsr_z = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R2, .R2, 0, 1);
    try Instruction.LSR(&cpu, lsr_z);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.C == true); // Bit 0 shifted out

    // Test C flag (carry from shift)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x000F);
    const lsr_c = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R3, .R3, 0, 1);
    try Instruction.LSR(&cpu, lsr_c);
    try expect(cpu.registers.SR.flags.C == true); // Bit 0 shifted out
}

test "LSR - Edge Case" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Shift by 0 (no change) - when imm16=0, uses Rs as shift amount
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x1234);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0); // R2 contains 0
    const lsr_zero = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R1, .R2, 0, 0);
    try Instruction.LSR(&cpu, lsr_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x1234);

    // Shift by 16 (masked to 0, no change)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x5678);
    const lsr_16 = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R2, .R2, 0, 16);
    try Instruction.LSR(&cpu, lsr_16);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x5678);

    // Shift all bits out
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xFFFF);
    const lsr_all = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R3, .R3, 0, 15);
    try Instruction.LSR(&cpu, lsr_all);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x0001);
}

test "LSR - R0 as destination and Illegal Mode" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // R0 destination should remain 0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    const lsr_r0 = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R0, .R1, 0, 4);
    try Instruction.LSR(&cpu, lsr_r0);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R0)) == 0x0000);

    // Illegal mode should set trap
    cpu.reset(false);
    const lsr_illegal = Instruction.pack(0, .LSR, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0);
    try Instruction.LSR(&cpu, lsr_illegal);
    try expect(cpu.registers.SR.flags.T == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));
}

test "ASR - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // ASR (via ASR) R1, R2 => R1 = R1 arithmetically shifted right by R2
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xF000); // Negative number
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 4);
    const asr_reg = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R1, .R2, 1, 0x0000);
    try Instruction.LSR(&cpu, asr_reg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0xFF00); // Sign extended

    // ASR R3, R4, 8 => R3 = R4 arithmetically shifted right by 8
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x8000); // Most negative
    const asr_imm = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R3, .R4, 1, 8);
    try Instruction.LSR(&cpu, asr_imm);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0xFF80); // Sign extended
}

test "ASR - Flag NZCV" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test N flag (negative result preserved)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x8000);
    const asr_n = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R1, .R1, 1, 1);
    try Instruction.LSR(&cpu, asr_n);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0xC000); // Sign preserved
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);

    // Test Z flag (shift positive to zero)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const asr_z = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R2, .R2, 1, 1);
    try Instruction.LSR(&cpu, asr_z);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.C == true); // Bit 0 shifted out

    // Test C flag (carry from shift)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xFFFF); // All ones
    const asr_c = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R3, .R3, 1, 1);
    try Instruction.LSR(&cpu, asr_c);
    try expect(cpu.registers.SR.flags.C == true); // Bit 0 shifted out
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0xFFFF); // Still all ones
}

test "ASR - Edge Case" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Shift by 0 (no change) - when imm16=0, uses Rs as shift amount
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x8234);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0); // R2 contains 0
    const asr_zero = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R1, .R2, 1, 0);
    try Instruction.LSR(&cpu, asr_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x8234);

    // Shift negative number by 15 (all ones or sign bit)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x8000);
    const asr_15 = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R2, .R2, 1, 15);
    try Instruction.LSR(&cpu, asr_15);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xFFFF); // All bits set to sign

    // Shift positive number (should behave like LSR)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x7FFF); // Positive
    const asr_pos = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R3, .R3, 1, 4);
    try Instruction.LSR(&cpu, asr_pos);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x07FF); // Zero-filled
}

test "ASR - R0 as destination and Illegal Mode" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // R0 destination should remain 0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    const asr_r0 = Instruction.pack(0, .LSR, .REGISTER_IMM16, 0, .R0, .R1, 1, 4);
    try Instruction.LSR(&cpu, asr_r0);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R0)) == 0x0000);

    // Illegal mode should set trap
    cpu.reset(false);
    const asr_illegal = Instruction.pack(0, .LSR, .OFFSET_INDEXED, 0, .R1, .R2, 1, 0);
    try Instruction.LSR(&cpu, asr_illegal);
    try expect(cpu.registers.SR.flags.T == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));
}

test "LD - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // LD R2, 0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 2);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 4);
    const ld_0 = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R2, .R0, 0, 0x0000);
    try Instruction.LD(&cpu, ld_0);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0);

    // LD R2, R0
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 2);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 4);
    const ld_R0 = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R2, .R0, 0, 0x0000);
    try Instruction.LD(&cpu, ld_R0);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0);

    // LD R2, R1
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 2);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 4);
    const ld_instruction = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0000);
    try Instruction.LD(&cpu, ld_instruction);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 2);

    // LD R2, 0xBEEF
    cpu.reset(false);
    const ld_beef = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R2, .R0, 0, 0xBEEF);
    try Instruction.LD(&cpu, ld_beef);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xBEEF);

    // LD -(SP), R1
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 2);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 4);
    const ld_push = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R14, .R1, 0, 0x0000);
    try Instruction.LD(&cpu, ld_push);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R14)) == 0xFFFC);
    try expect(cpu.ram.read16(cpu.registers.readRegister(@intFromEnum(RegistersName.R14))) == 0x0002);

    // LD R2, (SP)+
    const ld_pop = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R2, .R14, 0, 0x0000);
    try Instruction.LD(&cpu, ld_pop);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R14)) == 0xFFFE);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0002);

    // LD -(SP), 0xDEAD
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 2);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 4);
    const ld_push_dead = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R14, .R0, 0, 0xDEAD);
    try Instruction.LD(&cpu, ld_push_dead);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R14)) == 0xFFFC);
    try expect(cpu.ram.read16(cpu.registers.readRegister(@intFromEnum(RegistersName.R14))) == 0xDEAD);

    // LD R2, (SP)+
    const ld_pop_dead = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R2, .R14, 0, 0x0000);
    try Instruction.LD(&cpu, ld_pop_dead);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R14)) == 0xFFFE);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xDEAD);

    // LD R2, 2(R1)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 2);
    cpu.ram.write16(0x0002, 0xDEAD);
    cpu.ram.write16(0x0004, 0xBEEF);
    const ld_offset = Instruction.pack(0, .LD, .OFFSET_INDEXED, 0, .R2, .R1, 0, 0x0002);
    try Instruction.LD(&cpu, ld_offset);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xBEEF);
}

test "LD - Edge cases and illegal operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Edge Case: LD PC, * (should be illegal - loading into PC)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xDEAD);
    const ld_to_pc = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R15, .R1, 0, 0x0000);
    try Instruction.LD(&cpu, ld_to_pc);
    try expect(cpu.registers.SR.getFlag(.T) == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));

    // Edge Case: LD PC, 0xBEEF (immediate to PC - should be illegal)
    cpu.reset(false);
    const ld_imm_to_pc = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R15, .R0, 0, 0xBEEF);
    try Instruction.LD(&cpu, ld_imm_to_pc);
    try expect(cpu.registers.SR.getFlag(.T) == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));

    // Edge Case: LD SP, SP (should be illegal - SP to SP)
    cpu.reset(false);
    const original_sp = cpu.registers.readRegister(@intFromEnum(RegistersName.R14));
    const ld_sp_sp = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R14, .R14, 0, 0x0000);
    try Instruction.LD(&cpu, ld_sp_sp);
    try expect(cpu.registers.SR.getFlag(.T) == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R14)) == original_sp); // SP unchanged

    // Edge Case: LD R2, R1, IMM16 (all three different - should be illegal)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x1111);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x2222);
    const ld_three_operands = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0042);
    try Instruction.LD(&cpu, ld_three_operands);
    try expect(cpu.registers.SR.getFlag(.T) == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x2222); // R2 unchanged

    // Edge Case: Stack overflow - multiple pushes
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xAAAA);
    const initial_sp = cpu.registers.SP;

    // Push 3 times
    for (0..3) |_| {
        const ld_push = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R14, .R1, 0, 0x0000);
        try Instruction.LD(&cpu, ld_push);
    }

    try expect(cpu.registers.SP == initial_sp -% 6); // SP decreased by 6 (3 * 2 bytes)
    try expect(cpu.ram.read16(cpu.registers.SP) == 0xAAAA);
    try expect(cpu.ram.read16(cpu.registers.SP +% 2) == 0xAAAA);
    try expect(cpu.ram.read16(cpu.registers.SP +% 4) == 0xAAAA);

    // Edge Case: Stack underflow - multiple pops
    // Pop 3 times back
    for (0..3) |_| {
        const ld_pop = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R2, .R14, 0, 0x0000);
        try Instruction.LD(&cpu, ld_pop);
    }

    try expect(cpu.registers.SP == initial_sp); // SP back to original
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xAAAA);

    // Edge Case: LD with maximum immediate value
    cpu.reset(false);
    const ld_max_imm = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R3, .R0, 0, 0xFFFF);
    try Instruction.LD(&cpu, ld_max_imm);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0xFFFF);

    // Edge Case: OFFSET_INDEXED with zero offset
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x1000);
    cpu.ram.write16(0x1000, 0xCAFE);
    const ld_zero_offset = Instruction.pack(0, .LD, .OFFSET_INDEXED, 0, .R2, .R1, 0, 0x0000);
    try Instruction.LD(&cpu, ld_zero_offset);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xCAFE);

    // Edge Case: OFFSET_INDEXED with maximum offset causing address wraparound
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0010);
    cpu.ram.write16(0x000F, 0xBABE); // Wraparound: 0x0010 + 0xFFFF = 0x000F
    const ld_max_offset = Instruction.pack(0, .LD, .OFFSET_INDEXED, 0, .R2, .R1, 0, 0xFFFF);
    try Instruction.LD(&cpu, ld_max_offset);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xBABE);

    // Edge Case: OFFSET_INDEXED loading into same register as base
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x2000);
    cpu.ram.write16(0x2004, 0xFACE);
    const ld_same_reg = Instruction.pack(0, .LD, .OFFSET_INDEXED, 0, .R1, .R1, 0, 0x0004);
    try Instruction.LD(&cpu, ld_same_reg);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0xFACE);

    // Edge Case: Push immediate zero
    cpu.reset(false);
    const sp_before = cpu.registers.SP;
    const ld_push_zero = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R14, .R0, 0, 0x0000);
    try Instruction.LD(&cpu, ld_push_zero);
    try expect(cpu.registers.SP == sp_before -% 2);
    try expect(cpu.ram.read16(cpu.registers.SP) == 0x0000);

    // Edge Case: LD R0, R1
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x5555);
    const ld_to_r0 = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R0, .R1, 0, 0x0000);
    try Instruction.LD(&cpu, ld_to_r0);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R0)) == 0x0000);

    // Edge Case: LD Rd, Rd (self-assignment with register mode)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x7777);
    const ld_self = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R3, .R3, 0, 0x0000);
    try Instruction.LD(&cpu, ld_self);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x7777); // Should remain unchanged
}

test "LDM - Load Multiple (Push Multiple)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test: LDM -(SP), {R1,R2,R6}
    // Register list: R1 (bit 1), R2 (bit 2), R6 (bit 6)
    // Bitmask: 0b0000_0000_0100_0110 = 0x0046
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x1111);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x2222);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R6), 0x6666);
    const initial_sp = cpu.registers.SP;

    // LDM -(SP), {R1,R2,R6}: rd=SP(14), rs=0, fl=1, imm=0x0046
    const ldm_push = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R14, .R0, 1, 0x0046);
    try Instruction.LD(&cpu, ldm_push);

    // SP should decrease by 6 (3 registers * 2 bytes each)
    try expect(cpu.registers.SP == initial_sp -% 6);

    // Registers pushed in reverse order (R15 down to R0): R6, then R2, then R1
    // Each push decreases SP by 2, so the last register pushed (R1) is at lowest address
    // Stack layout (from low to high address): R1, R2, R6
    try expect(cpu.ram.read16(cpu.registers.SP) == 0x1111); // R1 at lowest address (last pushed)
    try expect(cpu.ram.read16(cpu.registers.SP +% 2) == 0x2222); // R2
    try expect(cpu.ram.read16(cpu.registers.SP +% 4) == 0x6666); // R6 at highest address (first pushed)
}

test "LDM - Load Multiple (Pop Multiple)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test: LDM {R1,R2,R6}, (SP)+
    // Register list: R1 (bit 1), R2 (bit 2), R6 (bit 6)
    // Bitmask: 0b0000_0000_0100_0110 = 0x0046
    cpu.reset(false);

    // Setup stack with test values
    const initial_sp = cpu.registers.SP -% 6;
    cpu.registers.SP = initial_sp;
    cpu.ram.write16(initial_sp, 0xAAAA);
    cpu.ram.write16(initial_sp +% 2, 0xBBBB);
    cpu.ram.write16(initial_sp +% 4, 0xCCCC);

    // Clear destination registers
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R6), 0x0000);

    // LDM {R1,R2,R6}, (SP)+: rd=0, rs=SP(14), fl=1, imm=0x0046
    const ldm_pop = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R0, .R14, 1, 0x0046);
    try Instruction.LD(&cpu, ldm_pop);

    // SP should increase by 6 (3 registers * 2 bytes each)
    try expect(cpu.registers.SP == initial_sp +% 6);

    // Registers popped in forward order: R1, R2, R6
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0xAAAA);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xBBBB);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R6)) == 0xCCCC);
}

test "LDM - Push and Pop roundtrip" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test: Push multiple registers and then pop them back
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x3333);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x5555);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R7), 0x7777);
    const initial_sp = cpu.registers.SP;

    // LDM -(SP), {R3,R5,R7}: bitmask 0b0000_0000_1010_1000 = 0x00A8
    const ldm_push = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R14, .R0, 1, 0x00A8);
    try Instruction.LD(&cpu, ldm_push);
    try expect(cpu.registers.SP == initial_sp -% 6);

    // Clear registers
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R7), 0x0000);

    // LDM {R3,R5,R7}, (SP)+
    const ldm_pop = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R0, .R14, 1, 0x00A8);
    try Instruction.LD(&cpu, ldm_pop);
    try expect(cpu.registers.SP == initial_sp);

    // Values should be restored
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R3)) == 0x3333);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R5)) == 0x5555);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R7)) == 0x7777);
}

test "LDM - Illegal operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Illegal: LDM with rd != SP and rd != 0
    cpu.reset(false);
    const ldm_bad_rd = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R5, .R0, 1, 0x0046);
    try Instruction.LD(&cpu, ldm_bad_rd);
    try expect(cpu.registers.SR.getFlag(.T) == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));

    // Illegal: LDM with rs != SP and rs != 0
    cpu.reset(false);
    const ldm_bad_rs = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R0, .R3, 1, 0x0046);
    try Instruction.LD(&cpu, ldm_bad_rs);
    try expect(cpu.registers.SR.getFlag(.T) == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));

    // Illegal: LDM with both rd and rs set incorrectly
    cpu.reset(false);
    const ldm_bad_both = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R2, .R3, 1, 0x0046);
    try Instruction.LD(&cpu, ldm_bad_both);
    try expect(cpu.registers.SR.getFlag(.T) == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));
}

test "LDM - Single register" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test: LDM -(SP), {R4} - single register
    // Bitmask: 0b0000_0000_0001_0000 = 0x0010
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x4444);
    const initial_sp = cpu.registers.SP;

    const ldm_push_single = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R14, .R0, 1, 0x0010);
    try Instruction.LD(&cpu, ldm_push_single);
    try expect(cpu.registers.SP == initial_sp -% 2);
    try expect(cpu.ram.read16(cpu.registers.SP) == 0x4444);

    // Pop it back
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x0000);
    const ldm_pop_single = Instruction.pack(0, .LD, .REGISTER_IMM16, 0, .R0, .R14, 1, 0x0010);
    try Instruction.LD(&cpu, ldm_pop_single);
    try expect(cpu.registers.SP == initial_sp);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R4)) == 0x4444);
}

test "ST - Basic operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // ST 0(R1), R2 - [R1 + 0] ← R2
    // rd=R1 (destination address base), rs=R2 (source value)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x1000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0xDEAD);
    const st_basic = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0000);
    try Instruction.ST(&cpu, st_basic);
    try expect(cpu.ram.read16(0x1000) == 0xDEAD);

    // ST 4(R1), R3 - [R1 + 4] ← R3
    // rd=R1 (destination address base), rs=R3 (source value)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x2000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xBEEF);
    const st_offset = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R1, .R3, 0, 0x0004);
    try Instruction.ST(&cpu, st_offset);
    try expect(cpu.ram.read16(0x2004) == 0xBEEF);

    // ST 0x100(R0), R4 - [R0 + 0x100] ← R4 (R0 is always 0)
    // rd=R0 (destination address base), rs=R4 (source value)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0xCAFE);
    const st_r0_base = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R0, .R4, 0, 0x0100);
    try Instruction.ST(&cpu, st_r0_base);
    try expect(cpu.ram.read16(0x0100) == 0xCAFE);

    // ST 2(R5), R5 - [R5 + 2] ← R5 (using same register for address and value)
    // rd=R5 (destination address base), rs=R5 (source value)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x3000);
    const st_same_reg = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R5, .R5, 0, 0x0002);
    try Instruction.ST(&cpu, st_same_reg);
    try expect(cpu.ram.read16(0x3002) == 0x3000);

    // ST 0(SP), R1 - [SP + 0] ← R1
    // rd=SP (destination address base), rs=R1 (source value)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x5555);
    const sp_addr = cpu.registers.SP;
    const st_sp_base = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R14, .R1, 0, 0x0000);
    try Instruction.ST(&cpu, st_sp_base);
    try expect(cpu.ram.read16(sp_addr) == 0x5555);

    // Multiple stores to adjacent addresses
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x4000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0xAAAA);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xBBBB);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0xCCCC);

    const st1 = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0000);
    const st2 = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R1, .R3, 0, 0x0002);
    const st3 = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R1, .R4, 0, 0x0004);

    try Instruction.ST(&cpu, st1);
    try Instruction.ST(&cpu, st2);
    try Instruction.ST(&cpu, st3);

    try expect(cpu.ram.read16(0x4000) == 0xAAAA);
    try expect(cpu.ram.read16(0x4002) == 0xBBBB);
    try expect(cpu.ram.read16(0x4004) == 0xCCCC);
}

test "ST - Edge cases and illegal operations" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Illegal: ST in REGISTER_IMM16 mode (only OFFSET_INDEXED is valid)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x1111);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x2222);
    const st_illegal_mode = Instruction.pack(0, .ST, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.ST(&cpu, st_illegal_mode);
    try expect(cpu.registers.SR.getFlag(.T) == true);
    const trap_code1 = cpu.registers.SR.raw & 0x7FFF;
    try expect(trap_code1 == @intFromEnum(Trap.Illegal_instruction));

    // Illegal: ST PC, Rs|IMM16 (storing to PC register)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x5000);
    const st_to_pc = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R15, .R1, 0, 0x0000);
    try Instruction.ST(&cpu, st_to_pc);
    try expect(cpu.registers.SR.getFlag(.T) == true);
    const trap_code2 = cpu.registers.SR.raw & 0x7FFF;
    try expect(trap_code2 == @intFromEnum(Trap.Illegal_instruction));

    // Illegal: ST with immediate in REGISTER_IMM16 mode
    cpu.reset(false);
    const st_illegal_imm = Instruction.pack(0, .ST, .REGISTER_IMM16, 0, .R2, .R0, 0, 0xDEAD);
    try Instruction.ST(&cpu, st_illegal_imm);
    try expect(cpu.registers.SR.getFlag(.T) == true);
    const trap_code3 = cpu.registers.SR.raw & 0x7FFF;
    try expect(trap_code3 == @intFromEnum(Trap.Illegal_instruction));

    // Edge Case: Store with maximum offset causing address wraparound
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0010);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0xFACE);
    const st_max_offset = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0xFFFF);
    try Instruction.ST(&cpu, st_max_offset);
    // 0x0010 + 0xFFFF wraps to 0x000F
    try expect(cpu.ram.read16(0x000F) == 0xFACE);

    // Edge Case: Store zero value
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x6000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R0), 0x0000);
    const st_zero = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R1, .R0, 0, 0x0000);
    try Instruction.ST(&cpu, st_zero);
    try expect(cpu.ram.read16(0x6000) == 0x0000);

    // Edge Case: Store maximum value (0xFFFF)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x7000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0xFFFF);
    const st_max_val = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0000);
    try Instruction.ST(&cpu, st_max_val);
    try expect(cpu.ram.read16(0x7000) == 0xFFFF);

    // Edge Case: Overwrite existing memory value
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x8000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x1111);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x2222);

    // First store
    const st_first = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0000);
    try Instruction.ST(&cpu, st_first);
    try expect(cpu.ram.read16(0x8000) == 0x1111);

    // Overwrite with second store
    const st_second = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R1, .R3, 0, 0x0000);
    try Instruction.ST(&cpu, st_second);
    try expect(cpu.ram.read16(0x8000) == 0x2222);

    // Edge Case: Store to address 0x0000
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x7777);
    const st_addr_zero = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R0, .R1, 0, 0x0000);
    try Instruction.ST(&cpu, st_addr_zero);
    try expect(cpu.ram.read16(0x0000) == 0x7777);

    // Edge Case: Store to maximum address (near 0xFFFF)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFF0);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x9999);
    const st_high_addr = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x000E);
    try Instruction.ST(&cpu, st_high_addr);
    try expect(cpu.ram.read16(0xFFFE) == 0x9999);

    // Edge Case: Store using PC as base address
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x3333);
    const st_pc_base = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R15, .R1, 0, 0x0010);
    try Instruction.ST(&cpu, st_pc_base);
    try expect(cpu.registers.SR.getFlag(.T) == true);
    try expect(cpu.registers.SR.raw & 0x7FFF == @intFromEnum(Trap.Illegal_instruction));

    // Edge Case: Negative offset (using two's complement)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x9000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x4444);
    // 0xFFFE is -2 in two's complement
    const st_neg_offset = Instruction.pack(0, .ST, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0xFFFE);
    try Instruction.ST(&cpu, st_neg_offset);
    // 0x9000 + 0xFFFE = 0x8FFE (wrapping arithmetic)
    try expect(cpu.ram.read16(0x8FFE) == 0x4444);
}

test "BPR - Compare with register (OFFSET_INDEXED, fl=0)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // BPR R1, R2 where R1 > R2 (positive result)
    // Syntax: BPR Rs, Rn => Instruction.pack(0, .B, .OFFSET_INDEXED, 0, Condition.PR, .Rs, 0, (Rn << 12))
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x5000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x3000);
    const bpr_greater = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R1, 0, (@as(u16, 2) << 12));
    try Instruction.B(&cpu, bpr_greater);
    // R1 - R2 = 0x5000 - 0x3000 = 0x2000 (positive)
    try expect(cpu.registers.SR.getFlag(.N) == false); // Negative flag clear
    try expect(cpu.registers.SR.getFlag(.Z) == false); // Zero flag clear
    try expect(cpu.registers.SR.getFlag(.C) == false); // Carry flag clear (no borrow)
    try expect(cpu.registers.SR.getFlag(.V) == false); // Overflow flag clear

    // BPR R3, R4 where R3 < R4 (negative result, borrow)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x2000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x5000);
    const bpr_less = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R3, 0, (@as(u16, 4) << 12));
    try Instruction.B(&cpu, bpr_less);
    // R3 - R4 = 0x2000 - 0x5000 = 0xD000 (negative, borrow)
    try expect(cpu.registers.SR.getFlag(.N) == true); // Negative flag set
    try expect(cpu.registers.SR.getFlag(.Z) == false); // Zero flag clear
    try expect(cpu.registers.SR.getFlag(.C) == true); // Carry flag set (borrow occurred)
    try expect(cpu.registers.SR.getFlag(.V) == false); // Overflow flag clear

    // BPR R5, R6 where R5 == R6 (zero result)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x4000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R6), 0x4000);
    const bpr_equal = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R5, 0, (@as(u16, 6) << 12));
    try Instruction.B(&cpu, bpr_equal);
    // R5 - R6 = 0x4000 - 0x4000 = 0x0000 (zero)
    try expect(cpu.registers.SR.getFlag(.N) == false);
    try expect(cpu.registers.SR.getFlag(.Z) == true); // Zero flag set
    try expect(cpu.registers.SR.getFlag(.C) == false);
    try expect(cpu.registers.SR.getFlag(.V) == false);
}

test "BPR - Compare with immediate (REGISTER_IMM16, fl=0)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // BPR R1, 0x2000 where R1 > IMM16
    // Syntax: BPR Rs, IMM16 => Instruction.pack(0, .B, .REGISTER_IMM16, 0, Condition.PR, .Rs, 0, IMM16)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x8000);
    const bpr_imm_greater = Instruction.pack(0, .B, .REGISTER_IMM16, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R1, 0, 0x2000);
    try Instruction.B(&cpu, bpr_imm_greater);
    // R1 - 0x2000 = 0x8000 - 0x2000 = 0x6000 (positive)
    try expect(cpu.registers.SR.getFlag(.N) == false);
    try expect(cpu.registers.SR.getFlag(.Z) == false);
    try expect(cpu.registers.SR.getFlag(.C) == false);
    try expect(cpu.registers.SR.getFlag(.V) == true);

    // BPR R2, 0x1000 where R2 < IMM16
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0500);
    const bpr_imm_less = Instruction.pack(0, .B, .REGISTER_IMM16, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R2, 0, 0x1000);
    try Instruction.B(&cpu, bpr_imm_less);
    // R2 - 0x1000 = 0x0500 - 0x1000 = 0xF500 (negative, borrow)
    try expect(cpu.registers.SR.getFlag(.N) == true);
    try expect(cpu.registers.SR.getFlag(.Z) == false);
    try expect(cpu.registers.SR.getFlag(.C) == true);

    // BPR R3, 0x4000 where R3 == IMM16
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x4000);
    const bpr_imm_equal = Instruction.pack(0, .B, .REGISTER_IMM16, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R3, 0, 0x4000);
    try Instruction.B(&cpu, bpr_imm_equal);
    // R3 - 0x4000 = 0x0000 (zero)
    try expect(cpu.registers.SR.getFlag(.Z) == true);
    try expect(cpu.registers.SR.getFlag(.N) == false);
    try expect(cpu.registers.SR.getFlag(.C) == false);
}

test "BPR - Overflow detection (fl=0)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Overflow: positive - negative = negative (should overflow)
    // 0x7FFF (max positive) - 0x8000 (max negative) = overflow
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x7FFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x8000);
    const bpr_overflow1 = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R1, 0, (@as(u16, 2) << 12));
    try Instruction.B(&cpu, bpr_overflow1);
    // 0x7FFF - 0x8000 = 0xFFFF (result appears negative but should be positive - overflow)
    try expect(cpu.registers.SR.getFlag(.V) == true); // Overflow flag set
    try expect(cpu.registers.SR.getFlag(.N) == true); // Result is negative
    try expect(cpu.registers.SR.getFlag(.C) == true); // Borrow occurred

    // Overflow: negative - positive = positive (should overflow)
    // 0x8000 (max negative) - 0x7FFF (max positive) = overflow
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x8000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x7FFF);
    const bpr_overflow2 = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R3, 0, (@as(u16, 4) << 12));
    try Instruction.B(&cpu, bpr_overflow2);
    // 0x8000 - 0x7FFF = 0x0001 (result appears positive but should be negative - overflow)
    try expect(cpu.registers.SR.getFlag(.V) == true); // Overflow flag set
    try expect(cpu.registers.SR.getFlag(.N) == false); // Result is positive
    try expect(cpu.registers.SR.getFlag(.C) == false); // No borrow

    // No overflow: same signs (both positive)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x5000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R6), 0x4000);
    const bpr_no_overflow1 = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R5, 0, (@as(u16, 6) << 12));
    try Instruction.B(&cpu, bpr_no_overflow1);
    // 0x5000 - 0x4000 = 0x1000 (no overflow)
    try expect(cpu.registers.SR.getFlag(.V) == false);

    // No overflow: same signs (both negative)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R7), 0x9000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R8), 0xA000);
    const bpr_no_overflow2 = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R7, 0, (@as(u16, 8) << 12));
    try Instruction.B(&cpu, bpr_no_overflow2);
    // 0x9000 - 0xA000 = 0xF000 (both negative, no overflow)
    try expect(cpu.registers.SR.getFlag(.V) == false);
}

test "BPR - Bit test with register (OFFSET_INDEXED, fl=1)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // BPR.B R1, R2 with complementary patterns (result = 0)
    // Syntax: BPR.B Rs, Rn => Instruction.pack(0, .B, .OFFSET_INDEXED, 0, Condition.PR, .Rs, 1, (Rn << 12))
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0b1010101010101010);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0b0101010101010101);
    const bpr_bit_zero = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R1, 1, (@as(u16, 2) << 12));
    try Instruction.B(&cpu, bpr_bit_zero);
    // 0xAAAA & 0x5555 = 0x0000 (zero)
    try expect(cpu.registers.SR.getFlag(.Z) == true);
    try expect(cpu.registers.SR.getFlag(.N) == false);
    try expect(cpu.registers.SR.getFlag(.C) == false);
    try expect(cpu.registers.SR.getFlag(.V) == false);

    // BPR.B R3, R4 with high bit set in result
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xF0F0);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x80FF);
    const bpr_bit_negative = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R3, 1, (@as(u16, 4) << 12));
    try Instruction.B(&cpu, bpr_bit_negative);
    // 0xF0F0 & 0x80FF = 0x80F0 (high bit set, negative)
    try expect(cpu.registers.SR.getFlag(.Z) == false);
    try expect(cpu.registers.SR.getFlag(.N) == true); // Bit 15 is set
    try expect(cpu.registers.SR.getFlag(.C) == false);
    try expect(cpu.registers.SR.getFlag(.V) == false);

    // BPR.B R5, R6 all bits set
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0xFFFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R6), 0xFFFF);
    const bpr_bit_allset = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R5, 1, (@as(u16, 6) << 12));
    try Instruction.B(&cpu, bpr_bit_allset);
    // 0xFFFF & 0xFFFF = 0xFFFF (all bits set, high bit set = negative)
    try expect(cpu.registers.SR.getFlag(.Z) == false);
    try expect(cpu.registers.SR.getFlag(.N) == true);
    try expect(cpu.registers.SR.getFlag(.C) == false);
    try expect(cpu.registers.SR.getFlag(.V) == false);

    // BPR.B R7, R8 testing single bit
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R7), 0x0007);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R8), 0x0001);
    const bpr_bit_single = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R7, 1, (@as(u16, 8) << 12));
    try Instruction.B(&cpu, bpr_bit_single);
    // 0x0007 & 0x0001 = 0x0001 (single bit, positive)
    try expect(cpu.registers.SR.getFlag(.Z) == false);
    try expect(cpu.registers.SR.getFlag(.N) == false);
}

test "BPR - Bit test with immediate (REGISTER_IMM16, fl=1)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // BPR.B R1, 0x00FF - mask low byte
    // Syntax: BPR.B Rs, IMM16 => Instruction.pack(0, .B, .REGISTER_IMM16, 0, Condition.PR, .Rs, 1, IMM16)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFF00);
    const bpr_bit_imm1 = Instruction.pack(0, .B, .REGISTER_IMM16, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R1, 1, 0x00FF);
    try Instruction.B(&cpu, bpr_bit_imm1);
    // 0xFF00 & 0x00FF = 0x0000 (zero)
    try expect(cpu.registers.SR.getFlag(.Z) == true);
    try expect(cpu.registers.SR.getFlag(.N) == false);
    try expect(cpu.registers.SR.getFlag(.C) == false);
    try expect(cpu.registers.SR.getFlag(.V) == false);

    // BPR.B R2, 0x8001 - test high and low bits
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0xFFFF);
    const bpr_bit_imm2 = Instruction.pack(0, .B, .REGISTER_IMM16, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R2, 1, 0x8001);
    try Instruction.B(&cpu, bpr_bit_imm2);
    // 0xFFFF & 0x8001 = 0x8001 (high bit set)
    try expect(cpu.registers.SR.getFlag(.Z) == false);
    try expect(cpu.registers.SR.getFlag(.N) == true);

    // BPR.B R3, 0x0001 - test single low bit
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x0003);
    const bpr_bit_imm3 = Instruction.pack(0, .B, .REGISTER_IMM16, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R3, 1, 0x0001);
    try Instruction.B(&cpu, bpr_bit_imm3);
    // 0x0003 & 0x0001 = 0x0001 (non-zero, high bit clear)
    try expect(cpu.registers.SR.getFlag(.Z) == false);
    try expect(cpu.registers.SR.getFlag(.N) == false);

    // BPR.B R4, 0x7FFF - test all bits except high bit
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x5555);
    const bpr_bit_imm4 = Instruction.pack(0, .B, .REGISTER_IMM16, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R4, 1, 0x7FFF);
    try Instruction.B(&cpu, bpr_bit_imm4);
    // 0x5555 & 0x7FFF = 0x5555 (positive)
    try expect(cpu.registers.SR.getFlag(.N) == false);
    try expect(cpu.registers.SR.getFlag(.Z) == false);
}

test "BPR - Edge cases with zero" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Compare 0 - 0 (fl=0)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0000);
    const bpr_zero_compare = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R1, 0, (@as(u16, 2) << 12));
    try Instruction.B(&cpu, bpr_zero_compare);
    // 0x0000 - 0x0000 = 0x0000
    try expect(cpu.registers.SR.getFlag(.Z) == true);
    try expect(cpu.registers.SR.getFlag(.N) == false);
    try expect(cpu.registers.SR.getFlag(.C) == false);
    try expect(cpu.registers.SR.getFlag(.V) == false);

    // Bit test 0 & IMM16 (fl=1)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x0000);
    const bpr_zero_bit = Instruction.pack(0, .B, .REGISTER_IMM16, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R3, 1, 0xFFFF);
    try Instruction.B(&cpu, bpr_zero_bit);
    // 0x0000 & 0xFFFF = 0x0000
    try expect(cpu.registers.SR.getFlag(.Z) == true);
    try expect(cpu.registers.SR.getFlag(.N) == false);

    // Compare 0 - FFFF (fl=0)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x0000);
    const bpr_zero_sub_max = Instruction.pack(0, .B, .REGISTER_IMM16, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R4, 0, 0xFFFF);
    try Instruction.B(&cpu, bpr_zero_sub_max);
    // 0x0000 - 0xFFFF = 0x0001 (with borrow)
    try expect(cpu.registers.SR.getFlag(.C) == true); // Borrow occurred
    try expect(cpu.registers.SR.getFlag(.Z) == false);

    // Compare using R0 (always 0)
    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R5), 0x1234);
    const bpr_r0 = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R0, 0, (@as(u16, 5) << 12));
    try Instruction.B(&cpu, bpr_r0);
    // 0x0000 - 0x1234 = negative (borrow)
    try expect(cpu.registers.SR.getFlag(.C) == true);
    try expect(cpu.registers.SR.getFlag(.N) == true);
}

test "BPR - PC preservation (no branch)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // BPR should NOT modify PC (it's a comparison only)
    cpu.reset(false);
    cpu.registers.PC = 0x1000;
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x5000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x3000);
    const initial_pc = cpu.registers.PC;
    const bpr_no_branch = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R1, 0, (@as(u16, 2) << 12));
    try Instruction.B(&cpu, bpr_no_branch);
    try expect(cpu.registers.PC == initial_pc); // PC unchanged

    // BPR.B should also NOT modify PC
    cpu.reset(false);
    cpu.registers.PC = 0x2000;
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0xAAAA);
    const initial_pc2 = cpu.registers.PC;
    const bpr_bit_no_branch = Instruction.pack(0, .B, .REGISTER_IMM16, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R3, 1, 0x5555);
    try Instruction.B(&cpu, bpr_bit_no_branch);
    try expect(cpu.registers.PC == initial_pc2); // PC unchanged
}

test "BPR - Register encoding in imm16" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Test all 16 registers can be encoded in bits 12-15
    var i: u4 = 2;
    while (i < 15) : (i += 1) {
        cpu.reset(false);
        cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x1000);
        cpu.registers.writeRegister(i, 0x0100);
        const bpr_reg = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.PR))), .R1, 0, (@as(u16, i) << 12));
        try Instruction.B(&cpu, bpr_reg);
        // R1 - Ri; flags should be set
        // 0x1000 - 0x0100 = 0x0F00 (positive, no flags set except maybe N based on result)
        try expect(cpu.registers.SR.getFlag(.C) == false);
        try expect(cpu.registers.SR.getFlag(.Z) == false);
    }
}

test "B - condition evaluation (PC relative)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    const cases = [_]struct {
        cond: Condition,
        flags: struct { N: bool, Z: bool, C: bool, V: bool },
        expect_taken: bool,
    }{
        .{ .cond = .EQ, .flags = .{ .N = false, .Z = true, .C = false, .V = false }, .expect_taken = true },
        .{ .cond = .EQ, .flags = .{ .N = false, .Z = false, .C = false, .V = false }, .expect_taken = false },
        .{ .cond = .NE, .flags = .{ .N = false, .Z = false, .C = false, .V = false }, .expect_taken = true },
        .{ .cond = .CS, .flags = .{ .N = false, .Z = false, .C = true, .V = false }, .expect_taken = true },
        .{ .cond = .CC, .flags = .{ .N = false, .Z = false, .C = false, .V = false }, .expect_taken = true },
        .{ .cond = .MI, .flags = .{ .N = true, .Z = false, .C = false, .V = false }, .expect_taken = true },
        .{ .cond = .PL, .flags = .{ .N = false, .Z = false, .C = false, .V = false }, .expect_taken = true },
        .{ .cond = .VS, .flags = .{ .N = false, .Z = false, .C = false, .V = true }, .expect_taken = true },
        .{ .cond = .VC, .flags = .{ .N = false, .Z = false, .C = false, .V = false }, .expect_taken = true },
        .{ .cond = .HI, .flags = .{ .N = false, .Z = false, .C = true, .V = false }, .expect_taken = true },
        .{ .cond = .HI, .flags = .{ .N = false, .Z = true, .C = true, .V = false }, .expect_taken = false },
        .{ .cond = .LS, .flags = .{ .N = false, .Z = false, .C = false, .V = false }, .expect_taken = true },
        .{ .cond = .GE, .flags = .{ .N = false, .Z = false, .C = false, .V = false }, .expect_taken = true },
        .{ .cond = .LT, .flags = .{ .N = true, .Z = false, .C = false, .V = false }, .expect_taken = true },
        .{ .cond = .GT, .flags = .{ .N = false, .Z = false, .C = false, .V = false }, .expect_taken = true },
        .{ .cond = .GT, .flags = .{ .N = false, .Z = true, .C = false, .V = false }, .expect_taken = false },
        .{ .cond = .LE, .flags = .{ .N = false, .Z = true, .C = false, .V = false }, .expect_taken = true },
        .{ .cond = .A, .flags = .{ .N = false, .Z = false, .C = false, .V = false }, .expect_taken = true },
    };

    for (cases) |c| {
        cpu.reset(false);
        cpu.registers.PC = 0x1000;
        cpu.registers.SP = 0xFFFE;
        cpu.registers.SR.raw = 0;
        cpu.registers.SR.updateFlag(.N, c.flags.N);
        cpu.registers.SR.updateFlag(.Z, c.flags.Z);
        cpu.registers.SR.updateFlag(.C, c.flags.C);
        cpu.registers.SR.updateFlag(.V, c.flags.V);

        const cond_reg: RegistersName = @as(RegistersName, @enumFromInt(@intFromEnum(c.cond)));
        const instr = Instruction.pack(0, .B, .REGISTER_IMM16, 0, cond_reg, .R0, 0, 0x0004);
        try Instruction.B(&cpu, instr);

        if (c.expect_taken) {
            try expect(cpu.registers.PC == 0x1004);
        } else {
            try expect(cpu.registers.PC == 0x1000);
        }
        try expect(cpu.registers.SP == 0xFFFE);
    }
}

test "B - PC relative negative offset" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);
    cpu.registers.PC = 0x2000;
    const instr = Instruction.pack(0, .B, .REGISTER_IMM16, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.A))), .R0, 0, 0xFFFC);
    try Instruction.B(&cpu, instr);
    try expect(cpu.registers.PC == 0x1FFC);
}

test "B - Link saves PC (PC relative)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);
    cpu.registers.PC = 0x3000;
    cpu.registers.SP = 0xFFFE;
    const instr = Instruction.pack(0, .B, .REGISTER_IMM16, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.A))), .R0, 1, 0x0004);
    try Instruction.B(&cpu, instr);
    try expect(cpu.registers.PC == 0x3004);
    try expect(cpu.registers.SP == 0xFFFC);
    try expect(cpu.ram.read16(0xFFFC) == 0x3000);
}

test "B - OFFSET_INDEXED taken" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x4000);
    cpu.registers.SR.updateFlag(.Z, false); // NE
    const instr = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.NE))), .R2, 0, 0x0010);
    try Instruction.B(&cpu, instr);
    try expect(cpu.registers.PC == 0x4010);
}

test "B - OFFSET_INDEXED not taken" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);
    cpu.registers.PC = 0x5555;
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R4), 0x1234);
    cpu.registers.SR.updateFlag(.Z, false);
    const instr = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.EQ))), .R4, 0, 0x0004);
    try Instruction.B(&cpu, instr);
    try expect(cpu.registers.PC == 0x5555);
    try expect(cpu.registers.SP == 0xFFFE);
}

test "B - OFFSET_INDEXED link and negative offset" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);
    cpu.registers.PC = 0x6000;
    cpu.registers.SP = 0xFFFE;
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R3), 0x5000);
    const instr = Instruction.pack(0, .B, .OFFSET_INDEXED, 0, @as(RegistersName, @enumFromInt(@intFromEnum(Condition.A))), .R3, 1, 0xFFF0);
    try Instruction.B(&cpu, instr);
    try expect(cpu.registers.PC == 0x4FF0);
    try expect(cpu.registers.SP == 0xFFFC);
    try expect(cpu.ram.read16(0xFFFC) == 0x6000);
}
