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
    LD,
    ST,
    ADD,
    SUB,
    MUL,
    DIV,
    AND,
    OR,
    XOR,
    ROL,
    ROR,
    SHL,
    SHR,
    SWI,
};

pub const Condition = enum(u4) {
    EQ = 0,
    NE,
    CS,
    CC,
    MI,
    PL,
    VS,
    VC,
    HI,
    LS,
    GE,
    LT,
    GT,
    LE,
    PR,
    A,
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

    pub fn execute(self: Instruction, cpu: *CPU) !void {
        switch (self.bytecode.opcode) {
            @intFromEnum(Opcode.ADD) => try ADD(cpu, self),
            @intFromEnum(Opcode.SUB) => try SUB(cpu, self),
            @intFromEnum(Opcode.MUL) => try MUL(cpu, self),
            @intFromEnum(Opcode.DIV) => try DIV(cpu, self),
        }
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

        // Can take the X form ADDX (When flag X is set ADD behave like ADC)

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        // Check if ADDX (Add with Carry)
        if (cpu.registers.SR.getFlag(.X)) {
            // ADDX: Add with carry
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
            cpu.registers.SR.clearFlag(.X); // Clear X flag after ADDX
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
            cpu.registers.SR.setFlag(.T);
            return;
        }

        // SUB Rd               => Rd = Rd - 1
        // SUB Rd, IMM16        => Rd = Rd - IMM16
        // SUB Rd, Rs           => Rd = Rd - Rs
        // SUB Rd, Rs, IMM16    => Rd = Rs - IMM16
        // SUB Rd, Rs, 0        => Defined behavior, but unexpected result! (Maybe better to reject parser side!?)

        // Can take the X form SUBX (When flag X is set SUB behave like SBC)

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        // Check if SUBX (Subtract with Borrow)
        if (cpu.registers.SR.getFlag(.X)) {
            // SUBX: Subtract with borrow
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
            cpu.registers.SR.clearFlag(.X); // Clear X flag after SUBX
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

        if (instruction.bytecode.mode == @intFromEnum(Mode.REGISTER_IMM16)) {
            // MUL Rd, Rs, imm16 → Rd = Rs * imm16

            // Check for MULX instruction
            if (!cpu.registers.SR.getFlag(.X)) {
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
                    cpu.registers.SR.clearFlag(.X);
                }
            }
        } else {
            // Illegal instruction - set T flag and return error
            cpu.registers.SR.flags.T = true;
        }
    }

    fn DIV(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
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
            cpu.registers.SR.flags.T = true; // Set trap flag
            return;
        }

        if (instruction.bytecode.mode == @intFromEnum(Mode.REGISTER_IMM16)) {
            const quotient: u32 = first_operand / second_operand;
            const remainder: u16 = first_operand % second_operand;
            const result: u16 = @truncate(quotient);

            // Update flags (N, Z, V)
            cpu.registers.SR.updateFlag(.N, (result & 0x8000) != 0);
            cpu.registers.SR.updateFlag(.Z, result == 0);
            cpu.registers.SR.clearFlag(.C);
            cpu.registers.SR.clearFlag(.V);

            // Write result to Rd (unless Rd is R0, which is always zero)
            if (instruction.bytecode.rd != 0) {
                cpu.registers.writeRegister(instruction.bytecode.rd, result);
                if (cpu.registers.SR.getFlag(.X)) {
                    cpu.registers.writeRegister(instruction.bytecode.rs, remainder);
                    cpu.registers.SR.clearFlag(.X);
                }
            }
        } else {
            // Illegal instruction - set T flag and return error
            cpu.registers.SR.flags.T = true;
        }
    }

    fn AND(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            cpu.registers.SR.setFlag(.T);
            return;
        }

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        if (instruction.bytecode.mode == @intFromEnum(Mode.REGISTER_IMM16)) {
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
        } else {
            // Illegal instruction - set T flag and return error
            cpu.registers.SR.flags.T = true;
        }
    }

    fn OR(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            cpu.registers.SR.setFlag(.T);
            return;
        }

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        if (instruction.bytecode.mode == @intFromEnum(Mode.REGISTER_IMM16)) {
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
        } else {
            // Illegal instruction - set T flag and return error
            cpu.registers.SR.flags.T = true;
        }
    }

    fn XOR(cpu: *CPU, instruction: Instruction) !void {
        // LOAD/STORE architecture all ALU are registers only.
        if (instruction.bytecode.mode == @intFromEnum(Mode.OFFSET_INDEXED)) {
            cpu.registers.SR.setFlag(.T);
            return;
        }

        const first_operand: u16 = if (instruction.bytecode.imm16 != 0) cpu.registers.readRegister(instruction.bytecode.rs) else cpu.registers.readRegister(instruction.bytecode.rd);
        const second_operand: u16 = if (instruction.bytecode.imm16 != 0) instruction.bytecode.imm16 else cpu.registers.readRegister(instruction.bytecode.rs);

        if (instruction.bytecode.mode == @intFromEnum(Mode.REGISTER_IMM16)) {
            // XOR Rd, Rs, imm16 → Rd = Rs ^ imm16
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
        } else {
            // Illegal instruction - set T flag and return error
            cpu.registers.SR.flags.T = true;
        }
    }

    fn ROL(cpu: *CPU, instruction: Instruction) !void {
        const rd_index = instruction.bytecode.rd;
        const rs_index = instruction.bytecode.rs;
        const imm16: u16 = instruction.bytecode.imm16;

        if (instruction.bytecode.mode == @intFromEnum(Mode.REGISTER_IMM16)) {
            // ROL Rd, Rs, imm16 → Rd = Rd rotated left by (Rs + imm16) & 0xF
            // const rd: u16 = cpu.registers.asArray()[rd_index];
            const rs: u16 = cpu.registers.asArray()[rs_index];
            const rotation: u16 = (rs +% imm16) & 0x000F; // Max rotation is 15

            // Perform rotation
            var result: u16 = rs;
            var carry_out: bool = false;

            if (rotation > 0) {
                result = (rs << @intCast(rotation)) | (rs >> @intCast(16 - rotation));
                carry_out = ((rs >> @intCast(16 - rotation)) & 0x0001) != 0;
            }

            // Update flags (N, Z, C) and clear V
            cpu.registers.SR.updateShiftRotateFlags(result, carry_out);

            // Write result to Rd (unless Rd is R0, which is always zero)
            if (rd_index != 0) {
                cpu.registers.asArray()[rd_index] = result;
            }
        } else {
            // Illegal instruction - set T flag and return error
            cpu.registers.SR.flags.T = true;
        }
    }

    fn ROR(cpu: *CPU, instruction: Instruction) !void {
        const rd_index = instruction.bytecode.rd;
        const rs_index = instruction.bytecode.rs;
        const imm16: u16 = instruction.bytecode.imm16;

        if (instruction.bytecode.mode == @intFromEnum(Mode.REGISTER_IMM16)) {
            // ROR Rd, Rs, imm16 → Rd = Rd rotated right by (Rs + imm16) & 0xF
            // const rd: u16 = cpu.registers.asArray()[rd_index];
            const rs: u16 = cpu.registers.asArray()[rs_index];
            const rotation: u16 = (rs +% imm16) & 0x000F; // Max rotation is 15

            // Perform rotation
            var result: u16 = rs;
            var carry_out: bool = false;

            if (rotation > 0) {
                result = (rs >> @intCast(rotation)) | (rs << @intCast(16 - rotation));
                carry_out = ((rs >> @intCast(rotation - 1)) & 0x0001) != 0;
            }

            // Update flags (N, Z, C) and clear V
            cpu.registers.SR.updateShiftRotateFlags(result, carry_out);

            // Write result to Rd (unless Rd is R0, which is always zero)
            if (rd_index != 0) {
                cpu.registers.asArray()[rd_index] = result;
            }
        } else {
            // Illegal instruction - set T flag and return error
            cpu.registers.SR.flags.T = true;
        }
    }

    fn SHL(cpu: *CPU, instruction: Instruction) !void {
        const rd_index = instruction.bytecode.rd;
        const rs_index = instruction.bytecode.rs;
        const imm16: u16 = instruction.bytecode.imm16;

        if (instruction.bytecode.mode == @intFromEnum(Mode.REGISTER_IMM16)) {
            // SHL Rd, Rs, imm16 → Rd = Rd << (Rs + imm16) & 0xF
            // const rd: u16 = cpu.registers.asArray()[rd_index];
            const rs: u16 = cpu.registers.asArray()[rs_index];
            const shift: u16 = (rs +% imm16) & 0x000F; // Max shift is 15

            // Perform shift
            var result: u16 = rs;
            var carry_out: bool = false;

            if (shift > 0) {
                result = rs << @intCast(shift);
                carry_out = ((rs >> @intCast(16 - shift)) & 0x0001) != 0;
            }

            // Update flags (N, Z, C) and clear V
            cpu.registers.SR.updateShiftRotateFlags(result, carry_out);

            // Write result to Rd (unless Rd is R0, which is always zero)
            if (rd_index != 0) {
                cpu.registers.asArray()[rd_index] = result;
            }
        } else {
            // Illegal instruction - set T flag and return error
            cpu.registers.SR.flags.T = true;
        }
    }

    fn SHR(cpu: *CPU, instruction: Instruction) !void {
        const rd_index = instruction.bytecode.rd;
        const rs_index = instruction.bytecode.rs;
        const imm16: u16 = instruction.bytecode.imm16;

        if (instruction.bytecode.mode == @intFromEnum(Mode.REGISTER_IMM16)) {
            // SHR Rd, Rs, imm16 → Rd = Rd >> (Rs + imm16) & 0xF
            // const rd: u16 = cpu.registers.asArray()[rd_index];
            const rs: u16 = cpu.registers.asArray()[rs_index];
            const shift: u16 = (rs +% imm16) & 0x000F; // Max shift is 15

            // Perform shift
            var result: u16 = rs;
            var carry_out: bool = false;

            if (shift > 0) {
                result = rs >> @intCast(shift);
                carry_out = ((rs >> @intCast(shift - 1)) & 0x0001) != 0;
            }

            // Update flags (N, Z, C) and clear V
            cpu.registers.SR.updateShiftRotateFlags(result, carry_out);

            // Write result to Rd (unless Rd is R0, which is always zero)
            if (rd_index != 0) {
                cpu.registers.asArray()[rd_index] = result;
            }
        } else {
            // Illegal instruction - set T flag and return error
            cpu.registers.SR.flags.T = true;
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
    try expect(@intFromEnum(Opcode.SHL) == 13);
    try expect(@intFromEnum(Opcode.SHR) == 14);
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

test "ADDX - Basic (ADC behaviour)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Set carry in
    cpu.registers.SR.setFlag(.C);

    // Set X flag
    cpu.registers.SR.setFlag(.X);

    // 1 + 1 + carry(1) = 3
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0001);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const addx_basic = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.ADD(&cpu, addx_basic);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0003);
}

test "ADDX - Flags N C Z V" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Case A: carry out
    cpu.reset(false);
    // Set X flag
    cpu.registers.SR.setFlag(.X);

    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const addx_carry = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.ADD(&cpu, addx_carry);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.C == true);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.V == false);

    // Case B: signed overflow
    cpu.reset(false);
    // Set X flag
    cpu.registers.SR.setFlag(.X);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x4000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x4000);
    const addx_of = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.ADD(&cpu, addx_of);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x8000);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.V == true);

    // Case C: overflow with carry-in affecting V
    cpu.reset(false);
    // Set X flag
    cpu.registers.SR.setFlag(.X);
    cpu.registers.SR.setFlag(.C);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x7FFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const addx_carryin_of = Instruction.pack(0, .ADD, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
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

test "SUBX - Basic (SBC behaviour)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Enable X and set carry-in
    cpu.registers.SR.setFlag(.X);
    cpu.registers.SR.setFlag(.C);

    // Assume SBC subtracts carry-in as extra 1: 2 - 1 - 1 = 0
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0002);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const subx_basic = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.SUB(&cpu, subx_basic);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000);
}

test "SUBX - Flags N C Z V" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Case A: borrow occurs -> 0 - 1 - 1 = 0xFFFE
    cpu.reset(false);
    cpu.registers.SR.setFlag(.X);
    cpu.registers.SR.setFlag(.C);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const subx_borrow = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.SUB(&cpu, subx_borrow);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0xFFFE);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.C == true);
    try expect(cpu.registers.SR.flags.V == false);

    // Case B: result zero -> 2 - 1 - 1 = 0
    cpu.reset(false);
    cpu.registers.SR.setFlag(.X);
    cpu.registers.SR.setFlag(.C);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0002);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const subx_zero = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.SUB(&cpu, subx_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.C == false);
    try expect(cpu.registers.SR.flags.V == false);

    // Case C: signed overflow example -> 0x8000 - 1 - 1 = 0x7FFE (overflow)
    cpu.reset(false);
    cpu.registers.SR.setFlag(.X);
    cpu.registers.SR.setFlag(.C);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x8000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const subx_of = Instruction.pack(0, .SUB, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
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
    try expect(cpu.registers.SR.flags.T == true); // T flag set on illegal instruction
}

test "MULX - (32-bit result)" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.reset(false);

    // Enable X flag so MUL stores full 32-bit result across Rd (MSB) and Rs (LSB)
    cpu.registers.SR.setFlag(.X);

    // Example: 0xFFFF * 0x0002 = 0x0001_FFFE
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0002);
    const mul_with_x = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
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
    cpu.registers.SR.setFlag(.X);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x1234);
    const mulx_zero = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.MUL(&cpu, mulx_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.V == false);
    try expect(cpu.registers.SR.flags.C == false);

    // Case 2: Small product (no overflow) -> Z=0, N=0, V=0, C=0
    cpu.reset(false);
    cpu.registers.SR.setFlag(.X);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x1234);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0002);
    const mulx_small = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.MUL(&cpu, mulx_small);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000); // hi
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x2468); // lo
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.V == false);
    try expect(cpu.registers.SR.flags.C == false);

    // Case 3: Overflow but not MSB of 32-bit -> V=1, C=1, N=0
    cpu.reset(false);
    cpu.registers.SR.setFlag(.X);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0002);
    const mulx_of = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.MUL(&cpu, mulx_of);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0001);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0xFFFE);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.V == true);
    try expect(cpu.registers.SR.flags.C == true);

    // Case 4: Large product with MSB set -> N=1, V=1, C=1
    cpu.reset(false);
    cpu.registers.SR.setFlag(.X);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0xFFFF);
    const mulx_big = Instruction.pack(0, .MUL, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
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
    try expect(cpu.registers.SR.flags.T == true); // Trap flag

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

    // Enable X flag so DIV stores remainder into Rs
    cpu.registers.SR.setFlag(.X);

    // Example: 100 / 30 = 3 remainder 10
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0064); // 100
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x001E); // 30
    const div_with_x = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.DIV(&cpu, div_with_x);

    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0003); // quotient
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x000A); // remainder (100 - 3*30 = 10)

    try expect(cpu.registers.SR.flags.X == false); // X flag must be clear after the operation.
}

test "DIVX - Flags Z N C V" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Case 1: Zero dividend -> Z=1, N=0, V=0, C=0
    cpu.reset(false);
    cpu.registers.SR.setFlag(.X);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x1234);
    const divx_zero = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.DIV(&cpu, divx_zero);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0000);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == true);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.V == false);
    try expect(cpu.registers.SR.flags.C == false);

    // Case 2: 100 / 30 -> quotient 3, remainder 10 -> Z=0, N=0, V=0, C=0
    cpu.reset(false);
    cpu.registers.SR.setFlag(.X);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x0064);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x001E);
    const divx_small = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.DIV(&cpu, divx_small);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x0003);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x000A);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == false);
    try expect(cpu.registers.SR.flags.V == false);
    try expect(cpu.registers.SR.flags.C == false);

    // Case 3: MSB set in quotient -> N=1
    cpu.reset(false);
    cpu.registers.SR.setFlag(.X);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0x8000);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0x0001);
    const divx_msb = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
    try Instruction.DIV(&cpu, divx_msb);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R1)) == 0x8000);
    try expect(cpu.registers.readRegister(@intFromEnum(RegistersName.R2)) == 0x0000);
    try expect(cpu.registers.SR.flags.Z == false);
    try expect(cpu.registers.SR.flags.N == true);
    try expect(cpu.registers.SR.flags.V == false);
    try expect(cpu.registers.SR.flags.C == false);

    // Case 4: Dividend equals divisor -> quotient 1, remainder 0 -> Z=0, N=0
    cpu.reset(false);
    cpu.registers.SR.setFlag(.X);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R1), 0xFFFF);
    cpu.registers.writeRegister(@intFromEnum(RegistersName.R2), 0xFFFF);
    const divx_eq = Instruction.pack(0, .DIV, .REGISTER_IMM16, 0, .R1, .R2, 0, 0x0000);
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
    try expect(cpu.registers.SR.flags.T == true); // T flag set on illegal instruction
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
}

// test "ROL - Basic operations" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     cpu.reset(false);

//     // Test 1: ROL by 1 (default)
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x8001;
//     const rol_one = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R1, .R0, 0, 0x0001);
//     try Instruction.ROL(&cpu, rol_one);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] == 0x0003); // Bit 15 rotates to bit 0
//     try expect(cpu.registers.SR.flags.C == true); // Bit that rotated from position 15: (0x8001 >> 15) & 0x0001 = 1
//     try expect(cpu.registers.SR.flags.Z == false);
//     try expect(cpu.registers.SR.flags.N == false);
//     try expect(cpu.registers.SR.flags.V == false);

//     // Test 2: ROL by 4
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] = 0x1234;
//     const rol_four = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R3, .R2, 0, 0x0004);
//     try Instruction.ROL(&cpu, rol_four);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] == 0x2341); // 0x1234 rotated left by 4
//     try expect(cpu.registers.SR.flags.C == true); // (0x1234 >> 12) & 0x0001 = 0x1 & 0x1 = 1

//     // Test 3: ROL by 8 (swap bytes)
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] = 0xABCD;
//     const rol_eight = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R5, .R4, 0, 0x0008);
//     try Instruction.ROL(&cpu, rol_eight);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R5)] == 0xCDAB);
//     try expect(cpu.registers.SR.flags.C == true); // (0xABCD >> 8) & 0x0001 = 0xAB & 0x1 = 1
// }

// test "ROL - Carry flag variations" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test: ROL with carry = 0
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x7FFE; // 0111 1111 1111 1110
//     const rol_no_carry = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0001);
//     try Instruction.ROL(&cpu, rol_no_carry);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] == 0xFFFD);
//     try expect(cpu.registers.SR.flags.C == false); // (0x7FFE >> 15) & 0x1 = 0

//     // Test: ROL by larger amount
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] = 0x0002; // 0000 0000 0000 0010
//     const rol_large = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x000F);
//     try Instruction.ROL(&cpu, rol_large);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] == 0x0001); // Rotated left by 15
//     try expect(cpu.registers.SR.flags.C == true); // (0x0002 >> 1) & 0x1 = 1
// }

// test "ROL - Flag Z and N" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test Z flag (rotating zero stays zero)
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x0000;
//     const rol_zero = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0004);
//     try Instruction.ROL(&cpu, rol_zero);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] == 0x0000);
//     try expect(cpu.registers.SR.flags.Z == true);

//     // Test N flag
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] = 0x4000;
//     const rol_neg = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x0001);
//     try Instruction.ROL(&cpu, rol_neg);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] == 0x8000);
//     try expect(cpu.registers.SR.flags.N == true);
// }

// test "ROL - Rotation amount masking and R0" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test: Rotation > 15 is masked to 0-15
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x1234;
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] = 0x0010; // 16, masked to 0
//     const rol_mask = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R3, .R2, 0, 0x0004); // (16 + 4) & 0xF = 4
//     try Instruction.ROL(&cpu, rol_mask);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] == 0x2341);

//     // Test: R0 destination
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] = 0x1234;
//     const rol_r0 = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R0, .R4, 0, 0x0004);
//     try Instruction.ROL(&cpu, rol_r0);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R0)] == 0x0000); // R0 stays 0
//     try expect(cpu.registers.SR.flags.C == true); // But flags updated
// }

// test "ROL - Zero rotation and illegal mode" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test: ROL by 0 (no change)
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x1234;
//     const rol_zero = Instruction.pack(0, .ROL, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0000);
//     try Instruction.ROL(&cpu, rol_zero);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] == 0x1234);
//     try expect(cpu.registers.SR.flags.C == false); // No rotation, no carry

//     // Illegal mode
//     cpu.reset(false);
//     const rol_illegal = Instruction.pack(0, .ROL, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0010);
//     _ = Instruction.ROL(&cpu, rol_illegal) catch {};
//     try expect(cpu.registers.SR.flags.T == true);
// }

// test "ROR - Basic operations" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     cpu.reset(false);

//     // Test 1: ROR by 1
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x8001;
//     const ror_one = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0001);
//     try Instruction.ROR(&cpu, ror_one);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] == 0xC000); // Bit 0 rotates to bit 15
//     try expect(cpu.registers.SR.flags.C == true); // (0x8001 >> 0) & 0x0001 = 1

//     // Test 2: ROR by 4
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] = 0x1234;
//     const ror_four = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x0004);
//     try Instruction.ROR(&cpu, ror_four);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] == 0x4123); // 0x1234 rotated right by 4
//     try expect(cpu.registers.SR.flags.C == false); // (0x1234 >> 3) & 0x0001 = 0x246 & 0x1 = 0

//     // Test 3: ROR by 8 (swap bytes)
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R5)] = 0xABCD;
//     const ror_eight = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R6, .R5, 0, 0x0008);
//     try Instruction.ROR(&cpu, ror_eight);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R6)] == 0xCDAB);
//     try expect(cpu.registers.SR.flags.C == true); // (0xABCD >> 7) & 0x1 = 0x157 & 0x1 = 1
// }

// test "ROR - Carry flag variations" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test: ROR with carry = 0
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0xFFFE; // Last bit is 0
//     const ror_no_carry = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0001);
//     try Instruction.ROR(&cpu, ror_no_carry);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] == 0x7FFF);
//     try expect(cpu.registers.SR.flags.C == false); // (0xFFFE >> 0) & 0x1 = 0

//     // Test: ROR with carry = 1
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] = 0x0007; // 0000 0000 0000 0111
//     const ror_carry = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x0002);
//     try Instruction.ROR(&cpu, ror_carry);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] == 0xC001); // Rotated right by 2
//     try expect(cpu.registers.SR.flags.C == true); // (0x0007 >> 1) & 0x1 = 0x3 & 0x1 = 1
// }

// test "ROR - Flag Z and N" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test Z flag
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x0000;
//     const ror_zero = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0004);
//     try Instruction.ROR(&cpu, ror_zero);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] == 0x0000);
//     try expect(cpu.registers.SR.flags.Z == true);

//     // Test N flag
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] = 0x0001;
//     const ror_neg = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x0001);
//     try Instruction.ROR(&cpu, ror_neg);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] == 0x8000);
//     try expect(cpu.registers.SR.flags.N == true);
// }

// test "ROR - Rotation amount masking and R0" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test: Rotation > 15 is masked
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x1234;
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] = 0x001C; // 28, masked to 12
//     const ror_mask = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R3, .R2, 0, 0x0000);
//     try Instruction.ROR(&cpu, ror_mask);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] == 0x2341); // Rotated right by 12 = left by 4

//     // Test: R0 destination
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] = 0x0003;
//     const ror_r0 = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R0, .R4, 0, 0x0001);
//     try Instruction.ROR(&cpu, ror_r0);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R0)] == 0x0000);
//     try expect(cpu.registers.SR.flags.C == true); // Flags still updated
// }

// test "ROR - Zero rotation and illegal mode" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test: ROR by 0
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x1234;
//     const ror_zero = Instruction.pack(0, .ROR, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0000);
//     try Instruction.ROR(&cpu, ror_zero);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] == 0x1234);
//     try expect(cpu.registers.SR.flags.C == false);

//     // Illegal mode
//     cpu.reset(false);
//     const ror_illegal = Instruction.pack(0, .ROR, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0010);
//     _ = Instruction.ROR(&cpu, ror_illegal) catch {};
//     try expect(cpu.registers.SR.flags.T == true);
// }

// test "SHL - Basic operations" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     cpu.reset(false);

//     // Test 1: SHL by 1
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x0001;
//     const shl_one = Instruction.pack(0, .SHL, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0001);
//     try Instruction.SHL(&cpu, shl_one);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] == 0x0002);
//     try expect(cpu.registers.SR.flags.C == false); // (0x0001 >> 15) & 0x1 = 0
//     try expect(cpu.registers.SR.flags.V == false);

//     // Test 2: SHL by 4
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] = 0x0123;
//     const shl_four = Instruction.pack(0, .SHL, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x0004);
//     try Instruction.SHL(&cpu, shl_four);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] == 0x1230);
//     try expect(cpu.registers.SR.flags.C == false); // (0x0123 >> 12) & 0x1 = 0

//     // Test 3: SHL with carry out
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R5)] = 0x8000;
//     const shl_carry = Instruction.pack(0, .SHL, .REGISTER_IMM16, 0, .R6, .R5, 0, 0x0001);
//     try Instruction.SHL(&cpu, shl_carry);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R6)] == 0x0000); // Shifted out
//     try expect(cpu.registers.SR.flags.C == true); // (0x8000 >> 15) & 0x1 = 1
//     try expect(cpu.registers.SR.flags.Z == true);
// }

// test "SHL - Large shifts" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test: SHL by 8
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x00FF;
//     const shl_eight = Instruction.pack(0, .SHL, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0008);
//     try Instruction.SHL(&cpu, shl_eight);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] == 0xFF00);
//     try expect(cpu.registers.SR.flags.C == false); // (0x00FF >> 8) & 0x1 = 0

//     // Test: SHL by 15
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] = 0xFFFF;
//     const shl_fifteen = Instruction.pack(0, .SHL, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x000F);
//     try Instruction.SHL(&cpu, shl_fifteen);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] == 0x8000);
//     try expect(cpu.registers.SR.flags.C == true); // (0xFFFF >> 1) & 0x1 = 1
//     try expect(cpu.registers.SR.flags.N == true);
// }

// test "SHL - Flag Z and N" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test Z flag
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x0000;
//     const shl_zero = Instruction.pack(0, .SHL, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0004);
//     try Instruction.SHL(&cpu, shl_zero);
//     try expect(cpu.registers.SR.flags.Z == true);

//     // Test N flag
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] = 0x4000;
//     const shl_neg = Instruction.pack(0, .SHL, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x0001);
//     try Instruction.SHL(&cpu, shl_neg);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] == 0x8000);
//     try expect(cpu.registers.SR.flags.N == true);
// }

// test "SHL - Shift amount masking and R0" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test: Shift > 15 is masked
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x0001;
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] = 0x0014; // 20, masked to 4
//     const shl_mask = Instruction.pack(0, .SHL, .REGISTER_IMM16, 0, .R3, .R2, 0, 0x0000);
//     try Instruction.SHL(&cpu, shl_mask);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] == 0x0010); // Shifted left by 4

//     // Test: R0 destination
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] = 0x4000;
//     const shl_r0 = Instruction.pack(0, .SHL, .REGISTER_IMM16, 0, .R0, .R4, 0, 0x0001);
//     try Instruction.SHL(&cpu, shl_r0);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R0)] == 0x0000);
//     try expect(cpu.registers.SR.flags.C == false); // (0x4000 >> 15) & 0x1 = 0
//     try expect(cpu.registers.SR.flags.N == true); // Result would be 0x8000
// }

// test "SHL - Zero shift and illegal mode" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test: SHL by 0
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x1234;
//     const shl_zero = Instruction.pack(0, .SHL, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0000);
//     try Instruction.SHL(&cpu, shl_zero);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] == 0x1234);
//     try expect(cpu.registers.SR.flags.C == false);

//     // Illegal mode
//     cpu.reset(false);
//     const shl_illegal = Instruction.pack(0, .SHL, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0010);
//     _ = Instruction.SHL(&cpu, shl_illegal) catch {};
//     try expect(cpu.registers.SR.flags.T == true);
// }

// test "SHR - Basic operations" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     cpu.reset(false);

//     // Test 1: SHR by 1
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x8000;
//     const shr_one = Instruction.pack(0, .SHR, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0001);
//     try Instruction.SHR(&cpu, shr_one);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] == 0x4000);
//     try expect(cpu.registers.SR.flags.C == false); // (0x8000 >> 0) & 0x1 = 0
//     try expect(cpu.registers.SR.flags.N == false); // Logical shift, no sign extension
//     try expect(cpu.registers.SR.flags.V == false);

//     // Test 2: SHR by 4
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] = 0x1230;
//     const shr_four = Instruction.pack(0, .SHR, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x0004);
//     try Instruction.SHR(&cpu, shr_four);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] == 0x0123);
//     try expect(cpu.registers.SR.flags.C == false); // (0x1230 >> 3) & 0x1 = 0x246 & 0x1 = 0

//     // Test 3: SHR with carry out
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R5)] = 0x0001;
//     const shr_carry = Instruction.pack(0, .SHR, .REGISTER_IMM16, 0, .R6, .R5, 0, 0x0001);
//     try Instruction.SHR(&cpu, shr_carry);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R6)] == 0x0000);
//     try expect(cpu.registers.SR.flags.C == true); // (0x0001 >> 0) & 0x1 = 1
//     try expect(cpu.registers.SR.flags.Z == true);
// }

// test "SHR - Large shifts" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test: SHR by 8
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0xFF00;
//     const shr_eight = Instruction.pack(0, .SHR, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0008);
//     try Instruction.SHR(&cpu, shr_eight);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] == 0x00FF);
//     try expect(cpu.registers.SR.flags.C == false); // (0xFF00 >> 7) & 0x1 = 0x1FE & 0x1 = 0

//     // Test: SHR by 15
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] = 0xFFFF;
//     const shr_fifteen = Instruction.pack(0, .SHR, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x000F);
//     try Instruction.SHR(&cpu, shr_fifteen);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] == 0x0001);
//     try expect(cpu.registers.SR.flags.C == true); // (0xFFFF >> 14) & 0x1 = 1
// }

// test "SHR - Flag Z and N" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test Z flag
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x0001;
//     const shr_zero = Instruction.pack(0, .SHR, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0001);
//     try Instruction.SHR(&cpu, shr_zero);
//     try expect(cpu.registers.SR.flags.Z == true);

//     // Test N flag (should always be 0 for logical shift right)
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] = 0xFFFF;
//     const shr_no_neg = Instruction.pack(0, .SHR, .REGISTER_IMM16, 0, .R4, .R3, 0, 0x0001);
//     try Instruction.SHR(&cpu, shr_no_neg);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] == 0x7FFF);
//     try expect(cpu.registers.SR.flags.N == false); // Bit 15 is 0 after logical shift
// }

// test "SHR - Shift amount masking and R0" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);

//     // Test: Shift > 15 is masked
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x1000;
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] = 0x0018; // 24, masked to 8
//     const shr_mask = Instruction.pack(0, .SHR, .REGISTER_IMM16, 0, .R3, .R2, 0, 0x0000);
//     try Instruction.SHR(&cpu, shr_mask);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R3)] == 0x0010); // Shifted right by 8
//     // Test: R0 destination
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R4)] = 0x0003;
//     const shr_r0 = Instruction.pack(0, .SHR, .REGISTER_IMM16, 0, .R0, .R4, 0, 0x0001);
//     try Instruction.SHR(&cpu, shr_r0);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R0)] == 0x0000);
//     try expect(cpu.registers.SR.flags.C == true); // (0x0003 >> 0) & 0x1 = 1
// }
// test "SHR - Zero shift and illegal mode" {
//     const allocator = std.testing.allocator;
//     var cpu = try CPU.init(allocator);
//     defer cpu.deinit(allocator);
//     // Test: SHR by 0
//     cpu.reset(false);
//     cpu.registers.asArray()[@intFromEnum(RegistersName.R1)] = 0x1234;
//     const shr_zero = Instruction.pack(0, .SHR, .REGISTER_IMM16, 0, .R2, .R1, 0, 0x0000);
//     try Instruction.SHR(&cpu, shr_zero);
//     try expect(cpu.registers.asArray()[@intFromEnum(RegistersName.R2)] == 0x1234);
//     try expect(cpu.registers.SR.flags.C == false);

//     // Illegal mode
//     cpu.reset(false);
//     const shr_illegal = Instruction.pack(0, .SHR, .OFFSET_INDEXED, 0, .R1, .R2, 0, 0x0010);
//     _ = Instruction.SHR(&cpu, shr_illegal) catch {};
//     try expect(cpu.registers.SR.flags.T == true);
// }
