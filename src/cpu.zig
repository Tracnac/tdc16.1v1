//! By convention, root.zig is the root source file when making a library.
const std = @import("std");
const native_endian = @import("builtin").target.cpu.arch.endian();
const expect = std.testing.expect;
const Ram = @import("memory.zig").Ram;
const Rom = @import("memory.zig").Rom;
pub const Instruction = @import("instruction.zig").Instruction;

pub const CPU = struct {
    registers: Registers,
    ram: Ram,
    rom: Rom,

    pub fn init(allocator: std.mem.Allocator) !CPU {
        return CPU{
            .registers = Registers{},
            .ram = try Ram.init(allocator),
            .rom = try Rom.init(allocator),
        };
    }

    pub fn deinit(self: *CPU, allocator: std.mem.Allocator) void {
        self.ram.deinit(allocator);
        self.rom.deinit(allocator);
    }

    pub fn reset(self: *CPU, clear_rom: bool) void {
        // Reset all registers to 0 (including SR and PC)
        self.registers = Registers{};

        // Clear RAM
        @memset(self.ram.ram, 0);

        // Optionally clear ROM
        if (clear_rom) {
            @memset(self.rom.rom, 0);
        }
    }

    pub fn fetch(self: *CPU) Instruction {
        const pc = self.registers.PC;

        const raw: u32 = self.ram.read32(pc);
        // Increment PC by 4
        self.registers.PC += 4;

        return Instruction{ .raw = raw };
    }

    pub fn step(self: *CPU) !void {
        const instruction = self.fetch();
        try instruction.execute(self);
    }
};

pub const Registers = struct {
    R0: u16 = 0,
    R1: u16 = 0,
    R2: u16 = 0,
    R3: u16 = 0,
    R4: u16 = 0,
    R5: u16 = 0,
    R6: u16 = 0,
    R7: u16 = 0,
    R8: u16 = 0,
    R9: u16 = 0,
    R10: u16 = 0,
    R11: u16 = 0,
    R12: u16 = 0,
    SR: SRType = SRType{ .raw = 0 },
    SP: u16 = 0xFFFE,
    PC: u16 = 0,

    pub fn asArray(self: *Registers) *[16]u16 {
        return @ptrCast(self);
    }

    pub fn writeRegister(self: *Registers, index: u4, value: u16) void {
        if (index == 0) return;
        self.asArray()[index] = value;
    }

    pub fn readRegister(self: *Registers, index: u4) u16 {
        return self.asArray()[index];
    }

    pub fn pushSP(self: *Registers, value: u16) void {
        _ = self;
        _ = value;
    }

    pub fn popSP(self: *Registers) u16 {
        _ = self;
    }
};

pub const RegistersName = enum(u4) {
    R0 = 0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
};

// Define alias for R13, R14, R15
pub const SR = RegistersName.R13;
pub const SP = RegistersName.R14;
pub const PC = RegistersName.R15;

pub const SRFlags = enum(u4) {
    N = 0,
    Z,
    C,
    V,
    X,
    S = 14,
    T = 15,
};

pub const SRType = packed union {
    raw: u16,
    flags: packed struct(u16) {
        N: bool,
        Z: bool,
        C: bool,
        V: bool,
        X: bool,
        usr: u3, // Not used
        sys: u6, // Not used
        S: bool,
        T: bool,
    },

    pub fn setFlag(self: *SRType, flag: SRFlags) void {
        const bit: u4 = @intFromEnum(flag);
        self.raw |= (@as(u16, 1) << bit);
    }

    pub fn clearFlag(self: *SRType, flag: SRFlags) void {
        const bit: u4 = @intFromEnum(flag);
        self.raw &= ~(@as(u16, 1) << bit);
    }

    pub fn getFlag(self: SRType, flag: SRFlags) bool {
        const bit: u4 = @intFromEnum(flag);
        return (self.raw & (@as(u16, 1) << bit)) != 0;
    }

    pub fn toggleFlag(self: *SRType, flag: SRFlags) void {
        const bit: u4 = @intFromEnum(flag);
        self.raw ^= (@as(u16, 1) << bit);
    }

    pub fn updateFlag(self: *SRType, flag: SRFlags, value: bool) void {
        const bit: u4 = @intFromEnum(flag);
        if (value) {
            self.raw |= (@as(u16, 1) << bit);
        } else {
            self.raw &= ~(@as(u16, 1) << bit);
        }
    }
    // Update N and Z flags based on result
    pub fn updateNZ(self: *SRType, result: u16) void {
        self.flags.N = (result & 0x8000) != 0; // Bit 15 = negative
        self.flags.Z = (result == 0);
    }

    // Update C and V flags for addition
    // ADD Rd, Rs, imm  →  Rd = Rs + imm
    pub fn updateCV_Add(self: *SRType, rs: u16, operand: u16, result: u32) void {
        // Carry: unsigned overflow (result exceeds 16 bits)
        self.flags.C = (result > 0xFFFF);

        // Overflow: signed overflow occurs when:
        // - Both operands have the same sign, AND
        // - Result has a different sign
        const rs_negative = (rs & 0x8000) != 0;
        const operand_negative = (operand & 0x8000) != 0;
        const result_negative = (result & 0x8000) != 0;
        self.flags.V = (rs_negative == operand_negative) and (rs_negative != result_negative);
    }

    // Update C and V flags for subtraction (ARM-style: C=1 means NO borrow)
    // SUB Rd, Rs, imm  →  Rd = Rd - Rs  or  Rd = Rd - imm
    pub fn updateCV_Sub(self: *SRType, rd: u16, operand: u16, result: u32) void {
        // ARM-style: C=1 means NO borrow, C=0 means borrow occurred
        // No borrow when rd >= operand (sufficient to subtract)
        self.flags.C = (rd >= operand);

        // Overflow: signed overflow occurs when:
        // - Operands have different signs, AND
        // - Result has different sign from rd (minuend)
        const rd_negative = (rd & 0x8000) != 0;
        const operand_negative = (operand & 0x8000) != 0;
        const result_negative = (result & 0x8000) != 0;
        self.flags.V = (rd_negative != operand_negative) and (rd_negative != result_negative);
    }

    // Update all arithmetic flags at once
    pub fn updateArithmeticFlags(self: *SRType, rd: u16, rs_or_operand: u16, result: u32, is_add: bool) void {
        self.updateNZ(@truncate(result));
        if (is_add) {
            self.updateCV_Add(rd, rs_or_operand, result);
        } else {
            self.updateCV_Sub(rd, rs_or_operand, result);
        }
    }

    // Clear C and V flags (used by logical operations: AND, OR, XOR)
    pub fn clearCV(self: *SRType) void {
        self.flags.C = false;
        self.flags.V = false;
    }

    // Update flags for shift/rotate operations
    pub fn updateShiftRotateFlags(self: *SRType, result: u16, carry_out: bool) void {
        self.updateNZ(result);
        self.flags.C = carry_out;
        self.flags.V = false; // V is cleared for shift/rotate operations
    }

    // Update flags for multiplication
    // MUL Rd, Rs, imm  →  Rd = Rs * imm
    pub fn updateMultiplyFlags(self: *SRType, result: u16, overflow: bool) void {
        self.updateNZ(result);
        self.flags.V = overflow; // Set if result doesn't fit in 16 bits
    }

    // Update flags for division
    // DIV Rd, Rs  →  Rd = Rd / Rs
    pub fn updateDivideFlags(self: *SRType, quotient: u16, divide_by_zero: bool) void {
        self.updateNZ(quotient);
        self.flags.V = divide_by_zero; // Set on divide-by-zero
    }
};

pub const Trap = enum(u5) {
    Stack_error = 0,
    Division_by_zero,
    Illegal_instruction,
    Illegal_memory_access,
    Bus_error,
};

test "Flags Offsets and Bytes align" {
    comptime {
        const FlagsType = @TypeOf(@as(SRType, undefined).flags);

        try expect(@bitOffsetOf(FlagsType, "N") == 0);
        try expect(@bitOffsetOf(FlagsType, "Z") == 1);
        try expect(@bitOffsetOf(FlagsType, "C") == 2);
        try expect(@bitOffsetOf(FlagsType, "V") == 3);
        try expect(@bitOffsetOf(FlagsType, "X") == 4);
        try expect(@bitOffsetOf(FlagsType, "S") == 14);
        try expect(@bitOffsetOf(FlagsType, "T") == 15);

        try expect(@offsetOf(FlagsType, "N") == 0);
        try expect(@offsetOf(FlagsType, "Z") == 0);
        try expect(@offsetOf(FlagsType, "C") == 0);
        try expect(@offsetOf(FlagsType, "V") == 0);
        try expect(@offsetOf(FlagsType, "X") == 0);
        try expect(@offsetOf(FlagsType, "usr") == 0);

        try expect(@offsetOf(FlagsType, "sys") == 1);

        try expect(@offsetOf(FlagsType, "S") == 1);
        try expect(@offsetOf(FlagsType, "T") == 1);
    }
}

test "Check SR flags by SR" {
    {
        const allocator = std.testing.allocator;

        var cpu = try CPU.init(allocator);
        defer cpu.deinit(allocator);

        cpu.registers.SR.raw = 0b101;
        try expect(cpu.registers.SR.flags.N == true);
        try expect(cpu.registers.SR.flags.Z == false);
        try expect(cpu.registers.SR.flags.C == true);
    }
}

test "Check SR flags by flag" {
    {
        const allocator = std.testing.allocator;

        var cpu = try CPU.init(allocator);
        defer cpu.deinit(allocator);

        cpu.registers.SR.flags.N = true;
        try expect(cpu.registers.SR.flags.N == true);
        try expect(cpu.registers.SR.flags.Z == false);
        try expect(cpu.registers.SR.raw == 0b1);
    }
}

test "Check SR.T must be MSB" {
    {
        const allocator = std.testing.allocator;
        var cpu = try CPU.init(allocator);
        defer cpu.deinit(allocator);

        cpu.registers.SR.flags.T = true;
        switch (native_endian) {
            .big => {
                // MSB is in the first byte
                const bytes: [2]u8 = @bitCast(cpu.registers.SR.raw);
                try expect(bytes[0] == 0b10000000);
                try expect(bytes[1] == 0b00000000);
            },
            .little => {
                // MSB is in the second byte
                const bytes: [2]u8 = @bitCast(cpu.registers.SR.raw);
                try expect(bytes[0] == 0b00000000);
                try expect(bytes[1] == 0b10000000);
            },
        }

        // Regardless of endianness, T=true should set bit 15
        try expect(cpu.registers.SR.raw == 0b1000000000000000);
        try expect(cpu.registers.SR.raw == 0x8000);
    }
}

test "CPU init allocates memory" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    try expect(cpu.ram.ram.len == 64 * 1024);
    try expect(cpu.rom.rom.len == 8 * 1024);
    try expect(cpu.registers.PC == 0);
    try expect(cpu.registers.SP == 0xFFFE);
}

test "CPU reset clears registers" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Modify some registers
    cpu.registers.R0 = 0x1234;
    cpu.registers.R5 = 0x5678;
    cpu.registers.PC = 0xABCD;
    cpu.registers.SR.raw = 0xFFFF;

    // Reset
    cpu.reset(false);

    // Check all registers are reset
    try expect(cpu.registers.R0 == 0);
    try expect(cpu.registers.R5 == 0);
    try expect(cpu.registers.PC == 0);
    try expect(cpu.registers.SP == 0xFFFE);
    try expect(cpu.registers.SR.raw == 0);
}

test "CPU reset clears RAM" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Write some data to RAM
    cpu.ram.write8(0, 0xFF);
    cpu.ram.write8(100, 0xAB);
    cpu.ram.write8(1000, 0xAB);

    cpu.reset(false);

    // RAM should be cleared
    try expect(cpu.ram.read8(0) == 0);
    try expect(cpu.ram.read8(100) == 0);
    try expect(cpu.ram.read8(1000) == 0);
}

test "CPU reset can clear ROM" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Write data to ROM
    cpu.rom.rom[0] = 0xFF;
    cpu.rom.rom[100] = 0xAB;

    // Reset without clearing ROM
    cpu.reset(false);
    try expect(cpu.rom.read8(0) == 0xFF);
    try expect(cpu.rom.read8(100) == 0xAB);

    // Reset with clearing ROM
    cpu.reset(true);
    try expect(cpu.rom.read8(0) == 0);
    try expect(cpu.rom.read8(100) == 0);
}

test "loadROM copies data correctly" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    const rom_data = [_]u8{ 0x12, 0x34, 0x56, 0x78, 0xAB, 0xCD, 0xEF };
    try cpu.rom.loadROM(&rom_data);

    try expect(cpu.rom.read32(0) == 0x12345678);
    try expect(cpu.rom.read16(4) == 0xABCD);
    try expect(cpu.rom.read8(6) == 0xEF);
}

test "loadROM fails if data too large" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Try to load more than 8KB
    var large_rom: [8 * 1024 + 1]u8 = undefined;
    @memset(&large_rom, 0xFF);

    const result = cpu.rom.loadROM(&large_rom);
    try expect(result == error.ROM_MAXLENGTH);
}

test "Registers asArray provides array access" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.registers.R0 = 0x1111;
    cpu.registers.R5 = 0x5555;
    cpu.registers.R12 = 0xCCCC;

    const arr = cpu.registers.asArray();
    try expect(arr[0] == 0x1111);
    try expect(arr[5] == 0x5555);
    try expect(arr[12] == 0xCCCC);

    // Modify via array
    arr[3] = 0x3333;
    try expect(cpu.registers.R3 == 0x3333);
}

test "SRType setFlag sets individual flags" {
    var sr = SRType{ .raw = 0 };

    sr.setFlag(.N);
    try expect(sr.flags.N == true);
    try expect(sr.raw == 0b1);

    sr.setFlag(.Z);
    try expect(sr.flags.Z == true);
    try expect(sr.raw == 0b11);

    sr.setFlag(.C);
    try expect(sr.flags.C == true);
    try expect(sr.raw == 0b111);

    sr.setFlag(.V);
    try expect(sr.flags.V == true);
    try expect(sr.raw == 0b1111);

    sr.setFlag(.X);
    try expect(sr.flags.X == true);
    try expect(sr.raw == 0b11111);

    sr.setFlag(.S);
    try expect(sr.flags.S == true);
    try expect(sr.raw == 0b0100000000011111);

    sr.setFlag(.T);
    try expect(sr.flags.T == true);
    try expect(sr.raw == 0b1100000000011111);
}

test "SRType clearFlag clears individual flags" {
    var sr = SRType{ .raw = 0xFFFF };

    sr.clearFlag(.N);
    try expect(sr.flags.N == false);

    sr.clearFlag(.Z);
    try expect(sr.flags.Z == false);

    sr.clearFlag(.C);
    try expect(sr.flags.C == false);

    sr.clearFlag(.V);
    try expect(sr.flags.V == false);

    sr.clearFlag(.X);
    try expect(sr.flags.X == false);

    sr.clearFlag(.S);
    try expect(sr.flags.S == false);

    sr.clearFlag(.T);
    try expect(sr.flags.T == false);
}

test "SRType getFlag reads individual flags" {
    var sr = SRType{ .raw = 0b101 };

    try expect(sr.getFlag(.N) == true);
    try expect(sr.getFlag(.Z) == false);
    try expect(sr.getFlag(.C) == true);
}

test "SRType toggleFlag flips flags" {
    var sr = SRType{ .raw = 0 };

    sr.toggleFlag(.N);
    try expect(sr.flags.N == true);

    sr.toggleFlag(.N);
    try expect(sr.flags.N == false);
}

test "SRType updateNZ with zero result" {
    var sr = SRType{ .raw = 0 };
    sr.updateNZ(0x0000);

    try expect(sr.flags.Z == true);
    try expect(sr.flags.N == false);
}

test "SRType updateNZ with negative result" {
    var sr = SRType{ .raw = 0 };
    sr.updateNZ(0x8000);

    try expect(sr.flags.Z == false);
    try expect(sr.flags.N == true);
}

test "SRType updateNZ with positive result" {
    var sr = SRType{ .raw = 0 };
    sr.updateNZ(0x1234);

    try expect(sr.flags.Z == false);
    try expect(sr.flags.N == false);
}

test "SRType updateCV_Add with carry" {
    var sr = SRType{ .raw = 0 };
    const a: u16 = 0xFFFF;
    const b: u16 = 0x0002;
    const result: u32 = @as(u32, a) + @as(u32, b);

    sr.updateCV_Add(a, b, result);
    try expect(sr.flags.C == true); // Carry occurred
}

test "SRType updateCV_Add with overflow" {
    var sr = SRType{ .raw = 0 };
    const a: u16 = 0x7FFF; // Max positive
    const b: u16 = 0x0001;
    const result: u32 = @as(u32, a) + @as(u32, b);

    sr.updateCV_Add(a, b, result);
    try expect(sr.flags.V == true); // Overflow occurred
}

test "SRType updateCV_Sub with borrow" {
    var sr = SRType{ .raw = 0 };
    const a: u16 = 0x0001;
    const b: u16 = 0x0002;
    const result: u32 = @as(u32, a) -% @as(u32, b);

    sr.updateCV_Sub(a, b, result);
    try expect(sr.flags.C == false); // Borrow occurred
}

test "SRType updateFlags for addition" {
    var sr = SRType{ .raw = 0 };
    const a: u16 = 0xFFFF;
    const b: u16 = 0x0001;
    const result: u32 = @as(u32, a) + @as(u32, b);

    sr.updateArithmeticFlags(a, b, result, true);
    try expect(sr.flags.Z == true); // Result is 0 (wrapped)
    try expect(sr.flags.C == true); // Carry occurred
}

test "Trap enum values" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    try expect(@intFromEnum(Trap.Stack_error) == 0);
    try expect(@intFromEnum(Trap.Division_by_zero) == 1);
    try expect(@intFromEnum(Trap.Illegal_instruction) == 2);
    try expect(@intFromEnum(Trap.Illegal_memory_access) == 3);
    try expect(@intFromEnum(Trap.Bus_error) == 4);
}

test "readOpcode increments PC" {
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.ram.write32(0, 0x12345678);
    cpu.registers.PC = 0;

    const fetch = cpu.fetch();
    try expect(fetch.raw == 0x12345678);
    try expect(cpu.registers.PC == 4);
}
