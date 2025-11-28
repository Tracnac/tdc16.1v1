const std = @import("std");
const native_endian = @import("builtin").target.cpu.arch.endian();
const expect = std.testing.expect;
const CPU = @import("cpu.zig").CPU;
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
