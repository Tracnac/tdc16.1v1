const std = @import("std");
const native_endian = @import("builtin").target.cpu.arch.endian();
const expect = std.testing.expect;

const memory_endian = .big;

pub const Ram = struct {
    ram: *[64 * 1024]u8,

    pub fn init(allocator: std.mem.Allocator) !Ram {
        return Ram{ .ram = try allocator.create([64 * 1024]u8) };
    }

    pub fn deinit(self: *Ram, allocator: std.mem.Allocator) void {
        allocator.destroy(self.ram);
    }

    pub fn read8(self: *Ram, address: u16) u8 {
        return self.ram[address];
    }

    pub fn write8(self: *Ram, address: u16, value: u8) void {
        self.ram[address] = value;
    }

    pub fn read16(self: *Ram, address: u16) u16 {
        return std.mem.readInt(u16, self.ram[address..][0..2], memory_endian);
    }

    pub fn write16(self: *Ram, address: u16, value: u16) void {
        std.mem.writeInt(u16, self.ram[address..][0..2], value, memory_endian);
    }

    pub fn read32(self: *Ram, address: u16) u32 {
        return std.mem.readInt(u32, self.ram[address..][0..4], memory_endian);
    }

    pub fn write32(self: *Ram, address: u16, value: u32) void {
        std.mem.writeInt(u32, self.ram[address..][0..4], value, memory_endian);
    }
};

pub const Rom = struct {
    rom: *[8 * 1024]u8,

    pub fn init(allocator: std.mem.Allocator) !Rom {
        return Rom{ .rom = try allocator.create([8 * 1024]u8) };
    }

    pub fn deinit(self: *Rom, allocator: std.mem.Allocator) void {
        allocator.destroy(self.rom);
    }

    pub fn loadROM(self: *Rom, rom_data: []const u8) !void {
        if (rom_data.len > self.rom.len) return error.ROM_MAXLENGTH;
        @memcpy(self.rom[0..rom_data.len], rom_data);
    }

    pub fn read8(self: *Rom, address: u16) u8 {
        return self.rom[address];
    }

    pub fn read16(self: *Rom, address: u16) u16 {
        return std.mem.readInt(u16, self.rom[address..][0..2], memory_endian);
    }

    pub fn read32(self: *Rom, address: u16) u32 {
        return std.mem.readInt(u32, self.rom[address..][0..4], memory_endian);
    }
};

// Yes I know this tests look silly, but I'm "Chat echaudé craint l'eau froide",
// yes I'm looking at you C.

test "read16 Big Endian" {
    const CPU = @import("cpu.zig").CPU;
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.ram.write8(0, 0x12);
    cpu.ram.write8(1, 0x34);
    try expect(cpu.ram.read16(0) == 0x1234);
}

test "write16 Big Endian" {
    const CPU = @import("cpu.zig").CPU;
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.ram.write16(0, 0xABCD);
    try expect(cpu.ram.read8(0) == 0xAB);
    try expect(cpu.ram.read8(1) == 0xCD);
}

test "read32 Big Endian" {
    const CPU = @import("cpu.zig").CPU;
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.ram.write8(0, 0x12);
    cpu.ram.write8(1, 0x34);
    cpu.ram.write8(2, 0x56);
    cpu.ram.write8(3, 0x78);
    try expect(cpu.ram.read32(0) == 0x12345678);
}

test "write32 Big Endian" {
    const CPU = @import("cpu.zig").CPU;
    const allocator = std.testing.allocator;
    var cpu = try CPU.init(allocator);
    defer cpu.deinit(allocator);

    cpu.ram.write32(0, 0xABCDEF12);
    try expect(cpu.ram.read8(0) == 0xAB);
    try expect(cpu.ram.read8(1) == 0xCD);
    try expect(cpu.ram.read8(2) == 0xEF);
    try expect(cpu.ram.read8(3) == 0x12);
}
