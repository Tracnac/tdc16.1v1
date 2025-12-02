const std = @import("std");
const tdc16_1v1 = @import("tdc16_1v1");
const expect = std.testing.expect;

pub fn main() !void {
    // Create an allocator
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    var cpu = try tdc16_1v1.CPU.init(allocator);
    defer cpu.deinit(allocator);
}
