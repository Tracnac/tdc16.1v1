const std = @import("std");
const tdc16_1v1 = @import("tdc16_1v1");
const expect = std.testing.expect;

pub fn main() !void {
    // Create an allocator
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    // Display a packed bytecode
    tdc16_1v1.Instruction.displayPacked(0x12345678);

    // Display an unpacked instruction
    const instr = tdc16_1v1.Instruction.pack(0, .ADD, .REGISTER_IMM16, 1, .R1, .R2, 0, 100);
    instr.displayUnpacked();

    // Example 1: Assemble from buffer
    std.debug.print("\n=== Assembling from buffer ===\n", .{});
    const asm_source =
        \\.START
        \\SUB R4, R5
        \\LD R7, (SP)
        \\.END
    ;

    std.debug.print("Source:\n{s}\n\n", .{asm_source});
    std.debug.print("Validating tokens...\n", .{});

    if (tdc16_1v1.assembler.assembleFromBuffer(allocator, asm_source)) {
        std.debug.print("Assembly from buffer successful!\n", .{});
    } else |err| {
        std.debug.print("Assembly from buffer failed: {}\n", .{err});
    }

    // Example 2: Assemble from file
    std.debug.print("\n=== Assembling from file ===\n", .{});
    const test_file = "test_program.asm";

    std.debug.print("Attempting to assemble from file: {s}\n", .{test_file});

    if (tdc16_1v1.assembler.assembleFromFile(allocator, test_file)) {
        std.debug.print("Assembly from file successful!\n", .{});
    } else |err| {
        switch (err) {
            tdc16_1v1.assembler.AsmError.FileNotFound => {
                std.debug.print("File not found: {s}\n", .{test_file});
            },
            tdc16_1v1.assembler.AsmError.FileReadError => {
                std.debug.print("Error reading file: {s}\n", .{test_file});
            },
            tdc16_1v1.assembler.AsmError.InvalidSyntax => {
                std.debug.print("Assembly syntax error in file\n", .{});
            },
            error.OutOfMemory => {
                std.debug.print("Out of memory\n", .{});
            },
        }
    }

    std.debug.print("\n", .{});
}
