const std = @import("std");
const tdc16_1v1 = @import("tdc16_1v1");
const expect = std.testing.expect;

pub fn main() !void {
    // Create an allocator
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    // Parse command-line arguments
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    // Check for command-line switches
    if (args.len > 1) {
        const command = args[1];

        if (std.mem.eql(u8, command, "--assemble") or std.mem.eql(u8, command, "-a")) {
            if (args.len < 3) {
                std.debug.print("Usage: {s} --assemble <asmfile>\n", .{args[0]});
                return;
            }
            try assembleFile(allocator, args[2]);
            return;
        } else if (std.mem.eql(u8, command, "--disassemble") or std.mem.eql(u8, command, "-d")) {
            if (args.len < 3) {
                std.debug.print("Usage: {s} --disassemble <binaryfile.bin>\n", .{args[0]});
                return;
            }
            try disassembleFile(allocator, args[2]);
            return;
        } else if (std.mem.eql(u8, command, "--uploadRam") or std.mem.eql(u8, command, "-ur")) {
            if (args.len < 3) {
                std.debug.print("Usage: {s} --uploadRam <binaryfile.bin>\n", .{args[0]});
                return;
            }
            try uploadToRam(allocator, args[2]);
            return;
        } else if (std.mem.eql(u8, command, "--uploadRom") or std.mem.eql(u8, command, "-urom")) {
            if (args.len < 3) {
                std.debug.print("Usage: {s} --uploadRom <binaryfile.bin>\n", .{args[0]});
                return;
            }
            try uploadToRom(allocator, args[2]);
            return;
        } else if (std.mem.eql(u8, command, "--help") or std.mem.eql(u8, command, "-h")) {
            printHelp(args[0]);
            return;
        } else {
            std.debug.print("Unknown command: {s}\n", .{command});
            printHelp(args[0]);
            return;
        }
    }

    // No command-line args, run demo mode
    runDemo(allocator) catch |err| {
        std.debug.print("Demo failed: {}\n", .{err});
    };
}

fn printHelp(program_name: []const u8) void {
    std.debug.print("TDC16.1v1 Assembler and Tools\n\n", .{});
    std.debug.print("Usage: {s} [command] [options]\n\n", .{program_name});
    std.debug.print("Commands:\n", .{});
    std.debug.print("  --assemble, -a <asmfile>           Assemble source file to binary\n", .{});
    std.debug.print("  --disassemble, -d <binfile>        Disassemble binary file\n", .{});
    std.debug.print("  --uploadRam, -ur <binfile>         Upload binary to RAM and execute\n", .{});
    std.debug.print("  --uploadRom, -urom <binfile>       Upload binary to ROM\n", .{});
    std.debug.print("  --help, -h                         Show this help message\n", .{});
    std.debug.print("\nIf no command is specified, runs in demo mode.\n", .{});
}

fn assembleFile(allocator: std.mem.Allocator, filename: []const u8) !void {
    std.debug.print("=== Assembling {s} ===\n", .{filename});

    // Read the source file
    const file = std.fs.cwd().openFile(filename, .{}) catch |err| {
        std.debug.print("Error: Cannot open file '{s}': {}\n", .{ filename, err });
        return;
    };
    defer file.close();

    const source = file.readToEndAlloc(allocator, 1024 * 1024) catch |err| {
        std.debug.print("Error: Cannot read file '{s}': {}\n", .{ filename, err });
        return;
    };
    defer allocator.free(source);

    // First pass
    const parsed_lines_result = tdc16_1v1.assembler.firstPass(allocator, source) catch |err| {
        std.debug.print("First pass failed: {}\n", .{err});
        return;
    };
    var parsed_lines = parsed_lines_result;
    defer {
        for (parsed_lines.items) |line| {
            if (line.label) |lbl| allocator.free(lbl);
            if (line.directive) |dir| allocator.free(dir);
            if (line.instruction) |inst| inst.deinit(allocator);
        }
        parsed_lines.deinit(allocator);
    }

    std.debug.print("First pass: Parsed {d} lines\n", .{parsed_lines.items.len});

    // Second pass
    const result = tdc16_1v1.assembler.secondPass(allocator, parsed_lines.items) catch |err| {
        std.debug.print("Second pass failed: {}\n", .{err});
        return;
    };
    var instructions = result.instructions;
    var symbols = result.symbols;
    defer {
        instructions.deinit(allocator);
        symbols.deinit();
    }

    std.debug.print("Second pass: Generated {d} instructions\n", .{instructions.items.len});

    // Write binary output
    const out_filename = try std.fmt.allocPrint(allocator, "{s}.bin", .{filename});
    defer allocator.free(out_filename);

    const out_file = std.fs.cwd().createFile(out_filename, .{}) catch |err| {
        std.debug.print("Error: Cannot create output file '{s}': {}\n", .{ out_filename, err });
        return;
    };
    defer out_file.close();

    // Write bytecode in big-endian format (32-bit words)
    for (instructions.items) |inst| {
        const bytes = [_]u8{
            @intCast((inst.bytecode >> 24) & 0xFF),
            @intCast((inst.bytecode >> 16) & 0xFF),
            @intCast((inst.bytecode >> 8) & 0xFF),
            @intCast(inst.bytecode & 0xFF),
        };
        _ = out_file.write(&bytes) catch |err| {
            std.debug.print("Error writing to output file: {}\n", .{err});
            return;
        };
    }

    std.debug.print("Output written to: {s}\n", .{out_filename});
    std.debug.print("Total size: {d} bytes\n", .{instructions.items.len * 4});
}

fn disassembleFile(allocator: std.mem.Allocator, filename: []const u8) !void {
    std.debug.print("=== Disassembling {s} ===\n", .{filename});

    const file = std.fs.cwd().openFile(filename, .{}) catch |err| {
        std.debug.print("Error: Cannot open file '{s}': {}\n", .{ filename, err });
        return;
    };
    defer file.close();

    const data = file.readToEndAlloc(allocator, 1024 * 1024) catch |err| {
        std.debug.print("Error: Cannot read file '{s}': {}\n", .{ filename, err });
        return;
    };
    defer allocator.free(data);

    if (data.len % 4 != 0) {
        std.debug.print("Warning: File size is not a multiple of 4 bytes\n", .{});
    }

    std.debug.print("File size: {d} bytes ({d} instructions)\n\n", .{ data.len, data.len / 4 });

    var address: u16 = 0;
    var i: usize = 0;
    while (i + 3 < data.len) : (i += 4) {
        const bytecode = (@as(u32, data[i]) << 24) |
            (@as(u32, data[i + 1]) << 16) |
            (@as(u32, data[i + 2]) << 8) |
            @as(u32, data[i + 3]);

        std.debug.print("0x{X:0>4}: ", .{address});
        tdc16_1v1.Instruction.displayPacked(bytecode);
        address += 4;
    }
}

fn uploadToRam(allocator: std.mem.Allocator, filename: []const u8) !void {
    std.debug.print("=== Uploading {s} to RAM ===\n", .{filename});

    const file = std.fs.cwd().openFile(filename, .{}) catch |err| {
        std.debug.print("Error: Cannot open file '{s}': {}\n", .{ filename, err });
        return;
    };
    defer file.close();

    const data = file.readToEndAlloc(allocator, 1024 * 1024) catch |err| {
        std.debug.print("Error: Cannot read file '{s}': {}\n", .{ filename, err });
        return;
    };
    defer allocator.free(data);

    if (data.len % 4 != 0) {
        std.debug.print("Warning: File size is not a multiple of 4 bytes\n", .{});
    }

    // Create CPU (which already includes RAM and ROM)
    var cpu = try tdc16_1v1.CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Load binary into CPU's RAM at address 0
    var i: usize = 0;
    while (i + 3 < data.len) : (i += 4) {
        const bytecode = (@as(u32, data[i]) << 24) |
            (@as(u32, data[i + 1]) << 16) |
            (@as(u32, data[i + 2]) << 8) |
            @as(u32, data[i + 3]);

        const address: u16 = @intCast(i);
        cpu.ram.write32(address, bytecode);
    }
    cpu.registers.PC = 0; // Start execution at address 0

    std.debug.print("Loaded {d} bytes into RAM\n", .{data.len});
    std.debug.print("Starting execution at PC=0x0000\n", .{});

    // Execute a limited number of instructions (safety)
    const max_instructions = 1000;
    var count: usize = 0;
    while (count < max_instructions) : (count += 1) {
        const pc = cpu.registers.PC;
        const instr_raw = cpu.ram.read32(pc);
        const instr = tdc16_1v1.Instruction.unpack(instr_raw);

        std.debug.print("[{d}] PC=0x{X:0>4}: ", .{ count, pc });
        instr.displayUnpacked();

        cpu.step() catch |err| {
            std.debug.print("Execution error: {}\n", .{err});
            break;
        };

        // Check for halt or infinite loop (SWI opcode is 15)
        if (instr.bytecode.opcode == 15) {
            std.debug.print("SWI encountered, halting\n", .{});
            break;
        }

        if (cpu.registers.PC == pc) {
            std.debug.print("Infinite loop detected at 0x{X:0>4}, halting\n", .{pc});
            break;
        }
    }

    std.debug.print("\nFinal CPU state:\n", .{});
    std.debug.print("  PC = 0x{X:0>4}\n", .{cpu.registers.PC});
    std.debug.print("  SR = 0x{X:0>4}\n", .{cpu.registers.SR.raw});
    std.debug.print("  SP = 0x{X:0>4}\n", .{cpu.registers.SP});
    for (0..16) |reg| {
        const value = cpu.registers.readRegister(@intCast(reg));
        std.debug.print("  R{d} = 0x{X:0>4}\n", .{ reg, value });
    }
}

fn uploadToRom(allocator: std.mem.Allocator, filename: []const u8) !void {
    std.debug.print("=== Uploading {s} to ROM ===\n", .{filename});

    const file = std.fs.cwd().openFile(filename, .{}) catch |err| {
        std.debug.print("Error: Cannot open file '{s}': {}\n", .{ filename, err });
        return;
    };
    defer file.close();

    const data = file.readToEndAlloc(allocator, 1024 * 1024) catch |err| {
        std.debug.print("Error: Cannot read file '{s}': {}\n", .{ filename, err });
        return;
    };
    defer allocator.free(data);

    if (data.len % 4 != 0) {
        std.debug.print("Warning: File size is not a multiple of 4 bytes\n", .{});
    }

    // Create CPU (which already includes RAM and ROM)
    var cpu = try tdc16_1v1.CPU.init(allocator);
    defer cpu.deinit(allocator);

    // Load binary data into CPU's ROM
    try cpu.rom.loadROM(data);
    cpu.registers.PC = 0;

    std.debug.print("Loaded {d} bytes into ROM\n", .{data.len});
    std.debug.print("ROM is read-only, program ready for execution\n", .{});
    std.debug.print("Starting PC=0x0000\n", .{});
}

fn runDemo(allocator: std.mem.Allocator) !void {
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
            tdc16_1v1.assembler.AsmError.InvalidRegister => {
                std.debug.print("Invalid register in file\n", .{});
            },
            tdc16_1v1.assembler.AsmError.InvalidImmediate => {
                std.debug.print("Invalid immediate value in file\n", .{});
            },
            tdc16_1v1.assembler.AsmError.InvalidOpcode => {
                std.debug.print("Invalid opcode in file\n", .{});
            },
            error.OutOfMemory => {
                std.debug.print("Out of memory\n", .{});
            },
        }
    }

    // Example 3: First pass - parse and encode instructions
    std.debug.print("\n=== Two-Pass Compilation Demo ===\n", .{});
    const simple_program =
        \\START:
        \\  ADD R1, R2
        \\  SUB R3, 5
        \\  LD R4, R5
        \\LOOP:
        \\  MUL R6, R7
        \\  DIV R8, 10
        \\  BNE LOOP
        \\  BEQ START
        \\.END
    ;

    if (tdc16_1v1.assembler.firstPass(allocator, simple_program)) |parsed_lines_result| {
        var parsed_lines = parsed_lines_result;
        defer {
            for (parsed_lines.items) |line| {
                if (line.label) |lbl| allocator.free(lbl);
                if (line.directive) |dir| allocator.free(dir);
                if (line.instruction) |inst| inst.deinit(allocator);
            }
            parsed_lines.deinit(allocator);
        }

        std.debug.print("Parsed {d} lines:\n", .{parsed_lines.items.len});
        for (parsed_lines.items) |line| {
            std.debug.print("Line {d}: ", .{line.line_num});
            if (line.label) |lbl| {
                std.debug.print("Label={s} ", .{lbl});
            }
            if (line.directive) |dir| {
                std.debug.print("Directive={s} ", .{dir});
            }
            if (line.instruction) |ins| {
                std.debug.print("Instruction={s} operands=[", .{ins.opcode});
                for (ins.operands, 0..) |op, i| {
                    if (i > 0) std.debug.print(", ", .{});
                    std.debug.print("{s}", .{op});
                }
                std.debug.print("]", .{});
            }
            std.debug.print("\n", .{});
        }

        // Now run second pass
        std.debug.print("\n=== Second Pass Compilation ===\n", .{});
        if (tdc16_1v1.assembler.secondPass(allocator, parsed_lines.items)) |result| {
            var instructions = result.instructions;
            var symbols = result.symbols;
            defer {
                instructions.deinit(allocator);
                symbols.deinit();
            }

            std.debug.print("Symbol Table:\n", .{});
            var symbol_iter = symbols.symbols.iterator();
            while (symbol_iter.next()) |entry| {
                std.debug.print("  {s} = 0x{X:0>4}\n", .{ entry.key_ptr.*, entry.value_ptr.* });
            }

            std.debug.print("\nGenerated {d} instructions:\n", .{instructions.items.len});
            for (instructions.items) |inst| {
                std.debug.print("  0x{X:0>4}: 0x{X:0>8} ; Line {d}: {s}\n", .{
                    inst.address,
                    inst.bytecode,
                    inst.line_num,
                    inst.raw_line,
                });
            }
        } else |err| {
            std.debug.print("Second pass failed: {}\n", .{err});
        }
    } else |err| {
        std.debug.print("First pass failed: {}\n", .{err});
    }

    std.debug.print("\n", .{});
}
