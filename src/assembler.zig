const std = @import("std");
const Instruction = @import("instruction.zig").Instruction;
const Opcode = @import("instruction.zig").Opcode;
const Mode = @import("instruction.zig").Mode;
const RegistersName = @import("cpu.zig").RegistersName;

// ============================================================================
// Error Types
// ============================================================================

pub const AsmError = error{
    InvalidSyntax,
    FileNotFound,
    FileReadError,
    InvalidRegister,
    InvalidImmediate,
    InvalidOpcode,
};

pub const TokenError = struct {
    line_num: usize,
    token_idx: usize,
    token: []const u8,
    reason: []const u8,
};

// ============================================================================
// Intermediate Representation
// ============================================================================

pub const ParsedLine = struct {
    line_num: usize,
    label: ?[]const u8,
    directive: ?[]const u8,
    instruction: ?ParsedInstruction,
    raw_line: []const u8,
};

pub const ParsedInstruction = struct {
    opcode: []const u8,
    operands: [][]const u8,
    line_num: usize,

    pub fn deinit(self: ParsedInstruction, allocator: std.mem.Allocator) void {
        for (self.operands) |op| {
            allocator.free(op);
        }
        allocator.free(self.operands);
        allocator.free(self.opcode);
    }
};

pub const CompiledInstruction = struct {
    address: u16,
    bytecode: u32,
    line_num: usize,
    raw_line: []const u8,
};

pub const SymbolTable = struct {
    symbols: std.StringHashMap(u16),

    pub fn init(allocator: std.mem.Allocator) SymbolTable {
        return .{
            .symbols = std.StringHashMap(u16).init(allocator),
        };
    }

    pub fn deinit(self: *SymbolTable) void {
        self.symbols.deinit();
    }

    pub fn put(self: *SymbolTable, name: []const u8, address: u16) !void {
        try self.symbols.put(name, address);
    }

    pub fn get(self: *SymbolTable, name: []const u8) ?u16 {
        return self.symbols.get(name);
    }
};

// ============================================================================
// Text Normalization
// ============================================================================

pub fn normalizeLine(allocator: std.mem.Allocator, line: []const u8) ![]const u8 {
    // Drop comments starting with ; (but not inside quotes or braces)
    var comment_idx: ?usize = null;
    var in_quotes = false;
    var in_braces = false;
    for (line, 0..) |c, i| {
        if (c == '"') {
            in_quotes = !in_quotes;
        } else if (c == '{') {
            in_braces = true;
        } else if (c == '}') {
            in_braces = false;
        } else if (c == ';' and !in_quotes and !in_braces) {
            comment_idx = i;
            break;
        }
    }

    const without_comment = if (comment_idx) |idx|
        line[0..idx]
    else
        line;

    const trimmed = std.mem.trim(u8, without_comment, " \t");
    var result = std.ArrayListUnmanaged(u8){};
    errdefer result.deinit(allocator);

    var in_space = false;
    in_quotes = false;
    in_braces = false;
    for (trimmed) |c| {
        if (c == '"') {
            // Preserve quotes and their content
            try result.append(allocator, c);
            in_quotes = !in_quotes;
            in_space = false;
        } else if (c == '{') {
            // Start of register list
            try result.append(allocator, c);
            in_braces = true;
            in_space = false;
        } else if (c == '}') {
            // End of register list
            try result.append(allocator, c);
            in_braces = false;
            in_space = false;
        } else if (in_quotes or in_braces) {
            // Inside quotes or braces: preserve everything as-is (no case conversion, no comma conversion)
            try result.append(allocator, c);
            in_space = false;
        } else if (c == ' ' or c == '\t' or c == ',') {
            if (!in_space) {
                try result.append(allocator, ',');
                in_space = true;
            }
        } else {
            // Convert to uppercase (outside quotes and braces only)
            const upper_c = if (c >= 'a' and c <= 'z') c - 32 else c;
            try result.append(allocator, upper_c);
            in_space = false;
        }
    }

    return result.toOwnedSlice(allocator);
}

pub fn tokenizeLine(allocator: std.mem.Allocator, line: []const u8) ![]const []const u8 {
    var list = std.ArrayListUnmanaged([]const u8){};
    errdefer list.deinit(allocator);

    var start: usize = 0;
    var i: usize = 0;
    var in_quotes = false;
    var in_braces = false;

    while (i < line.len) : (i += 1) {
        if (line[i] == '"') {
            in_quotes = !in_quotes;
        } else if (line[i] == '{') {
            in_braces = true;
        } else if (line[i] == '}') {
            in_braces = false;
        } else if (line[i] == ',' and !in_quotes and !in_braces) {
            // Found a delimiter outside quotes and braces
            if (i > start) {
                const token = line[start..i];
                if (token.len > 0) {
                    const token_copy = try allocator.dupe(u8, token);
                    errdefer allocator.free(token_copy);
                    try list.append(allocator, token_copy);
                }
            }
            start = i + 1;
        }
    }

    // Add the last token
    if (start < line.len) {
        const token = line[start..];
        if (token.len > 0) {
            const token_copy = try allocator.dupe(u8, token);
            errdefer allocator.free(token_copy);
            try list.append(allocator, token_copy);
        }
    }

    if (list.items.len == 0) {
        list.deinit(allocator);
        return error.InvalidSyntax;
    }

    return list.toOwnedSlice(allocator);
}

// ============================================================================
// Token Types
// ============================================================================

pub const TokenType = enum {
    directive,
    label,
    register,
    opcode,
    immediate,
    addressing_mode, // (Rn) or immediate(Rn)
    label_addressing, // label(Rn)
    register_stack,
    string_literal, // "quoted string"
    register_list, // {R1,R2,R6}
    unknown,
};

pub const Token = struct {
    text: []const u8,
    type: TokenType,

    pub fn classify(text: []const u8) Token {
        return .{
            .text = text,
            .type = classifyTokenType(text),
        };
    }
};

fn classifyTokenType(text: []const u8) TokenType {
    if (text.len == 0) return .unknown;

    if (text[0] == '"' and text.len >= 2 and text[text.len - 1] == '"') return .string_literal;
    if (text[0] == '{' and text.len >= 3 and text[text.len - 1] == '}') return .register_list;
    if (text[0] == '.') return .directive;
    if (std.mem.endsWith(u8, text, ":")) return .label;
    if (isRegister(text)) return .register;
    if (isRegisterStack(text)) return .register_stack;
    if (isLabelAddressing(text)) return .label_addressing;
    if (isAddressingMode(text)) return .addressing_mode;
    if (isOpcode(text)) return .opcode;
    if (isImmediate(text)) return .immediate;

    return .unknown;
}

// ============================================================================
// Validators
// ============================================================================

fn isRegister(text: []const u8) bool {
    if (std.mem.eql(u8, text, "SP") or
        std.mem.eql(u8, text, "PC") or
        std.mem.eql(u8, text, "SR"))
    {
        return true;
    }

    if (text[0] == 'R' and text.len >= 2 and text.len <= 3) {
        const num = std.fmt.parseInt(u8, text[1..], 10) catch return false;
        return num <= 15;
    }

    return false;
}

fn isRegisterStack(text: []const u8) bool {
    return std.mem.eql(u8, text, "(SP)") or
        std.mem.eql(u8, text, "(SP)+") or
        std.mem.eql(u8, text, "-(SP)");
}

fn isLabelAddressing(text: []const u8) bool {
    // label(Rn) format - e.g., LOOP(R5), DATA_START(R2)
    if (std.mem.indexOf(u8, text, "(")) |open_paren| {
        if (open_paren == 0) return false; // Must have label name before (
        if (text[text.len - 1] != ')') return false;

        const label_part = text[0..open_paren];
        const reg_part = text[open_paren + 1 .. text.len - 1];

        // Label part must not be a register or immediate
        // It should be a valid identifier (alphanumeric + underscore/hyphen)
        if (isRegister(label_part) or isImmediate(label_part)) return false;

        for (label_part) |c| {
            const valid = (c >= 'A' and c <= 'Z') or
                (c >= '0' and c <= '9') or
                c == '_' or c == '-';
            if (!valid) return false;
        }

        return isRegister(reg_part);
    }

    return false;
}

fn isAddressingMode(text: []const u8) bool {
    // (Rn) format
    if (text.len >= 4 and text[0] == '(' and text[text.len - 1] == ')') {
        const reg = text[1 .. text.len - 1];
        return isRegister(reg);
    }

    // immediate(Rn) format - e.g., 0x10(R5), 100(R3)
    if (std.mem.indexOf(u8, text, "(")) |open_paren| {
        if (text[text.len - 1] != ')') return false;

        const imm_part = text[0..open_paren];
        const reg_part = text[open_paren + 1 .. text.len - 1];

        return isImmediate(imm_part) and isRegister(reg_part);
    }

    return false;
}

fn isImmediate(text: []const u8) bool {
    if (text.len == 0) return false;

    // Try to parse as integer with auto-detection of base
    // This handles: 0xFF (hex), 255 (decimal), 0b11111111 (binary)
    _ = std.fmt.parseInt(i32, text, 0) catch return false;
    return true;
}

fn isOpcode(text: []const u8) bool {
    // Check branches - classify ALL B-prefixed tokens as opcodes
    // Validation of whether they're valid branches happens later in validateToken
    if (text.len > 1 and text[0] == 'B') {
        return true;
    }

    // Check basic opcodes
    const opcodes = [_][]const u8{ "ADD", "SUB", "LD", "LDM", "ST", "AND", "OR", "XOR", "LSL", "LSR", "ASR", "ROL", "ROR", "TST", "MUL", "DIV", "ADC", "SBC", "MULX", "DIVX", "SWI" };

    for (opcodes) |op| {
        if (std.mem.eql(u8, text, op)) return true;
    }

    return false;
}

fn validateBranch(text: []const u8) ?[]const u8 {
    const after_b = text[1..];

    const valid_conditions = [_][]const u8{ "EQ", "NE", "CS", "CC", "HS", "LO", "MI", "PL", "VS", "VC", "HI", "LS", "GE", "LT", "GT", "LE", "PR", "A" };

    // First, try to match as Bcc (simple branch)
    for (valid_conditions) |cond| {
        if (std.mem.eql(u8, after_b, cond)) {
            return null; // Valid Bcc
        }
    }

    // Then try to match as BLcc (branch-and-link)
    if (after_b.len > 1 and after_b[0] == 'L') {
        const condition = after_b[1..];

        // Check if it's a valid BLcc instruction
        for (valid_conditions) |cond| {
            if (std.mem.eql(u8, condition, cond)) {
                // BLPR is explicitly invalid
                if (std.mem.eql(u8, condition, "PR")) {
                    return "BLPR is not valid";
                }
                return null; // Valid BLcc
            }
        }
    }

    return "invalid branch condition";
}

fn validateDirective(text: []const u8) ?[]const u8 {
    const directives = [_][]const u8{ ".START", ".ORG", ".CONST", ".DATA", ".DB", ".DW", ".DL", ".ASCII", ".CODE", ".END" };

    for (directives) |dir| {
        if (std.mem.eql(u8, text, dir)) return null;
    }

    return "invalid directive";
}

fn validateLabel(text: []const u8) ?[]const u8 {
    if (text.len < 2) return "label must have a name";

    const name = text[0 .. text.len - 1];
    for (name) |c| {
        const valid = (c >= 'A' and c <= 'Z') or
            (c >= 'a' and c <= 'z') or
            (c >= '0' and c <= '9') or
            c == '_' or c == '-';
        if (!valid) return "invalid character in label name";
    }

    return null;
}

fn validateOpcode(text: []const u8) ?[]const u8 {
    // Branch instructions need special validation
    if (text.len > 1 and text[0] == 'B') {
        return validateBranch(text);
    }

    // Other opcodes are already validated by isOpcode during classification
    return null;
}

// ============================================================================
// Public Validation API
// ============================================================================

pub fn validateToken(text: []const u8) ?[]const u8 {
    if (text.len == 0) return "token is empty";

    const token = Token.classify(text);

    return switch (token.type) {
        .directive => validateDirective(text),
        .label => validateLabel(text),
        .opcode => validateOpcode(text),
        .register, .register_stack, .addressing_mode, .label_addressing, .immediate, .string_literal, .register_list => null,
        .unknown => validateUnknownToken(text),
    };
}

fn validateUnknownToken(text: []const u8) ?[]const u8 {
    // Check if it could be a valid label reference (identifier)
    // Labels can contain alphanumeric characters, underscores, and hyphens
    if (text.len == 0) return "empty token";

    for (text) |c| {
        const valid = (c >= 'A' and c <= 'Z') or
            (c >= '0' and c <= '9') or
            c == '_' or c == '-';
        if (!valid) return "unknown token";
    }

    // It looks like a valid identifier, assume it's a label reference
    return null;
}

pub fn validateTokens(allocator: std.mem.Allocator, tokens: []const []const u8, line_num: usize) !?TokenError {
    for (tokens, 0..) |token, idx| {
        if (validateToken(token)) |reason| {
            const reason_copy = try allocator.dupe(u8, reason);
            const token_copy = try allocator.dupe(u8, token);
            return TokenError{
                .line_num = line_num,
                .token_idx = idx,
                .token = token_copy,
                .reason = reason_copy,
            };
        }
    }
    return null;
}

pub fn printTokenError(error_info: TokenError, original_line: []const u8) void {
    std.debug.print("Error at line {d}, token #{d}\n", .{ error_info.line_num, error_info.token_idx });
    std.debug.print("  Line: {s}\n", .{original_line});

    // Print a caret pointing to the problematic token position
    var caret_pos: usize = 8; // "  Line: " is 8 chars
    var token_count: usize = 0;
    var pos: usize = 0;

    while (pos < original_line.len and token_count < error_info.token_idx) {
        if (original_line[pos] == ',' or original_line[pos] == ' ' or original_line[pos] == '\t') {
            if (token_count < error_info.token_idx) {
                caret_pos += 1;
            }
            pos += 1;
            // Skip multiple delimiters
            while (pos < original_line.len and (original_line[pos] == ',' or original_line[pos] == ' ' or original_line[pos] == '\t')) {
                caret_pos += 1;
                pos += 1;
            }
            if (token_count < error_info.token_idx) {
                token_count += 1;
            }
        } else {
            caret_pos += 1;
            pos += 1;
        }
    }

    std.debug.print("  ", .{});
    var i: usize = 0;
    while (i < caret_pos) : (i += 1) {
        std.debug.print(" ", .{});
    }
    std.debug.print("^ {s}\n", .{error_info.token});
    std.debug.print("  Reason: {s}\n", .{error_info.reason});
}

pub fn assembleFromBuffer(allocator: std.mem.Allocator, source: []const u8) (AsmError || error{OutOfMemory})!void {
    var line_iter = std.mem.tokenizeAny(u8, source, "\n\r");
    var line_num: usize = 1;

    while (line_iter.next()) |raw_line| {
        const normalized = try normalizeLine(allocator, raw_line);
        defer allocator.free(normalized);

        // Skip empty lines
        if (normalized.len == 0) {
            line_num += 1;
            continue;
        }

        const tokens = try tokenizeLine(allocator, normalized);
        defer {
            for (tokens) |token| allocator.free(token);
            allocator.free(tokens);
        }

        // Step 1: Validate individual tokens
        if (try validateTokens(allocator, tokens, line_num)) |err| {
            printTokenError(err, raw_line);
            allocator.free(err.token);
            allocator.free(err.reason);
            return AsmError.InvalidSyntax;
        }

        // Step 2: Validate instruction patterns (skip directives and labels)
        if (tokens.len > 0 and tokens[0][0] != '.' and !std.mem.endsWith(u8, tokens[0], ":")) {
            if (try validateInstructionPattern(allocator, tokens, line_num)) |err| {
                printTokenError(err, raw_line);
                allocator.free(err.token);
                allocator.free(err.reason);
                return AsmError.InvalidSyntax;
            }
        }

        line_num += 1;
    }
}

pub fn assembleFromFile(allocator: std.mem.Allocator, file_path: []const u8) (AsmError || error{OutOfMemory})!void {
    const file = std.fs.cwd().openFile(file_path, .{}) catch |err| {
        if (err == error.FileNotFound) {
            return AsmError.FileNotFound;
        }
        return AsmError.FileReadError;
    };
    defer file.close();

    const source = file.readToEndAlloc(allocator, 1024 * 1024) catch return AsmError.FileReadError;
    defer allocator.free(source);

    try assembleFromBuffer(allocator, source);
}

// ============================================================================
// First Pass - Parse and Encode Instructions
// ============================================================================

pub fn firstPass(allocator: std.mem.Allocator, source: []const u8) !std.ArrayList(ParsedLine) {
    var parsed_lines: std.ArrayList(ParsedLine) = .{};
    try parsed_lines.ensureTotalCapacity(allocator, 0);
    errdefer {
        for (parsed_lines.items) |line| {
            if (line.label) |lbl| allocator.free(lbl);
            if (line.directive) |dir| allocator.free(dir);
            if (line.instruction) |instr| instr.deinit(allocator);
        }
        parsed_lines.deinit(allocator);
    }

    var line_iter = std.mem.tokenizeAny(u8, source, "\n\r");
    var line_num: usize = 1;

    while (line_iter.next()) |raw_line| {
        const normalized = try normalizeLine(allocator, raw_line);
        defer allocator.free(normalized);

        // Skip empty lines
        if (normalized.len == 0) {
            line_num += 1;
            continue;
        }

        const tokens = try tokenizeLine(allocator, normalized);
        defer {
            for (tokens) |token| allocator.free(token);
            allocator.free(tokens);
        }

        // Validate tokens
        if (try validateTokens(allocator, tokens, line_num)) |err| {
            printTokenError(err, raw_line);
            allocator.free(err.token);
            allocator.free(err.reason);
            return AsmError.InvalidSyntax;
        }

        // Parse the line
        var parsed = ParsedLine{
            .line_num = line_num,
            .label = null,
            .directive = null,
            .instruction = null,
            .raw_line = raw_line,
        };

        var token_idx: usize = 0;

        // Check for label
        if (tokens.len > 0 and std.mem.endsWith(u8, tokens[0], ":")) {
            parsed.label = try allocator.dupe(u8, tokens[0][0 .. tokens[0].len - 1]);
            token_idx += 1;
        }

        // Check for directive or instruction
        if (token_idx < tokens.len) {
            if (tokens[token_idx][0] == '.') {
                // Directive
                parsed.directive = try allocator.dupe(u8, tokens[token_idx]);
            } else {
                // Instruction - validate pattern first
                if (try validateInstructionPattern(allocator, tokens[token_idx..], line_num)) |err| {
                    printTokenError(err, raw_line);
                    allocator.free(err.token);
                    allocator.free(err.reason);
                    return AsmError.InvalidSyntax;
                }

                // Create parsed instruction
                const opcode = try allocator.dupe(u8, tokens[token_idx]);
                var operands: std.ArrayList([]const u8) = .{};
                try operands.ensureTotalCapacity(allocator, 0);

                token_idx += 1;
                while (token_idx < tokens.len) : (token_idx += 1) {
                    try operands.append(allocator, try allocator.dupe(u8, tokens[token_idx]));
                }

                parsed.instruction = ParsedInstruction{
                    .opcode = opcode,
                    .operands = try operands.toOwnedSlice(allocator),
                    .line_num = line_num,
                };
            }
        }

        try parsed_lines.append(allocator, parsed);
        line_num += 1;
    }

    return parsed_lines;
}

// ============================================================================
// Second Pass - Symbol Resolution and Bytecode Generation
// ============================================================================

pub fn secondPass(
    allocator: std.mem.Allocator,
    parsed_lines: []const ParsedLine,
) !struct { instructions: std.ArrayList(CompiledInstruction), symbols: SymbolTable } {
    var symbols = SymbolTable.init(allocator);
    errdefer symbols.deinit();

    var instructions: std.ArrayList(CompiledInstruction) = .{};
    try instructions.ensureTotalCapacity(allocator, 0);
    errdefer {
        instructions.deinit(allocator);
    }

    var current_address: u16 = 0;

    // First sub-pass: Build symbol table and calculate addresses
    for (parsed_lines) |line| {
        // Handle .ORG directive
        if (line.directive) |dir| {
            if (std.mem.eql(u8, dir, ".ORG")) {
                // Next line should have the address
                // For now, assume .ORG is followed by address on same line
                // This is a simplified implementation
                continue;
            }
            // Other directives don't affect address calculation for now
            continue;
        }

        // Store label address (label already has ':' removed from firstPass)
        if (line.label) |label| {
            try symbols.put(label, current_address);
        }

        // Instructions occupy 4 bytes (32-bit bytecode)
        if (line.instruction != null) {
            current_address += 4;
        }
    }

    // Second sub-pass: Generate bytecode with resolved symbols
    current_address = 0;
    for (parsed_lines) |line| {
        if (line.directive != null) {
            continue;
        }

        if (line.instruction) |instr| {
            // Encode the instruction with symbol resolution
            const bytecode = try encodeInstructionWithSymbols(allocator, instr, &symbols, current_address);

            try instructions.append(allocator, CompiledInstruction{
                .address = current_address,
                .bytecode = bytecode,
                .line_num = line.line_num,
                .raw_line = line.raw_line,
            });

            current_address += 4;
        }
    }

    return .{
        .instructions = instructions,
        .symbols = symbols,
    };
}

// Helper functions for encoding

fn parseRegister(text: []const u8) !RegistersName {
    if (std.mem.eql(u8, text, "SP")) return .R14;
    if (std.mem.eql(u8, text, "PC")) return .R15;
    if (std.mem.eql(u8, text, "SR")) return .R13;

    if (text[0] == 'R' and text.len >= 2 and text.len <= 3) {
        const num = try std.fmt.parseInt(u8, text[1..], 10);
        if (num <= 15) {
            return @enumFromInt(num);
        }
    }

    return AsmError.InvalidRegister;
}

fn parseImmediate(text: []const u8) !u16 {
    const value = std.fmt.parseInt(i32, text, 0) catch return AsmError.InvalidImmediate;
    return @intCast(@as(u32, @bitCast(value)) & 0xFFFF);
}

fn encodeInstruction(allocator: std.mem.Allocator, instr: ParsedInstruction) !u32 {
    _ = allocator;

    // Map opcode string to Opcode enum
    const opcode = if (std.mem.eql(u8, instr.opcode, "ADD"))
        Opcode.ADD
    else if (std.mem.eql(u8, instr.opcode, "SUB"))
        Opcode.SUB
    else if (std.mem.eql(u8, instr.opcode, "LD"))
        Opcode.LD
    else if (std.mem.eql(u8, instr.opcode, "ST"))
        Opcode.ST
    else if (std.mem.eql(u8, instr.opcode, "MUL"))
        Opcode.MUL
    else if (std.mem.eql(u8, instr.opcode, "DIV"))
        Opcode.DIV
    else if (std.mem.eql(u8, instr.opcode, "AND"))
        Opcode.AND
    else if (std.mem.eql(u8, instr.opcode, "OR"))
        Opcode.OR
    else if (std.mem.eql(u8, instr.opcode, "XOR"))
        Opcode.XOR
    else if (std.mem.eql(u8, instr.opcode, "ROL"))
        Opcode.ROL
    else if (std.mem.eql(u8, instr.opcode, "ROR"))
        Opcode.ROR
    else if (std.mem.eql(u8, instr.opcode, "LSL"))
        Opcode.LSL
    else if (std.mem.eql(u8, instr.opcode, "LSR"))
        Opcode.LSR
    else if (instr.opcode[0] == 'B')
        Opcode.B
    else
        return AsmError.InvalidOpcode;

    // Simple encoding for now - need to parse operands and determine mode
    // This is a placeholder that creates a basic instruction
    const instruction = Instruction.pack(
        0, // arch
        opcode,
        Mode.REGISTER_IMM16,
        1, // size (WORD)
        .R0, // rd
        .R0, // rs
        0, // fl
        0, // imm16
    );

    return instruction.raw;
}

fn stringToOpcode(opcode_str: []const u8) !Opcode {
    if (std.mem.eql(u8, opcode_str, "ADD")) return Opcode.ADD;
    if (std.mem.eql(u8, opcode_str, "ADC")) return Opcode.ADD; // ADC is ADD variant
    if (std.mem.eql(u8, opcode_str, "SUB")) return Opcode.SUB;
    if (std.mem.eql(u8, opcode_str, "SBC")) return Opcode.SUB; // SBC is SUB variant
    if (std.mem.eql(u8, opcode_str, "LD")) return Opcode.LD;
    if (std.mem.eql(u8, opcode_str, "LDM")) return Opcode.LD; // LDM is LD variant
    if (std.mem.eql(u8, opcode_str, "ST")) return Opcode.ST;
    if (std.mem.eql(u8, opcode_str, "MUL")) return Opcode.MUL;
    if (std.mem.eql(u8, opcode_str, "MULX")) return Opcode.MUL; // MULX is MUL variant
    if (std.mem.eql(u8, opcode_str, "DIV")) return Opcode.DIV;
    if (std.mem.eql(u8, opcode_str, "DIVX")) return Opcode.DIV; // DIVX is DIV variant
    if (std.mem.eql(u8, opcode_str, "AND")) return Opcode.AND;
    if (std.mem.eql(u8, opcode_str, "OR")) return Opcode.OR;
    if (std.mem.eql(u8, opcode_str, "XOR")) return Opcode.XOR;
    if (std.mem.eql(u8, opcode_str, "ROL")) return Opcode.ROL;
    if (std.mem.eql(u8, opcode_str, "ROR")) return Opcode.ROR;
    if (std.mem.eql(u8, opcode_str, "LSL")) return Opcode.LSL;
    if (std.mem.eql(u8, opcode_str, "LSR")) return Opcode.LSR;
    if (std.mem.eql(u8, opcode_str, "ASR")) return Opcode.LSR; // ASR is LSR variant
    if (std.mem.eql(u8, opcode_str, "TST")) return Opcode.AND; // TST is AND variant (no writeback)
    if (std.mem.eql(u8, opcode_str, "SWI")) return Opcode.SWI;
    if (opcode_str.len > 1 and opcode_str[0] == 'B') return Opcode.B;

    return AsmError.InvalidOpcode;
}

fn encodeInstructionWithSymbols(
    allocator: std.mem.Allocator,
    instr: ParsedInstruction,
    symbols: *SymbolTable,
    current_address: u16,
) !u32 {
    _ = allocator;

    const opcode = try stringToOpcode(instr.opcode);

    // Determine instruction encoding based on operand count and types
    const operand_count = instr.operands.len;

    if (operand_count == 0) {
        return AsmError.InvalidSyntax;
    }

    // Classify operands
    const op0_type = Token.classify(instr.operands[0]).type;
    const op1_type = if (operand_count > 1) Token.classify(instr.operands[1]).type else .unknown;

    // Handle branches (opcode B with various conditions)
    if (opcode == .B) {
        // Branch target is in operand[0] (for simple branch) or operand[1] (for BPR compare)
        const is_bpr = std.mem.eql(u8, instr.opcode, "BPR");

        if (is_bpr and operand_count == 2) {
            // BPR Rd, Rs - compare and branch on positive result
            const rd = try parseRegister(instr.operands[0]);
            const rs = try parseRegister(instr.operands[1]);

            // BPR uses Mode.REGISTER_IMM16 with imm16=0 for register-register
            const instruction = Instruction.pack(
                0, // arch
                opcode,
                Mode.REGISTER_IMM16,
                1, // size (WORD)
                rd,
                rs,
                0, // fl (condition code extracted from opcode string)
                0, // imm16 = 0
            );
            return instruction.raw;
        } else if (operand_count == 1) {
            // Simple branch: Bcc label
            const target = instr.operands[0];
            var imm16: u16 = 0;

            // Check if target is a label
            if (op0_type == .label or (!isImmediate(target) and !isRegister(target))) {
                // Try to resolve label
                if (symbols.get(target)) |target_address| {
                    // Calculate relative offset
                    const offset = @as(i32, target_address) - @as(i32, current_address + 4);
                    imm16 = @intCast(@as(u32, @bitCast(offset)) & 0xFFFF);
                } else {
                    // Label not found - could be forward reference
                    // For now, use 0 and would need another pass to fix
                    imm16 = 0;
                }
            } else {
                // Direct immediate address
                imm16 = try parseImmediate(target);
            }

            const instruction = Instruction.pack(
                0, // arch
                opcode,
                Mode.REGISTER_IMM16,
                1, // size (WORD)
                .R0, // rd (not used for simple branch)
                .R0, // rs (not used)
                0, // fl (condition code)
                imm16,
            );
            return instruction.raw;
        }
    }

    // Two-operand instructions
    if (operand_count == 2) {
        const rd = try parseRegister(instr.operands[0]);

        // Rd, Rs (register-register mode)
        if (op1_type == .register) {
            const rs = try parseRegister(instr.operands[1]);

            // Register-register uses Mode.REGISTER_IMM16 with imm16=0
            const instruction = Instruction.pack(
                0, // arch
                opcode,
                Mode.REGISTER_IMM16,
                1, // size (WORD)
                rd,
                rs,
                0, // fl
                0, // imm16 = 0 indicates register-register
            );
            return instruction.raw;
        }

        // Rd, #immediate (register-immediate mode)
        if (op1_type == .immediate) {
            const imm16 = try parseImmediate(instr.operands[1]);

            // Immediate mode uses Mode.REGISTER_IMM16 with rs=R0
            const instruction = Instruction.pack(
                0, // arch
                opcode,
                Mode.REGISTER_IMM16,
                1, // size (WORD)
                rd,
                .R0, // rs = 0 indicates immediate mode
                0, // fl
                imm16,
            );
            return instruction.raw;
        }

        // Handle label references (e.g., ADD R1, LOOP)
        if (op1_type == .label or (!isImmediate(instr.operands[1]) and !isRegister(instr.operands[1]))) {
            const label = instr.operands[1];
            var imm16: u16 = 0;

            if (symbols.get(label)) |address| {
                imm16 = address;
            }

            const instruction = Instruction.pack(
                0, // arch
                opcode,
                Mode.REGISTER_IMM16,
                1, // size (WORD)
                rd,
                .R0, // rs
                0, // fl
                imm16,
            );
            return instruction.raw;
        }
    }

    // Default fallback
    const instruction = Instruction.pack(
        0, // arch
        opcode,
        Mode.REGISTER_IMM16,
        1, // size (WORD)
        .R0, // rd
        .R0, // rs
        0, // fl
        0, // imm16
    );

    return instruction.raw;
}

// ============================================================================
// Pattern-Based Instruction Validation
// ============================================================================

// Operands allowed:
// Rn
// Rn, Rn
// Rn, Immediate
// Rn, Rn, Immediate
// (Rn), Rn
// Rn, (Rn)
// Rn, Immediate(Rn)
// Immediate(Rn), Rn
// Label, Rn
// Rn, Label
// Rn, Label(Rn)
// Label(Rn), Rn
// -(SP), Rn
// -(SP), Immediate
// Rn, (SP)+

pub const OperandType = enum {
    register,
    immediate,
    label,
    addressing_mode, // (Rn) or immediate(Rn)
    label_addressing, // label(Rn)
    register_stack,
    register_list, // {R1,R2,R6}
};

pub const InstructionPattern = struct {
    opcode: []const u8,
    operands: []const OperandType,
};

pub const instruction_patterns = [_]InstructionPattern{

    // ========================================================================
    // CONDITIONAL BRANCH INSTRUCTIONS
    // Branch to address if condition is met
    // Syntax: Bcc <target>  where cc = condition code
    // ========================================================================

    // BEQ - Branch if Equal (Z flag set)
    // Examples: BEQ R5        (branch to address in R5)
    //           BEQ 0x1000    (branch to absolute address)
    //           BEQ LOOP      (branch to label)
    .{ .opcode = "BEQ", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BEQ", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BEQ", .operands = &[_]OperandType{.label} },

    // BLEQ - Branch with Link if Equal (saves return address)
    // Examples: BLEQ SUBROUTINE  (call subroutine if equal)
    //           BLEQ R7          (call address in R7 if equal)
    .{ .opcode = "BLEQ", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLEQ", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLEQ", .operands = &[_]OperandType{.label} },

    // BNE - Branch if Not Equal (Z flag clear)
    // Examples: BNE R5        (branch to address in R5 if not equal)
    //           BNE 0x2000    (branch to absolute address if not equal)
    //           BNE RETRY     (branch to label if not equal)
    .{ .opcode = "BNE", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BNE", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BNE", .operands = &[_]OperandType{.label} },

    // BLNE - Branch with Link if Not Equal
    .{ .opcode = "BLNE", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLNE", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLNE", .operands = &[_]OperandType{.label} },

    // BCS - Branch if Carry Set (C flag set)
    // Examples: BCS OVERFLOW   (branch if carry occurred)
    //           BCS R3         (branch to address in R3 if carry)
    .{ .opcode = "BCS", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BCS", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BCS", .operands = &[_]OperandType{.label} },

    // BLCS - Branch with Link if Carry Set
    .{ .opcode = "BLCS", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLCS", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLCS", .operands = &[_]OperandType{.label} },

    // BCC - Branch if Carry Clear (C flag clear)
    // Examples: BCC NO_CARRY   (branch if no carry occurred)
    //           BCC 0x3000     (branch to address if no carry)
    .{ .opcode = "BCC", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BCC", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BCC", .operands = &[_]OperandType{.label} },

    // BLCC - Branch with Link if Carry Clear
    .{ .opcode = "BLCC", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLCC", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLCC", .operands = &[_]OperandType{.label} },

    // BHS - Branch if Higher or Same (unsigned >=, C flag set)
    // Examples: BHS GREATER_OR_EQUAL  (unsigned comparison)
    //           BHS R10               (branch to R10 if >=)
    .{ .opcode = "BHS", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BHS", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BHS", .operands = &[_]OperandType{.label} },

    // BLHS - Branch with Link if Higher or Same
    .{ .opcode = "BLHS", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLHS", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLHS", .operands = &[_]OperandType{.label} },

    // BLO - Branch if Lower (unsigned <, C flag clear)
    // Examples: BLO LESS_THAN     (unsigned comparison)
    //           BLO 0x4000        (branch if lower)
    .{ .opcode = "BLO", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLO", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLO", .operands = &[_]OperandType{.label} },

    // BLLO - Branch with Link if Lower
    .{ .opcode = "BLLO", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLLO", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLLO", .operands = &[_]OperandType{.label} },

    // BMI - Branch if Minus (N flag set, result negative)
    // Examples: BMI NEGATIVE      (branch if result was negative)
    //           BMI R8            (branch to R8 if negative)
    .{ .opcode = "BMI", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BMI", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BMI", .operands = &[_]OperandType{.label} },

    // BLMI - Branch with Link if Minus
    .{ .opcode = "BLMI", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLMI", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLMI", .operands = &[_]OperandType{.label} },

    // BPL - Branch if Plus (N flag clear, result positive or zero)
    // Examples: BPL POSITIVE      (branch if result was positive)
    //           BPL 0x5000        (branch to address if positive)
    .{ .opcode = "BPL", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BPL", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BPL", .operands = &[_]OperandType{.label} },

    // BLPL - Branch with Link if Plus
    .{ .opcode = "BLPL", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLPL", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLPL", .operands = &[_]OperandType{.label} },

    // BVS - Branch if Overflow Set (V flag set)
    // Examples: BVS OVERFLOW_HANDLER  (branch if signed overflow)
    //           BVS R4                (branch to R4 if overflow)
    .{ .opcode = "BVS", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BVS", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BVS", .operands = &[_]OperandType{.label} },

    // BLVS - Branch with Link if Overflow Set
    .{ .opcode = "BLVS", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLVS", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLVS", .operands = &[_]OperandType{.label} },

    // BVC - Branch if Overflow Clear (V flag clear)
    // Examples: BVC NO_OVERFLOW  (branch if no signed overflow)
    //           BVC 0x6000       (branch to address if no overflow)
    .{ .opcode = "BVC", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BVC", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BVC", .operands = &[_]OperandType{.label} },

    // BLVC - Branch with Link if Overflow Clear
    .{ .opcode = "BLVC", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLVC", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLVC", .operands = &[_]OperandType{.label} },

    // BHI - Branch if Higher (unsigned >, C set AND Z clear)
    // Examples: BHI GREATER      (unsigned greater than)
    //           BHI R6           (branch to R6 if higher)
    .{ .opcode = "BHI", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BHI", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BHI", .operands = &[_]OperandType{.label} },

    // BLHI - Branch with Link if Higher
    .{ .opcode = "BLHI", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLHI", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLHI", .operands = &[_]OperandType{.label} },

    // BLS - Branch if Lower or Same (unsigned <=, C clear OR Z set)
    // Examples: BLS LESS_OR_EQUAL  (unsigned less than or equal)
    //           BLS 0x7000         (branch if lower or same)
    .{ .opcode = "BLS", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLS", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLS", .operands = &[_]OperandType{.label} },

    // BLLS - Branch with Link if Lower or Same
    .{ .opcode = "BLLS", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLLS", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLLS", .operands = &[_]OperandType{.label} },

    // BGE - Branch if Greater or Equal (signed >=, N == V)
    // Examples: BGE SIGNED_GE    (signed comparison)
    //           BGE R9           (branch to R9 if >=)
    .{ .opcode = "BGE", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BGE", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BGE", .operands = &[_]OperandType{.label} },

    // BLGE - Branch with Link if Greater or Equal
    .{ .opcode = "BLGE", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLGE", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLGE", .operands = &[_]OperandType{.label} },

    // BLT - Branch if Less Than (signed <, N != V)
    // Examples: BLT SIGNED_LESS  (signed comparison)
    //           BLT 0x8000       (branch if less than)
    .{ .opcode = "BLT", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLT", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLT", .operands = &[_]OperandType{.label} },

    // BLLT - Branch with Link if Less Than
    .{ .opcode = "BLLT", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLLT", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLLT", .operands = &[_]OperandType{.label} },

    // BGT - Branch if Greater Than (signed >, Z clear AND N == V)
    // Examples: BGT SIGNED_GT    (signed greater than)
    //           BGT R11          (branch to R11 if >)
    .{ .opcode = "BGT", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BGT", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BGT", .operands = &[_]OperandType{.label} },

    // BLGT - Branch with Link if Greater Than
    .{ .opcode = "BLGT", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLGT", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLGT", .operands = &[_]OperandType{.label} },

    // BLE - Branch if Less or Equal (signed <=, Z set OR N != V)
    // Examples: BLE SIGNED_LE    (signed less than or equal)
    //           BLE 0x9000       (branch if <=)
    .{ .opcode = "BLE", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLE", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLE", .operands = &[_]OperandType{.label} },

    // BLLE - Branch with Link if Less or Equal
    .{ .opcode = "BLLE", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLLE", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLLE", .operands = &[_]OperandType{.label} },

    // BPR - Branch on Parity (special condition)
    // Can also be used with two operands for compare-and-branch
    // Examples: BPR PARITY_CHECK     (branch based on parity)
    //           BPR R1, R2           (compare R1 and R2, branch on result)
    //           BPR R1, 100          (compare R1 with 100, branch on result)
    .{ .opcode = "BPR", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BPR", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BPR", .operands = &[_]OperandType{.label} },
    .{ .opcode = "BPR", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "BPR", .operands = &[_]OperandType{ .register, .immediate } },

    // ========================================================================
    // UNCONDITIONAL BRANCH AND CONTROL FLOW
    // ========================================================================

    // BA - Branch Always (unconditional jump)
    // Examples: BA MAIN              (jump to MAIN label)
    //           BA R15               (jump to address in R15)
    //           BA 0xA000            (jump to absolute address)
    //           BA (SP)+             (return from subroutine - pop address from stack)
    .{ .opcode = "BA", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BA", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BA", .operands = &[_]OperandType{.label} },
    .{ .opcode = "BA", .operands = &[_]OperandType{.register_stack} },

    // BLA - Branch with Link Always (unconditional call/JSR)
    // Saves return address before jumping
    // Examples: BLA FUNCTION         (call FUNCTION)
    //           BLA R12              (call address in R12)
    //           BLA 0xB000           (call absolute address)
    .{ .opcode = "BLA", .operands = &[_]OperandType{.register} },
    .{ .opcode = "BLA", .operands = &[_]OperandType{.immediate} },
    .{ .opcode = "BLA", .operands = &[_]OperandType{.label} },

    // ========================================================================
    // TEST INSTRUCTION
    // ========================================================================

    // TST - Test (compare and set flags without storing result)
    // Replaces BPR.B functionality
    // Examples: TST R1, R2           (compare R1 with R2, update flags)
    //           TST R3, 0xFF         (test R3 against 0xFF, update flags)
    .{ .opcode = "TST", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "TST", .operands = &[_]OperandType{ .register, .immediate } },

    // ========================================================================
    // LOAD INSTRUCTIONS
    // Move data from memory/source to register
    // ========================================================================

    // LD - Load
    // Examples: LD R1, R2            (copy R2 to R1)
    //           LD R1, 0xFF          (load immediate 0xFF into R1)
    //           LD -(SP), R1         (push R1 into stack)
    //           LD R1, (SP)+         (load from stack, pop after)
    //           LD R1, (R5)          (load from address in R5)
    //           LD R1, DATA_LABEL    (load from label address)
    //           LD R1, 0x10(R5)      (load from R5 + 0x10)
    //           LD R1, ARRAY(R3)     (load from ARRAY base + R3)
    .{ .opcode = "LD", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "LD", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "LD", .operands = &[_]OperandType{ .register_stack, .register } },
    .{ .opcode = "LD", .operands = &[_]OperandType{ .register, .register_stack } },
    .{ .opcode = "LD", .operands = &[_]OperandType{ .register, .addressing_mode } },
    .{ .opcode = "LD", .operands = &[_]OperandType{ .register, .label } },
    .{ .opcode = "LD", .operands = &[_]OperandType{ .register, .label_addressing } },

    // ========================================================================
    // LOAD MULTIPLE (LDM) INSTRUCTIONS
    // Load/Store multiple registers from/to stack (SP only)
    // ========================================================================

    // LDM - Load Multiple (only works with SP)
    // Examples: LDM -(SP), {R1,R2,R6}  (push multiple registers onto stack)
    //           LDM {R6,R2,R1}, (SP)+  (pop multiple registers from stack)
    // Register list order doesn't matter - registers are sorted automatically
    // Register list is encoded as bitmask in IMM16
    .{ .opcode = "LDM", .operands = &[_]OperandType{ .register_stack, .register_list } },
    .{ .opcode = "LDM", .operands = &[_]OperandType{ .register_list, .register_stack } },

    // ========================================================================
    // STORE INSTRUCTIONS
    // Move data from register to memory
    // ========================================================================

    // ST - Store
    // Examples: ST (R5), R1          (store R1 to address in R5)
    //           ST DATA_LABEL, R2    (store R2 to label address)
    //           ST 0x20(R3), R4      (store R4 to R3 + 0x20)
    //           ST BUFFER(R7), R8    (store R8 to BUFFER base + R7)
    .{ .opcode = "ST", .operands = &[_]OperandType{ .addressing_mode, .register } },
    .{ .opcode = "ST", .operands = &[_]OperandType{ .label, .register } },
    .{ .opcode = "ST", .operands = &[_]OperandType{ .label_addressing, .register } },

    // ========================================================================
    // ARITHMETIC INSTRUCTIONS
    // ========================================================================

    // ADD - Addition
    // 1 operand:  ADD R1              → R1 = R1 + 1 (INC)
    // 2 operands: ADD R1, R2          → R1 = R1 + R2
    //             ADD R1, 5           → R1 = R1 + 5
    // 3 operands: ADD R1, R2, 10      → R1 = R2 + 10
    .{ .opcode = "ADD", .operands = &[_]OperandType{.register} },
    .{ .opcode = "ADD", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "ADD", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "ADD", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // ADC - Add with Carry
    // Same operand formats as ADD, but includes carry flag
    // Examples: ADC R1, R2           (R1 = R1 + R2 + Carry)
    //           ADC R3, 7            (R3 = R3 + 7 + Carry)
    //           ADC R4, R5, 12       (R4 = R5 + 12 + Carry)
    .{ .opcode = "ADC", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "ADC", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "ADC", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // SUB - Subtraction
    // 1 operand:  SUB R1              → R1 = R1 - 1 (DEC)
    // 2 operands: SUB R1, R2          → R1 = R1 - R2
    //             SUB R1, 5           → R1 = R1 - 5
    // 3 operands: SUB R1, R2, 10      → R1 = R2 - 10
    .{ .opcode = "SUB", .operands = &[_]OperandType{.register} },
    .{ .opcode = "SUB", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "SUB", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "SUB", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // SBC - Subtract with Carry (borrow)
    // Same operand formats as SUB, but includes carry flag
    // Examples: SBC R1, R2           (R1 = R1 - R2 - Carry)
    //           SBC R3, 7            (R3 = R3 - 7 - Carry)
    //           SBC R4, R5, 12       (R4 = R5 - 12 - Carry)
    .{ .opcode = "SBC", .operands = &[_]OperandType{.register} },
    .{ .opcode = "SBC", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "SBC", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "SBC", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // MUL - Multiply (basic, result fits in destination)
    // 2 operands: MUL R1, R2          → R1 = R1 * R2 (lower bits only)
    //             MUL R1, 3           → R1 = R1 * 3
    // 3 operands: MUL R1, R2, 5       → R1 = R2 * 5
    .{ .opcode = "MUL", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "MUL", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "MUL", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // MULX - Multiply Extended (full width result)
    // Stores full result across multiple registers
    // Examples: MULX R1, R2          (R1:R2 = R1 * R2, full 32-bit result)
    //           MULX R1, R2, 12      (R1:R2 = R2 * 12, full 32-bit result)

    .{ .opcode = "MULX", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "MULX", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // DIV - Divide (basic, quotient only)
    // 2 operands: DIV R1, R2          → R1 = R1 / R2
    //             DIV R1, 4           → R1 = R1 / 4
    // 3 operands: DIV R1, R2, 8       → R1 = R2 / 8
    .{ .opcode = "DIV", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "DIV", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "DIV", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // DIVX - Divide Extended (with remainder)
    // Stores quotient and remainder in separate registers
    // Examples: DIVX R1, R2          (R1 = quotient, R2 = remainder)
    //           DIVX R3, R2, 7           (R3 = R2/7, R2 = R2%7)
    .{ .opcode = "DIVX", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "DIVX", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // ========================================================================
    // LOGICAL INSTRUCTIONS
    // ========================================================================

    // AND - Logical AND
    // 2 operands: AND R1, R2          → R1 = R1 & R2
    //             AND R1, 0xFF        → R1 = R1 & 0xFF (mask lower byte)
    // 3 operands: AND R1, R2, 0x0F    → R1 = R2 & 0x0F
    .{ .opcode = "AND", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "AND", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "AND", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // OR - Logical OR
    // 2 operands: OR R1, R2           → R1 = R1 | R2
    //             OR R1, 0x80         → R1 = R1 | 0x80 (set bit 7)
    // 3 operands: OR R1, R2, 0x01     → R1 = R2 | 0x01
    .{ .opcode = "OR", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "OR", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "OR", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // XOR - Logical XOR (exclusive OR)
    // 2 operands: XOR R1, R2          → R1 = R1 ^ R2
    //             XOR R1, 0xFF        → R1 = R1 ^ 0xFF (invert all bits)
    // 3 operands: XOR R1, R2, 0xAA    → R1 = R2 ^ 0xAA
    .{ .opcode = "XOR", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "XOR", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "XOR", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // ========================================================================
    // SHIFT AND ROTATE INSTRUCTIONS
    // ========================================================================

    // ROL - Rotate Left (circular shift left)
    // Bits shifted out on left reenter on right
    // 2 operands: ROL R1, R2          → R1 = R1 rotated left by R2 positions
    //             ROL R1, 3           → R1 = R1 rotated left by 3
    // 3 operands: ROL R1, R2, 4       → R1 = R2 rotated left by 4
    .{ .opcode = "ROL", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "ROL", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "ROL", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // ROR - Rotate Right (circular shift right)
    // Bits shifted out on right reenter on left
    // 2 operands: ROR R1, R2          → R1 = R1 rotated right by R2 positions
    //             ROR R1, 2           → R1 = R1 rotated right by 2
    // 3 operands: ROR R1, R2, 5       → R1 = R2 rotated right by 5
    .{ .opcode = "ROR", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "ROR", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "ROR", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // LSL - Logical Shift Left
    // Shift left, filling with zeros on right
    // 2 operands: LSL R1, R2          → R1 = R1 << R2 (multiply by 2^R2)
    //             LSL R1, 4           → R1 = R1 << 4 (multiply by 16)
    // 3 operands: LSL R1, R2, 3       → R1 = R2 << 3
    .{ .opcode = "LSL", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "LSL", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "LSL", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // LSR - Logical Shift Right
    // Shift right, filling with zeros on left (unsigned divide)
    // 2 operands: LSR R1, R2          → R1 = R1 >> R2 (unsigned divide by 2^R2)
    //             LSR R1, 3           → R1 = R1 >> 3 (unsigned divide by 8)
    // 3 operands: LSR R1, R2, 2       → R1 = R2 >> 2
    .{ .opcode = "LSR", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "LSR", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "LSR", .operands = &[_]OperandType{ .register, .register, .immediate } },

    // ASR - Arithmetic Shift Right
    // Shift right, preserving sign bit (signed divide)
    // 2 operands: ASR R1, R2          → R1 = R1 >> R2 (signed divide by 2^R2)
    //             ASR R1, 2           → R1 = R1 >> 2 (signed divide by 4)
    // 3 operands: ASR R1, R2, 5       → R1 = R2 >> 5 (preserves sign)
    .{ .opcode = "ASR", .operands = &[_]OperandType{ .register, .register } },
    .{ .opcode = "ASR", .operands = &[_]OperandType{ .register, .immediate } },
    .{ .opcode = "ASR", .operands = &[_]OperandType{ .register, .register, .immediate } },
};

pub fn validateInstructionPattern(allocator: std.mem.Allocator, tokens: []const []const u8, line_num: usize) !?TokenError {
    if (tokens.len == 0) return null;

    const opcode_text = tokens[0];

    // Convert string tokens to Token structs for pattern matching
    var token_structs = try allocator.alloc(Token, tokens.len);
    defer allocator.free(token_structs);

    for (tokens, 0..) |token_str, i| {
        token_structs[i] = Token.classify(token_str);
    }

    // Try to find a matching pattern
    for (instruction_patterns) |pattern| {
        if (!std.mem.eql(u8, pattern.opcode, opcode_text)) continue;
        if (tokens.len - 1 != pattern.operands.len) continue;

        var matches = true;
        for (pattern.operands, 0..) |expected, i| {
            const token = token_structs[i + 1];
            if (!matchesOperandType(token, expected)) {
                matches = false;
                break;
            }
        }

        if (matches) return null; // Found a matching pattern
    }

    // No matching pattern found
    const reason_copy = try allocator.dupe(u8, "no matching instruction pattern");
    const token_copy = try allocator.dupe(u8, opcode_text);
    return TokenError{
        .line_num = line_num,
        .token_idx = 0,
        .token = token_copy,
        .reason = reason_copy,
    };
}

pub fn validateInstruction(tokens: []const Token) ?[]const u8 {
    if (tokens.len == 0) return "empty instruction";

    const opcode_text = tokens[0].text;

    for (instruction_patterns) |pattern| {
        if (!std.mem.eql(u8, pattern.opcode, opcode_text)) continue;
        if (tokens.len - 1 != pattern.operands.len) continue;

        var matches = true;
        for (pattern.operands, 0..) |expected, i| {
            const token = tokens[i + 1];
            if (!matchesOperandType(token, expected)) {
                matches = false;
                break;
            }
        }

        if (matches) return null;
    }

    return "no matching instruction pattern";
}

fn matchesOperandType(token: Token, expected: OperandType) bool {
    return switch (expected) {
        .register => token.type == .register,
        .immediate => token.type == .immediate,
        .label => token.type == .unknown, // Labels appear as unknown before resolution
        .addressing_mode => token.type == .addressing_mode,
        .label_addressing => token.type == .label_addressing,
        .register_stack => token.type == .register_stack,
        .register_list => token.type == .register_list,
    };
}

// ============================================================================
// Tests
// ============================================================================

test "normalizeLine trims and collapses whitespace" {
    const got = try normalizeLine(std.testing.allocator, "\t  ADD R1,    R4,   1234  \t");
    defer std.testing.allocator.free(got);
    try std.testing.expect(std.mem.eql(u8, got, "ADD,R1,R4,1234"));
}

test "normalizeLine converts to uppercase" {
    const got = try normalizeLine(std.testing.allocator, "add r1, r2, 0xff");
    defer std.testing.allocator.free(got);
    try std.testing.expect(std.mem.eql(u8, got, "ADD,R1,R2,0XFF"));
}

test "normalizeLine drops comments" {
    const got = try normalizeLine(std.testing.allocator, "ADD R1, R2 ; this is a comment");
    defer std.testing.allocator.free(got);
    try std.testing.expect(std.mem.eql(u8, got, "ADD,R1,R2"));
}

test "normalizeLine preserves register lists" {
    const got = try normalizeLine(std.testing.allocator, "LDM -(SP), {R1, R2, R6}");
    defer std.testing.allocator.free(got);
    try std.testing.expect(std.mem.eql(u8, got, "LDM,-(SP),{R1, R2, R6}"));
}

test "normalizeLine register list with uppercase conversion outside braces" {
    const got = try normalizeLine(std.testing.allocator, "ldm {r1,r2,r6}, (sp)+");
    defer std.testing.allocator.free(got);
    try std.testing.expect(std.mem.eql(u8, got, "LDM,{r1,r2,r6},(SP)+"));
}

test "tokenizeLine splits on commas" {
    const normalized = try normalizeLine(std.testing.allocator, "\t  ADD R1,    R4,   1234  \t");
    defer std.testing.allocator.free(normalized);

    const tokens = try tokenizeLine(std.testing.allocator, normalized);
    defer {
        for (tokens) |token| std.testing.allocator.free(token);
        std.testing.allocator.free(tokens);
    }

    try std.testing.expect(tokens.len == 4);
    try std.testing.expect(std.mem.eql(u8, tokens[0], "ADD"));
    try std.testing.expect(std.mem.eql(u8, tokens[1], "R1"));
    try std.testing.expect(std.mem.eql(u8, tokens[2], "R4"));
    try std.testing.expect(std.mem.eql(u8, tokens[3], "1234"));
}

test "classify tokens" {
    try std.testing.expect(Token.classify("R0").type == .register);
    try std.testing.expect(Token.classify("ADD").type == .opcode);
    try std.testing.expect(Token.classify("LDM").type == .opcode);
    try std.testing.expect(Token.classify(".START").type == .directive);
    try std.testing.expect(Token.classify("LOOP:").type == .label);
    try std.testing.expect(Token.classify("0xFF").type == .immediate);
    try std.testing.expect(Token.classify("(SP)").type == .register_stack);
    try std.testing.expect(Token.classify("(SP)+").type == .register_stack);
    try std.testing.expect(Token.classify("-(SP)").type == .register_stack);
    try std.testing.expect(Token.classify("4(SP)").type == .addressing_mode);
    try std.testing.expect(Token.classify("(R5)").type == .addressing_mode);
    try std.testing.expect(Token.classify("0x10(R5)").type == .addressing_mode);
    try std.testing.expect(Token.classify("100(R3)").type == .addressing_mode);
    try std.testing.expect(Token.classify("LOOP(R2)").type == .label_addressing);
    try std.testing.expect(Token.classify("DATA_START(R5)").type == .label_addressing);
    try std.testing.expect(Token.classify("LOOP").type == .unknown); // Bare label reference
    try std.testing.expect(Token.classify("\"Hello world!\"").type == .string_literal);
    try std.testing.expect(Token.classify("\"Text with spaces\"").type == .string_literal);
    try std.testing.expect(Token.classify("{R1,R2,R6}").type == .register_list);
    try std.testing.expect(Token.classify("{R0}").type == .register_list);
}

test "validate branches" {
    try std.testing.expect(validateToken("BEQ") == null);
    try std.testing.expect(validateToken("BLEQ") == null);
    try std.testing.expect(validateToken("BPR") == null);
    try std.testing.expect(validateToken("BLPR") != null);
    try std.testing.expect(validateToken("TST") == null);
}

test "validate instruction patterns - valid instructions" {
    // Valid ADD patterns
    {
        const tokens = [_]Token{
            Token.classify("ADD"),
            Token.classify("R1"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }
    {
        const tokens = [_]Token{
            Token.classify("ADD"),
            Token.classify("R1"),
            Token.classify("R2"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }
    {
        const tokens = [_]Token{
            Token.classify("ADD"),
            Token.classify("R1"),
            Token.classify("255"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }
    {
        const tokens = [_]Token{
            Token.classify("ADD"),
            Token.classify("R1"),
            Token.classify("R2"),
            Token.classify("0xFF"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }

    // Valid branch patterns
    {
        const tokens = [_]Token{
            Token.classify("BEQ"),
            Token.classify("R5"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }
    {
        const tokens = [_]Token{
            Token.classify("BLEQ"),
            Token.classify("0x100"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }

    {
        const tokens = [_]Token{
            Token.classify("BLGT"),
            Token.classify("LABEL"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }

    // Valid LD patterns
    {
        const tokens = [_]Token{
            Token.classify("LD"),
            Token.classify("R1"),
            Token.classify("R2"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }
    {
        const tokens = [_]Token{
            Token.classify("LD"),
            Token.classify("R1"),
            Token.classify("(R5)"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }
    {
        const tokens = [_]Token{
            Token.classify("LD"),
            Token.classify("R1"),
            Token.classify("0x10(R5)"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }

    // Valid ST patterns
    {
        const tokens = [_]Token{
            Token.classify("ST"),
            Token.classify("(R5)"),
            Token.classify("R1"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }
    {
        const tokens = [_]Token{
            Token.classify("ST"),
            Token.classify("DATA_START(R2)"),
            Token.classify("R1"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }

    // Valid TST pattern
    {
        const tokens = [_]Token{
            Token.classify("TST"),
            Token.classify("R1"),
            Token.classify("R2"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }

    // Valid BPR compare pattern
    {
        const tokens = [_]Token{
            Token.classify("BPR"),
            Token.classify("R1"),
            Token.classify("R2"),
        };
        try std.testing.expect(validateInstruction(&tokens) == null);
    }
}

test "validate instruction patterns - invalid instructions" {
    // Invalid: ADD with 3 registers
    {
        const tokens = [_]Token{
            Token.classify("ADD"),
            Token.classify("R1"),
            Token.classify("R2"),
            Token.classify("R3"),
        };
        try std.testing.expect(validateInstruction(&tokens) != null);
    }

    // Invalid: Wrong operand order for ST
    {
        const tokens = [_]Token{
            Token.classify("ST"),
            Token.classify("R1"),
            Token.classify("(R5)"),
        };
        try std.testing.expect(validateInstruction(&tokens) != null);
    }

    // Invalid: LD with immediate as first operand
    {
        const tokens = [_]Token{
            Token.classify("LD"),
            Token.classify("0xFF"),
            Token.classify("R1"),
        };
        try std.testing.expect(validateInstruction(&tokens) != null);
    }

    // Invalid: Branch with no operands
    {
        const tokens = [_]Token{
            Token.classify("BEQ"),
        };
        try std.testing.expect(validateInstruction(&tokens) != null);
    }

    // Invalid: TST with only one operand
    {
        const tokens = [_]Token{
            Token.classify("TST"),
            Token.classify("R1"),
        };
        try std.testing.expect(validateInstruction(&tokens) != null);
    }

    // Invalid: BPR with three operands
    {
        const tokens = [_]Token{
            Token.classify("BPR"),
            Token.classify("R1"),
            Token.classify("R2"),
            Token.classify("R3"),
        };
        try std.testing.expect(validateInstruction(&tokens) != null);
    }

    // Invalid: ADD with no operands
    {
        const tokens = [_]Token{
            Token.classify("ADD"),
        };
        try std.testing.expect(validateInstruction(&tokens) != null);
    }

    // Invalid: XOR with addressing mode
    {
        const tokens = [_]Token{
            Token.classify("XOR"),
            Token.classify("R1"),
            Token.classify("(R5)"),
        };
        try std.testing.expect(validateInstruction(&tokens) != null);
    }
}
