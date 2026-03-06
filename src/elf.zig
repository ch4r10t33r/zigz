// Minimal ELF parser for RISC-V zkVM: read entry point and PT_LOAD segments.
// Supports ELF32 and ELF64, little-endian only.

const std = @import("std");

pub const PT_LOAD: u32 = 1;

pub const Segment = struct {
    vaddr: u64,
    data: []const u8,
};

pub const LoadResult = struct {
    entry_pc: u64,
    segments: []const Segment,
    /// Owned by caller; free with allocator.free(segments)
    segments_owned: []Segment,
};

pub const Error = error{
    NotElf,
    UnsupportedClass,
    UnsupportedData,
    InvalidPhdr,
    NoLoadSegments,
};

pub fn isElf(data: []const u8) bool {
    if (data.len < 4) return false;
    return data[0] == 0x7f and data[1] == 'E' and data[2] == 'L' and data[3] == 'F';
}

fn readU16Le(data: []const u8, offset: usize) u16 {
    return data[offset] | (@as(u16, data[offset + 1]) << 8);
}
fn readU32Le(data: []const u8, offset: usize) u32 {
    return data[offset] | (@as(u32, data[offset + 1]) << 8) | (@as(u32, data[offset + 2]) << 16) | (@as(u32, data[offset + 3]) << 24);
}
fn readU64Le(data: []const u8, offset: usize) u64 {
    return readU32Le(data, offset) | (@as(u64, readU32Le(data, offset + 4)) << 32);
}

/// Parse ELF and return entry point plus PT_LOAD segments (slices into data).
/// Caller must not free data before using segments. segments_owned is allocated and must be freed.
pub fn load(allocator: std.mem.Allocator, data: []const u8) !LoadResult {
    if (!isElf(data)) return error.NotElf;
    if (data.len < 64) return error.NotElf;

    const class = data[4]; // 1 = 32-bit, 2 = 64-bit
    const data_enc = data[5]; // 1 = LE, 2 = BE
    if (data_enc != 1) return error.UnsupportedData;

    var segments = std.ArrayList(Segment){};
    errdefer segments.deinit(allocator);
    var entry_pc: u64 = 0;

    if (class == 2) {
        // ELF64
        if (data.len < 0x40) return error.InvalidPhdr;
        entry_pc = readU64Le(data, 0x18);
        const e_phoff = readU64Le(data, 0x20);
        const e_phentsize = readU16Le(data, 0x36);
        const e_phnum = readU16Le(data, 0x38);
        if (e_phentsize != 56) return error.InvalidPhdr;

        var i: u16 = 0;
        while (i < e_phnum) : (i += 1) {
            const phoff = e_phoff + @as(usize, e_phentsize) * i;
            if (phoff + 56 > data.len) return error.InvalidPhdr;
            const p_type = readU32Le(data, phoff + 0);
            if (p_type != PT_LOAD) continue;
            const p_offset = readU64Le(data, phoff + 8);
            const p_vaddr = readU64Le(data, phoff + 16);
            const p_filesz = readU64Le(data, phoff + 32);
            _ = readU64Le(data, phoff + 40); // p_memsz (reserved for BSS later)
            if (p_offset > data.len or p_offset + p_filesz > data.len) return error.InvalidPhdr;
            const seg_data = data[p_offset..][0..p_filesz];
            try segments.append(allocator, .{ .vaddr = p_vaddr, .data = seg_data });
        }
    } else if (class == 1) {
        // ELF32
        if (data.len < 0x30) return error.InvalidPhdr;
        entry_pc = readU32Le(data, 0x18);
        const e_phoff = readU32Le(data, 0x1c);
        const e_phentsize = readU16Le(data, 0x2a);
        const e_phnum = readU16Le(data, 0x2c);
        if (e_phentsize != 32) return error.InvalidPhdr;

        var i: u16 = 0;
        while (i < e_phnum) : (i += 1) {
            const phoff = e_phoff + @as(usize, e_phentsize) * i;
            if (phoff + 32 > data.len) return error.InvalidPhdr;
            const p_type = readU32Le(data, phoff + 0);
            if (p_type != PT_LOAD) continue;
            const p_offset = readU32Le(data, phoff + 4);
            const p_vaddr = readU32Le(data, phoff + 8);
            const p_filesz = readU32Le(data, phoff + 16);
            _ = readU32Le(data, phoff + 20); // p_memsz (reserved for BSS later)
            if (p_offset > data.len or p_offset + p_filesz > data.len) return error.InvalidPhdr;
            const seg_data = data[p_offset..][0..p_filesz];
            try segments.append(allocator, .{ .vaddr = p_vaddr, .data = seg_data });
        }
    } else {
        return error.UnsupportedClass;
    }

    if (segments.items.len == 0) return error.NoLoadSegments;

    const owned = try allocator.dupe(Segment, segments.items);
    segments.deinit(allocator);
    return LoadResult{
        .entry_pc = entry_pc,
        .segments = owned,
        .segments_owned = owned,
    };
}

test "elf: isElf" {
    try std.testing.expect(!isElf(""));
    try std.testing.expect(!isElf("xxx"));
    try std.testing.expect(isElf("\x7fELF"));
}
