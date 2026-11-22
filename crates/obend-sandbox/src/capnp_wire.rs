#![forbid(unsafe_code)]
//! Allocation-bounded, pure-Rust Cap'n Proto wire codec (`Signature`, `Archive`, `Manifest`,
//! and `BridgeConfig` / `ViewInfo` with `List(Bool)` permission bitsets).
//!
//! Quarried and hardened from `breadstuffs/sandstorm-package/src/capnp_wire.rs` +
//! `minidregg/native/spk-rpc/src/bridge_config.rs` with zero `unsafe` and zero external codegen.

use std::fmt;

/// Why decoding a Cap'n Proto message failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CapnpError {
    Framing(&'static str),
    OutOfBounds(&'static str),
    ListTooLarge,
    TooDeep,
    WrongKind(&'static str),
}

impl fmt::Display for CapnpError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CapnpError::Framing(s) => write!(f, "capnp framing: {s}"),
            CapnpError::OutOfBounds(s) => write!(f, "capnp pointer out of bounds: {s}"),
            CapnpError::ListTooLarge => write!(f, "capnp list count exceeds message bytes"),
            CapnpError::TooDeep => write!(f, "capnp pointer nesting too deep"),
            CapnpError::WrongKind(s) => write!(f, "capnp field has unexpected kind: {s}"),
        }
    }
}

impl std::error::Error for CapnpError {}

const MAX_DEPTH: u32 = 256;
const MAX_SEGMENTS: usize = 4096;

/// A parsed, framed Cap'n Proto message borrowing its segments from the input slice.
pub struct Message<'a> {
    segments: Vec<&'a [u8]>,
}

impl<'a> Message<'a> {
    /// Parse one framed Cap'n Proto message from the front of `bytes`, returning `(Message, consumed_bytes)`.
    pub fn parse_prefix(bytes: &'a [u8]) -> Result<(Message<'a>, usize), CapnpError> {
        let seg_count_minus_one =
            read_u32(bytes, 0).ok_or(CapnpError::Framing("missing segment count"))?;
        let seg_count = (seg_count_minus_one as usize)
            .checked_add(1)
            .ok_or(CapnpError::Framing("segment count overflow"))?;
        if seg_count > MAX_SEGMENTS {
            return Err(CapnpError::Framing("segment count exceeds bound"));
        }
        let table_bytes = 4usize
            .checked_add(
                seg_count
                    .checked_mul(4)
                    .ok_or(CapnpError::Framing("table overflow"))?,
            )
            .ok_or(CapnpError::Framing("table overflow"))?;
        if table_bytes > bytes.len() {
            return Err(CapnpError::Framing("segment table truncated"));
        }
        let mut sizes = Vec::with_capacity(seg_count);
        let mut total_words: usize = 0;
        for i in 0..seg_count {
            let sz = read_u32(bytes, 4 + i * 4)
                .ok_or(CapnpError::Framing("segment size truncated"))?
                as usize;
            total_words = total_words
                .checked_add(sz)
                .ok_or(CapnpError::Framing("segment words overflow"))?;
            sizes.push(sz);
        }
        let header = (table_bytes + 7) & !7;
        // Require padding bytes in the segment table tail (if odd segment count) to be canonical or present
        let data_bytes = total_words
            .checked_mul(8)
            .ok_or(CapnpError::Framing("segment bytes overflow"))?;
        let consumed = header
            .checked_add(data_bytes)
            .ok_or(CapnpError::Framing("message size overflow"))?;
        if consumed > bytes.len() {
            return Err(CapnpError::Framing("message body truncated"));
        }
        let mut segments = Vec::with_capacity(seg_count);
        let mut off = header;
        for sz in sizes {
            let n = sz * 8;
            segments.push(&bytes[off..off + n]);
            off += n;
        }
        Ok((Message { segments }, consumed))
    }

    pub fn root(&self) -> Result<Struct<'a, '_>, CapnpError> {
        let seg0 = self
            .segments
            .first()
            .ok_or(CapnpError::Framing("no segments"))?;
        let ptr = read_u64(seg0, 0).ok_or(CapnpError::Framing("missing root pointer"))?;
        match self.follow(0, 0, ptr, 0)? {
            Resolved::Struct(s) => Ok(s),
            _ => Err(CapnpError::WrongKind("root is not a struct")),
        }
    }

    fn seg(&self, idx: usize) -> Result<&'a [u8], CapnpError> {
        self.segments
            .get(idx)
            .copied()
            .ok_or(CapnpError::OutOfBounds("segment index"))
    }

    fn follow(
        &self,
        seg: usize,
        ptr_word_idx: usize,
        ptr: u64,
        depth: u32,
    ) -> Result<Resolved<'a, '_>, CapnpError> {
        if depth > MAX_DEPTH {
            return Err(CapnpError::TooDeep);
        }
        if ptr == 0 {
            return Ok(Resolved::Null);
        }
        match ptr & 3 {
            2 => {
                let landing_word = ((ptr >> 3) & 0x1fff_ffff) as usize;
                let double = (ptr >> 2) & 1 == 1;
                let target_seg = (ptr >> 32) as usize;
                let lseg = self.seg(target_seg)?;
                let landing_byte = landing_word
                    .checked_mul(8)
                    .ok_or(CapnpError::OutOfBounds("far landing overflow"))?;
                if !double {
                    let landing = read_u64(lseg, landing_byte)
                        .ok_or(CapnpError::OutOfBounds("far landing pad"))?;
                    self.follow(target_seg, landing_word, landing, depth + 1)
                } else {
                    let pad2_byte = landing_byte
                        .checked_add(8)
                        .ok_or(CapnpError::OutOfBounds("double-far overflow"))?;
                    let far = read_u64(lseg, landing_byte)
                        .ok_or(CapnpError::OutOfBounds("double-far pad"))?;
                    let tag = read_u64(lseg, pad2_byte)
                        .ok_or(CapnpError::OutOfBounds("double-far tag"))?;
                    if far & 3 != 2 || ((far >> 2) & 1) != 0 {
                        return Err(CapnpError::Framing("double-far first word not a single far ptr"));
                    }
                    let content_word = ((far >> 3) & 0x1fff_ffff) as usize;
                    let content_seg = (far >> 32) as usize;
                    self.resolve_with_tag(content_seg, content_word, tag)
                }
            }
            _ => {
                let off = sign_extend_30((ptr >> 2) & 0x3fff_ffff);
                let target = (ptr_word_idx as i64) + 1 + off;
                if target < 0 {
                    return Err(CapnpError::OutOfBounds("negative target"));
                }
                self.resolve_with_tag(seg, target as usize, ptr)
            }
        }
    }

    fn resolve_with_tag(
        &self,
        seg: usize,
        content_word: usize,
        tag: u64,
    ) -> Result<Resolved<'a, '_>, CapnpError> {
        match tag & 3 {
            0 => {
                let data_words = ((tag >> 32) & 0xffff) as usize;
                let ptr_words = ((tag >> 48) & 0xffff) as usize;
                self.bound_struct(seg, content_word, data_words, ptr_words)?;
                Ok(Resolved::Struct(Struct {
                    msg: self,
                    seg,
                    data_word: content_word,
                    data_words,
                    ptr_words,
                }))
            }
            1 => {
                let elem_type = ((tag >> 32) & 7) as u8;
                let count = ((tag >> 35) & 0x1fff_ffff) as usize;
                Ok(Resolved::List(List {
                    msg: self,
                    seg,
                    start_word: content_word,
                    elem_type,
                    count,
                }))
            }
            _ => Err(CapnpError::Framing("tag is itself a far/other pointer")),
        }
    }

    fn bound_struct(
        &self,
        seg: usize,
        data_word: usize,
        data_words: usize,
        ptr_words: usize,
    ) -> Result<(), CapnpError> {
        let s = self.seg(seg)?;
        let total = data_word
            .checked_add(data_words)
            .and_then(|w| w.checked_add(ptr_words))
            .ok_or(CapnpError::OutOfBounds("struct extent overflow"))?;
        let total_bytes = total
            .checked_mul(8)
            .ok_or(CapnpError::OutOfBounds("struct byte overflow"))?;
        if total_bytes > s.len() {
            return Err(CapnpError::OutOfBounds("struct extends past segment"));
        }
        Ok(())
    }
}

enum Resolved<'a, 'm> {
    Null,
    Struct(Struct<'a, 'm>),
    List(List<'a, 'm>),
}

pub struct Struct<'a, 'm> {
    msg: &'m Message<'a>,
    seg: usize,
    data_word: usize,
    data_words: usize,
    ptr_words: usize,
}

impl<'a, 'm> Struct<'a, 'm> {
    fn seg_bytes(&self) -> &'a [u8] {
        self.msg.segments[self.seg]
    }

    /// Read a `Bool` at bit offset `bit_off` inside the struct's data section (`false` if past end).
    pub fn get_bool(&self, bit_off: usize) -> bool {
        let byte_off = bit_off / 8;
        let bit_in_byte = bit_off % 8;
        if byte_off >= self.data_words * 8 {
            return false;
        }
        let abs = self.data_word * 8 + byte_off;
        self.seg_bytes()
            .get(abs)
            .map(|b| ((b >> bit_in_byte) & 1) == 1)
            .unwrap_or(false)
    }

    pub fn get_u16(&self, byte_off: usize) -> u16 {
        if byte_off + 2 > self.data_words * 8 {
            return 0;
        }
        read_u16(self.seg_bytes(), self.data_word * 8 + byte_off).unwrap_or(0)
    }

    pub fn get_u32(&self, byte_off: usize) -> u32 {
        if byte_off + 4 > self.data_words * 8 {
            return 0;
        }
        read_u32(self.seg_bytes(), self.data_word * 8 + byte_off).unwrap_or(0)
    }

    pub fn get_i64(&self, byte_off: usize) -> i64 {
        if byte_off + 8 > self.data_words * 8 {
            return 0;
        }
        read_u64(self.seg_bytes(), self.data_word * 8 + byte_off).unwrap_or(0) as i64
    }

    fn raw_ptr(&self, i: usize) -> Result<Option<(usize, u64)>, CapnpError> {
        if i >= self.ptr_words {
            return Ok(None);
        }
        let ptr_word = self.data_word + self.data_words + i;
        let p = read_u64(self.seg_bytes(), ptr_word * 8)
            .ok_or(CapnpError::OutOfBounds("pointer slot"))?;
        Ok(Some((ptr_word, p)))
    }

    pub fn get_struct(&self, i: usize) -> Result<Option<Struct<'a, 'm>>, CapnpError> {
        match self.raw_ptr(i)? {
            None => Ok(None),
            Some((pw, p)) => match self.msg.follow(self.seg, pw, p, 0)? {
                Resolved::Null => Ok(None),
                Resolved::Struct(s) => Ok(Some(s)),
                Resolved::List(_) => Err(CapnpError::WrongKind("expected struct, got list")),
            },
        }
    }

    pub fn get_list(&self, i: usize) -> Result<Option<List<'a, 'm>>, CapnpError> {
        match self.raw_ptr(i)? {
            None => Ok(None),
            Some((pw, p)) => match self.msg.follow(self.seg, pw, p, 0)? {
                Resolved::Null => Ok(None),
                Resolved::List(l) => Ok(Some(l)),
                Resolved::Struct(_) => Err(CapnpError::WrongKind("expected list, got struct")),
            },
        }
    }

    pub fn get_data(&self, i: usize) -> Result<Vec<u8>, CapnpError> {
        match self.get_list(i)? {
            None => Ok(Vec::new()),
            Some(l) => l.bytes(),
        }
    }

    pub fn get_text(&self, i: usize) -> Result<String, CapnpError> {
        let mut b = self.get_data(i)?;
        if b.is_empty() {
            return Ok(String::new());
        }
        if b.pop() != Some(0) {
            return Err(CapnpError::Framing("Text lacks trailing NUL"));
        }
        String::from_utf8(b).map_err(|_| CapnpError::Framing("Text is not UTF-8"))
    }

    pub fn get_bool_list(&self, i: usize) -> Result<Vec<bool>, CapnpError> {
        match self.get_list(i)? {
            None => Ok(Vec::new()),
            Some(l) => l.bools(),
        }
    }
}

pub struct List<'a, 'm> {
    msg: &'m Message<'a>,
    seg: usize,
    start_word: usize,
    elem_type: u8,
    count: usize,
}

impl<'a, 'm> List<'a, 'm> {
    pub fn len(&self) -> usize {
        if self.elem_type == 7 {
            self.composite_count().unwrap_or(0)
        } else {
            self.count
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn seg_bytes(&self) -> Result<&'a [u8], CapnpError> {
        self.msg.seg(self.seg)
    }

    /// Decode a `List(Bool)` (`elem_type == 1`, 1-bit packed elements) with pre-allocation bounds check.
    pub fn bools(&self) -> Result<Vec<bool>, CapnpError> {
        if self.count == 0 {
            return Ok(Vec::new());
        }
        if self.elem_type != 1 {
            return Err(CapnpError::WrongKind("expected a 1-bit Bool list"));
        }
        let s = self.seg_bytes()?;
        let start = self
            .start_word
            .checked_mul(8)
            .ok_or(CapnpError::OutOfBounds("bool list start overflow"))?;
        let byte_len = self.count.div_ceil(8);
        let end = start
            .checked_add(byte_len)
            .ok_or(CapnpError::OutOfBounds("bool list end overflow"))?;
        if end > s.len() {
            return Err(CapnpError::ListTooLarge);
        }
        let mut out = Vec::with_capacity(self.count);
        for bit_idx in 0..self.count {
            let b = s[start + bit_idx / 8];
            out.push(((b >> (bit_idx % 8)) & 1) == 1);
        }
        Ok(out)
    }

    pub fn bytes(&self) -> Result<Vec<u8>, CapnpError> {
        if self.count == 0 {
            return Ok(Vec::new());
        }
        if self.elem_type != 2 {
            return Err(CapnpError::WrongKind("expected a byte list"));
        }
        let s = self.seg_bytes()?;
        let start = self
            .start_word
            .checked_mul(8)
            .ok_or(CapnpError::OutOfBounds("list start overflow"))?;
        let end = start
            .checked_add(self.count)
            .ok_or(CapnpError::OutOfBounds("list end overflow"))?;
        if end > s.len() {
            return Err(CapnpError::ListTooLarge);
        }
        Ok(s[start..end].to_vec())
    }

    fn composite_count(&self) -> Result<usize, CapnpError> {
        let s = self.seg_bytes()?;
        let off = self
            .start_word
            .checked_mul(8)
            .ok_or(CapnpError::OutOfBounds("composite tag overflow"))?;
        let tag = read_u64(s, off).ok_or(CapnpError::OutOfBounds("composite tag"))?;
        Ok(((tag >> 2) & 0x3fff_ffff) as usize)
    }

    pub fn structs(&self) -> Result<Vec<Struct<'a, 'm>>, CapnpError> {
        if self.elem_type != 7 {
            return Err(CapnpError::WrongKind("expected a composite list"));
        }
        let s = self.seg_bytes()?;
        let off = self
            .start_word
            .checked_mul(8)
            .ok_or(CapnpError::OutOfBounds("composite tag overflow"))?;
        let tag = read_u64(s, off).ok_or(CapnpError::OutOfBounds("composite tag"))?;
        if tag & 3 != 0 {
            return Err(CapnpError::Framing("composite tag is not a struct tag"));
        }
        let elem_count = ((tag >> 2) & 0x3fff_ffff) as usize;
        let data_words = ((tag >> 32) & 0xffff) as usize;
        let ptr_words = ((tag >> 48) & 0xffff) as usize;
        let stride = data_words
            .checked_add(ptr_words)
            .ok_or(CapnpError::OutOfBounds("stride overflow"))?;
        let body_words = elem_count
            .checked_mul(stride)
            .ok_or(CapnpError::ListTooLarge)?;
        if body_words != self.count {
            return Err(CapnpError::Framing("composite word count mismatch"));
        }
        if stride == 0 && elem_count != 0 {
            return Err(CapnpError::ListTooLarge);
        }
        let total_words = self
            .start_word
            .checked_add(1)
            .and_then(|w| w.checked_add(body_words))
            .ok_or(CapnpError::ListTooLarge)?;
        if total_words
            .checked_mul(8)
            .ok_or(CapnpError::ListTooLarge)?
            > s.len()
        {
            return Err(CapnpError::ListTooLarge);
        }
        let mut out = Vec::with_capacity(elem_count);
        for i in 0..elem_count {
            let data_word = self.start_word + 1 + i * stride;
            out.push(Struct {
                msg: self.msg,
                seg: self.seg,
                data_word,
                data_words,
                ptr_words,
            });
        }
        Ok(out)
    }

    pub fn text_list(&self) -> Result<Vec<String>, CapnpError> {
        if self.count == 0 {
            return Ok(Vec::new());
        }
        if self.elem_type != 6 {
            return Err(CapnpError::WrongKind("expected a pointer list"));
        }
        let s = self.seg_bytes()?;
        let total = self
            .start_word
            .checked_add(self.count)
            .ok_or(CapnpError::ListTooLarge)?;
        if total.checked_mul(8).ok_or(CapnpError::ListTooLarge)? > s.len() {
            return Err(CapnpError::ListTooLarge);
        }
        let mut out = Vec::with_capacity(self.count);
        for i in 0..self.count {
            let pw = self.start_word + i;
            let p = read_u64(s, pw * 8).ok_or(CapnpError::OutOfBounds("text list slot"))?;
            match self.msg.follow(self.seg, pw, p, 0)? {
                Resolved::Null => out.push(String::new()),
                Resolved::List(l) => {
                    let mut b = l.bytes()?;
                    if !b.is_empty() && b.pop() != Some(0) {
                        return Err(CapnpError::Framing("Text lacks trailing NUL"));
                    }
                    out.push(
                        String::from_utf8(b)
                            .map_err(|_| CapnpError::Framing("Text is not UTF-8"))?,
                    );
                }
                Resolved::Struct(_) => {
                    return Err(CapnpError::WrongKind("text list slot is a struct"))
                }
            }
        }
        Ok(out)
    }
}

// =========================================================================
// Single-Segment Cap'n Proto Builders (`Signature`, `Archive`, `Manifest`, `BridgeConfig`)
// =========================================================================

pub struct Builder {
    buf: Vec<u8>,
}

impl Builder {
    pub fn new() -> Self {
        Self { buf: Vec::new() }
    }

    pub(crate) fn alloc(&mut self, words: usize) -> usize {
        let wi = self.buf.len() / 8;
        self.buf.resize(self.buf.len() + words * 8, 0);
        wi
    }

    pub(crate) fn put_word(&mut self, word_idx: usize, v: u64) {
        self.buf[word_idx * 8..word_idx * 8 + 8].copy_from_slice(&v.to_le_bytes());
    }

    fn put_bytes(&mut self, byte_off: usize, data: &[u8]) {
        self.buf[byte_off..byte_off + data.len()].copy_from_slice(data);
    }

    pub(crate) fn struct_ptr_at(&mut self, slot: usize, target_word: usize, dwords: u16, pwords: u16) {
        let off = target_word as i64 - (slot as i64 + 1);
        let off30 = (off as u64) & 0x3fff_ffff;
        let p = (off30 << 2) | ((dwords as u64) << 32) | ((pwords as u64) << 48);
        self.put_word(slot, p);
    }

    pub(crate) fn bytes_ptr_at(&mut self, slot: usize, data: &[u8], text: bool) {
        let count = data.len() + usize::from(text);
        if count == 0 {
            self.put_word(slot, 1);
            return;
        }
        let words = count.div_ceil(8);
        let content = self.alloc(words);
        self.put_bytes(content * 8, data);
        let off = content as i64 - (slot as i64 + 1);
        let off30 = (off as u64) & 0x3fff_ffff;
        let p = 1 | (off30 << 2) | (2u64 << 32) | ((count as u64) << 35);
        self.put_word(slot, p);
    }

    pub(crate) fn bool_list_ptr_at(&mut self, slot: usize, bits: &[bool]) {
        if bits.is_empty() {
            self.put_word(slot, 0);
            return;
        }
        let words = bits.len().div_ceil(64);
        let content = self.alloc(words);
        for (idx, &bit) in bits.iter().enumerate() {
            if bit {
                self.buf[content * 8 + idx / 8] |= 1u8 << (idx % 8);
            }
        }
        let off = content as i64 - (slot as i64 + 1);
        let off30 = (off as u64) & 0x3fff_ffff;
        let p = 1 | (off30 << 2) | (1u64 << 32) | ((bits.len() as u64) << 35);
        self.put_word(slot, p);
    }

    pub(crate) fn text_list_ptr_at(&mut self, slot: usize, items: &[&str]) {
        if items.is_empty() {
            self.put_word(slot, 0);
            return;
        }
        let list_word = self.alloc(items.len());
        let off = list_word as i64 - (slot as i64 + 1);
        let off30 = (off as u64) & 0x3fff_ffff;
        let p = 1 | (off30 << 2) | (6u64 << 32) | ((items.len() as u64) << 35);
        self.put_word(slot, p);
        for (i, s) in items.iter().enumerate() {
            self.bytes_ptr_at(list_word + i, s.as_bytes(), true);
        }
    }

    pub(crate) fn localized_text_at(&mut self, slot: usize, default_text: &str) {
        if default_text.is_empty() {
            self.put_word(slot, 0);
            return;
        }
        // Util.LocalizedText: 0 data words, 2 pointer words (defaultText@0, localizations@1)
        let lt = self.alloc(2);
        self.struct_ptr_at(slot, lt, 0, 2);
        self.bytes_ptr_at(lt, default_text.as_bytes(), true);
    }

    fn file_list_ptr_at(&mut self, slot: usize, files: &[WireFile]) {
        if files.is_empty() {
            self.put_word(slot, 0);
            return;
        }
        const DW: usize = 2;
        const PW: usize = 2;
        const STRIDE: usize = DW + PW;
        let total = 1 + files.len() * STRIDE;
        let tag_word = self.alloc(total);
        let count30 = (files.len() as u64) & 0x3fff_ffff;
        let tag = (count30 << 2) | ((DW as u64) << 32) | ((PW as u64) << 48);
        self.put_word(tag_word, tag);
        let off = tag_word as i64 - (slot as i64 + 1);
        let off30 = (off as u64) & 0x3fff_ffff;
        let body_words = (files.len() * STRIDE) as u64;
        let p = 1 | (off30 << 2) | (7u64 << 32) | (body_words << 35);
        self.put_word(slot, p);
        for (i, f) in files.iter().enumerate() {
            let base = tag_word + 1 + i * STRIDE;
            self.put_word(base, f.discriminant() as u64);
            self.put_word(base + 1, f.mtime_ns as u64);
            let name_slot = base + DW;
            let union_slot = base + DW + 1;
            self.bytes_ptr_at(name_slot, f.name.as_bytes(), true);
            match &f.content {
                WireContent::Regular(b) | WireContent::Executable(b) => {
                    self.bytes_ptr_at(union_slot, b, false)
                }
                WireContent::Symlink(t) => self.bytes_ptr_at(union_slot, t.as_bytes(), true),
                WireContent::Directory(sub) => self.file_list_ptr_at(union_slot, sub),
            }
        }
    }

    pub(crate) fn into_framed(self) -> Vec<u8> {
        let words = self.buf.len() / 8;
        let mut out = Vec::with_capacity(8 + self.buf.len());
        out.extend_from_slice(&0u32.to_le_bytes());
        out.extend_from_slice(&(words as u32).to_le_bytes());
        out.extend_from_slice(&self.buf);
        out
    }
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

pub enum WireContent<'a> {
    Regular(&'a [u8]),
    Executable(&'a [u8]),
    Symlink(&'a str),
    Directory(Vec<WireFile<'a>>),
}

pub struct WireFile<'a> {
    pub name: &'a str,
    pub content: WireContent<'a>,
    pub mtime_ns: i64,
}

impl WireFile<'_> {
    fn discriminant(&self) -> u16 {
        match self.content {
            WireContent::Regular(_) => 0,
            WireContent::Executable(_) => 1,
            WireContent::Symlink(_) => 2,
            WireContent::Directory(_) => 3,
        }
    }
}

pub fn write_archive(files: &[WireFile]) -> Vec<u8> {
    let mut b = Builder::new();
    let root_slot = b.alloc(1);
    let archive_struct = b.alloc(1);
    b.struct_ptr_at(root_slot, archive_struct, 0, 1);
    b.file_list_ptr_at(archive_struct, files);
    b.into_framed()
}

pub fn write_signature(public_key: &[u8], signature: &[u8]) -> Vec<u8> {
    let mut b = Builder::new();
    let root_slot = b.alloc(1);
    let sig_struct = b.alloc(2);
    b.struct_ptr_at(root_slot, sig_struct, 0, 2);
    b.bytes_ptr_at(sig_struct, public_key, false);
    b.bytes_ptr_at(sig_struct + 1, signature, false);
    b.into_framed()
}

/// Wire input for building a canonical Cap'n Proto `sandstorm-http-bridge-config` (`package.capnp:BridgeConfig`).
pub struct WirePermissionDef<'a> {
    pub name: &'a str,
    pub title: &'a str,
    pub obsolete: bool,
}

pub struct WireRoleDef<'a> {
    pub title: &'a str,
    pub verb_phrase: &'a str,
    pub permissions: &'a [bool],
    pub obsolete: bool,
    pub default: bool,
}

pub struct WireBridgeConfig<'a> {
    pub app_title: &'a str,
    pub permissions: &'a [WirePermissionDef<'a>],
    pub roles: &'a [WireRoleDef<'a>],
    pub denied_permissions: &'a [bool],
    pub api_path: Option<&'a str>,
    pub save_identity_caps: bool,
    pub expect_app_hooks: bool,
}

/// Encode a canonical `package.capnp:BridgeConfig` Cap'n Proto message (`sandstorm-http-bridge-config`).
pub fn write_bridge_config(cfg: &WireBridgeConfig<'_>) -> Vec<u8> {
    let mut b = Builder::new();
    let root_slot = b.alloc(1);
    // BridgeConfig: 1 data word (saveIdentityCaps@bit0, expectAppHooks@bit1), 3 ptr words (viewInfo@0, apiPath@1, powerboxApis@2)
    let bc = b.alloc(1 + 3);
    b.struct_ptr_at(root_slot, bc, 1, 3);
    let mut flags = 0u64;
    if cfg.save_identity_caps {
        flags |= 1;
    }
    if cfg.expect_app_hooks {
        flags |= 2;
    }
    b.put_word(bc, flags);

    // ViewInfo: 0 data words, 8 ptr words (permissions@0, roles@1, deniedPermissions@2, ..., appTitle@5)
    let vi = b.alloc(8);
    b.struct_ptr_at(bc + 1, vi, 0, 8);
    if let Some(api_path) = cfg.api_path {
        b.bytes_ptr_at(bc + 2, api_path.as_bytes(), true);
    }

    if !cfg.permissions.is_empty() {
        // PermissionDef: 1 data word (obsolete@bit0), 3 ptr words (title@0, description@1, name@2)
        const DW: usize = 1;
        const PW: usize = 3;
        const STRIDE: usize = DW + PW;
        let tag_word = b.alloc(1 + cfg.permissions.len() * STRIDE);
        let tag = ((cfg.permissions.len() as u64) << 2) | ((DW as u64) << 32) | ((PW as u64) << 48);
        b.put_word(tag_word, tag);
        let off = tag_word as i64 - ((vi) as i64 + 1);
        let p = 1 | (((off as u64) & 0x3fff_ffff) << 2) | (7u64 << 32) | (((cfg.permissions.len() * STRIDE) as u64) << 35);
        b.put_word(vi, p);
        for (i, perm) in cfg.permissions.iter().enumerate() {
            let base = tag_word + 1 + i * STRIDE;
            b.put_word(base, u64::from(perm.obsolete));
            b.localized_text_at(base + 1, perm.title);
            b.bytes_ptr_at(base + 3, perm.name.as_bytes(), true);
        }
    }

    if !cfg.roles.is_empty() {
        // RoleDef: 1 data word (obsolete@bit0, default@bit1), 4 ptr words (title@0, verbPhrase@1, description@2, permissions@3)
        const DW: usize = 1;
        const PW: usize = 4;
        const STRIDE: usize = DW + PW;
        let tag_word = b.alloc(1 + cfg.roles.len() * STRIDE);
        let tag = ((cfg.roles.len() as u64) << 2) | ((DW as u64) << 32) | ((PW as u64) << 48);
        b.put_word(tag_word, tag);
        let off = tag_word as i64 - ((vi + 1) as i64 + 1);
        let p = 1 | (((off as u64) & 0x3fff_ffff) << 2) | (7u64 << 32) | (((cfg.roles.len() * STRIDE) as u64) << 35);
        b.put_word(vi + 1, p);
        for (i, role) in cfg.roles.iter().enumerate() {
            let base = tag_word + 1 + i * STRIDE;
            let rflags = u64::from(role.obsolete) | (u64::from(role.default) << 1);
            b.put_word(base, rflags);
            b.localized_text_at(base + 1, role.title);
            b.localized_text_at(base + 2, role.verb_phrase);
            b.bool_list_ptr_at(base + 4, role.permissions);
        }
    }

    b.bool_list_ptr_at(vi + 2, cfg.denied_permissions);
    b.localized_text_at(vi + 5, cfg.app_title);

    b.into_framed()
}

/// Encode a canonical `package.capnp:Manifest` Cap'n Proto message (`sandstorm-manifest`).
pub fn write_manifest_capnp(
    app_title: &str,
    app_version: u32,
    marketing_version: &str,
    continue_argv: &[&str],
) -> Vec<u8> {
    let mut b = Builder::new();
    let root_slot = b.alloc(1);
    // Manifest: 2 data words (minApi@0, maxApi@4, appVersion@8, minUpgradable@12), 5 ptr words
    // (actions@0, continueCommand@1, appMarketingVersion@2, appTitle@3, metadata@4)
    let m = b.alloc(2 + 5);
    b.struct_ptr_at(root_slot, m, 2, 5);
    b.put_word(m + 1, app_version as u64);

    // Command: 0 data words, 3 ptr words (deprecatedExecutablePath@0, argv@1, environ@2)
    let cmd = b.alloc(3);
    b.struct_ptr_at(m + 2 + 1, cmd, 0, 3);
    b.text_list_ptr_at(cmd + 1, continue_argv);
    b.localized_text_at(m + 2 + 2, marketing_version);
    b.localized_text_at(m + 2 + 3, app_title);
    b.into_framed()
}

fn read_u16(b: &[u8], off: usize) -> Option<u16> {
    b.get(off..off + 2)
        .map(|s| u16::from_le_bytes([s[0], s[1]]))
}
fn read_u32(b: &[u8], off: usize) -> Option<u32> {
    b.get(off..off + 4)
        .map(|s| u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
}
fn read_u64(b: &[u8], off: usize) -> Option<u64> {
    b.get(off..off + 8)
        .map(|s| u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]))
}

fn sign_extend_30(v: u64) -> i64 {
    let v = v & 0x3fff_ffff;
    if v & 0x2000_0000 != 0 {
        (v as i64) - (1 << 30)
    } else {
        v as i64
    }
}
