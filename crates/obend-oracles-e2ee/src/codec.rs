//! Strict ASCII hex and RFC 4648 base64 codecs for attestation and transcript wire formats.

/// Lowercase ASCII hex encoding.
pub fn hex_encode_lower(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0f) as usize] as char);
    }
    out
}

/// Strict ASCII hex decoding (even length, ASCII hex digits only, no whitespace).
pub fn hex_decode_strict(s: &str) -> Option<Vec<u8>> {
    let bytes = s.as_bytes();
    if !bytes.len().is_multiple_of(2) {
        return None;
    }
    let nibble = |c: u8| -> Option<u8> {
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            b'A'..=b'F' => Some(c - b'A' + 10),
            _ => None,
        }
    };
    let mut out = Vec::with_capacity(bytes.len() / 2);
    for pair in bytes.as_chunks::<2>().0 {
        let hi = nibble(pair[0])?;
        let lo = nibble(pair[1])?;
        out.push((hi << 4) | lo);
    }
    Some(out)
}

/// Strict RFC 4648 standard Base64 decoding (requires canonical padding, zero non-canonical
/// trailing bits, no whitespace).
pub fn base64_decode_strict(s: &str) -> Option<Vec<u8>> {
    let b = s.as_bytes();
    if !b.len().is_multiple_of(4) {
        return None;
    }
    let val = |c: u8| -> Option<u8> {
        match c {
            b'A'..=b'Z' => Some(c - b'A'),
            b'a'..=b'z' => Some(c - b'a' + 26),
            b'0'..=b'9' => Some(c - b'0' + 52),
            b'+' => Some(62),
            b'/' => Some(63),
            _ => None,
        }
    };
    let mut out = Vec::with_capacity((b.len() / 4) * 3);
    let total_chunks = b.len() / 4;
    for (idx, chunk) in b.as_chunks::<4>().0.iter().enumerate() {
        let is_last = idx + 1 == total_chunks;
        let c0 = val(chunk[0])?;
        let c1 = val(chunk[1])?;
        match (chunk[2], chunk[3]) {
            (b'=', b'=') => {
                if !is_last || (c1 & 0x0f) != 0 {
                    return None;
                }
                out.push((c0 << 2) | (c1 >> 4));
            }
            (c2_raw, b'=') => {
                if !is_last {
                    return None;
                }
                let c2 = val(c2_raw)?;
                if (c2 & 0x03) != 0 {
                    return None;
                }
                out.push((c0 << 2) | (c1 >> 4));
                out.push((c1 << 4) | (c2 >> 2));
            }
            (b'=', _) => return None,
            (c2_raw, c3_raw) => {
                let c2 = val(c2_raw)?;
                let c3 = val(c3_raw)?;
                out.push((c0 << 2) | (c1 >> 4));
                out.push((c1 << 4) | (c2 >> 2));
                out.push((c2 << 6) | c3);
            }
        }
    }
    Some(out)
}
