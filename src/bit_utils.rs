#![allow(dead_code)]

/// return a nibble from a 16-bit uint
///
/// # Examples
/// ```
/// let short: u16 = 0xABCD
/// nibble_from_short(short, 0) // 0xA
/// nibble_from_short(short, 1) // 0xB
/// nibble_from_short(short, 2) // 0xC
/// nibble_from_short(short, 3) // 0xD
/// ```
pub fn nibble_from_short(short: u16, n: u8) -> Result<u8, String> {
    if n > 3 {
        return Err(format!("nibble N must be <= 3: nibble_from_short(short: {}, n: {})", short, n));
    }

    return Ok((short >> ((3 - n) * 4) & 0xF) as u8);
}

/// return a byte from a 16-bit uint
///
/// # Examples
/// ```
/// let short: u16 = 0xABCD
/// byte_from_short(short, 0) // 0xAB
/// byte_from_short(short, 1) // 0xCD
/// ```
pub fn byte_from_short(short: u16, n: u8) -> Result<u8, String> {
    if n > 1 {
        return Err(format!("short N must be <= 1: byte_from_short(short: {}, n: {})", short, n));
    }

    return Ok((short >> ((1 - n) * 8) & 0xFF) as u8);
}

/// return a short from 2 8-bit uint
///
/// # Examples
/// ```
/// let high: u8 = 0xAB
/// let low: u8 = 0xCD
/// short_from_bytes(high, low) // 0xABCD
/// ```
pub fn short_from_bytes(high: u8, low: u8) -> Result<u16, String> {
    return Ok((u16::from(high) << 8) | u16::from(low));
}