use std::fmt;

pub fn write_hex<W: fmt::Write>(s: &mut W, bytes: &[u8]) -> fmt::Result {
    for b in bytes {
        write!(s, "{b:02x}")?;
    }
    Ok(())
}
