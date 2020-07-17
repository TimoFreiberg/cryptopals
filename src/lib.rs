use std::{convert::TryFrom, fmt, num::ParseIntError};

#[derive(Debug)]
struct Base64(Vec<u8>);

#[derive(Debug)]
struct InvalidU8ForBase64(u8);

fn u8_to_base64(it: u8) -> Result<char, InvalidU8ForBase64> {
    Ok(match it {
        0..=25 => (b'A' + it).into(),
        26..=51 => (b'a' + (it - 26)).into(),
        52..=61 => (b'0' + (it - 52)).into(),
        62 => '+',
        63 => '/',
        _ => return Err(InvalidU8ForBase64(it)),
    })
}

impl fmt::Display for Base64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for chunk in self.0.chunks_exact(3) {
            let (a, b, c) = match chunk {
                [a, b, c] => (*a, *b, *c),
                [a, b] => (*a, *b, 0),
                [a] => (*a, 0, 0),
                _ => continue,
            };

            write!(f, "{}", u8_to_base64(a >> 2).unwrap())?;
            write!(
                f,
                "{}",
                u8_to_base64(((a & 0b0000_0011) << 4) + (b >> 4)).unwrap()
            )?;
            write!(
                f,
                "{}",
                u8_to_base64(((b & 0b0000_1111) << 2) + (c >> 6)).unwrap()
            )?;
            write!(f, "{}", u8_to_base64(c & 0b0011_1111).unwrap())?;
        }
        Ok(())
    }
}

impl From<Hex> for Base64 {
    fn from(hex: Hex) -> Self {
        Base64(hex.0)
    }
}

struct Hex(Vec<u8>);

#[derive(Debug)]
enum InvalidHex {
    InvalidLength,
    ParseError(ParseIntError),
}

impl From<ParseIntError> for InvalidHex {
    fn from(it: ParseIntError) -> Self {
        InvalidHex::ParseError(it)
    }
}

impl TryFrom<&str> for Hex {
    type Error = InvalidHex;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        if value.len() % 2 != 0 {
            return Err(InvalidHex::InvalidLength);
        }
        let mut result = Vec::with_capacity(value.len() / 2);
        let mut chars = value.chars();
        while let Some(one) = chars.next() {
            let two = chars.next().unwrap();
            result.push(u8::from_str_radix(&format!("{}{}", one, two), 16)?);
        }
        Ok(Hex(result))
    }
}

#[derive(Debug)]
struct InvalidBase64;

impl TryFrom<&[u8]> for Base64 {
    type Error = InvalidBase64;
    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        if value.len() % 4 == 0 {
            Ok(Base64(value.iter().copied().collect()))
        } else {
            Err(InvalidBase64)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hex_to_base64_test() {
        let hex_str = Hex::try_from("49276d206b696c6c696e6720796f757220627261696e206c696b65206120706f69736f6e6f7573206d757368726f6f6d").unwrap();

        assert_eq!(
            Base64::from(hex_str).to_string(),
            "SSdtIGtpbGxpbmcgeW91ciBicmFpbiBsaWtlIGEgcG9pc29ub3VzIG11c2hyb29t"
        );
    }
}
