use std::{convert::TryFrom, fmt, num::ParseIntError};

#[derive(Debug)]
struct Base64(Vec<u8>);

const BASE64_ALPHABET: &str = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

impl fmt::Display for Base64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for chunk in self.0.chunks_exact(3) {
            let first = (usize::from(chunk[0]) & 0b1111_1100) >> 2;
            write!(f, "{}", &BASE64_ALPHABET[first..=first])?;

            // 6    f    6    f    6    d
            // 0110 1111 0110 1111 0110 1101
            // 01101111 01101111 01101101
            // 011011 110110  111101 101101

            let second = ((usize::from(chunk[0]) & 0b0000_0011) << 4)
                + ((usize::from(chunk[1]) & 0b1111_0000) >> 4);
            write!(f, "{}", &BASE64_ALPHABET[second..=second])?;

            let third = ((usize::from(chunk[1]) & 0b0000_1111) << 2)
                + ((usize::from(chunk[2]) & 0b1100_0000) >> 6);
            write!(f, "{}", &BASE64_ALPHABET[third..=third])?;

            let fourth = usize::from(chunk[2]) & 0b0011_1111;
            write!(f, "{}", &BASE64_ALPHABET[fourth..=fourth])?;
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
    fn print_base64_alphabet() {
        let mut expected = String::new();
        for range in ['A'..='Z', 'a'..='z', '0'..='9'].iter_mut() {
            for c in range {
                expected.push(c);
            }
        }
        expected.push_str("+/");
        assert_eq!(BASE64_ALPHABET, expected);
    }

    #[test]
    fn hex_to_base64_test() {
        let hex_str = Hex::try_from("49276d206b696c6c696e6720796f757220627261696e206c696b65206120706f69736f6e6f7573206d757368726f6f6d").unwrap();

        assert_eq!(
            Base64::from(hex_str).to_string(),
            "SSdtIGtpbGxpbmcgeW91ciBicmFpbiBsaWtlIGEgcG9pc29ub3VzIG11c2hyb29t"
        );
    }
}
