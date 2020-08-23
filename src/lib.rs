use std::{convert::TryFrom, fmt, num::ParseIntError, str::Utf8Error};

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
        for chunk in self.0.chunks(3) {
            let (a, b, c) = match chunk {
                [a, b, c] => (*a, *b, *c),
                [a, b] => (*a, *b, 0),
                [a] => (*a, 0, 0),
                _ => unreachable!(),
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

#[derive(Eq, PartialEq, Debug, Clone)]
struct Hex(Vec<u8>);

impl Hex {
    pub fn xor(&mut self, key: &[u8]) {
        for (u, k) in self.0.iter_mut().zip(key.iter().cycle()) {
            *u ^= *k;
        }
    }

    pub fn to_ascii(&self) -> Result<&str, Utf8Error> {
        std::str::from_utf8(&self.0)
    }
}

impl fmt::Display for Hex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn hex_char(u: u8) -> char {
            match u {
                0..=9 => (b'0' + u).into(),
                10..=16 => (b'A' + (u - 10)).into(),
                _ => unreachable!(),
            }
        }
        for u in &self.0 {
            write!(f, "{}", hex_char(u >> 4))?;
            write!(f, "{}", hex_char(u & 0b0000_1111))?
        }
        Ok(())
    }
}

#[derive(Debug)]
enum InvalidHex {
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
        let mut result = Vec::with_capacity(value.len() / 2);
        let mut chars = value.chars();
        while let Some(one) = chars.next() {
            result.push(match chars.next() {
                Some(two) => u8::from_str_radix(&format!("{}{}", one, two), 16)?,
                None => u8::from_str_radix(&format!("0{}", one), 16)?,
            });
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

fn char_score(s: &str) -> Option<u32> {
    let len = s.len() as f64;
    let count_diff = |c, expected_freq: f64| {
        let expected = expected_freq / 100f64 * len;
        let actual = s.chars().filter(|it| *it == c).count() as f64;
        (expected - actual).abs()
    };
    if !s.is_ascii() {
        return None;
    }
    if s.chars().any(|it| it.is_control() && it != '\n') {
        return None;
    }
    Some(
        ([
            (' ', 12.17),
            ('.', 6.57),
            ('a', 6.09),
            ('e', 11.36),
            ('i', 7.546),
            ('o', 7.507),
            ('r', 4.95),
            ('t', 8.03),
        ]
        .iter()
        .map(|(c, freq)| count_diff(*c, *freq))
        .sum::<f64>()
            * 100f64) as u32,
    )
}

fn find_cypher(hex: &Hex) -> Option<(u8, u32, Hex)> {
    (0u8..=255)
        .filter_map(|cypher| {
            let mut hex = hex.clone();
            hex.xor(&[cypher]);
            let score = char_score(hex.to_ascii().ok()?)?;
            Some((cypher, score, hex))
        })
        .min_by_key(|(_, score, _)| *score)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn challenge_1_hex_to_base64() {
        let hex_str = Hex::try_from("49276d206b696c6c696e6720796f757220627261696e206c696b65206120706f69736f6e6f7573206d757368726f6f6d").unwrap();

        assert_eq!(
            Base64::from(hex_str).to_string(),
            "SSdtIGtpbGxpbmcgeW91ciBicmFpbiBsaWtlIGEgcG9pc29ub3VzIG11c2hyb29t"
        );
    }

    #[test]
    fn challenge_2_xor() {
        let mut hex = Hex::try_from("1c0111001f010100061a024b53535009181c").unwrap();
        let xor = Hex::try_from("686974207468652062756c6c277320657965")
            .unwrap()
            .0;
        hex.xor(&xor);
        assert_eq!(
            hex,
            Hex::try_from("746865206b696420646f6e277420706c6179").unwrap()
        )
    }

    #[test]
    fn challenge_3_single_byte_xor_cipher() {
        let hex =
            Hex::try_from("1b37373331363f78151b7f2b783431333d78397828372d363c78373e783a393b3736")
                .unwrap();
        let bytes: Vec<_> = (0u8..=255).collect();
        let hexes: Vec<_> = bytes
            .iter()
            .map(|b| {
                let mut h = hex.clone();
                h.xor(&[*b]);
                (h, *b)
            })
            .collect();
        let base64s: Vec<_> = hexes
            .into_iter()
            .filter_map(|(hex, b)| {
                let string = hex.to_ascii().ok()?.to_string();
                let score = char_score(&string)?;
                Some((string, b, score))
            })
            .collect();

        let (result, _b, _score) = base64s.iter().min_by_key(|(_, _, score)| score).unwrap();

        assert_eq!(result, "Cooking MC's like a pound of bacon");
    }

    #[test]
    fn challenge_4_find_single_xor() {
        let input = fs::read_to_string("4.txt").unwrap();
        let input = input.lines();

        let (_, _, decrypted_message) = input
            .filter_map(|s| {
                let hex = Hex::try_from(s).ok()?;
                find_cypher(&hex)
            })
            .min_by_key(|(score, _, _)| *score)
            .unwrap();

        assert_eq!(
            decrypted_message.to_ascii().unwrap(),
            "Now that the party is jumping\n"
        )
    }

    #[test]
    fn challenge_5_repeating_key_xor() {
        let msg = b"Burning 'em, if you ain't quick and nimble\nI go crazy when I hear a cymbal";
        let mut hex = Hex(msg.iter().copied().collect());
        hex.xor(b"ICE");
        assert_eq!(
            hex,
            Hex::try_from(
                "0b3637272a2b2e63622c2e69692a23693a2a3c6324202d623d63343c2a26226324272765272a282b2f20430a652e2c652a3124333a653e2b2027630c692b20283165286326302e27282f"
            ).unwrap()
        );
    }
}
