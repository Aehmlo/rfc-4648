#![deny(
    clippy::dbg_macro,
    clippy::doc_markdown,
    clippy::enum_glob_use,
    clippy::explicit_into_iter_loop,
    clippy::explicit_iter_loop,
    clippy::filter_map,
    clippy::float_arithmetic,
    clippy::get_unwrap,
    clippy::if_not_else,
    clippy::map_flatten,
    clippy::missing_const_for_fn,
    clippy::module_name_repetitions,
    clippy::multiple_inherent_impl,
    clippy::mut_mut,
    clippy::needless_borrow,
    clippy::needless_pass_by_value,
    clippy::option_map_unwrap_or,
    clippy::option_map_unwrap_or_else,
    clippy::option_unwrap_used,
    clippy::print_stdout,
    clippy::pub_enum_variant_names,
    clippy::redundant_clone,
    clippy::replace_consts,
    clippy::similar_names,
    clippy::unimplemented,
    clippy::unseparated_literal_suffix,
    clippy::use_debug,
    clippy::use_self,
    clippy::used_underscore_binding,
    clippy::wildcard_dependencies,
    clippy::wildcard_enum_match_arm
)]

use bitvec::prelude::*;

#[allow(clippy::pub_enum_variant_names)]
#[derive(Clone, Copy, Debug)]
pub enum Encoding {
    Base16,
    Base32,
    Base32Hex,
    Base64,
}

// TODO: Revisit when const fn becomes more mature
mod alphabet {
    fn stringify<I: Iterator<Item = u8>>(iter: I) -> String {
        // This is safe because we only ever use it with iterators over ASCII characters.
        unsafe { String::from_utf8_unchecked(iter.collect()) }
    }
    pub(super) fn base16() -> String {
        let letters = (b'0'..=b'9').chain(b'A'..=b'F');
        stringify(letters)
    }
    pub(super) fn base32() -> String {
        let letters = (b'A'..=b'Z').chain(b'2'..=b'7');
        stringify(letters)
    }
    pub(super) fn base32_hex() -> String {
        let letters = (b'0'..=b'9').chain(b'A'..=b'V');
        stringify(letters)
    }
    pub(super) fn base64() -> String {
        let letters = (b'A'..=b'Z').chain(b'a'..=b'z').chain(b'0'..=b'9');
        let mut s = stringify(letters);
        s.push('+');
        s.push('/');
        s
    }
}

impl Encoding {
    fn alphabet(self) -> String {
        match self {
            Encoding::Base16 => alphabet::base16(),
            Encoding::Base32 => alphabet::base32(),
            Encoding::Base32Hex => alphabet::base32_hex(),
            Encoding::Base64 => alphabet::base64(),
        }
    }
    fn chunk_size(self) -> usize {
        match self {
            Encoding::Base16 => 4,
            Encoding::Base32 | Encoding::Base32Hex => 5,
            Encoding::Base64 => 6,
        }
    }
    fn min_chunks(self) -> usize {
        match self {
            Encoding::Base16 => 2,
            Encoding::Base32 | Encoding::Base32Hex => 8,
            Encoding::Base64 => 4,
        }
    }
    fn padding(self) -> Option<char> {
        match self {
            Encoding::Base16 => None,
            Encoding::Base32 | Encoding::Base32Hex => Some('='),
            Encoding::Base64 => Some('='),
        }
    }
}

/// An error encountered while decoding.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DecodeError {
    /// The given string does not have a correct length for the specified encoding.
    InvalidLength,
    /// A character not in the "alphabet" of possible output characters for the desired encoding
    /// was encountered.
    UnknownCharacter,
    /// A non-UTF-8 byte sequence was encountered and so the output could not be converted to a
    /// `String`. If this error is encountered, [`decode_bytes`](fn.decode_bytes.html) is likely
    /// the way forward.
    NonUtf8,
}

impl From<std::string::FromUtf8Error> for DecodeError {
    fn from(_: std::string::FromUtf8Error) -> Self {
        DecodeError::NonUtf8
    }
}

/// Attempts to decode an encoded string to a vector of bytes.
///
/// # Notes
/// Unlike [`decode`](fn.decode.html), this function *does not* trim null bytes from the end of the
/// decoded payload.
pub fn decode_bytes<S: AsRef<str>>(encoding: Encoding, s: S) -> Result<Vec<u8>, DecodeError> {
    let s = s.as_ref();
    if s.len() % encoding.min_chunks() != 0 {
        return Err(DecodeError::InvalidLength);
    }
    let s = if let Some(pad) = encoding.padding() {
        s.replace(pad, "")
    } else {
        s.to_string()
    };
    let alphabet = encoding.alphabet();
    let indices = s
        .chars()
        .map(|c| alphabet.chars().position(|e| e == c))
        .collect::<Vec<_>>();
    if indices.iter().any(Option::is_none) {
        return Err(DecodeError::UnknownCharacter);
    }
    // Let's hope the optimizer is cleverer than I am (likely)
    let indices = indices
        .into_iter()
        .filter_map(|e| e.map(|v| v as u8))
        .collect::<Vec<_>>();
    let bits: &[u8] = &indices;
    let bits: &BitSlice<BigEndian, u8> = BitSlice::from_slice(bits);
    let chunk_size = encoding.chunk_size();
    Ok(bits
        .chunks(8)
        .flat_map(|chunk| (&chunk[(8 - chunk_size)..]).into_iter())
        .collect::<BitVec<BigEndian>>()
        .into_vec())
}

/// Attempts to decode a string to a UTF-8 string, stripping any trailing null bytes.
///
/// For non-UTF-8 data, see [`decode_bytes`](fn.decode_bytes.html).
pub fn decode<S: AsRef<str>>(encoding: Encoding, s: S) -> Result<String, DecodeError> {
    let bytes = decode_bytes(encoding, s)?;
    let s = String::from_utf8(bytes)?;
    let nul = char::from(0);
    let trimmed = s.trim_end_matches(nul);
    Ok(trimmed.to_string())
}

fn encode_raw<T: AsRef<BitSlice>>(encoding: Encoding, bits: T) -> String {
    let bits = bits.as_ref();
    let chunks = bits.chunks(encoding.chunk_size());
    let numbered = chunks.map(|chunk| ((0..encoding.chunk_size()).rev()).zip(chunk));
    let f = |acc, (shift, val)| {
        let bit = val as u8;
        let val = (bit << shift) as usize;
        acc + val
    };
    let indices = numbered.map(|chunk| chunk.fold(0, f));
    let alphabet = encoding.alphabet();
    let mut s = indices
        .map(|index| {
            alphabet
                .chars()
                .nth(index)
                .expect("Character index out of bounds.")
        })
        .collect::<String>();
    let chunks = encoding.min_chunks();
    let rem = s.len() % chunks;
    if rem != 0 {
        for _ in 0..(chunks - rem) {
            s.push(encoding.padding().expect("No padding character found."))
        }
    }
    s
}

/// Encode arbitrary data in the specified encoding.
///
/// # Non-UTF-8 data
///
/// Due to the nature of the encodings in the RFC, the data does not have to be valid UTF-8, just a
/// bunch of bytes.
/// However, care must be taken when decoding the data again; if using this crate, be sure to use
/// `decode_bytes`, which does not attempt any UTF-8 conversions, instead of `decode`, which does.
pub fn encode_bytes<T: AsRef<[u8]>>(encoding: Encoding, payload: T) -> String {
    let vec: BitVec<BigEndian, _> = BitVec::from_slice(payload.as_ref());
    encode_raw(encoding, vec)
}

/// Encodes a UTF-8 string using the specified encoding.
pub fn encode<S: AsRef<str>>(encoding: Encoding, s: S) -> String {
    let s = s.as_ref();
    let bytes = s.bytes().collect::<Vec<_>>();
    let bytes: BitVec<BigEndian, _> = bytes.into();
    encode_bytes(encoding, bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn rfc_base16_test_vectors() {
        assert_eq!(encode(Encoding::Base16, ""), "");
        assert_eq!(encode(Encoding::Base16, "f"), "66");
        assert_eq!(encode(Encoding::Base16, "fo"), "666F");
        assert_eq!(encode(Encoding::Base16, "foo"), "666F6F");
        assert_eq!(encode(Encoding::Base16, "foob"), "666F6F62");
        assert_eq!(encode(Encoding::Base16, "fooba"), "666F6F6261");
        assert_eq!(encode(Encoding::Base16, "foobar"), "666F6F626172");
    }
    #[test]
    fn rfc_base32_test_vectors() {
        assert_eq!(encode(Encoding::Base32, ""), "");
        assert_eq!(encode(Encoding::Base32, "f"), "MY======");
        assert_eq!(encode(Encoding::Base32, "fo"), "MZXQ====");
        assert_eq!(encode(Encoding::Base32, "foo"), "MZXW6===");
        assert_eq!(encode(Encoding::Base32, "foob"), "MZXW6YQ=");
        assert_eq!(encode(Encoding::Base32, "fooba"), "MZXW6YTB");
        assert_eq!(encode(Encoding::Base32, "foobar"), "MZXW6YTBOI======");
    }
    #[test]
    fn rfc_base32_hex_test_vectors() {
        assert_eq!(encode(Encoding::Base32Hex, ""), "");
        assert_eq!(encode(Encoding::Base32Hex, "f"), "CO======");
        assert_eq!(encode(Encoding::Base32Hex, "fo"), "CPNG====");
        assert_eq!(encode(Encoding::Base32Hex, "foo"), "CPNMU===");
        assert_eq!(encode(Encoding::Base32Hex, "foob"), "CPNMUOG=");
        assert_eq!(encode(Encoding::Base32Hex, "fooba"), "CPNMUOJ1");
        assert_eq!(encode(Encoding::Base32Hex, "foobar"), "CPNMUOJ1E8======");
    }
    #[test]
    fn rfc_base64_test_vectors() {
        assert_eq!(encode(Encoding::Base64, ""), "");
        assert_eq!(encode(Encoding::Base64, "f"), "Zg==");
        assert_eq!(encode(Encoding::Base64, "fo"), "Zm8=");
        assert_eq!(encode(Encoding::Base64, "foo"), "Zm9v");
        assert_eq!(encode(Encoding::Base64, "foob"), "Zm9vYg==");
        assert_eq!(encode(Encoding::Base64, "fooba"), "Zm9vYmE=");
        assert_eq!(encode(Encoding::Base64, "foobar"), "Zm9vYmFy");
    }
    #[test]
    fn round_trip() {
        assert_eq!(
            decode(Encoding::Base16, encode(Encoding::Base16, "foo")),
            Ok(String::from("foo"))
        );
        assert_eq!(
            decode(Encoding::Base32, encode(Encoding::Base32, "foo")),
            Ok(String::from("foo"))
        );
        assert_eq!(
            decode(Encoding::Base32Hex, encode(Encoding::Base32Hex, "foo")),
            Ok(String::from("foo"))
        );
        assert_eq!(
            decode(Encoding::Base64, encode(Encoding::Base64, "foo")),
            Ok(String::from("foo"))
        );
    }
}
