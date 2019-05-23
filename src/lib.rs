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

fn encode_bytes<T: AsRef<BitSlice>>(encoding: Encoding, bits: T) -> String {
    let bits = bits.as_ref();
    let chunks = bits.chunks(encoding.chunk_size());
    let indices = (0..encoding.chunk_size()).rev();
    let numbered = chunks.map(|chunk| indices.clone().zip(chunk));
    let f = |acc, (shift, val)| {
        let bit = if val { 1 } else { 0 };
        let val = (bit << shift) as usize;
        acc + val
    };
    let indices = numbered.map(|chunk| chunk.fold(0, f));
    let alphabet = encoding.alphabet().chars().collect::<Vec<_>>();
    let mut s = indices.map(|index| alphabet[index]).collect::<String>();
    let chunks = encoding.min_chunks();
    let rem = s.len() % chunks;
    if rem != 0 {
        for _ in 0..(chunks - rem) {
            s.push(encoding.padding().expect("No padding character found."))
        }
    }
    s
}

pub fn encode_str<S: AsRef<str>>(encoding: Encoding, s: S) -> String {
    let s = s.as_ref();
    let bytes = s.bytes().collect::<Vec<_>>();
    let bytes: BitVec<_, _> = bytes.into();
    encode_bytes(encoding, bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn rfc_base16_test_vectors() {
        assert_eq!(encode_str(Encoding::Base16, ""), "");
        assert_eq!(encode_str(Encoding::Base16, "f"), "66");
        assert_eq!(encode_str(Encoding::Base16, "fo"), "666F");
        assert_eq!(encode_str(Encoding::Base16, "foo"), "666F6F");
        assert_eq!(encode_str(Encoding::Base16, "foob"), "666F6F62");
        assert_eq!(encode_str(Encoding::Base16, "fooba"), "666F6F6261");
        assert_eq!(encode_str(Encoding::Base16, "foobar"), "666F6F626172");
    }
    #[test]
    fn rfc_base32_test_vectors() {
        assert_eq!(encode_str(Encoding::Base32, ""), "");
        assert_eq!(encode_str(Encoding::Base32, "f"), "MY======");
        assert_eq!(encode_str(Encoding::Base32, "fo"), "MZXQ====");
        assert_eq!(encode_str(Encoding::Base32, "foo"), "MZXW6===");
        assert_eq!(encode_str(Encoding::Base32, "foob"), "MZXW6YQ=");
        assert_eq!(encode_str(Encoding::Base32, "fooba"), "MZXW6YTB");
        assert_eq!(encode_str(Encoding::Base32, "foobar"), "MZXW6YTBOI======");
    }
    #[test]
    fn rfc_base32_hex_test_vectors() {
        assert_eq!(encode_str(Encoding::Base32Hex, ""), "");
        assert_eq!(encode_str(Encoding::Base32Hex, "f"), "CO======");
        assert_eq!(encode_str(Encoding::Base32Hex, "fo"), "CPNG====");
        assert_eq!(encode_str(Encoding::Base32Hex, "foo"), "CPNMU===");
        assert_eq!(encode_str(Encoding::Base32Hex, "foob"), "CPNMUOG=");
        assert_eq!(encode_str(Encoding::Base32Hex, "fooba"), "CPNMUOJ1");
        assert_eq!(
            encode_str(Encoding::Base32Hex, "foobar"),
            "CPNMUOJ1E8======"
        );
    }
    #[test]
    fn rfc_base64_test_vectors() {
        assert_eq!(encode_str(Encoding::Base64, ""), "");
        assert_eq!(encode_str(Encoding::Base64, "f"), "Zg==");
        assert_eq!(encode_str(Encoding::Base64, "fo"), "Zm8=");
        assert_eq!(encode_str(Encoding::Base64, "foo"), "Zm9v");
        assert_eq!(encode_str(Encoding::Base64, "foob"), "Zm9vYg==");
        assert_eq!(encode_str(Encoding::Base64, "fooba"), "Zm9vYmE=");
        assert_eq!(encode_str(Encoding::Base64, "foobar"), "Zm9vYmFy");
    }
}
