#[macro_use]
extern crate cfg_if;

use std::fmt::{self, Display, Formatter};
use std::str;

#[derive(Debug, PartialEq)]
pub enum MarkupDisplay<T>
where
    T: Display,
{
    Safe(T),
    Unsafe(T),
}

impl<T> MarkupDisplay<T>
where
    T: Display,
{
    pub fn mark_safe(self) -> MarkupDisplay<T> {
        match self {
            MarkupDisplay::Unsafe(t) => MarkupDisplay::Safe(t),
            _ => self,
        }
    }
}

impl<T> From<T> for MarkupDisplay<T>
where
    T: Display,
{
    fn from(t: T) -> MarkupDisplay<T> {
        MarkupDisplay::Unsafe(t)
    }
}

impl<T> Display for MarkupDisplay<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            MarkupDisplay::Unsafe(ref t) => escape(&t.to_string()).fmt(f),
            MarkupDisplay::Safe(ref t) => t.fmt(f),
        }
    }
}

pub fn escape(s: &str) -> Escaped {
    Escaped {
        bytes: s.as_bytes(),
    }
}

pub struct Escaped<'a> {
    bytes: &'a [u8],
}

impl<'a> Display for Escaped<'a> {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        _imp(self.bytes, fmt)
    }
}

cfg_if! {
    if #[cfg(all(target_arch = "x86_64", askama_runtime_avx))] {

        use std::arch::x86_64::*;
        use std::mem::{self, size_of};
        use std::sync::atomic::{AtomicUsize, Ordering};

        const VECTOR_SIZE: usize = size_of::<__m256i>();
        const VECTOR_ALIGN: usize = VECTOR_SIZE - 1;

        const LOOP_SIZE: usize = 2 * VECTOR_SIZE;

        #[inline(always)]
        fn _imp(bytes: &[u8], fmt: &mut Formatter) -> fmt::Result {
            // https://github.com/BurntSushi/rust-memchr/blob/master/src/x86/mod.rs#L9-L29
            static mut FN: fn(bytes: &[u8], fmt: &mut Formatter) -> fmt::Result = detect;

            fn detect(bytes: &[u8], fmt: &mut Formatter) -> fmt::Result {
                let fun = if is_x86_feature_detected!("avx2") {
                    _avx_escape as usize
                } else {
                    _escape as usize
                };

                let slot = unsafe { &*(&FN as *const _ as *const AtomicUsize) };
                slot.store(fun as usize, Ordering::Relaxed);
                unsafe {
                    mem::transmute::<usize, fn(bytes: &[u8], fmt: &mut Formatter) -> fmt::Result>(fun)(bytes, fmt)
                }
            }

            unsafe {
                let slot = &*(&FN as *const _ as * const AtomicUsize);
                let fun = slot.load(Ordering::Relaxed);
                mem::transmute::<usize, fn(bytes: &[u8], fmt: &mut Formatter) -> fmt::Result>(fun)(bytes, fmt)
            }
        }

        // Subtract `b` from `a` and return the difference. `a` should be greater than
        // or equal to `b`.
        #[inline(always)]
        fn sub(a: *const u8, b: *const u8) -> usize {
            debug_assert!(b <= a);
            (a as usize) - (b as usize)
        }
    } else {

        #[inline(always)]
        fn _imp(bytes: &[u8], fmt: &mut Formatter) -> fmt::Result {
            _escape(bytes, fmt)
        }
    }
}

macro_rules! escaping_body {
    ($i:ident, $start:ident, $fmt:ident, $bytes:ident, $quote:expr) => {{
        if $start < $i {
            #[allow(unused_unsafe)]
            $fmt.write_str(unsafe { str::from_utf8_unchecked(&$bytes[$start..$i]) })?;
        }
        $fmt.write_str($quote)?;
        $start = $i + 1;
    }};
}

macro_rules! escaping_bodies {
    ($i:ident, $b: ident, $start:ident, $fmt:ident, $bytes:ident) => {{
        // Unsafe
        match $b {
            b'<' => escaping_body!($i, $start, $fmt, $bytes, "&lt;"),
            b'>' => escaping_body!($i, $start, $fmt, $bytes, "&gt;"),
            b'&' => escaping_body!($i, $start, $fmt, $bytes, "&amp;"),
            b'"' => escaping_body!($i, $start, $fmt, $bytes, "&quot;"),
            b'\'' => escaping_body!($i, $start, $fmt, $bytes, "&#x27;"),
            b'/' => escaping_body!($i, $start, $fmt, $bytes, "&#x2f;"),
            _ => (),
        }
    }};
}

macro_rules! write_char {
    ($i:ident, $ptr: ident, $start: ident, $fmt: ident, $bytes:ident) => {{
        // Unsafe
        let b = *$ptr;
        if b.wrapping_sub(FLAG_BELOW) <= LEN {
            // Unsafe
            escaping_bodies!($i, b, $start, $fmt, $bytes);
        }
    }};
}

macro_rules! write_mask_body {
    ($mask: ident, $cur: ident, $at:ident, $ptr: ident, $start: ident, $fmt: ident, $bytes:ident) => {
        // Unsafe
        let b = *$ptr.add($cur);
        let i = $at + $cur;

        // Unsafe
        escaping_bodies!(i, b, $start, $fmt, $bytes);

        $mask ^= 1 << $cur;
        if $mask == 0 {
            break;
        }

        $cur = $mask.trailing_zeros() as usize;
    };
}
// Unsafe
macro_rules! write_mask {
    ($cmp: ident, $ptr: ident, $start_ptr: ident, $start: ident, $fmt: ident, $bytes:ident) => {{
        let mut mask = _mm256_movemask_epi8($cmp);
        if mask != 0 {
            let at = sub($ptr, $start_ptr);
            let mut cur = mask.trailing_zeros() as usize;

            loop {
                write_mask_body!(mask, cur, at, $ptr, $start, $fmt, $bytes);
            }

            debug_assert_eq!(at, sub($ptr, $start_ptr))
        }
    }};
}

// Unsafe
macro_rules! write_forward {
    ($cmp: ident, $align: ident, $ptr: ident, $start_ptr: ident, $start: ident, $fmt: ident, $bytes:ident) => {{
        let mut mask = _mm256_movemask_epi8($cmp);
        if mask != 0 {
            let at = sub($ptr, $start_ptr);
            let mut cur = mask.trailing_zeros() as usize;

            while cur < $align {
                write_mask_body!(mask, cur, at, $ptr, $start, $fmt, $bytes);
            }

            debug_assert_eq!(at, sub($ptr, $start_ptr))
        }
    }};
}

fn _escape(bytes: &[u8], fmt: &mut Formatter) -> fmt::Result {
    let mut start = 0;

    for (i, b) in bytes.iter().enumerate() {
        write_char!(i, b, start, fmt, bytes);
    }

    fmt.write_str(unsafe { str::from_utf8_unchecked(&bytes[start..]) })?;

    Ok(())
}

#[cfg(all(target_arch = "x86_64", askama_runtime_avx))]
unsafe fn _avx_escape(bytes: &[u8], fmt: &mut Formatter) -> fmt::Result {
    let len = bytes.len();
    let mut start = 0;

    if len < VECTOR_SIZE {
        for (i, b) in bytes.iter().enumerate() {
            write_char!(i, b, start, fmt, bytes);
        }

        if start < len {
            fmt.write_str(str::from_utf8_unchecked(&bytes[start..len]))?;
        }

        return Ok(());
    }

    let v_flag = _mm256_set1_epi8((LEN + 1) as i8);
    let v_flag_below = _mm256_set1_epi8(FLAG_BELOW as i8);

    let start_ptr = bytes.as_ptr();
    let end_ptr = bytes[len..].as_ptr();
    let mut ptr = start_ptr;

    {
        let align = (start_ptr as usize & VECTOR_ALIGN) % VECTOR_SIZE;
        if 0 < align {
            let a = _mm256_loadu_si256(ptr as *const __m256i);
            let cmp = _mm256_cmpgt_epi8(v_flag, _mm256_sub_epi8(a, v_flag_below));

            write_forward!(cmp, align, ptr, start_ptr, start, fmt, bytes);
            ptr = ptr.add(align);

            debug_assert!(start <= sub(ptr, start_ptr));
        }
    }

    debug_assert!(start_ptr <= ptr && start_ptr <= end_ptr.sub(VECTOR_SIZE));

    if LOOP_SIZE <= len {
        while ptr <= end_ptr.sub(LOOP_SIZE) {
            debug_assert_eq!(0, (ptr as usize) % VECTOR_SIZE);

            let a = _mm256_load_si256(ptr as *const __m256i);
            let b = _mm256_load_si256(ptr.add(VECTOR_SIZE) as *const __m256i);
            let cmp_a = _mm256_cmpgt_epi8(v_flag, _mm256_sub_epi8(a, v_flag_below));
            let cmp_b = _mm256_cmpgt_epi8(v_flag, _mm256_sub_epi8(b, v_flag_below));

            if _mm256_movemask_epi8(_mm256_or_si256(cmp_a, cmp_b)) != 0 {
                write_mask!(cmp_a, ptr, start_ptr, start, fmt, bytes);
                let ptr = ptr.add(VECTOR_SIZE);

                debug_assert!(start <= sub(ptr, start_ptr));

                write_mask!(cmp_b, ptr, start_ptr, start, fmt, bytes);
            }

            ptr = ptr.add(LOOP_SIZE);

            debug_assert!(start <= sub(ptr, start_ptr));
        }
    }

    if ptr <= end_ptr.sub(VECTOR_SIZE) {
        debug_assert_eq!(0, (ptr as usize) % VECTOR_SIZE);

        let a = _mm256_load_si256(ptr as *const __m256i);
        let cmp = _mm256_cmpgt_epi8(v_flag, _mm256_sub_epi8(a, v_flag_below));

        write_mask!(cmp, ptr, start_ptr, start, fmt, bytes);
        ptr = ptr.add(VECTOR_SIZE);

        debug_assert!(start <= sub(ptr, start_ptr));
    }

    debug_assert!(end_ptr.sub(VECTOR_SIZE) < ptr);

    if ptr < end_ptr {
        debug_assert_eq!(0, (ptr as usize) % VECTOR_SIZE);

        let a = _mm256_load_si256(ptr as *const __m256i);
        let cmp = _mm256_cmpgt_epi8(v_flag, _mm256_sub_epi8(a, v_flag_below));
        let end = sub(end_ptr, ptr);

        write_forward!(cmp, end, ptr, start_ptr, start, fmt, bytes);
    }

    debug_assert!(start <= len);

    if start < len {
        fmt.write_str(str::from_utf8_unchecked(&bytes[start..len]))?;
    }

    Ok(())
}

// Defining character interval from ASCII table to create bit masks from slice to be escaped
const LEN: u8 = b'>' - b'"';
const FLAG_BELOW: u8 = b'"';

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_escape() {
        assert_eq!(escape("").to_string(), "");
        assert_eq!(escape("<&>").to_string(), "&lt;&amp;&gt;");
        assert_eq!(escape("bar&").to_string(), "bar&amp;");
        assert_eq!(escape("<foo").to_string(), "&lt;foo");
        assert_eq!(escape("bar&h").to_string(), "bar&amp;h");
    }

    #[cfg(all(target_arch = "x86_64", askama_runtime_avx))]
    #[test]
    fn test_avx_escape() {
        let escapes = "<>&\"'/";
        let escaped = "&lt;&gt;&amp;&quot;&#x27;&#x2f;";
        let string_long: &str = &["foobar"; 1024].join("");

        assert_eq!(escape("").to_string(), "");
        assert_eq!(escape("<&>").to_string(), "&lt;&amp;&gt;");
        assert_eq!(escape("bar&").to_string(), "bar&amp;");
        assert_eq!(escape("<foo").to_string(), "&lt;foo");
        assert_eq!(escape("bar&h").to_string(), "bar&amp;h");
        assert_eq!(escape(string_long).to_string(), string_long);
        assert_eq!(
            escape(&[string_long, "<"].join("")).to_string(),
            [string_long, "&lt;"].join("")
        );
        assert_eq!(
            escape(&["<", string_long].join("")).to_string(),
            ["&lt;", string_long].join("")
        );
        assert_eq!(
            escape(&["<"; 1024].join("")).to_string(),
            ["&lt;"; 1024].join("")
        );
        assert_eq!(
            escape(&[escapes; 1024].join("")).to_string(),
            [escaped; 1024].join("")
        );
        assert_eq!(
            escape(&[string_long, "<", string_long].join("")).to_string(),
            [string_long, "&lt;", string_long].join("")
        );
        assert_eq!(
            escape(&[string_long, "<", string_long, escapes, string_long,].join("")).to_string(),
            [string_long, "&lt;", string_long, escaped, string_long,].join("")
        );
    }
}
