#![no_std]

type WidthInt = u32;
type Word = u64;

/// # Safety
/// Caller should guarantee that `dst` and `source` point to slice of valid length 
#[unsafe(no_mangle)]
pub unsafe extern "C" fn slice(
    dst: *mut Word,
    dst_len: usize,
    source: *const Word,
    source_len: usize,
    hi: usize,
    lo: usize,
) {
    let hi = hi as u32;
    let lo = lo as u32;
    let (dst, source) = unsafe {
        (
            core::slice::from_raw_parts_mut(dst, dst_len),
            core::slice::from_raw_parts(source, source_len),
        )
    };

    let lo_offset = lo % Word::BITS;
    let hi_word = (hi / Word::BITS) as usize;
    let lo_word = (lo / Word::BITS) as usize;
    let src = &source[lo_word..(hi_word + 1)];

    let shift_right = lo_offset;
    if shift_right == 0 {
        assign(dst, src);
    } else {
        // assign with a shift
        let shift_left = Word::BITS - shift_right;
        let m = mask(shift_right);
        let mut prev = src[0] >> shift_right;
        // We append a zero to the src iter in case src.len() == dst.len().
        // If src.len() == dst.len() + 1, then the 0 will just be ignored by `zip`.
        for (d, s) in dst.iter_mut().zip(src.iter().skip(1).chain([0].iter())) {
            *d = prev | ((*s) & m) << shift_left;
            prev = (*s) >> shift_right;
        }
    }
    // mask the result msb
    mask_msb(dst, hi - lo + 1);
}

/// # Safety
/// Caller should guarantee that `dst`, `msb` and `lsb` point to slice of valid length 
#[unsafe(no_mangle)]
pub unsafe extern "C" fn concat(
    dst: *mut Word,
    dst_len: usize,
    msb: *const Word,
    msb_len: usize,
    lsb: *const Word,
    lsb_len: usize,
    lsb_width: usize,
) {
    let (dst, msb, lsb) = unsafe {
        (
            core::slice::from_raw_parts_mut(dst, dst_len),
            core::slice::from_raw_parts(msb, msb_len),
            core::slice::from_raw_parts(lsb, lsb_len),
        )
    };
    // copy lsb to dst
    assign(dst, lsb);

    let lsb_offset = (lsb_width as u32) % Word::BITS;
    if lsb_offset == 0 {
        // copy msb to dst
        for (d, m) in dst.iter_mut().skip(lsb.len()).zip(msb.iter()) {
            *d = *m;
        }
    } else {
        // copy a shifted version of the msb to dst
        let shift_right = Word::BITS - lsb_offset;
        let m = mask(shift_right);
        let mut prev = dst[lsb.len() - 1]; // the msb of the lsb
        for (d, s) in dst
            .iter_mut()
            .skip(lsb.len() - 1)
            .zip(msb.iter().copied().chain(core::iter::once(0)))
        {
            *d = prev | (s & m) << lsb_offset;
            prev = s >> shift_right;
        }
    }
}

fn mask(bits: WidthInt) -> Word {
    if bits == Word::BITS || bits == 0 {
        Word::MAX
    } else {
        ((1 as Word) << bits) - 1
    }
}

fn assign(dst: &mut [Word], source: &[Word]) {
    for (d, s) in dst.iter_mut().zip(source.iter()) {
        *d = *s;
    }
}

fn mask_msb(dst: &mut [Word], width: WidthInt) {
    let m = mask(width % Word::BITS);
    *dst.last_mut().unwrap() &= m;
}
