use std::{fmt::Debug, ops::BitXorAssign};

const MAX_LIGHTS: usize = 512;

type BitVecElem = u64;
const BIT_VEC_SIZE: usize =
    (MAX_LIGHTS + BitVecElem::BITS as usize - 1) / BitVecElem::BITS as usize;
const BIT_VEC_MASK_BITS: usize = BitVecElem::BITS.trailing_zeros() as usize; // ilog2 is not supported on 1.66
const BIT_VEC_MASK: usize = (1usize << BIT_VEC_MASK_BITS) - 1;

#[derive(Clone, PartialEq, Eq)]
struct BitVec([BitVecElem; BIT_VEC_SIZE]);
impl Debug for BitVec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in self.0 {
            write!(f, "{i:00$b}", BitVecElem::BITS as usize)?;
        }
        Ok(())
    }
}
impl BitVec {
    const ZERO: Self = Self([0; BIT_VEC_SIZE]);

    fn from_ones(pos: &[usize]) -> Self {
        let mut ret = Self::ZERO;
        for p in pos {
            ret.set(*p);
        }
        ret
    }
    #[inline]
    fn set(&mut self, pos: usize) {
        self.0[pos >> BIT_VEC_MASK_BITS] |= 1 << (pos & BIT_VEC_MASK);
    }
    #[inline]
    fn test(&self, pos: usize) -> bool {
        self.0[pos >> BIT_VEC_MASK_BITS] & (1 << (pos & BIT_VEC_MASK)) != 0
    }
}
impl BitXorAssign<&Self> for BitVec {
    #[inline]
    fn bitxor_assign(&mut self, rhs: &Self) {
        for i in 0..BIT_VEC_SIZE {
            self.0[i] ^= rhs.0[i]
        }
    }
}

#[derive(Debug, Clone)]
struct BasisVec {
    light: BitVec,
    switch: BitVec,
}
impl BasisVec {
    const ZERO: Self = Self {
        light: BitVec::ZERO,
        switch: BitVec::ZERO,
    };
}
impl BitXorAssign<&BasisVec> for BasisVec {
    #[inline]
    fn bitxor_assign(&mut self, rhs: &BasisVec) {
        self.light ^= &rhs.light;
        self.switch ^= &rhs.switch;
    }
}

pub struct LightController {
    n: usize,
    m: usize,
    basis: Box<[BasisVec]>,
}
impl LightController {
    fn add_switch(&mut self, id: usize, lights_list: &[usize]) {
        let mut v = BasisVec {
            light: BitVec::from_ones(lights_list),
            switch: {
                let mut ret = BitVec::ZERO;
                ret.set(id);
                ret
            },
        };
        for i in (0..self.n).rev() {
            if !v.light.test(i) {
                continue;
            }
            if self.basis[i].light != BitVec::ZERO {
                v ^= &self.basis[i];
            } else {
                for (idx, j) in self.basis[0..i].iter().enumerate() {
                    if v.light.test(idx) {
                        v ^= &j;
                    }
                }
                for j in &mut self.basis[i + 1..] {
                    if j.light.test(i) {
                        *j ^= &v;
                    }
                }
                self.basis[i] = v;
                break;
            }
        }
    }
    pub fn new(n: usize, corresponding_lights_list: &[Vec<usize>]) -> Self {
        let mut ret = Self {
            n,
            m: corresponding_lights_list.len(),
            basis: vec![BasisVec::ZERO; n].into_boxed_slice(),
        };
        for (id, sw) in corresponding_lights_list.iter().enumerate() {
            ret.add_switch(id, sw);
        }
        ret
    }
    pub fn solve(&self, lights: &Vec<usize>) -> Option<Vec<usize>> {
        let mut state = BasisVec::ZERO;
        for l in lights {
            state ^= &self.basis[*l];
        }
        if state.light == BitVec::from_ones(lights) {
            Some((0..self.m).filter(|p| state.switch.test(*p)).collect())
        } else {
            None
        }
    }
}
