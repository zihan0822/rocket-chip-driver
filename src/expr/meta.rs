// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Expression Metadata
//! Provides the `[ExprMetaData]` trait and a dense as well as sparse implementation for it.

use super::ExprRef;
use baa::Word;
use rustc_hash::FxHashMap;
use std::fmt::Debug;
use std::ops::Index;

pub trait ExprMetaData<T>: Debug + Clone + Index<ExprRef, Output = T>
where
    T: Default + Clone,
{
    fn iter<'a>(&'a self) -> impl Iterator<Item = (ExprRef, &'a T)>
    where
        T: 'a;

    fn insert(&mut self, e: ExprRef, data: T);
}

pub fn extract_fixed_point(data: &impl ExprMetaData<Option<ExprRef>>, mut key: ExprRef) -> ExprRef {
    // TODO: actually update data in order to speed up future lookups, similar to union find
    loop {
        let value = data[key].unwrap();
        if value == key {
            return value;
        }
        key = value;
    }
}

/// A sparse hash map to stare meta-data related to each expression
#[derive(Debug, Default, Clone)]
pub struct SparseExprMetaData<T: Default + Clone + Debug> {
    inner: FxHashMap<ExprRef, T>,
    // we need actual storage so that we can return a reference
    default: T,
}

impl<T: Default + Clone + Debug> Index<ExprRef> for SparseExprMetaData<T> {
    type Output = T;

    fn index(&self, e: ExprRef) -> &Self::Output {
        self.inner.get(&e).unwrap_or(&self.default)
    }
}

impl<T: Default + Clone + Debug> ExprMetaData<T> for SparseExprMetaData<T> {
    fn iter<'a>(&'a self) -> impl Iterator<Item = (ExprRef, &'a T)>
    where
        T: 'a,
    {
        self.inner.iter().map(|(k, v)| (*k, v))
    }

    fn insert(&mut self, e: ExprRef, data: T) {
        self.inner.insert(e, data);
    }
}

/// A dense hash map to store meta-data related to each expression
#[derive(Debug, Default, Clone)]
pub struct DenseExprMetaData<T: Default + Clone + Debug> {
    inner: Vec<T>,
    // we need actual storage so that we can return a reference
    default: T,
}

impl<T: Default + Clone + Debug> DenseExprMetaData<T> {
    pub fn into_vec(self) -> Vec<T> {
        self.inner
    }
}

impl<T: Default + Clone + Debug> Index<ExprRef> for DenseExprMetaData<T> {
    type Output = T;

    fn index(&self, e: ExprRef) -> &Self::Output {
        self.inner.get(e.index()).unwrap_or(&self.default)
    }
}

impl<T: Default + Clone + Debug> ExprMetaData<T> for DenseExprMetaData<T> {
    fn iter<'a>(&'a self) -> impl Iterator<Item = (ExprRef, &'a T)>
    where
        T: 'a,
    {
        ExprMetaDataIter {
            inner: self.inner.iter(),
            index: 0,
        }
    }

    fn insert(&mut self, e: ExprRef, data: T) {
        if self.inner.len() <= e.index() {
            self.inner.resize(e.index(), T::default());
            self.inner.push(data);
        } else {
            self.inner[e.index()] = data;
        }
    }
}

struct ExprMetaDataIter<'a, T> {
    inner: std::slice::Iter<'a, T>,
    index: usize,
}

impl<'a, T> Iterator for ExprMetaDataIter<'a, T> {
    type Item = (ExprRef, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            None => None,
            Some(value) => {
                let index_ref = ExprRef::from_index(self.index);
                self.index += 1;
                Some((index_ref, value))
            }
        }
    }
}

/// A dense hash map to store boolean meta-data related to each expression
#[derive(Debug, Default, Clone)]
pub struct DenseExprMetaDataBool {
    inner: Vec<u64>,
}

fn index_to_word_and_bit(index: ExprRef) -> (usize, u32) {
    let index = index.index();
    let word = index / Word::BITS as usize;
    let bit = index % Word::BITS as usize;
    (word, bit as u32)
}

impl Index<ExprRef> for DenseExprMetaDataBool {
    type Output = bool;

    fn index(&self, index: ExprRef) -> &Self::Output {
        let (word_idx, bit) = index_to_word_and_bit(index);
        let word = self.inner.get(word_idx).cloned().unwrap_or_default();
        if ((word >> bit) & 1) == 1 {
            &TRU
        } else {
            &FALS
        }
    }
}

impl ExprMetaData<bool> for DenseExprMetaDataBool {
    fn iter<'a>(&'a self) -> impl Iterator<Item = (ExprRef, &'a bool)>
    where
        bool: 'a,
    {
        ExprMetaBoolIter {
            inner: self.inner.iter(),
            value: 0,
            index: 0,
        }
    }

    fn insert(&mut self, e: ExprRef, data: bool) {
        let (word_idx, bit) = index_to_word_and_bit(e);
        if self.inner.len() <= word_idx {
            self.inner.resize(e.index(), 0);
        }
        if data {
            // set bit
            self.inner[word_idx] |= 1u64 << bit;
        } else {
            // clear bit
            self.inner[word_idx] &= !(1u64 << bit);
        }
    }
}

struct ExprMetaBoolIter<'a> {
    inner: std::slice::Iter<'a, u64>,
    value: u64,
    index: usize,
}

impl<'a> Iterator for ExprMetaBoolIter<'a> {
    type Item = (ExprRef, &'a bool);

    fn next(&mut self) -> Option<Self::Item> {
        if self.index % u64::BITS as usize == 0 {
            match self.inner.next() {
                None => return None,
                Some(value) => {
                    self.value = *value;
                }
            }
        }
        let index_ref = ExprRef::from_index(self.index);
        self.index += 1;
        let bit = self.index / u64::BITS as usize;
        if ((self.value >> bit) & 1) == 1 {
            Some((index_ref, &TRU))
        } else {
            Some((index_ref, &FALS))
        }
    }
}

const TRU: bool = true;
const FALS: bool = false;
