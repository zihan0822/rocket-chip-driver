// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Expression Metadata
//! Provides the `[ExprMetaData]` trait and a dense as well as sparse implementation for it.

use super::ExprRef;
use std::fmt::Debug;
use std::ops::{Index, IndexMut};

pub trait ExprMetaData<T>: Debug + Clone + Index<ExprRef>
where
    T: Default + Clone,
{
    fn iter<'a>(&'a self) -> impl Iterator<Item = (ExprRef, &'a T)>
    where
        T: 'a;

    fn insert(&mut self, e: ExprRef, data: T);
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
pub struct DenseExprMetaBool {
    inner: Vec<u64>,
}

const TRU: bool = true;
const FALS: bool = false;
