use std::{collections::HashMap, hash::Hash, ops::Index};

pub struct ScopedMap<K, V> {
    scope: usize,
    map: Vec<(K, V, usize)>,
    allow_shadowing: bool,
}

impl<K, V> ScopedMap<K, V> {
    pub fn new(allow_shadowing: bool) -> Self {
        ScopedMap { scope: 0, map: vec![], allow_shadowing }
    }

    fn is_defined_in_current_scope<Q: PartialEq<K>>(&self, key: &Q) -> bool {
        self.map.iter().rev()
            .take_while(|x| x.2 == self.scope)
            .any(|x| key == &x.0)
    }

    pub fn get<Q: PartialEq<K> + ?Sized>(&self, key: &Q) -> Option<&V> {
        self.map.iter().rev()
            .find(|x| key == &x.0)
            .map(|x| &x.1)
    }

    pub fn enter_new_scope(&mut self) {
        self.scope += 1;
    }

    pub fn exit_scope(&mut self) {
        self.scope -= 1;
    }

    pub fn exit_scope_and_get_elements(&mut self) -> Vec<(K, V)> {
        let mut old_elements = vec![];
        for i in (0..self.map.len()).rev() {
            if self.map[i].2 == self.scope {
                let (k, v, _) = self.map.remove(i);
                old_elements.push((k, v));
            }
        }
        self.scope -= 1;
        old_elements
    }

    pub fn reset(&mut self) {
        self.map.clear();
        self.scope = 0;
    }
}

impl<K: Eq, V> ScopedMap<K, V> {
    pub fn insert_new(&mut self, key: K, value: V) {
        if self.allow_shadowing && self.is_defined_in_current_scope(&key) {
            panic!("symbol already defined in current scope");
        } else if !self.allow_shadowing && self.get(&key).is_some() {
            panic!("symbol already defined");
        }
        self.map.push((key, value, self.scope));
    }

    pub fn insert(&mut self, key: K, value: V) {
        self.map.push((key, value, self.scope));
    }
}

impl<K, V, Q: PartialEq<K>> Index<Q> for ScopedMap<K, V> {
    type Output = V;

    fn index(&self, index: Q) -> &Self::Output {
        self.get(&index).unwrap()
    }
}

pub enum Either<L, R> { Left(L), Right(R) }

impl<L, R> Either<L, R> {
    pub fn collect_separate(i: impl Iterator<Item = Self>) -> (Vec<L>, Vec<R>) {
        let mut l = vec![];
        let mut r = vec![];
        for x in i {
            match x {
                Either::Left(x) => l.push(x),
                Either::Right(x) => r.push(x),
            }
        }
        (l, r)
    }
}

pub(crate) trait HashMapExt<K, V> {
    /// Equivalent to [`std::collections::HashSet::intersection`] but for HashMap
    fn intersection<'a>(&'a self, other: &Self) -> impl Iterator<Item = (&'a K, &'a V)>
        where K: 'a, V: 'a;
    /// Equivalent to [`std::collections::HashSet::difference`] but for HashMap
    fn difference<'a>(&'a self, other: &Self) -> impl Iterator<Item = (&'a K, &'a V)>
        where K: 'a, V: 'a;
}

impl<K: Eq + Hash, V> HashMapExt<K, V> for HashMap<K, V> {
    fn intersection<'a>(&'a self, other: &Self) -> impl Iterator<Item = (&'a K, &'a V)>
    where K: 'a, V: 'a {
        self.iter()
            .filter_map(|(k, v)| {
                if other.contains_key(k) {
                    Some((k, v))
                } else { None }
            })
    }

    fn difference<'a>(&'a self, other: &Self) -> impl Iterator<Item = (&'a K, &'a V)>
    where K: 'a, V: 'a {
        self.iter()
            .filter_map(|(k, v)| {
                if !other.contains_key(k) {
                    Some((k, v))
                } else { None }
            })
    }
}