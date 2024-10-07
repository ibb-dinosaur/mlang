use std::ops::Index;

pub struct ScopedMap<K, V> {
    scope: usize,
    map: Vec<(K, V, usize)>,
}

impl<K, V> ScopedMap<K, V> {
    pub fn new() -> Self {
        ScopedMap { scope: 0, map: vec![] }
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
        if self.is_defined_in_current_scope(&key) {
            panic!("symbol already defined in current scope");
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