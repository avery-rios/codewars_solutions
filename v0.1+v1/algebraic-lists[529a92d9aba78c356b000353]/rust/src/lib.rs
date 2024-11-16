#[derive(Debug, PartialEq, Eq)]
pub enum Cons<T: Clone> {
    Cons(T, Box<Cons<T>>),
    Null,
}

impl<T: Clone> Cons<T> {
    pub fn new(head: T, tail: Self) -> Self {
        Cons::Cons(head, Box::new(tail))
    }

    pub fn to_vec(&self) -> Vec<T> {
        match &self {
            Cons::Null => vec![],
            Cons::Cons(ref head, ref tail) => {
                let mut head = vec![head.clone()];
                head.extend(tail.to_vec());
                head
            }
        }
    }
}

impl<T: Clone> Cons<T> {
    pub fn from_iter<I>(it: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let vs = it.into_iter().collect::<Vec<_>>();
        let mut ret = Self::Null;
        for v in vs.into_iter().rev() {
            ret = Self::Cons(v, Box::new(ret))
        }
        ret
    }

    pub fn filter<F>(&self, fun: F) -> Self
    where
        F: Fn(&T) -> bool,
    {
        match &self {
            Self::Cons(h, t) if fun(h) => Self::Cons(h.clone(), Box::new(t.filter(fun))),
            Self::Cons(_, t) => t.filter(fun),
            Self::Null => Self::Null,
        }
    }

    pub fn map<F, S>(&self, fun: F) -> Cons<S>
    where
        F: Fn(T) -> S,
        S: Clone,
    {
        match &self {
            Self::Cons(h, t) => Cons::Cons(fun(h.clone()), Box::new(t.map(fun))),
            Self::Null => Cons::Null,
        }
    }
}

