/// so, when are two type, `a` and `b`, considered equal?
/// a definition might be, it is possible to go from `a` to `b`,
/// and from `b` to `a`.
/// Going a roundway trip should leave you the same value.
/// Unfortunately it is virtually impossible to test this in Haskell,
/// neither in Rust.
/// This is called Isomorphism.
pub enum Void {}

impl PartialEq for Void {
    fn eq(&self, _: &Void) -> bool {
        true
    }
}

pub fn absurd(_: Void) -> ! {
    panic!("You must be kidding! Where did you find that void instance?");
}

pub type ISO<A, B> = (Box<dyn Fn(A) -> B>, Box<dyn Fn(B) -> A>);

pub fn iso<A: 'static, B: 'static, F1, F2>(a: F1, b: F2) -> ISO<A, B>
where
    F1: 'static + Fn(A) -> B,
    F2: 'static + Fn(B) -> A,
{
    (Box::new(a), Box::new(b))
}

/// given ISO a b, we can go from a to b
pub fn sub_st_l<A, B>(iso: ISO<A, B>) -> Box<dyn Fn(A) -> B> {
    iso.0
}

/// and vise versa
pub fn sub_st_r<A, B>(iso: ISO<A, B>) -> Box<dyn Fn(B) -> A> {
    iso.1
}

/// There can be more than one ISO a b
pub fn iso_bool() -> ISO<bool, bool> {
    iso(|v| v, |v| v)
}

pub fn iso_bool_not() -> ISO<bool, bool> {
    iso(|v: bool| !v, |v: bool| !v)
}

/// isomorphism is reflexive
pub fn refl<A: 'static>() -> ISO<A, A> {
    iso(|v| v, |v| v)
}

/// isomorphism is symmetric
pub fn symm<A: 'static, B: 'static>(i: ISO<A, B>) -> ISO<B, A> {
    (i.1, i.0)
}

/// isomorphism is transitive
pub fn trans<A: 'static, B: 'static, C: 'static>(ab: ISO<A, B>, bc: ISO<B, C>) -> ISO<A, C> {
    iso(move |a| bc.0(ab.0(a)), move |c| ab.1(bc.1(c)))
}

/// we can combine isomorphism
pub fn iso_tuple<A: 'static, B: 'static, C: 'static, D: 'static>(
    ab: ISO<A, B>,
    cd: ISO<C, D>,
) -> ISO<(A, C), (B, D)> {
    iso(
        move |(a, c)| (ab.0(a), cd.0(c)),
        move |(b, d)| (ab.1(b), cd.1(d)),
    )
}

pub fn iso_vec<A: 'static, B: 'static>(i: ISO<A, B>) -> ISO<Vec<A>, Vec<B>> {
    iso(
        move |va: Vec<A>| va.into_iter().map(|a| i.0(a)).collect(),
        move |vb: Vec<B>| vb.into_iter().map(|b| i.1(b)).collect(),
    )
}

pub fn iso_option<A: 'static, B: 'static>(i: ISO<A, B>) -> ISO<Option<A>, Option<B>> {
    iso(
        move |oa: Option<A>| oa.map(|a| i.0(a)),
        move |ob| ob.map(|b| i.1(b)),
    )
}

pub fn iso_result<A: 'static, B: 'static, C: 'static, D: 'static>(
    ab: ISO<A, B>,
    cd: ISO<C, D>,
) -> ISO<Result<A, C>, Result<B, D>> {
    iso(
        move |oa| match oa {
            Ok(a) => Ok(ab.0(a)),
            Err(c) => Err(cd.0(c)),
        },
        move |ob| match ob {
            Ok(b) => Ok(ab.1(b)),
            Err(d) => Err(cd.1(d)),
        },
    )
}

/// Going another way is hard (and is generally impossible)
/// Remember, for all valid ISO, converting and converting back
/// is the same as the original value.
/// You need this to prove some case are impossible.
pub fn iso_un_option<A: 'static, B: 'static>(i: ISO<Option<A>, Option<B>>) -> ISO<A, B> {
    iso(
        move |a| match i.0(Some(a)) {
            Some(b) => b,
            None => i.0(None).unwrap(),
        },
        move |b| match i.1(Some(b)) {
            Some(a) => a,
            None => i.1(None).unwrap(),
        },
    )
}

/// inf + 0 = inf + 1
pub fn iso_eu() -> ISO<Result<Vec<()>, ()>, Result<Vec<()>, Void>> {
    iso(
        |r: Result<Vec<()>, ()>| match r {
            Ok(mut v) => {
                v.push(());
                Ok(v)
            }
            Err(()) => Ok(Vec::new()),
        },
        |r| match r {
            Ok(mut v) => match v.pop() {
                Some(_) => Ok(v),
                None => Err(()),
            },
            Err(v) => match v {},
        },
    )
}

pub type IsoFL<A, B, C, D> = Box<dyn FnOnce(Box<dyn Fn(A) -> C>) -> Box<dyn FnOnce(B) -> D>>;
pub type IsoFR<A, B, C, D> = Box<dyn FnOnce(Box<dyn Fn(B) -> D>) -> Box<dyn FnOnce(A) -> C>>;
pub type IsoF<A, B, C, D> = (IsoFL<A, B, C, D>, IsoFR<A, B, C, D>);

/// translator note:
/// You should return the function with correct type,
/// which will be checked by the tests.
/// The type annotation is shown above. You need you return something like
/// (Box::new(...), Box::new(...))
pub fn iso_func<A: 'static, B: 'static, C: 'static, D: 'static>(
    ab: ISO<A, B>,
    cd: ISO<C, D>,
) -> IsoF<A, B, C, D> {
    (
        Box::new(|fac| Box::new(move |b| cd.0(fac(ab.1(b))))),
        Box::new(|fcd| Box::new(move |a| cd.1(fcd(ab.0(a))))),
    )
}

/// And we have isomorphism on isomorphism!
pub fn iso_symm<A: 'static, B: 'static>() -> ISO<ISO<A, B>, ISO<B, A>> {
    iso(symm, symm)
}
