/// so, when are two type, `a` and `b`, considered equal?
/// a definition might be, it is possible to go from `a` to `b`,
/// and from `b` to `a`.
/// Going a roundway trip should leave you the same value.
/// Unfortunately it is virtually impossible to test this in Haskell,
/// neither in Rust.
/// This is called ISO.
pub enum Void {}

impl PartialEq for Void {
    fn eq(&self, _: &Void) -> bool {
        true
    }
}

pub fn absurd(_: Void) -> ! {
    panic!("You must be kidding! Where did you find that void instance?");
}

pub type Func<A, B> = Box<dyn Fn(A) -> B>;
pub type RetFunc<A, B> = Box<dyn FnOnce(A) -> B>;
pub type ISO<A, B> = (Func<A, B>, Func<B, A>);

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

/// Sometimes, we can treat a Type as a Number:
/// if a Type t has n distinct value, it's Number is n.
/// This is formally called cardinality.
/// See https://en.wikipedia.org/wiki/Cardinality
///
/// Void has cardinality of 0 (we will abbreviate it Void is 0).
/// () is 1.
/// Bool is 2.
/// Maybe a is 1 + a.
/// We will be using peano arithmetic so we will write it as S a.
/// https://en.wikipedia.org/wiki/Peano_axioms
/// Either a b is a + b.
/// (a, b) is a * b.
/// a => b is b ^ a. Try counting (() => Bool) and (Bool => ())
///
/// Algebraic data type got the name because
/// it satisfies a lot of algebraic rules under isomorphism    

/// a = b => c = d => a * c = b * d
pub fn iso_prod<A: 'static, B: 'static, C: 'static, D: 'static>(
    ab: ISO<A, B>,
    cd: ISO<C, D>,
) -> ISO<(A, C), (B, D)> {
    iso_tuple(ab, cd)
}

/// a = b => c = d => a + c = b + d
pub fn iso_plus<A: 'static, B: 'static, C: 'static, D: 'static>(
    ab: ISO<A, B>,
    cd: ISO<C, D>,
) -> ISO<Result<A, C>, Result<B, D>> {
    iso_result(ab, cd)
}

/// a = b => S a = S b
pub fn iso_s<A: 'static, B: 'static>(i: ISO<A, B>) -> ISO<Option<A>, Option<B>> {
    iso_option(i)
}

/// a = b => c = d => c ^ a = d ^ b
pub fn iso_pow<A: 'static, B: 'static, C: 'static, D: 'static>(
    ab: ISO<A, B>,
    cd: ISO<C, D>,
) -> IsoF<A, B, C, D> {
    iso_func(ab, cd)
}

/// a + b = b + a
pub fn plus_comm<A: 'static, B: 'static>() -> ISO<Result<A, B>, Result<B, A>> {
    fn swap_result<A, B>(r: Result<A, B>) -> Result<B, A> {
        match r {
            Ok(a) => Err(a),
            Err(b) => Ok(b),
        }
    }

    iso(swap_result, swap_result)
}

/// a + b + c = a + (b + c)
pub fn plus_assoc<A: 'static, B: 'static, C: 'static>(
) -> ISO<Result<Result<A, B>, C>, Result<A, Result<B, C>>> {
    iso(
        |r| match r {
            Ok(Ok(a)) => Ok(a),
            Ok(Err(b)) => Err(Ok(b)),
            Err(c) => Err(Err(c)),
        },
        |r| match r {
            Ok(a) => Ok(Ok(a)),
            Err(Ok(b)) => Ok(Err(b)),
            Err(Err(c)) => Err(c),
        },
    )
}

/// a * b = b * a
pub fn mult_comm<A: 'static, B: 'static>() -> ISO<(A, B), (B, A)> {
    fn swap_t<A, B>(t: (A, B)) -> (B, A) {
        (t.1, t.0)
    }
    iso(swap_t, swap_t)
}

/// a * b * c = a * (b * c)
pub fn mult_assoc<A: 'static, B: 'static, C: 'static>() -> ISO<((A, B), C), (A, (B, C))> {
    iso(|((a, b), c)| (a, (b, c)), |(a, (b, c))| ((a, b), c))
}

/// a * (b + c) = a * b + a * c
pub fn dist<A: 'static, B: 'static, C: 'static>() -> ISO<(A, Result<B, C>), Result<(A, B), (A, C)>>
{
    iso(
        |(a, r)| match r {
            Ok(b) => Ok((a, b)),
            Err(c) => Err((a, c)),
        },
        |r| match r {
            Ok((a, b)) => (a, Ok(b)),
            Err((a, c)) => (a, Err(c)),
        },
    )
}

pub type IsoCL<A, B, C> = RetFunc<Func<A, Func<B, C>>, RetFunc<(A, B), C>>;
pub type IsoCR<A, B, C> = RetFunc<Func<(A, B), C>, RetFunc<A, RetFunc<B, C>>>;
pub type IsoC<A, B, C> = (IsoCL<A, B, C>, IsoCR<A, B, C>);

/// translator note:
/// FnBox is not yet supported, we can only return an uncallable
/// Box<FnOnce> (RetFunc). You should return the function with
/// correct type, which will be checked by the tests.
/// later you'll have to implement three more functions that related
/// to `RetFunc`. enjoy!

/// (c ^ b) ^ a = c ^ (a * b)
pub fn curry_iso<A: 'static, B: 'static, C: 'static>() -> IsoC<A, B, C> {
    (
        Box::new(|f| Box::new(move |(a, b)| f(a)(b))),
        Box::new(|f| Box::new(move |a| Box::new(move |b| f((a, b))))),
    )
}

/// 1 = S O (we are using peano arithmetic)
/// https://en.wikipedia.org/wiki/Peano_axioms  
pub fn one() -> ISO<(), Option<Void>> {
    iso(
        |()| None,
        |v| match v {
            Some(r) => absurd(r),
            None => (),
        },
    )
}

/// 2 = S (S O)
pub fn two() -> ISO<bool, Option<Option<Void>>> {
    iso(
        |b| if b { Some(None) } else { None },
        |r| match r {
            Some(Some(v)) => absurd(v),
            Some(None) => true,
            None => false,
        },
    )
}

/// 0 + b = b
pub fn plus_o<B: 'static>() -> ISO<Result<Void, B>, B> {
    iso(
        |r| match r {
            Ok(v) => absurd(v),
            Err(b) => b,
        },
        Err,
    )
}

/// S a + b = S (a + b)
pub fn plus_s<A: 'static, B: 'static>() -> ISO<Result<Option<A>, B>, Option<Result<A, B>>> {
    iso(
        |r| match r {
            Ok(Some(a)) => Some(Ok(a)),
            Ok(None) => None,
            Err(b) => Some(Err(b)),
        },
        |r| match r {
            Some(Ok(a)) => Ok(Some(a)),
            Some(Err(b)) => Err(b),
            None => Ok(None),
        },
    )
}

/// 1 + b = S b
pub fn plus_so<B: 'static>() -> ISO<Result<(), B>, Option<B>> {
    trans(iso_plus(one(), refl()), trans(plus_s(), iso_s(plus_o())))
}

/// 0 * a = 0
pub fn mult_o<A: 'static>() -> ISO<(Void, A), Void> {
    iso(|(v, _)| v, |v| match v {})
}

/// S a * b = b + a * b
pub fn mult_s<A: 'static, B: 'static>() -> ISO<(Option<A>, B), Result<B, (A, B)>> {
    iso(
        |(r, b)| match r {
            Some(a) => Err((a, b)),
            None => Ok(b),
        },
        |r| match r {
            Ok(b) => (None, b),
            Err((a, b)) => (Some(a), b),
        },
    )
}

/// S a * b = b + a * b
pub fn mult_so<B: 'static>() -> ISO<((), B), B> {
    trans(
        iso_prod(one(), refl()),
        trans(
            mult_s(),
            trans(iso_plus(refl(), mult_o()), trans(plus_comm(), plus_o())),
        ),
    )
}

/// Here we go, the last three functions related to
/// RetFunc. They're easy!

pub type IsoPL<A> = RetFunc<Func<Void, A>, ()>;
pub type IsoPR<A> = RetFunc<(), RetFunc<Void, A>>;
pub type IsoP<A> = (IsoPL<A>, IsoPR<A>);

/// a ^ 0 = 1
pub fn pow_o<A: 'static>() -> IsoP<A> {
    (Box::new(|_| ()), Box::new(|()| Box::new(|v| match v {})))
}

pub type IsoPsL<A, B> = RetFunc<Func<Option<B>, A>, (A, RetFunc<B, A>)>;
pub type IsoPsR<A, B> = RetFunc<(A, Func<B, A>), RetFunc<Option<B>, A>>;
pub type IsoPs<A, B> = (IsoPsL<A, B>, IsoPsR<A, B>);

/// a ^ (S b) = a * (a ^ b)
pub fn pow_s<A: 'static, B: 'static>() -> IsoPs<A, B> {
    (
        Box::new(|f| (f(None), Box::new(move |b| f(Some(b))))),
        Box::new(|(a, f)| {
            Box::new(move |r| match r {
                Some(b) => f(b),
                None => a,
            })
        }),
    )
}

pub type IsoPsoL<A> = RetFunc<Func<(), A>, A>;
pub type IsoPsoR<A> = RetFunc<A, RetFunc<(), A>>;
pub type IsoPso<A> = (IsoPsoL<A>, IsoPsoR<A>);

/// a ^ 1 = a
/// In Haskell/Java/Dart, you can go the hard way
/// (like mult_so, plus_so) to prove that you really get what is
/// going on.
/// Unfortunately, in Rust, you can only go the trivial way.
/// Because Rust doesn't support FnBox ATM.
pub fn pow_so<A: 'static>() -> IsoPso<A> {
    (Box::new(|f| f(())), Box::new(|a| Box::new(|()| a)))
}
