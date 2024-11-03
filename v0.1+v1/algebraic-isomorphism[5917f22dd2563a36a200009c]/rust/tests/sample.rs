#[cfg(feature = "local")]
use algebraic_isomorphism::*;

#[cfg(test)]
mod tests {
use super::*;

fn moe() -> String {
    "MOE".to_string()
}

fn meow() -> String {
    "MEOW".to_string()
}

fn verbose() -> String {
    "It was me, DIO!".to_string()
}

fn lrl<A: 'static, B: 'static>(i: ISO<A, B>, a: A) -> A {
    let (fw, bw) = i;
    bw(fw(a))
}

fn rlr<A: 'static, B: 'static>(i: ISO<A, B>, b: B) -> B {
    let (fw, bw) = i;
    fw(bw(b))
}

#[test]
fn sub_st_l_test() {
    assert!(sub_st_l(iso_bool())(true));
    assert!(!sub_st_l(iso_bool())(false));
    assert!(sub_st_l(iso_bool_not())(false));
}

#[test]
fn sub_st_r_test() {
    assert!(sub_st_r(iso_bool())(true));
    assert!(!sub_st_r(iso_bool())(false));
}

#[test]
fn assoc_test() {
    assert_eq!(Ok::<Result<i16, bool>, String>(Ok(233)),
               lrl(plus_assoc(), Ok::<Result<i16, bool>, String>(Ok(233))));
    assert_eq!(Ok::<Result<i16, bool>, String>(Err(true)),
               lrl(plus_assoc(), Ok::<Result<i16, bool>, String>(Err(true))));
    assert_eq!(Err::<Result<i16, bool>, String>(verbose()),
               lrl(plus_assoc(), Err::<Result<i16, bool>, String>(verbose())));
    assert_eq!(Ok::<i16, Result<bool, String>>(233),
               rlr(plus_assoc(), Ok::<i16, Result<bool, String>>(233)));
    assert_eq!(Err::<i16, Result<bool, String>>(Ok(true)),
               rlr(plus_assoc(), Err::<i16, Result<bool, String>>(Ok(true))));
    assert_eq!(Err::<i16, Result<bool, String>>(Err(verbose())),
               rlr(plus_assoc(), Err::<i16, Result<bool, String>>(Err(verbose()))));
}

}