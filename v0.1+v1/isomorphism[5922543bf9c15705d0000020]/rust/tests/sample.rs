#[cfg(feature = "local")]
use isomorphism::*;

// mod preloaded;

#[cfg(test)]
mod tests {
    use super::*;
    // use preloaded::*;

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

    // #[test]
    // fn refl_test() {
    //     assert!(MEOW == sub_st_l(sub_st_l(refl())(t_iso()))(true));
    // }
    // other tests are hidden
}
