use can_you_control_the_lights::LightController;

fn toggle_switches(
    corresponding_lights_list: &Vec<Vec<usize>>,
    n: usize,
    switches_indices: &Vec<usize>,
) -> Vec<usize> {
    let mut lights_states = vec![false; n];
    for switch in switches_indices {
        for light in &corresponding_lights_list[*switch] {
            lights_states[*light] = !lights_states[*light]
        }
    }
    (0..n).filter(|i| lights_states[*i]).collect()
}

#[cfg(test)]
mod fixed_tests {
    use super::{toggle_switches, LightController};

    #[test]
    fn exhaustive_small_tests() {
        let tests = vec![
            (2, vec![vec![0], vec![1]], vec![true, true, true, true]),
            (2, vec![vec![1, 0], vec![1]], vec![true, true, true, true]),
            (
                2,
                vec![vec![0, 1], vec![0, 1]],
                vec![true, false, false, true],
            ),
            (
                3,
                vec![vec![], vec![2], vec![0], vec![1, 0, 2]],
                vec![true, true, true, true, true, true, true, true],
            ),
            (
                3,
                vec![vec![], vec![], vec![], vec![2, 1]],
                vec![true, false, false, false, false, false, true, false],
            ),
            (0, vec![vec![]], vec![true]),
            (1, vec![], vec![true, false]),
            (0, vec![], vec![true]),
            (1, vec![vec![0]], vec![true, true]),
            (1, vec![vec![]], vec![true, false]),
            (
                4,
                vec![vec![0, 2, 3], vec![1, 2, 3], vec![1], vec![2]],
                vec![
                    true, true, true, true, true, true, true, true, true, true, true, true, true,
                    true, true, true,
                ],
            ),
            (
                4,
                vec![vec![3], vec![1], vec![0, 1, 2], vec![0, 1, 2, 3]],
                vec![
                    true, false, true, false, false, true, false, true, true, false, true, false,
                    false, true, false, true,
                ],
            ),
            (
                4,
                vec![vec![1, 2, 3], vec![0, 1, 3], vec![1, 2, 3], vec![], vec![3]],
                vec![
                    true, false, false, true, false, true, true, false, true, false, false, true,
                    false, true, true, false,
                ],
            ),
            (
                4,
                vec![vec![0, 1], vec![], vec![0, 1, 2, 3]],
                vec![
                    true, false, false, true, false, false, false, false, false, false, false,
                    false, true, false, false, true,
                ],
            ),
        ];

        for (n, corresponding_lights_list, are_possible) in tests {
            let controller = LightController::new(n, &corresponding_lights_list);
            for (lights_choice, is_possible) in
                powerset(n).into_iter().zip(are_possible.into_iter())
            {
                test_controller(
                    n,
                    &corresponding_lights_list,
                    &controller,
                    lights_choice,
                    is_possible,
                );
            }
        }
    }

    fn powerset(n: usize) -> Vec<Vec<usize>> {
        if n == 0 {
            vec![vec![]]
        } else {
            let mut s = powerset(n - 1);
            let mut s2 = s.clone();
            s2.iter_mut().for_each(|ss| ss.push(n - 1));
            s.append(&mut s2);
            s
        }
    }

    fn test_controller(
        n: usize,
        corresponding_lights_list: &Vec<Vec<usize>>,
        controller: &LightController,
        lights_choice: Vec<usize>,
        is_possible: bool,
    ) {
        if let Some(switches_indices) = controller.solve(&lights_choice) {
            assert_eq!(
                toggle_switches(corresponding_lights_list, n, &switches_indices),
                lights_choice,
                "controller for corresponding_lights_list {:?} failed to provide a right set of switches: tried to turn on the lights {:?} with the switches {:?}",
                corresponding_lights_list,
                lights_choice,
                switches_indices
            )
        } else {
            assert!(!is_possible, "controller for corresponding_lights_list {:?} returned None for the lights set {:?}", corresponding_lights_list, lights_choice);
        }
    }

    #[rustfmt::skip]
    #[test]
    fn larger_tests() {
        let tests = include!("./full/larger_tests.rs");

        for (n, corresponding_lights_list, controller_tests) in tests {
            let controller = LightController::new(n, &corresponding_lights_list);
            for (lights_choice, is_possible) in controller_tests {
                if let Some(switches_indices) = controller.solve(&lights_choice) {
                    assert_eq!(
                        toggle_switches(&corresponding_lights_list, n, &switches_indices),
                        lights_choice,
                        "controller for n = {} provided a wrong list of switches",
                        n,
                    )
                } else {
                    assert!(
                        !is_possible,
                        "controller for n = {} returned None for a possible choice of lights",
                        n
                    );
                }
            }
        }
    }
}

#[cfg(test)]
mod random_tests {
    use super::{toggle_switches, LightController};
    use num::bigint::BigUint;
    use rand::{
        rngs::ThreadRng,
        seq::{index, SliceRandom},
        Rng,
    };

    fn random_test(n: usize, m: usize, combination_count: usize) {
        let corresponding_lights_list = random_subsets(n, m);
        let solver = LightController::new(n, &corresponding_lights_list);
        for lights_subset in random_subsets(n, combination_count) {
            if let Some(switches_subset) = solver.solve(&lights_subset) {
                let resp = toggle_switches(&corresponding_lights_list, n, &switches_subset);
                assert_eq!(resp, lights_subset);
            }
        }
    }

    #[test]
    fn n100_m200() {
        random_test(100, 200, 400);
    }

    #[test]
    fn n200_m100() {
        random_test(200, 100, 400);
    }

    #[test]
    fn n200_m200() {
        random_test(200, 200, 200);
    }

    #[test]
    fn n300_m300() {
        random_test(300, 300, 200);
    }

    #[test]
    fn n500_m500() {
        random_test(500, 500, 3000);
    }

    #[test]
    fn workarounds() {
        workarounds_test(500, 500);
    }

    fn random_subsets(set_size: usize, subset_count: usize) -> Vec<Vec<usize>> {
        let mut rng = rand::thread_rng();
        (0..subset_count)
            .map(|_| random_subset(set_size, rng.gen_range(0..=set_size), &mut rng))
            .collect()
    }

    fn random_subset(set_size: usize, subset_size: usize, rng: &mut ThreadRng) -> Vec<usize> {
        let mut set: Vec<usize> = (0..set_size).collect();
        set.shuffle(rng);
        let mut subset = set[..subset_size].to_vec();
        subset.sort();
        subset
    }

    fn workarounds_test(n: usize, m: usize) {
        let base = random_subsets(n, m);
        let mut matrix: Vec<BigUint> = base
            .iter()
            .map(|light| {
                let mut ind = BigUint::default();
                for i in light {
                    ind.set_bit(*i as u64, true);
                }
                ind
            })
            .collect();
        let mut rng = rand::thread_rng();
        for _ in 0..m {
            let sample = index::sample(&mut rng, m, 2);
            let x = matrix[sample.index(1)].clone();
            matrix[sample.index(0)] ^= x;
        }
        let corresponding_lights_list: Vec<Vec<usize>> = matrix
            .into_iter()
            .map(|row| (0..n).filter(|i| row.bit(*i as u64)).collect())
            .collect();
        let solver = LightController::new(n, &corresponding_lights_list);
        for lights_subset in base {
            assert_eq!(
                toggle_switches(
                    &corresponding_lights_list,
                    n,
                    &solver
                        .solve(&lights_subset)
                        .expect("returned None for a possible choice of lights")
                ),
                lights_subset,
                "controller for n = {} provided a wrong list of switches",
                n,
            )
        }
    }
}
