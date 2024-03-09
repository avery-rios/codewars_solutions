use challenge::tower;

#[test]
fn not_coprime() {
    assert_eq!(tower(34, 2, 40), 16);
}
