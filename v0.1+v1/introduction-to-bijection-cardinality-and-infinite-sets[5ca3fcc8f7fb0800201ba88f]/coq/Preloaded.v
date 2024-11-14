Record iso (A B : Set) : Set :=
  bijection {
    A_to_B : A -> B;
    B_to_A : B -> A;
    A_B_A  : forall a : A, B_to_A (A_to_B a) = a;
    B_A_B  : forall b : B, A_to_B (B_to_A b) = b
  }.

Inductive nat_plus_1 : Set := null | is_nat (n : nat). 

Inductive nat_plus_nat : Set := left (n : nat) | right (n : nat). 

