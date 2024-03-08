Fixpoint div_mod2 (n : nat) : (nat * bool) :=
  match n with
  | 0 => (0, false)
  | 1 => (0, true)
  | S (S n) => let (a, b) := div_mod2 n in (S a, b)
  end.

Fixpoint pow_sqr_aux (k b e : nat) : nat :=
  match k, e with
  | 0, _ => 1
  | _, 0 => 1
  | S k, _ => match div_mod2 e with
              | (e', false) => pow_sqr_aux k (b * b) e'
              | (e', true) => b * pow_sqr_aux k (b * b) e'
              end
  end.
  
Definition pow_sqr (b e : nat) : nat := pow_sqr_aux e b e.

