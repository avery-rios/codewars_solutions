CoInductive conat : Set :=
  | O : conat
  | S : conat -> conat.

CoInductive bisim : conat -> conat -> Prop :=
  | OO : bisim O O
  | SS : forall n m, bisim n m -> bisim (S n) (S m).

Notation "x == y" := (bisim x y) (at level 80) : conat_scope.

CoFixpoint plus (n m : conat) : conat := match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity) : conat_scope.

