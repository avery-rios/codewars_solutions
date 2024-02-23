Definition axiom_pem := forall (P : Prop), P \/ ~P.

Definition axiom_dne := forall (P : Prop), ~ ~P -> P.

Lemma not_or : forall (P : Prop), ~ (P \/ ~P) -> ~P /\ ~~P.
Proof. 
  intros P Hno. split.
  - intros Hp. exact (Hno (or_introl Hp)).
  - intros Hnp. exact (Hno (or_intror Hnp)). 
Qed.

Theorem from : axiom_dne -> axiom_pem.
Proof.
  intros Dne P. apply Dne. intros Ho. apply not_or in Ho.
  destruct Ho as [Hl Hr]. exact (Hr Hl).
Qed.

Theorem to : axiom_pem -> axiom_dne.
Proof.
  intros Em P Hnnp. destruct (Em P).
  - apply H.
  - exfalso. apply Hnnp. apply H.
Qed. 