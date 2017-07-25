Require Import Setoid.

Parameter expr : Set.
Parameter comp : expr -> expr -> expr.

Notation "a ** b" := (comp a b) (at level 10).

Axiom associativity : forall a b c, (a ** b) ** c = a ** (b ** c).

Definition existsunique {A} (P : A -> Prop) := exists x, P x /\ forall x', P x' -> x' = x.

Definition pullback f g h := 
  exists h', h ** f = g ** h' /\ 
             forall i j, h ** i = g ** j -> existsunique (fun k => f ** k = i /\ h' ** k = j).

Definition monic f :=
  forall g h, f ** g = f ** h -> g = h.

Lemma pullback_of_monic_is_monic :
  forall f g h, pullback f g h -> monic g -> monic f.
Proof.
  intros f g h H_pullback H_g_monic g0 h0 H_f_monic_ass.
  assert (H_f_monic_ass_left_h : h ** f ** g0 = h ** f ** h0) by (repeat (rewrite associativity); congruence).
  destruct H_pullback as [h' [H_pullback_comm H_pullback_univ]].
  assert (h'_cofork : h' ** g0 = h' ** h0).
  * rewrite H_pullback_comm in H_f_monic_ass_left_h.
    repeat rewrite associativity in H_f_monic_ass_left_h.
    apply H_g_monic; assumption.
  * clear H_g_monic. 
    rewrite H_pullback_comm in H_f_monic_ass_left_h at 2.
    repeat rewrite associativity in H_f_monic_ass_left_h.
    specialize (H_pullback_univ _ _ H_f_monic_ass_left_h). clear H_f_monic_ass_left_h.
    destruct H_pullback_univ as [k [[k_comm_1 k_comm_2] k_unique]].
    assert (g0 = k).
    + specialize (k_unique g0). 
      rewrite h'_cofork in k_unique.
      auto.
    + assert (h0 = k).
      - specialize (k_unique h0).
        rewrite H_f_monic_ass in k_unique.
        auto.
      - congruence.
Qed.
  