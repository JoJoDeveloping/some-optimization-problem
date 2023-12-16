From stdpp Require Export options ssreflect.

#[global]
Open Scope Z_scope.

Inductive inf_int := NegInfty | PosInfty | Num (z:Z).

#[global]
Coercion Num : Z >-> inf_int.

Definition inf_int_le (a b : inf_int) : Prop := match a, b with
| NegInfty, _        => True
|        _, NegInfty  => False
|        _, PosInfty => True
| PosInfty, _        => False
| Num a   , Num b    => a ≤ b end.

Definition inf_int_lt (a b : inf_int) : Prop := match a, b with
| NegInfty, NegInfty => False
| PosInfty, PosInfty => False
| NegInfty, _        => True
|        _, NegInfty  => False
|        _, PosInfty => True
| PosInfty, _        => False
| Num a   , Num b    => a < b end.

#[global]
Instance inf_int_lt_dec : RelDecision inf_int_lt.
Proof.
  intros [] []; simpl; apply _.
Defined.

Lemma inf_int_lt_le a b : inf_int_le a b ∧ a ≠ b ↔ inf_int_lt a b.
Proof.
  move : a b => [| |a] [| |b].
  1-8: naive_solver.
  split; simpl.
  - intros [H H2]. assert (a ≠ b) by congruence. lia.
  - intros H. split; first lia. intros [=]. lia.
Qed.

#[global]
Instance inf_int_le_dec : RelDecision inf_int_le.
Proof.
  intros [] []; simpl; apply _.
Defined.

Definition inf_int_off a z : inf_int := match a with
  Num a => Num (a+z)
| x => x end.

#[global]
Instance inf_int_eq_dec : EqDecision inf_int.
Proof.
  intros ? ?. unfold Decision. decide equality. apply Z.eq_dec.
Defined.

(* Proofs *)

Lemma lt_trichotomy i1 i2 : inf_int_lt i1 i2 ∨ i1 = i2 ∨ inf_int_lt i2 i1.
Proof.
  move : i1 i2 => [| |z1] [| |z2]; simpl; eauto.
  destruct (Z.lt_trichotomy z1 z2) as [?|[->|?]]; eauto.
Qed.

Lemma le_neg_lt i1 i2 : inf_int_le i1 i2 ↔ ¬inf_int_lt i2 i1.
Proof.
  move : i1 i2 => [| |z1] [| |z2]; simpl; split; eauto.
  all: apply Z.le_ngt.
Qed.

Lemma lt_neg_le i1 i2 : ¬inf_int_le i1 i2 ↔ inf_int_lt i2 i1.
Proof.
  move : i1 i2 => [| |z1] [| |z2]; simpl; split; eauto.
  all: apply Z.lt_nge.
Qed.

Lemma le_lt_up z1 i2 : inf_int_lt (Num z1) i2 → inf_int_le (Num (z1 + 1)) i2.
Proof.
  move : i2 => [| |z2] /= H //. lia.
Qed.



