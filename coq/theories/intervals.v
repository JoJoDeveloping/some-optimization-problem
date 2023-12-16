From trick Require Import inf_int.

Record interval := FromTo {
  left_bound: inf_int;
  right_bound: inf_int
}.

Definition right_bounded (i: inf_int) := {| left_bound := NegInfty; right_bound := i |}.
Definition with_left_bound (i: interval) (l: inf_int) := {| left_bound := l; right_bound := i.(right_bound) |}.

Inductive cover_from_left_decision := NoOverlap | SomeOverlap | FullOverlap.

Definition cover_from_left_with (i: interval) (x: inf_int) :=
  if decide (inf_int_lt x i.(left_bound)) then NoOverlap else
  if decide (inf_int_lt x i.(right_bound)) then SomeOverlap else FullOverlap.

(* Proofs *)

Definition interval_wf i : Prop :=
  inf_int_le i.(left_bound) i.(right_bound) ∧
  i.(left_bound) ≠ PosInfty ∧
  i.(right_bound) ≠ NegInfty.

Lemma right_bounded_wf i : i ≠ NegInfty → interval_wf (right_bounded i).
Proof. done. Qed.

Lemma with_left_bound_wf i l :
  l ≠ PosInfty → inf_int_le l i.(right_bound) → interval_wf i → interval_wf (with_left_bound i l).
Proof. by intros H1 H2 (H3&H4&H5). Qed.

Definition is_outside_left (i: interval) (x: inf_int) :=
  inf_int_lt x i.(left_bound).
Definition is_inside (i: interval) (x: inf_int) :=
  inf_int_le i.(left_bound) x ∧ inf_int_le x i.(right_bound).
Definition is_outside_right (i: interval) (x: inf_int) :=
  inf_int_lt i.(right_bound) x.

Definition overlaps_nowhere (i: interval) (x: inf_int) :=
  inf_int_lt x i.(left_bound).
Definition overlaps_partial (i: interval) (x: inf_int) :=
  inf_int_le i.(left_bound) x ∧ inf_int_lt x i.(right_bound).
Definition overlaps_fully (i: interval) (x: inf_int) :=
  inf_int_le i.(right_bound) x.

Definition is_overlap dec := match dec with
  NoOverlap => overlaps_nowhere
| SomeOverlap => overlaps_partial
| FullOverlap => overlaps_fully end.

Lemma cover_from_left_with_correct i x : interval_wf i → is_overlap (cover_from_left_with i x) i x.
Proof.
  rewrite /cover_from_left_with => Hwf.
  destruct decide as [Hlt|Hge]; last destruct decide as [Hlt|Hge2]; try done.
  - split; try eapply le_neg_lt; done.
  - eapply le_neg_lt. done.
Qed.

Inductive sorted_dense_covering_up_to : list interval → inf_int → Prop :=
  (* bogus case, only appears at the beginning *)
| upto_empty k : sorted_dense_covering_up_to nil k
| upto_singleton k : k ≠ PosInfty → sorted_dense_covering_up_to [FromTo k PosInfty] k
| upto_next it1 it2 rst z lb : 
    it1 = FromTo lb (Num z) →
    interval_wf it1 →
    sorted_dense_covering_up_to (it2 :: rst) (Num (z + 1)) →
    sorted_dense_covering_up_to (it1 :: it2 :: rst) lb.

Definition list_interval_wf lst := sorted_dense_covering_up_to lst NegInfty.

Lemma list_interval_contais_wf' lst upto : 
  sorted_dense_covering_up_to lst upto → ∀ iv, In iv lst → interval_wf iv.
Proof.
  induction 1 as [|k Hk|it1 it2 rst upto lb H1 H2 H3 IH]; first done;
   (intros v [Hin|Hin]%in_inv; first subst).
  - by destruct k.
  - by inversion Hin.
  - done.
  - by apply IH.
Qed. 

Lemma list_interval_wf_covers' lst upto :
  sorted_dense_covering_up_to lst upto →
  lst ≠ nil →
  ∀ z, inf_int_le upto z → ∃ iv, In iv lst ∧ is_inside iv z.
Proof.
  induction 1 as [|k Hk|it1 it2 rst upto lb H1 H2 H3 IH]; intros Hnn z Hle.
  - done.
  - eexists; split; first by econstructor.
    split; first done.
    by destruct z.
  - destruct (decide (inf_int_le z (Num upto))) as [Hin|Hne%lt_neg_le%le_lt_up].
    + exists it1. split; first by econstructor.
      by rewrite H1.
    + destruct (IH (ltac:(congruence)) _ Hne) as (iv&Hiv1&Hiv2).
      exists iv; split; first by econstructor.
      done.
Qed.

Lemma list_interval_contais_wf lst : 
  list_interval_wf lst → ∀ iv, In iv lst → interval_wf iv.
Proof.
  apply list_interval_contais_wf'.
Qed. 

Lemma list_interval_wf_covers lst :
  list_interval_wf lst →
  lst ≠ nil →
  ∀ z, ∃ iv, In iv lst ∧ is_inside iv z.
Proof.
  intros H1 Hnn z.
  by eapply list_interval_wf_covers'.
Qed.












