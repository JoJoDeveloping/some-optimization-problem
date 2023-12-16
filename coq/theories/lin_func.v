From trick Require Import inf_int.

Record lin_func := lfn {
  x_is: Z;
  gradient: Z
}.

Definition eval_lin_func (f : lin_func) (x:Z) : Z := f.(x_is) + f.(gradient) * x.

Definition lin_func_intersection (f1 f2 : lin_func) : inf_int := 
 (if decide (f1.(gradient) = f2.(gradient)) then
    if decide (f1.(x_is) < f2.(x_is)) then NegInfty else PosInfty else
    Num ((f2.(x_is) - f1.(x_is)) / (f1.(gradient) - f2.(gradient))))%Z.

(* Proofs *)

#[global]
Coercion eval_lin_func : lin_func >-> Funclass.

Definition dominates_at (z: Z) (f1 f2  : lin_func) :=
  f2 z ≤ f1 z.

Definition strictly_dominates_at (z: Z) (f1 f2  : lin_func) :=
  f2 z < f1 z.

Lemma Z_add_neg_sub z1 z2 : z1 + - z2 = z1 - z2.
Proof. reflexivity. Qed.

Lemma lin_func_intersection_correct f1 f2 : 
  f1.(gradient) ≤ f2.(gradient) →
  let z := lin_func_intersection f1 f2 in ∀ (k:Z),
  (inf_int_lt z k → strictly_dominates_at k f2 f1) ∧
  (inf_int_le k z → dominates_at k f1 f2).
Proof.
  intros Hgrad z. unfold lin_func_intersection in z.
  destruct f1 as [f1x f1g], f2 as [f2x f2g]; simpl in *.
  destruct decide as [-> | Hne].
  - destruct decide as [Hsame | Hdiff];
      subst z; intros k; split; try done; intros _.
    + rewrite /strictly_dominates_at /eval_lin_func /=. lia.
    + rewrite /dominates_at /eval_lin_func /=. lia.
  - rename z into z'.
    pose ((f2x - f1x) `div` (f1g - f2g)) as z.
    change (Num ?a) with (Num z) in z'. subst z'.
    rewrite /inf_int_lt /= /strictly_dominates_at /dominates_at /eval_lin_func /=.

    intros k; split; intros Hk.
    + eapply Z.add_lt_mono_r with (-(f2g * k)).
      erewrite <-!Z.add_assoc, Z.add_opp_diag_r, Z.add_0_r.
      eapply Z.add_lt_mono_l with (-f1x).
      erewrite !Z.add_assoc, Z.add_opp_diag_l, Z.add_0_l.
      rewrite Z_add_neg_sub -Zmult_minus_distr_r.
      erewrite (Z.add_comm (- _)), Z_add_neg_sub.
      rewrite (Z_div_mod_eq_full (f2x - f1x) (f1g - f2g)).
      assert (z ≤ k-1) as Hk' by lia.
      eapply (Z.mul_le_mono_neg_l _ _ (f1g - f2g)) in Hk'; last lia.
      eapply Z.lt_le_trans.
      2: apply Zplus_le_compat_r, Hk'.
      rewrite Z.mul_sub_distr_l -Z.add_assoc Z.mul_1_r.
      apply Z.lt_add_pos_r.
      eapply Z.add_lt_mono_l with ((f1g - f2g)).
      erewrite !Z.add_assoc, Z.add_opp_diag_r, Z.add_0_l, Z.add_0_r.
      apply Z.mod_neg_bound. lia.
    + eapply Z.add_le_mono_r with (-(f2g * k)).
      erewrite <-!Z.add_assoc, Z.add_opp_diag_r, Z.add_0_r.
      eapply Z.add_le_mono_l with (-f1x).
      erewrite !Z.add_assoc, Z.add_opp_diag_l, Z.add_0_l.
      rewrite Z_add_neg_sub -Zmult_minus_distr_r.
      erewrite (Z.add_comm (- _)), Z_add_neg_sub.
      rewrite (Z_div_mod_eq_full (f2x - f1x) (f1g - f2g)).
      eapply (Z.mul_le_mono_neg_l _ _ (f1g - f2g)) in Hk; last lia.
      etransitivity; last apply Hk.
      rewrite <- Z.add_0_r.
      eapply Zplus_le_compat_l, Z_mod_neg. lia.
Qed.
  