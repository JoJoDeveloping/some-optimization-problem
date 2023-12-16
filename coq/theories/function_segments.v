From trick Require Import inf_int intervals lin_func.

Record func_seg := {
  func: lin_func;
  on: interval
}.

Definition func_on (func: lin_func) (higher: inf_int) : func_seg :=
  {| func := func; on := right_bounded higher |}.

Definition with_lowest (fs: func_seg) (lower: inf_int) : func_seg :=
  {| func := fs.(func); on := with_left_bound fs.(on) lower |}.

Definition add_lowest (f: lin_func) (upto: inf_int) (s: list func_seg) :=
  let with_modification := match s with
    nil => nil
  | f :: rest => with_lowest f (inf_int_off upto 1) :: rest end in
  func_on f upto :: with_modification.

Definition add_lowest_combining (f: lin_func) (upto: inf_int) (s: list func_seg) :=
  let with_modification := match s with
    nil => nil
  | f :: rest => if decide (f.(on).(right_bound) = upto) then rest else f :: rest end in
  add_lowest f upto with_modification.

Definition add_lowest_all (fl: list func_seg) (s: list func_seg) := 
  fold_left (λ s f, add_lowest f.(func) f.(on).(right_bound) s) fl s.

Definition add_lowest_all_combining_one (fl: list func_seg) (s: list func_seg) :=
  match fl with nil => s | f :: fl => add_lowest_all fl (add_lowest_combining f.(func) f.(on).(right_bound) s) end.


(* Proofs *)

Definition func_seg_wf fs := interval_wf fs.(on).

Lemma func_on_wf func higher :
  higher ≠ NegInfty → func_seg_wf (func_on func higher).
Proof.
  apply right_bounded_wf.
Qed.

Lemma with_lowest_wf fs lower :
  lower ≠ PosInfty →
  inf_int_le lower fs.(on).(right_bound) →
  func_seg_wf fs →
  func_seg_wf (with_lowest fs lower).
Proof.
  apply with_left_bound_wf.
Qed.

Definition strictly_dominates_on (f1: func_seg) (f2: lin_func) :=
 ∀ (z:Z), is_inside f1.(on) z → strictly_dominates_at z f1.(func) f2.

Inductive is_dom_order : list func_seg → Prop :=
  is_dom_nil : is_dom_order nil
| is_dom_singleton fs : is_dom_order [fs]
| is_dom_cons f1 f2 rst : 
    strictly_dominates_on f1 f2.(func) →
    is_dom_order (f2::rst) →
    is_dom_order (f1::f2::rst).

Definition func_seg_list_wf lst := 
  is_dom_order lst ∧ list_interval_wf (map on lst).


