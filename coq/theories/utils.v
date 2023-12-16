From stdpp Require Export options ssreflect.

Inductive exiting (A B : Type) := Continue of A | Return of B.
#[global] Arguments Continue {_} {_} a.
#[global] Arguments Return {_} {_} b.
Fixpoint fold_left_with_exit {A B L : Type} (f: A → L → list L → exiting A B) (default: B) (a: A) (lst: list L) : B :=
  match lst with
    nil => default
  | x::xr => match f a x xr with
      Continue a => fold_left_with_exit f default a xr
    | Return b => b end end.
