From stdpp Require Export options ssreflect.
From trick Require Import inf_int intervals lin_func utils function_segments.

Section list_utils.

End list_utils.

Inductive structure := {
  data: list func_seg;
  lower: option structure
}.

Fixpoint new_structure depth : structure :=
  {| data := nil; lower := match depth with 0 => None | S n => Some (new_structure n) end |}.

Definition map_data f s := {| data := f s.(data); lower := s.(lower) |}.

Fixpoint with_insert (s: structure) (f: lin_func) : structure :=
  let
    with_insert_at_coord
      s_data (coord: inf_int) (f_old: lin_func) (f_stack : list func_seg) : structure :=
    let s_data := add_lowest f coord s_data in
    let new_lower := match s.(lower) with None => None | Some next => 
      let next := with_insert next f in
      let next := map_data (add_lowest_combining f_old coord) next in
      let next := map_data (add_lowest_all_combining_one f_stack) next in
      Some(next)
    end in
    {| data := s_data; lower := new_lower |}
  in
  let loop_func (f_stack : list func_seg) (entry: func_seg) s_data :=
    let intersect := lin_func_intersection f entry.(func) in
    match intersect, cover_from_left_with entry.(on) intersect with
    | _, NoOverlap =>
        let insert_coord := inf_int_off entry.(on).(left_bound) (-1) in
        Return (with_insert_at_coord (entry :: s_data) insert_coord entry.(func) f_stack)
    | NegInfty, _ =>
        let new_lower := match s.(lower) with None => None | Some next =>
          Some (with_insert next f) end in
        Return ({| data := entry :: s_data; lower := new_lower |})
    | _, SomeOverlap =>
        let insert_coord := intersect in
        Return (with_insert_at_coord (entry :: s_data) insert_coord entry.(func) f_stack)
    | _, FullOverlap =>
        Continue (entry :: f_stack) end
  in
  let default := 
    {| data := [func_on f PosInfty]; lower := s.(lower) |}
  in
  fold_left_with_exit loop_func default [] s.(data).


Section test.

  Let data1 := [
    lfn (-11) 2;
    lfn 0 1;
    lfn 8 0;
    lfn 5 (-1) ].

  Let data2 := [
    lfn (-5) 1;
    lfn 0 0;
    lfn 5 (-1) ].

  Eval compute in (fold_left with_insert data2 (new_structure 2)).

End test.

