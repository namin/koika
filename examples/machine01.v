Require Import Koika.Frontend.

(*|
Koika port of https://github.com/namin/bluespec-sandbox/blob/main/machine01.bsv
|*)

Definition ext_fn_t := empty_ext_fn_t.

Module Machine01.
Definition sz := 2.

Inductive reg_t :=
| state
| input_valid
| input.

Definition R r :=
  match r with
  | state => bits_t sz
  | input_valid => bits_t 1
  | input => bits_t 1
  end.

Definition r idx : R idx :=
  match idx with
  | state => Bits.of_nat sz 0
  | input_valid => Bits.of_nat 1 0
  | input => Bits.of_nat 1 0
  end.

Definition _state0 : uaction reg_t ext_fn_t :=
  {{ guard(read0(input_valid));
     let v := read0(input) in
     (if !v then
       write0(state, Ob~0~1)
     else
       write0(state, Ob~1~1));
     write0(input_valid, Ob~0) }}.

Definition _state1 : uaction reg_t ext_fn_t :=
  {{ guard(read0(input_valid));
     let v := read0(input) in
     (if v then
       write0(state, Ob~1~0)
     else
       write0(state, Ob~1~1));
     write0(input_valid, Ob~0) }}.

Definition _state2 : uaction reg_t ext_fn_t :=
  {{ guard(read0(input_valid));
     write0(state, Ob~1~1);
     write0(input_valid, Ob~0) }}.

Definition _state3 : uaction reg_t ext_fn_t :=
  {{ guard(read0(input_valid));
     write0(input_valid, Ob~0) }}.

(* TODO: how can these be part of the interface, akin to Bluespec methods? *)
Definition put : UInternalFunction reg_t ext_fn_t :=
  {{ fun put (c: bits_t 1) : unit_t =>
       guard(!read0(input_valid)); write0(input, c); write0(input_valid, Ob~1) }}.

Definition observe : UInternalFunction reg_t ext_fn_t :=
  {{ fun observe () : bits_t 1 =>
       guard(state == Ob~0~1 || state == Ob~1~0);
     state == Ob~0~1 }}.

Inductive rule_name_t := state0 | state1 | state2 | state3.

Definition machine01 : scheduler :=
  state0 |> state1 |> state2 |> state3 |> done.

Definition rules :=
  tc_rules R empty_Sigma
           (fun r => match r with
                  | state0 => _state0
                  | state1 => _state1
                  | state2 => _state2
                  | state3 => _state3
                  end).

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := empty_Sigma;
                     koika_rules := rules;
                     koika_rule_external := (fun _ => false);
                     koika_scheduler := machine01;
                     koika_module_name := "machine01" |};

       ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                   sp_prelude := None |};

       ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.

End Machine01.

Definition prog := Interop.Backends.register Machine01.package.
