(*! Pipelined instantiation of the core !*)
Require Import Koika.Frontend.
Require Import RV.RVCore.
Import RV32ICore.

Definition rv_schedule : scheduler :=
  Writeback |> Execute |> StepMultiplier |> Decode |> WaitImem |> Fetch |> ExternalI |> ExternalD  |>  done.

Definition circuits :=
  compile_scheduler rv_rules rv_external rv_schedule.

Instance Show_rf : Show (Rf.reg_t) :=
  {| show '(Rf.rData v) := rv_register_name v |}.

Instance Show_scoreboard : Show (Scoreboard.reg_t) :=
  {| show '(Scoreboard.Scores (Scoreboard.Rf.rData v)) := rv_register_name v |}.

Definition koika_package :=
  {| koika_reg_types := R;
     koika_reg_init := r;
     koika_ext_fn_types := empty_Sigma;
     koika_rules := rv_rules;
     koika_rule_external := rv_external;
     koika_scheduler := rv_schedule;
     koika_module_name := "rv32" |}.

Definition package :=
  {| ip_koika := koika_package;
     ip_sim := {| sp_ext_fn_names := empty_ext_fn_names;
                 sp_extfuns := None |};
     ip_verilog := {| vp_ext_fn_names := empty_ext_fn_names |} |}.

Definition prog := Interop.Backends.register package.
Extraction "rv32.ml" prog.
