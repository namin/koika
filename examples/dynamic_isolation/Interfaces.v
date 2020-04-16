(*! Implementation of our RISC-V core !*)
Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.

Require Import DynamicIsolation.Tactics.
Require Import DynamicIsolation.Scoreboard.

Definition post_t := unit.
Definition var_t := string.
Definition fn_name_t := string.

(* Our machine consists of two cores, a security monitor, a memory hierarchy, and external memory modules.
 * We have a well-defined interface to each component.
 *)

Module Common.

  Definition mem_req :=
    {| struct_name := "mem_req";
       struct_fields := [("byte_en" , bits_t 4);
                         ("addr"     , bits_t 32);
                         ("data"     , bits_t 32)] |}.
  Definition mem_resp :=
    {| struct_name := "mem_resp";
       struct_fields := [("byte_en", bits_t 4); ("addr", bits_t 32); ("data", bits_t 32)] |}.

  Module FifoMemReq <: Fifo.
    Definition T:= struct_t mem_req.
  End FifoMemReq.
  Module MemReq := Fifo1Bypass FifoMemReq.

  Module FifoMemResp <: Fifo.
    Definition T:= struct_t mem_resp.
  End FifoMemResp.
  Module MemResp := Fifo1 FifoMemResp.

  Module RfParams <: RfPow2_sig.
    Definition idx_sz := log2 32.
    Definition T := bits_t 32.
    Definition init := Bits.zeroes 32.
    Definition read_style := Scoreboard.read_style 32.
    Definition write_style := Scoreboard.write_style.
  End RfParams.
  Module Rf := RfPow2 RfParams.

  Instance FiniteType_MemReq : FiniteType MemReq.reg_t := _.
  Instance FiniteType_MemResp : FiniteType MemResp.reg_t := _.
  Instance FiniteType_Rf : FiniteType Rf.reg_t := _.

  Definition addr_t := bits_t 32.
  Definition data_t := bits_t 32.

  (* Alignment *)
  Definition addr_index_t := bits_t 30.

  Definition initial_mem_t := addr_index_t -> data_t.

End Common.

Module Type EnclaveParameters.

End EnclaveParameters.

Module Type CoreParameters.
  Parameter core_id : bits_t 1.
End CoreParameters.

Module Type External_sig.
  Parameter ext_fn_t : Type.
  Parameter Sigma : ext_fn_t -> ExternalSignature.
  Parameter sigma : (forall fn: ext_fn_t, Sig_denote (Sigma fn)).

  Parameter reg_t : Type.

End External_sig.

Module Type Core_sig (External: External_sig) (Params: EnclaveParameters) (CoreParams: CoreParameters).
  Import Common.
  Parameter internal_reg_t : Type.
  Parameter R_internal_reg : internal_reg_t -> type.
  Parameter r_internal_reg : forall (idx: internal_reg_t), R_internal_reg idx.
  Declare Instance FiniteType_internal_reg_t : FiniteType internal_reg_t.

  Inductive reg_t :=
  | core_id
  | ToIMem (state: MemReq.reg_t)
  | ToDMem (state: MemReq.reg_t)
  | FromIMem (state: MemResp.reg_t)
  | FromDMem (state: MemResp.reg_t)
  | internal (r: internal_reg_t)
  .

  Definition R (idx: reg_t) : type :=
   match idx with
   | core_id => bits_t 1
   | ToIMem r => MemReq.R r
   | ToDMem r => MemReq.R r
   | FromIMem  r => MemResp.R r
   | FromDMem  r => MemResp.R r
   | internal r => R_internal_reg r
   end.

  Declare Instance FiniteType_reg_t : FiniteType reg_t.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  Definition sigma := External.sigma.

  Parameter rule_name_t : Type.
  Parameter rules  : rule_name_t -> rule.

  Axiom schedule : Syntax.scheduler pos_t rule_name_t.

  Definition state := env_t ContextEnv (fun idx : reg_t => R idx).

End Core_sig.

Module ModuleLift.
  Record RLift {reg_t reg_t': Type} {R: reg_t -> type} {R': reg_t' -> type} := mk_RLift
    { lift: reg_t -> reg_t'
    ; pf_R_equal: forall (reg: reg_t), R' (lift reg) = R reg
    ; pf_inj_lift: forall (r1 r2: reg_t), lift r1 = lift r2 -> r1 = r2
    }.
  Arguments RLift : clear implicits.

  Ltac mk_rlift lift :=
    exists lift;
    match goal with
    | [ |- forall r, _ (lift r) = _ r ] =>  destruct r; auto
    | [ |- forall r1 r2, lift r1 = lift r2 -> r1 = r2] =>
        destruct r1; destruct r2; simpl; destruct_all_matches
   end.

  Section ScheduleLift.
    Context {pos_t : Type} {rule_name_t : Type} {rule_name_t' : Type}.
    Context (lift: rule_name_t -> rule_name_t').

    Fixpoint lift_scheduler (sched: Syntax.scheduler pos_t rule_name_t)
                             : Syntax.scheduler pos_t rule_name_t' :=
      match sched with
      | Done => Done
      | Cons r s => Cons (lift r) (lift_scheduler s)
      | Try r s1 s2 => Try (lift r) (lift_scheduler s1) (lift_scheduler s2)
      | SPos pos s => SPos pos (lift_scheduler s)
      end.

  End ScheduleLift.

End ModuleLift.

Module SecurityMonitor (External: External_sig) (Params: EnclaveParameters).
  Inductive internal_reg_t := .
  Definition R_internal_reg (idx: internal_reg_t) : type :=
    match idx with end.

  Definition r_internal_reg (idx: internal_reg_t) : R_internal_reg idx :=
    match idx with end.

  Instance FiniteType_internal_reg_t : FiniteType internal_reg_t := _.

  Import Common.

  Inductive reg_t : Type :=
  | FromCore0_IMem (state: MemReq.reg_t)
  | FromCore0_DMem (state: MemReq.reg_t)
  | ToCore0_IMem (state: MemResp.reg_t)
  | ToCore0_DMem (state: MemResp.reg_t)
  (* Core1 <-> SM *)
  | FromCore1_IMem (state: MemReq.reg_t)
  | FromCore1_DMem (state: MemReq.reg_t)
  | ToCore1_IMem (state: MemResp.reg_t)
  | ToCore1_DMem (state: MemResp.reg_t)
  (* SM <-> Mem *)
  | ToMem0_IMem (state: MemReq.reg_t)
  | ToMem0_DMem (state: MemReq.reg_t)
  | ToMem1_IMem (state: MemReq.reg_t)
  | ToMem1_DMem (state: MemReq.reg_t)
  | FromMem0_IMem (state: MemResp.reg_t)
  | FromMem0_DMem (state: MemResp.reg_t)
  | FromMem1_IMem (state: MemResp.reg_t)
  | FromMem1_DMem (state: MemResp.reg_t)
  | internal (idx: internal_reg_t)
  .

  Definition R (idx: reg_t) :=
    match idx with
    | FromCore0_IMem st => MemReq.R st
    | FromCore0_DMem st => MemReq.R st
    | ToCore0_IMem st => MemResp.R st
    | ToCore0_DMem st => MemResp.R st
    (* Core1 <-> SM *)
    | FromCore1_IMem st => MemReq.R st
    | FromCore1_DMem st => MemReq.R st
    | ToCore1_IMem st => MemResp.R st
    | ToCore1_DMem st => MemResp.R st
    (* SM <-> Mem *)
    | ToMem0_IMem st => MemReq.R st
    | ToMem0_DMem st => MemReq.R st
    | ToMem1_IMem st => MemReq.R st
    | ToMem1_DMem st => MemReq.R st
    | FromMem0_IMem st => MemResp.R st
    | FromMem0_DMem st => MemResp.R st
    | FromMem1_IMem st => MemResp.R st
    | FromMem1_DMem st => MemResp.R st
    | internal st => R_internal_reg st
    end.

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition Sigma := External.Sigma.
  Definition ext_fn_t := External.ext_fn_t.
  Definition state := env_t ContextEnv (fun idx : reg_t => R idx).

  (* Placeholder rule; do nothing *)
  Definition forward : uaction reg_t ext_fn_t :=
    {{ (when (FromCore0_IMem.(MemReq.can_deq)() &&
              ToMem0_IMem.(MemReq.can_enq)()) do
         let req := FromCore0_IMem.(MemReq.deq)() in
         ToMem0_IMem.(MemReq.enq)(req)
       );
       (when (FromCore1_IMem.(MemReq.can_deq)() &&
              ToMem1_IMem.(MemReq.can_enq)()) do
         let req := FromCore1_IMem.(MemReq.deq)() in
         ToMem1_IMem.(MemReq.enq)(req)
       );
       (when (FromCore0_DMem.(MemReq.can_deq)() &&
              ToMem0_DMem.(MemReq.can_enq)()) do
         let req := FromCore0_DMem.(MemReq.deq)() in
         ToMem0_DMem.(MemReq.enq)(req)
       );
       (when (FromCore1_DMem.(MemReq.can_deq)() &&
              ToMem1_DMem.(MemReq.can_enq)()) do
         let req := FromCore1_DMem.(MemReq.deq)() in
         ToMem1_DMem.(MemReq.enq)(req)
       );
       (when (FromMem0_IMem.(MemResp.can_deq)() &&
              ToCore0_IMem.(MemResp.can_enq)()) do
         let req := FromMem0_IMem.(MemResp.deq)() in
         ToCore0_IMem.(MemResp.enq)(req)
       );
       (when (FromMem1_IMem.(MemResp.can_deq)() &&
              ToCore1_IMem.(MemResp.can_enq)()) do
         let req := FromMem1_IMem.(MemResp.deq)() in
         ToCore1_IMem.(MemResp.enq)(req)
       );
       (when (FromMem0_DMem.(MemResp.can_deq)() &&
              ToCore0_DMem.(MemResp.can_enq)()) do
         let req := FromMem0_DMem.(MemResp.deq)() in
         ToCore0_DMem.(MemResp.enq)(req)
       );
       (when (FromMem1_DMem.(MemResp.can_deq)() &&
              ToCore1_DMem.(MemResp.can_enq)()) do
         let req := FromMem1_DMem.(MemResp.deq)() in
         ToCore1_DMem.(MemResp.enq)(req)
       )
    }}.

  Definition tc_forward := tc_rule R Sigma forward <: rule R Sigma.

  Inductive rule_name_t := | Forward.

  Definition rules (rl : rule_name_t) : rule R Sigma :=
    match rl with
    | Forward => tc_forward
    end.

  Definition schedule : Syntax.scheduler pos_t rule_name_t :=
    Forward |> done.

End SecurityMonitor.

Module Type Memory_sig (External: External_sig).
  Parameter internal_reg_t : Type.
  Parameter R_internal_reg : internal_reg_t -> type.
  Parameter r_internal_reg : (forall (idx: internal_reg_t), R_internal_reg idx).

  Import Common.

  Declare Instance FiniteType_internal_reg_t : FiniteType internal_reg_t.

  Inductive reg_t :=
  | ToIMem0 (state: MemReq.reg_t)
  | ToIMem1 (state: MemReq.reg_t)
  | ToDMem0 (state: MemReq.reg_t)
  | ToDMem1 (state: MemReq.reg_t)
  | FromIMem0 (state: MemResp.reg_t)
  | FromIMem1 (state: MemResp.reg_t)
  | FromDMem0 (state: MemResp.reg_t)
  | FromDMem1 (state: MemResp.reg_t)
  | internal (r: internal_reg_t)
  .

  Definition R (idx: reg_t) :=
    match idx with
    | ToIMem0 st => MemReq.R st
    | ToIMem1 st => MemReq.R st
    | ToDMem0 st => MemReq.R st
    | ToDMem1 st => MemReq.R st
    | FromIMem0 st => MemResp.R st
    | FromIMem1 st => MemResp.R st
    | FromDMem0 st => MemResp.R st
    | FromDMem1 st => MemResp.R st
    | internal st => R_internal_reg st
    end.

  Declare Instance FiniteType_reg_t : FiniteType reg_t.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  Definition sigma := External.sigma.

  Parameter rule_name_t : Type.
  Parameter rules  : rule_name_t -> rule.

  Axiom schedule : Syntax.scheduler pos_t rule_name_t.

  Definition state := env_t ContextEnv (fun idx : reg_t => R idx).

End Memory_sig.

Module Machine (External: External_sig) (EnclaveParams: EnclaveParameters)
               (Params0: CoreParameters) (Params1: CoreParameters)
               (Core: Core_sig External EnclaveParams) (Memory: Memory_sig External).

  Module Core0 := Core Params0.
  Module Core1 := Core Params1.

  Module SM := SecurityMonitor External EnclaveParams.

  Include Common.

  Inductive reg_t : Type :=
  | core_id0
  | core_id1
  | pc0
  | pc1
  (* TODO: reset memory *)
  (* Core0 <-> SM *)
  | Core0ToSM_IMem (state: MemReq.reg_t)
  | Core0ToSM_DMem (state: MemReq.reg_t)
  | SMToCore0_IMem (state: MemResp.reg_t)
  | SMToCore0_DMem (state: MemResp.reg_t)
  (* Core1 <-> SM *)
  | Core1ToSM_IMem (state: MemReq.reg_t)
  | Core1ToSM_DMem (state: MemReq.reg_t)
  | SMToCore1_IMem (state: MemResp.reg_t)
  | SMToCore1_DMem (state: MemResp.reg_t)
  (* SM <-> Mem *)
  | SMToMem0_IMem (state: MemReq.reg_t)
  | SMToMem0_DMem (state: MemReq.reg_t)
  | SMToMem1_IMem (state: MemReq.reg_t)
  | SMToMem1_DMem (state: MemReq.reg_t)
  | MemToSM0_IMem (state: MemResp.reg_t)
  | MemToSM0_DMem (state: MemResp.reg_t)
  | MemToSM1_IMem (state: MemResp.reg_t)
  | MemToSM1_DMem (state: MemResp.reg_t)
  (* Internal registers *)
  | Core0_internal (state: Core0.internal_reg_t)
  | Core1_internal (state: Core1.internal_reg_t)
  | SM_internal (state: SM.internal_reg_t)
  | Mem_internal (state: Memory.internal_reg_t)
  .

  Definition R (idx: reg_t) : type :=
    match idx with
    | core_id0 => bits_t 1
    | core_id1 => bits_t 1
    | pc0 => bits_t 32
    | pc1 => bits_t 32
    (* TODO: reset memory *)
    (* Core0 <-> SM *)
    | Core0ToSM_IMem st => MemReq.R st
    | Core0ToSM_DMem st => MemReq.R st
    | SMToCore0_IMem st => MemResp.R st
    | SMToCore0_DMem st => MemResp.R st
    (* Core1 <-> SM *)
    | Core1ToSM_IMem st => MemReq.R st
    | Core1ToSM_DMem st => MemReq.R st
    | SMToCore1_IMem st => MemResp.R st
    | SMToCore1_DMem st => MemResp.R st
    (* SM <-> Mem *)
    | SMToMem0_IMem st => MemReq.R st
    | SMToMem0_DMem st => MemReq.R st
    | SMToMem1_IMem st => MemReq.R st
    | SMToMem1_DMem st => MemReq.R st
    | MemToSM0_IMem st => MemResp.R st
    | MemToSM0_DMem st => MemResp.R st
    | MemToSM1_IMem st => MemResp.R st
    | MemToSM1_DMem st => MemResp.R st
    (* Internal registers *)
    | Core0_internal st => Core0.R_internal_reg st
    | Core1_internal st => Core1.R_internal_reg st
    | SM_internal st => SM.R_internal_reg st
    | Mem_internal st => Memory.R_internal_reg st
    end.

  Definition Sigma := External.Sigma.
  Definition rule : Type := rule R Sigma.

  (* TODO: 40s *)
  (* Instance FiniteType_reg_t : FiniteType reg_t := _. *)
  Declare Instance FiniteType_reg_t : FiniteType reg_t.

  Instance EqDec_reg_t : EqDec reg_t := _.

  Inductive rule_name_t :=
  | Core0Rule (r: Core0.rule_name_t)
  | Core1Rule (r: Core1.rule_name_t)
  | SmRule   (r: SM.rule_name_t)
  | MemRule  (r: Memory.rule_name_t)
  .

  Import ModuleLift.

  Section Core0_Lift.
    Definition core0_lift (reg: Core0.reg_t) : reg_t :=
      match reg with
      | Core0.core_id => core_id0
      | Core0.ToIMem s => Core0ToSM_IMem s
      | Core0.ToDMem s => Core0ToSM_DMem s
      | Core0.FromIMem s => SMToCore0_IMem s
      | Core0.FromDMem s => SMToCore0_DMem s
      | Core0.internal s => Core0_internal s
      end.

    Definition Lift_core0 : RLift Core0.reg_t reg_t Core0.R R := ltac:(mk_rlift core0_lift).

    Definition core0_rule_name_lift (rl: Core0.rule_name_t) : rule_name_t :=
      Core0Rule rl.

  End Core0_Lift.

  Section Core1_Lift.
    Definition core1_lift (reg: Core1.reg_t) : reg_t :=
      match reg with
      | Core1.core_id => core_id1
      | Core1.ToIMem s => Core1ToSM_IMem s
      | Core1.ToDMem s => Core1ToSM_DMem s
      | Core1.FromIMem s => SMToCore1_IMem s
      | Core1.FromDMem s => SMToCore1_DMem s
      | Core1.internal s => Core1_internal s
      end.

    Definition Lift_core1 : RLift Core1.reg_t reg_t Core1.R R := ltac:(mk_rlift core1_lift).

    Definition core1_rule_name_lift (rl: Core1.rule_name_t) : rule_name_t :=
      Core1Rule rl.

  End Core1_Lift.

  Section SM_Lift.

    Definition sm_lift (reg: SM.reg_t) : reg_t :=
      match reg with
      | SM.FromCore0_IMem st => Core0ToSM_IMem st
      | SM.FromCore0_DMem st => Core0ToSM_DMem st
      | SM.ToCore0_IMem st => SMToCore0_IMem st
      | SM.ToCore0_DMem st => SMToCore0_DMem st
      (* Core1 <-> SM *)
      | SM.FromCore1_IMem st => Core1ToSM_IMem st
      | SM.FromCore1_DMem st => Core1ToSM_DMem st
      | SM.ToCore1_IMem st => SMToCore1_IMem st
      | SM.ToCore1_DMem st => SMToCore1_DMem st
      (* SM <-> Mem *)
      | SM.ToMem0_IMem st => SMToMem0_IMem st
      | SM.ToMem0_DMem st => SMToMem0_DMem st
      | SM.ToMem1_IMem st => SMToMem1_IMem st
      | SM.ToMem1_DMem st => SMToMem1_DMem st
      | SM.FromMem0_IMem st => MemToSM0_IMem st
      | SM.FromMem0_DMem st => MemToSM0_DMem st
      | SM.FromMem1_IMem st => MemToSM1_IMem st
      | SM.FromMem1_DMem st => MemToSM1_DMem st
      | SM.internal st => SM_internal st
      end.

    Definition Lift_sm : RLift SM.reg_t reg_t SM.R R := ltac:(mk_rlift sm_lift).

    Definition sm_rule_name_lift (rl: SM.rule_name_t) : rule_name_t :=
      SmRule rl.

  End SM_Lift.

  Section Mem_Lift.
    Definition mem_lift (reg: Memory.reg_t) : reg_t :=
      match reg with
      | Memory.ToIMem0 st => SMToMem0_IMem st
      | Memory.ToIMem1 st => SMToMem1_IMem st
      | Memory.ToDMem0 st => SMToMem0_DMem st
      | Memory.ToDMem1 st => SMToMem1_DMem st
      | Memory.FromIMem0 st => MemToSM0_IMem st
      | Memory.FromIMem1 st => MemToSM1_IMem st
      | Memory.FromDMem0 st => MemToSM0_DMem st
      | Memory.FromDMem1 st => MemToSM1_DMem st
      | Memory.internal st => Mem_internal st
      end.

    Definition Lift_mem : RLift Memory.reg_t reg_t Memory.R R := ltac:(mk_rlift mem_lift).

    Definition mem_rule_name_lift (rl: Memory.rule_name_t) : rule_name_t :=
      MemRule rl.

  End Mem_Lift.

End Machine.
