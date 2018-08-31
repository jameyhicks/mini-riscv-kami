(*
	coqtop -R ../../../kami/Kami Kami -R $PWD BK 
*)

Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer Lib.Struct.
Require Import Bsvtokami.
Require Import MiniRiscvMMode.
Require Import Kami.Duplicate.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Definition spec := ProcMMode'modules (mkMiniRiscvMMode "spec" ($$(natToWord 1 0))%kami ($$ (natToWord 1 0))%kami ($$ (natToWord 1 0))%kami).
Definition impl := ProcMMode'modules (mkMiniRiscvMMode "impl" ($$(natToWord 1 0))%kami ($$ (natToWord 1 0))%kami ($$ (natToWord 1 0))%kami).

Check spec.
Check impl.

Compute (map (fun reg => (attrName reg)) (getRegInits (spec))).

Hint Unfold spec impl: ModuleDefs.

Definition spec_impl_ruleMap (_: RegsT): string -> option string :=
  fun regname => Some regname.

Compute 1.

Lemma spec_ModEquiv:
  ModPhoasWf spec.
Proof. kequiv. Qed.
Hint Resolve spec_ModEquiv.

Compute 2.

Lemma impl_ModEquiv:
  ModPhoasWf impl.
Proof. kequiv. Qed.
Hint Resolve impl_ModEquiv.

Compute 3.

Require Import Kami.Wf.
Require Import Lib.Reflection.
Require Import Lib.StringEq.

Definition Is_true (b : bool) :=
  match b with
  | true => True
  | false => False
  end.

Theorem eqb_a_a:
  (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
    simpl. exact I.
    simpl. exact I.
Qed.

Theorem spec_impl_refinement:
  impl <<== spec.
Proof.
  (* repeat autounfold with ModuleDefs. *)
  apply traceRefines_inlining_left.
  apply impl_ModEquiv.
  kinline_compute.
  noDup_tac.
  remember (inlineF impl) as im eqn:Heq.
  repeat autounfold with ModuleDefs in Heq.

  cbv [string_eq attrName withPrefix append prefixSymbol] in Heq.
  cbv [inlineF inline inlineDms inlineDms'
               inlineDmToMod inlineDmToRules inlineDmToRule
               inlineDmToDms inlineDmToDm inlineDm
               filterDms filter
               noInternalCalls noCalls
               noCallsRules noCallsDms noCallDm isLeaf
               getBody inlineArg
               appendAction getAttribute
               makeModule makeModule' max plus
	       ] in Heq.

  cbv [getDefsBodies namesOf filter map app attrName string_eq ascii_eq] in Heq.
  rewrite eqb_reflx in Heq.
  rewrite andb_diag in Heq.

  cbv [getDefsBodies namesOf filter map app attrName string_eq ascii_eq andb orb negb] in Heq.

  cbv [inlineF inline inlineDms inlineDms'
               inlineDmToMod inlineDmToRules inlineDmToRule
               inlineDmToDms inlineDmToDm inlineDm
               filterDms filter
               noInternalCalls noCalls
               noCallsRules noCallsDms noCallDm isLeaf
               getBody inlineArg
               appendAction getAttribute
               makeModule makeModule' max plus
               getRegInits getDefs getDefsBodies getRules namesOf
               map app attrName attrType
               getCalls getCallsR getCallsM getCallsA
	       ] in Heq.


  cbv [inlineF inline inlineDms inlineDms'
               inlineDmToMod inlineDmToRules inlineDmToRule
               inlineDmToDms inlineDmToDm inlineDm
               filterDms filter
               noInternalCalls noCalls
               noCallsRules noCallsDms noCallDm isLeaf
               getBody inlineArg
               appendAction getAttribute
               makeModule makeModule' max plus
               getRegInits getDefs getDefsBodies getRules namesOf
               map app attrName attrType
               getCalls getCallsR getCallsM getCallsA
               ret arg fst snd projT1 projT2
               string_in string_eq ascii_eq
               eqb existsb andb orb negb] in Heq.

  (* kinline_left implInlined. *)

  kdecompose_nodefs spec_impl_regMap spec_impl_ruleMap.
Qed.
