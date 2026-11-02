/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliarySnocTrace
public import LeanCanny.Geometry.CanonicalAuxiliaryInitialFrame
public import LeanCanny.Algebra.IntegralMixedFramedStateTransport

/-! # Literal source-framed scripts extracted from actual sampling traces

The chronological induction appends each proved tagged limit birth. Final
comparison explicitly reframes the bank-only result at the terminal source;
it does not identify the family's default source with that source.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory
open IntegralMixedFramedHistoryScript (Instruction Index run)
open AuxiliaryTiltedTerm SampleFrame
open scoped Classical
attribute [local irreducible] source
variable {n S B D : ℕ} {t : Term} {ht : (term n t).degreeBound≤D}

def IsLimitInstruction {p W : ℕ} (c : Instruction p W) : Prop :=
  match c.command with
  | .cut _ (.limitCoordinate ..) .. => True
  | _ => False

theorem SnocTrace.exists_framed_run (hn : n≤S)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    {r : ℕ} {L : SampleFrame n S B D t ht} (H : SnocTrace hcap (initialFrame t ht hn hcap) r L) :
    ∃ cs : List (Instruction (n+2) B), ∃ _ : cs.length=r, ∃ hcs : cs.length≤S+1,
      (∀ c∈cs, IsLimitInstruction c) ∧ Index (Fin 0) cs=L.carrier ∧
      HEq (reframe (run (initialState (S:=S) t ht hcap) cs hcs)
        (source L.frozen D t ht L.birth B L.height) L.state.critical_cap) L.state := by
  induction H with
  | nil =>
    refine ⟨[],rfl,by simp,by simp,rfl,?_⟩
    change HEq (reframe (initialState (S:=S) t ht hcap) _ (initialState (S:=S) t ht hcap).critical_cap) (initialState (S:=S) t ht hcap)
    rw [reframe_same]
  | @snoc G r prior hk b W ih =>
    obtain ⟨cs,hlen,hcs,hLimit,hIndex,hState⟩ := ih
    let _ := G.finite
    let c0 : Instruction (n+2) B := IntegralMixedLimitCoordinate.instruction G.state (criticalRule G)
      (coordinate G) W.choice W.degree W.degree_le
    let L := W.frame hcap
    have HB : cs.length=G.birth := by
      have HC := prior.toForward.birth_count
      change G.birth=0+r at HC
      omega
    have HM : cs.length≤S := HB.trans_le (birth_le G)
    have HH : (c0::cs).length≤S+1 := by simp only [List.length_cons]; omega
    have HI : Index (Fin 0) (c0::cs)=L.carrier := by
      change (Index (Fin 0) cs ⊕ Unit)=(G.carrier ⊕ Unit)
      exact congrArg (fun α : Type => α ⊕ Unit) hIndex
    let R := source L.frozen D t ht L.birth B L.height
    have HS := IntegralMixedFramedStateTransport.step_reframe_heq
      (reframe (run (initialState (S:=S) t ht hcap) cs hcs)
        (source G.frozen D t ht G.birth B G.height) G.state.critical_cap)
      G.state HB hIndex hState HM (birth_le G) c0.command R L.state.critical_cap
    have HR : reframe (IntegralMixedFullHistoryScript.step G.state (birth_le G) c0.command)
        R L.state.critical_cap=L.state := by
      dsimp only [R,L,CutWitness.frame,SampleFrame.child,SampleFrame.cutState,nextState,c0,
        IntegralMixedLimitCoordinate.instruction,IntegralMixedDilationAdvance.advance,reframeDegree]
      unfold source SampleFrame.criticalRule
      rfl
    have HLimits : ∀ c∈c0::cs, IsLimitInstruction c := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · trivial
      · exact hLimit c hc
    refine ⟨c0::cs,by simp only [List.length_cons,hlen],HH,HLimits,HI,?_⟩
    have HL : reframe (run (initialState (S:=S) t ht hcap) (c0::cs) HH) R L.state.critical_cap=
        reframe (IntegralMixedFullHistoryScript.step
          (reframe (run (initialState (S:=S) t ht hcap) cs hcs)
            (source G.frozen D t ht G.birth B G.height) G.state.critical_cap) HM c0.command)
          R L.state.critical_cap := rfl
    exact (heq_of_eq HL).trans (HS.trans (heq_of_eq HR))

theorem SampleTrace.exists_framed_run (hn : n≤S)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    {r : ℕ} {L : SampleFrame n S B D t ht} (H : SampleTrace hcap (initialFrame t ht hn hcap) r L) :
    ∃ cs : List (Instruction (n+2) B), ∃ _ : cs.length=r, ∃ hcs : cs.length≤S+1,
      (∀ c∈cs, IsLimitInstruction c) ∧ Index (Fin 0) cs=L.carrier ∧
      HEq (reframe (run (initialState (S:=S) t ht hcap) cs hcs)
        (source L.frozen D t ht L.birth B L.height) L.state.critical_cap) L.state :=
  H.toSnoc.exists_framed_run hn hcap

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
