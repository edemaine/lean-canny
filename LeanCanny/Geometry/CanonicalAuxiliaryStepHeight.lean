/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryContinuation
public import LeanCanny.Algebra.IntegralMixedFramedStepHeight
public import LeanCanny.Algebra.IntegralMixedCausalLevelLowHeight
/-! # The actual limit birth derives its next bank-height charge

The old bank and original LOW syntax determine the source charge before the
cut. The tagged command then supplies the next bank bound by the existing
interpreter theorem. Reframing chooses a new causal level from that bound.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory IntegralMixedCriticalSweep
open AuxiliaryTiltedTerm IntegralMixedCanonicalDilation IntegralMixedDilationAdvance
open IntegralMixedCausalLevelCapacity IntegralMixedCausalLevelSchedule
open scoped Classical BigOperators

private theorem height_nodes {n k m : ℕ} (select : Fin k → Fin m) (i : Fin (n+2)) :
    (heightExpr select i).nodes=1 := by
  unfold heightExpr
  split_ifs <;> rfl

private theorem height_coefficients {n k m : ℕ} (select : Fin k → Fin m) (i : Fin (n+2)) (C : ℕ) :
    (heightExpr select i).CoefficientsBound C := by
  unfold heightExpr
  split_ifs <;> first | exact Nat.zero_le C | trivial

def sourceFactor (n S B D : ℕ) := cfactor (n+1) D (IntegralMixedFullScriptHeight.rank S B)
def nextHeight (n S B D G : ℕ) :=
  IntegralMixedFramedStepHeight.growth (n+2) S B (FixedLeadingTiltedSource.degree D).size
    (FixedLeadingTiltedSource.degree D) 1 (sourceFactor n S B D+2)*G

theorem le_nextHeight (n S B D G : ℕ) : G≤nextHeight n S B D G := by
  simpa only [nextHeight,one_mul] using Nat.mul_le_mul_right G
    (IntegralMixedFramedStepHeight.growth_pos (n+2) S B (FixedLeadingTiltedSource.degree D).size
      (FixedLeadingTiltedSource.degree D) 1 (sourceFactor n S B D+2))

theorem nextHeight_pos (n S B D G : ℕ) (hG : 1≤G) : 1≤nextHeight n S B D G :=
  hG.trans (le_nextHeight n S B D G)

def wordBudget (n D : ℕ) (t : Term) : ℕ :=
  ∑ j : Fin (n+1), (FixedLeadingTiltedSource.lowTerm j.val D (Fin.last n).val (term n t)).toData.size

theorem word_le_budget (n k D : ℕ) (t : Term) (hk : k≤n) :
    (FixedLeadingTiltedSource.lowTerm k D (Fin.last n).val (term n t)).toData.size≤wordBudget n D t := by
  unfold wordBudget
  exact Finset.single_le_sum (f:=fun j : Fin (n+1) => (FixedLeadingTiltedSource.lowTerm j.val D (Fin.last n).val (term n t)).toData.size) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨k,by omega⟩ : Fin (n+1)))

variable {n k D S B m G : ℕ} {t : Term} {ht : (term n t).degreeBound≤D} {ι : Type}

theorem source_exponent_bound (hm : m≤S) (hG : 1≤G) :
    exponent (n+1) D (FixedWidthPolynomial.count m B) G≤sourceFactor n S B D*G := by
  have HR : FixedWidthPolynomial.count m B≤IntegralMixedFullScriptHeight.rank S B :=
    Nat.pow_le_pow_right (Nat.two_pow_pos B) (by omega : m≤S+2)
  exact (exponent_linear_of_pos (n+1) D _ G hG).trans
    (Nat.mul_le_mul_right G (cfactor_mono (n:=n+1) (D:=D) HR))

theorem limit_command_bounds (x : State (source k D t ht m B G) S B m ι)
    (hk : k≤n+1) (select : Fin k → Fin m)
    (j : Fin (n+2-(rule hk select).critical.offset.val+1))
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source k D t ht m B G) (rule hk select)))
    (d C : ℕ) (hd : d≤IntegralMixedLimitCoordinate.degree (source k D t ht m B G) (rule hk select))
    (hC : 1≤C) :
    IntegralMixedFullScriptHeight.CommandBounds C 1 (IntegralMixedLimitCoordinate.command x (rule hk select) j c d hd) := by
  change (∀ i, (heightExpr select i).nodes≤1) ∧ (∀ i, (heightExpr select i).CoefficientsBound C) ∧
    (∀ _ : Fin (n+3), (1:ℤ).natAbs.size≤C) ∧ (1:ℤ).natAbs.size≤C
  refine ⟨fun i => (height_nodes select i).le,fun i => height_coefficients select i C,?_,?_⟩
  · intro _
    simpa only [Int.natAbs_one,Nat.size_one] using hC
  · simpa only [Int.natAbs_one,Nat.size_one] using hC

variable [Fintype ι]

theorem limit_bank_bounds (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (HG : x.bank.Bounds G) (hG : 1≤G)
    (hword : (FixedLeadingTiltedSource.lowTerm k D (Fin.last n).val (term n t)).toData.size≤G)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (hk : k≤n+1) (select : Fin k → Fin m)
    (j : Fin (n+2-(rule hk select).critical.offset.val+1))
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source k D t ht m B G) (rule hk select)))
    (d : ℕ) (hd : d≤IntegralMixedLimitCoordinate.degree (source k D t ht m B G) (rule hk select)) :
    (IntegralMixedFullHistoryScript.step x hm (IntegralMixedLimitCoordinate.command x (rule hk select) j c d hd)).bank.Bounds
      (nextHeight n S B D G) := by
  have HE := source_exponent_bound (n:=n) (D:=D) (B:=B) hm hG
  have HL := IntegralMixedCausalLevelLowHeight.tilted_source_coefficient (Fin.last n) (term n t) ht
    (Nat.le_refl _) hG hword HE
  have HI : IntegralMixedFramedStepHeight.InstructionBounds G (sourceFactor n S B D+2)
      (FixedLeadingTiltedSource.degree D).size (FixedLeadingTiltedSource.degree D) 1
      (IntegralMixedLimitCoordinate.instruction x (rule hk select) j c d hd) := {
    low := fun e => (HL e).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
    leading := by
      simp only [IntegralMixedLimitCoordinate.instruction,source,FermatLevelLift.source,FixedLeadingTiltedSource.source,
        Int.natAbs_one,Nat.size_one]
      omega
    width := Nat.le_refl _
    degree := Nat.le_refl _
    auxiliary := hcap
    command := limit_command_bounds x hk select j c d _ hd (by omega) }
  have HB := IntegralMixedFramedStepHeight.step_bounds x hm
    (IntegralMixedLimitCoordinate.instruction x (rule hk select) j c d hd) G (sourceFactor n S B D+2)
    (FixedLeadingTiltedSource.degree D).size (FixedLeadingTiltedSource.degree D) 1 HG hG HI
  dsimp only [IntegralMixedLimitCoordinate.instruction] at HB
  rw [reframe_same] at HB
  simpa only [nextHeight] using HB

theorem advanced_limit_bank_bounds (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (HG : x.bank.Bounds G) (hG : 1≤G)
    (hword : (FixedLeadingTiltedSource.lowTerm k D (Fin.last n).val (term n t)).toData.size≤G)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (hk : k≤n+1) (select : Fin k → Fin m)
    (j : Fin (n+2-(rule hk select).critical.offset.val+1))
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source k D t ht m B G) (rule hk select)))
    (d : ℕ) (hd : d≤IntegralMixedLimitCoordinate.degree (source k D t ht m B G) (rule hk select)) (nextA : ℤ) :
    (advance (IntegralMixedFullHistoryScript.step x hm (IntegralMixedLimitCoordinate.command x (rule hk select) j c d hd))
      (Fin.last n) nextA).bank.Bounds (nextHeight n S B D G) :=
  limit_bank_bounds x hm HG hG hword hcap hk select j c d hd

noncomputable def nextState (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (hk : k≤n+1) (select : Fin k → Fin m)
    (j : Fin (n+2-(rule hk select).critical.offset.val+1))
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source k D t ht m B G) (rule hk select)))
    (d : ℕ) (hd : d≤IntegralMixedLimitCoordinate.degree (source k D t ht m B G) (rule hk select)) :
    State (source (k+1) D t ht (m+1) B (nextHeight n S B D G)) S B (m+1) (ι ⊕ Unit) :=
  advance (IntegralMixedFullHistoryScript.step x hm (IntegralMixedLimitCoordinate.command x (rule hk select) j c d hd))
    (Fin.last n) (coefficient (n+1) D (FixedWidthPolynomial.count (m+1) B) (nextHeight n S B D G))

theorem nextState_bank_bounds (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (HG : x.bank.Bounds G) (hG : 1≤G)
    (hword : (FixedLeadingTiltedSource.lowTerm k D (Fin.last n).val (term n t)).toData.size≤G)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (hk : k≤n+1) (select : Fin k → Fin m)
    (j : Fin (n+2-(rule hk select).critical.offset.val+1))
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source k D t ht m B G) (rule hk select)))
    (d : ℕ) (hd : d≤IntegralMixedLimitCoordinate.degree (source k D t ht m B G) (rule hk select)) :
    (nextState x hm hk select j c d hd).bank.Bounds (nextHeight n S B D G) :=
  advanced_limit_bank_bounds x hm HG hG hword hcap hk select j c d hd _

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
