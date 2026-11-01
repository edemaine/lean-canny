/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutMatrix
public import LeanCanny.Algebra.IntegralMixedBankCanonical
/-! # Actual mixed commands including normalized relative-cut births

Every command adds one scalar-prefix digit. Only the critical-point
command adds the auxiliary physical variables. Relative cuts use their
literal polynomial over the current retained algebra and exact truncation.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHistoryScript
open LeanCanny.Encoding LeanCanny.Computation IntegralHistorySampler UniformIntegralPrefix
open IntegralMixedHistory
open scoped Classical

inductive Command {n : ℕ} (P : SpatialSource n) (B : ℕ) where
  | integer (polynomial : Polynomial ℤ) (nonzero : polynomial ≠ 0) (degree_cap : polynomial.natDegree ≤ 2 ^ B)
  | critical (rule : CriticalRule n)
  | cut (rule : IntegralMixedCriticalSweep.Rule n) (kind : IntegralMixedRelativeCuts.Kind P rule)
      (degree : ℕ) (source_cap : degree ≤ IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree)
      (degree_cap : degree ≤ 2 ^ B)

def Command.isCritical {n B : ℕ} {P : SpatialSource n} : Command P B → Bool
  | .critical _ => true
  | _ => false

def NextIndex {n B : ℕ} {P : SpatialSource n} (ι : Type) : Command P B → Type
  | .integer .. => ι ⊕ Unit
  | .critical _ => (ι ⊕ FlatAffineCriticalStage.Variables (n + 1)) ⊕ Unit
  | .cut .. => ι ⊕ Unit

instance nextFintype {n B : ℕ} {P : SpatialSource n} (ι : Type) [Fintype ι] (c : Command P B) : Fintype (NextIndex ι c) := by
  cases c <;> dsimp only [NextIndex] <;> infer_instance

noncomputable def polynomial {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) : Command P B → Polynomial x.sampler.scalarPrefix.carrier
  | .integer p _ _ => p.map (Int.castRingHom x.sampler.scalarPrefix.carrier)
  | .critical r => criticalPolynomial x hm r
  | .cut r k d _ _ => normalizedScalarPolynomial x (IntegralMixedCutMatrix.raw x hm r k d) d

def degree {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) : Command P B → ℕ
  | .integer p _ _ => p.natDegree
  | .critical r => criticalDegree x hm r
  | .cut _ _ d _ _ => d

noncomputable def leading {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) : Command P B → ℤ
  | .integer p _ _ => p.leadingCoeff
  | .critical r => criticalLeading x hm r
  | .cut r k d _ _ => normalizedScalarLeading x (IntegralMixedCutMatrix.raw x hm r k d) d

theorem degree_cap {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (c : Command P B) : degree x hm c ≤ 2 ^ B := by
  cases c with
  | integer _ _ h => exact h
  | critical r => exact criticalDegree_cap x hm r
  | cut _ _ _ _ h => exact h

theorem leading_ne_zero {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (c : Command P B) : leading x hm c ≠ 0 := by
  cases c with
  | integer _ h _ => exact Polynomial.leadingCoeff_ne_zero.mpr h
  | critical r => exact criticalLeading_ne_zero x hm r
  | cut r k d _ _ => exact IntegralRelativeLeadingNormalization.denominator_ne_zero _ _

theorem leading_coefficient {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (c : Command P B) :
    (polynomial x hm c).coeff (degree x hm c) = (leading x hm c : x.sampler.scalarPrefix.carrier) := by
  cases c with
  | integer p _ _ => simp only [polynomial, degree, leading, Polynomial.coeff_map, Polynomial.coeff_natDegree]; rfl
  | critical r => exact criticalLeading_coefficient x hm r
  | cut r k d _ _ => exact IntegralRelativeLeadingNormalization.coefficient _ _ _

noncomputable def step {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) : (c : Command P B) → State P S B (m + 1) (NextIndex ι c)
  | .integer p hp hd => integerStep x hm p hp hd
  | .critical r => IntegralMixedHistory.criticalStep x hm r
  | .cut r k d _ _ => IntegralMixedRelativeCuts.step x hm r k d

theorem step_prefix {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (c : Command P B) :
    (step x hm c).sampler.scalarPrefix = UniformIntegralPrefix.step x.sampler.scalarPrefix hm
      (Nat.two_pow_pos B) (polynomial x hm c) (degree x hm c) := by cases c <;> rfl

theorem step_denominator_zero {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (c : Command P B) :
    (step x hm c).bank.denominator 0 = leading x hm c := by cases c <;> rfl

theorem step_denominator_succ {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (c : Command P B) (i : Fin m) :
    (step x hm c).bank.denominator i.succ = x.bank.denominator i := by cases c <;> rfl

def Index {n B : ℕ} {P : SpatialSource n} (ι : Type) : List (Command P B) → Type
  | [] => ι
  | c :: cs => NextIndex (Index ι cs) c

instance indexFintype {n B : ℕ} {P : SpatialSource n} (ι : Type) [Fintype ι] : (cs : List (Command P B)) → Fintype (Index ι cs)
  | [] => inferInstanceAs (Fintype ι)
  | c :: cs => by
    change Fintype (NextIndex (Index ι cs) c)
    letI := indexFintype ι cs
    exact nextFintype _ c

noncomputable def run {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) : (cs : List (Command P B)) → cs.length ≤ S + 1 → State P S B cs.length (Index ι cs)
  | [], _ => initial
  | c :: cs, hcs => step (run initial cs (by simp only [List.length_cons] at hcs; omega))
      (by simp only [List.length_cons] at hcs; omega) c

noncomputable def continueRun {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B m ι) : (cs : List (Command P B)) → m + cs.length ≤ S + 1 → State P S B (m + cs.length) (Index ι cs)
  | [], _ => initial
  | c :: cs, hcs => step (continueRun initial cs (by simp only [List.length_cons] at hcs; omega))
      (by simp only [List.length_cons] at hcs; omega) c

def criticalCount {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) := cs.countP Command.isCritical

theorem physical_arity {n B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι] (cs : List (Command P B)) :
    Fintype.card (Index ι cs) = Fintype.card ι + cs.length + (2 * n + 3) * criticalCount cs := by
  induction cs with
  | nil => simp only [Index, List.length_nil, criticalCount, List.countP_nil, Nat.mul_zero, Nat.add_zero]; rfl
  | cons c cs ih =>
    cases c <;> simp only [Index, NextIndex, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unique, FlatAffineCriticalStage.Variables, List.length_cons, criticalCount,
      List.countP_cons, Command.isCritical, Bool.false_eq_true, ite_true, ite_false]
    all_goals rw [ih]
    all_goals unfold criticalCount
    all_goals ring

theorem step_canonical {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (H : Canonical x) (hm : m ≤ S) (c : Command P B) : Canonical (step x hm c) := by
  cases c with
  | integer p hp hd => exact integerStep_canonical x H hm p hp hd
  | critical r => exact criticalStep_canonical x H hm r
  | cut r k d _ _ => exact cutStep_canonical x H hm r k d

theorem run_canonical {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (H : Canonical initial) (cs : List (Command P B)) (h : cs.length ≤ S + 1) :
    Canonical (run initial cs h) := by
  induction cs with
  | nil => exact H
  | cons c cs ih => exact step_canonical _ (ih (by simp only [List.length_cons] at h; omega)) _ c

def ofLegacy {n B : ℕ} {P : SpatialSource n} : IntegralMixedHistoryScript.Command n B → Command P B
  | .integer p hp hd => .integer p hp hd
  | .critical r => .critical r

theorem leading_ofLegacy {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (c : IntegralMixedHistoryScript.Command n B) :
    leading x hm (ofLegacy c) = IntegralMixedHistoryScript.leading x hm c := by cases c <;> rfl
end LeanCanny.Algebra.IntegralMixedFullHistoryScript
