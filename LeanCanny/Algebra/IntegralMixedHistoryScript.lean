/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedHistory

/-! # Tagged mixed-history commands and their actual interpreter

Each command adds one scalar to the same fixed-cap coefficient prefix.
Integer commands retain the original integer polynomial and actual degree;
critical commands construct the relative polynomial from the current bank
and immutable spatial source. The physical sampler retains all old variables.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistoryScript
open LeanCanny.Encoding LeanCanny.Computation IntegralHistorySampler UniformIntegralPrefix
open IntegralMixedHistory
open scoped Classical

inductive Command (n B : ℕ) where
  | integer (polynomial : Polynomial ℤ) (nonzero : polynomial ≠ 0) (degree_cap : polynomial.natDegree ≤ 2 ^ B)
  | critical (rule : CriticalRule n)

def Command.isCritical {n B : ℕ} : Command n B → Bool
  | .integer .. => false
  | .critical _ => true

def NextIndex {n B : ℕ} (ι : Type) : Command n B → Type
  | .integer .. => ι ⊕ Unit
  | .critical _ => (ι ⊕ FlatAffineCriticalStage.Variables (n + 1)) ⊕ Unit

instance nextFintype {n B : ℕ} (ι : Type) [Fintype ι] (c : Command n B) : Fintype (NextIndex ι c) := by
  cases c <;> dsimp only [NextIndex] <;> infer_instance

noncomputable def polynomial {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) : Command n B → Polynomial x.sampler.scalarPrefix.carrier
  | .integer p _ _ => p.map (Int.castRingHom x.sampler.scalarPrefix.carrier)
  | .critical r => criticalPolynomial x hm r

def degree {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) : Command n B → ℕ
  | .integer p _ _ => p.natDegree
  | .critical r => criticalDegree x hm r

noncomputable def leading {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) : Command n B → ℤ
  | .integer p _ _ => p.leadingCoeff
  | .critical r => criticalLeading x hm r

theorem degree_cap {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (c : Command n B) : degree x hm c ≤ 2 ^ B := by
  cases c with
  | integer p hp hcap => exact hcap
  | critical r => exact criticalDegree_cap x hm r

theorem leading_ne_zero {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (c : Command n B) : leading x hm c ≠ 0 := by
  cases c with
  | integer p hp _ => exact Polynomial.leadingCoeff_ne_zero.mpr hp
  | critical r => exact criticalLeading_ne_zero x hm r

theorem leading_coefficient {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (c : Command n B) :
    (polynomial x hm c).coeff (degree x hm c) = (leading x hm c : x.sampler.scalarPrefix.carrier) := by
  cases c with
  | integer p _ _ => simp only [polynomial, degree, leading, Polynomial.coeff_map, Polynomial.coeff_natDegree]; rfl
  | critical r => exact criticalLeading_coefficient x hm r

noncomputable def step {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) : (c : Command n B) → State P S B (m + 1) (NextIndex ι c)
  | .integer p hp hcap => integerStep x hm p hp hcap
  | .critical r => IntegralMixedHistory.criticalStep x hm r

theorem step_prefix {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (c : Command n B) :
    (step x hm c).sampler.scalarPrefix = UniformIntegralPrefix.step x.sampler.scalarPrefix hm
      (Nat.two_pow_pos B) (polynomial x hm c) (degree x hm c) := by
  cases c <;> rfl

theorem step_denominator_zero {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (c : Command n B) :
    (step x hm c).bank.denominator 0 = leading x hm c := by cases c <;> rfl

theorem step_denominator_succ {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (c : Command n B) (i : Fin m) :
    (step x hm c).bank.denominator i.succ = x.bank.denominator i := by cases c <;> rfl

def Index {n B : ℕ} (ι : Type) : List (Command n B) → Type
  | [] => ι
  | c :: cs => NextIndex (Index ι cs) c

instance indexFintype {n B : ℕ} (ι : Type) [Fintype ι] : (cs : List (Command n B)) → Fintype (Index ι cs)
  | [] => inferInstanceAs (Fintype ι)
  | c :: cs => by
    change Fintype (NextIndex (Index ι cs) c)
    letI := indexFintype ι cs
    exact nextFintype _ c

noncomputable def run {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) : (cs : List (Command n B)) → cs.length ≤ S + 1 →
      State P S B cs.length (Index ι cs)
  | [], _ => initial
  | c :: cs, hcs => step (run initial cs (by simp only [List.length_cons] at hcs; omega))
      (by simp only [List.length_cons] at hcs; omega) c

def criticalCount {n B : ℕ} (cs : List (Command n B)) : ℕ := cs.countP Command.isCritical

theorem physical_arity {n B : ℕ} {ι : Type} [Fintype ι] (cs : List (Command n B)) :
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

end LeanCanny.Algebra.IntegralMixedHistoryScript
