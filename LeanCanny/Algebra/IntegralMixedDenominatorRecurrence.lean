/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHistoryContinuation
/-! # Actual mixed-bank denominators use scalar integer recurrence only -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedDenominatorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedHistoryScript
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def criticalExponent {n : ℕ} (P : SpatialSource n) (r : CriticalRule n) : ℕ :=
  (PurePowerReductionBounds.bound (n - r.offset.val + 1) P.degree + 1) *
    PurePowerReductionBounds.dimension (n - r.offset.val + 1) P.degree

noncomputable def criticalDenominator {n : ℕ} (P : SpatialSource n) (r : CriticalRule n) (Q : ℤ) : ℤ :=
  (P.leading * (Q ^ (n + 1) * ∏ i, r.scales i) ^ P.degree * (P.degree : ℤ)) ^ criticalExponent P r

theorem common_scales {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) :
    CoordinateFrozenCriticalElimination.denominator (fun i => (data x hm r).scales i) =
      commonDenominator x ^ (n + 1) * ∏ i, r.scales i := by
  change (∏ i, commonDenominator x * r.scales i) = _
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem criticalLeading_eq {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) :
    criticalLeading x hm r = criticalDenominator P r (commonDenominator x) := by
  change (P.leading * CoordinateFrozenCriticalElimination.denominator (fun i => (data x hm r).scales i) ^ P.degree *
    (P.degree : ℤ)) ^ criticalExponent P r = _
  rw [common_scales]
  rfl

noncomputable def bankList {n S B m : ℕ} {P : SpatialSource n} {ι : Type} (x : State P S B m ι) : List ℤ := List.ofFn x.bank.denominator

theorem bankList_prod {n S B m : ℕ} {P : SpatialSource n} {ι : Type} (x : State P S B m ι) :
    (bankList x).prod = commonDenominator x := by
  rw [bankList, List.prod_ofFn]
  rfl

noncomputable def scalarLeading {n B : ℕ} (P : SpatialSource n) (c : Command n B) (v : List ℤ) : ℤ :=
  match c with
  | .integer p _ _ => p.leadingCoeff
  | .critical r => criticalDenominator P r v.prod

theorem leading_eq {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (c : Command n B) :
    IntegralMixedHistoryScript.leading x hm c = scalarLeading P c (bankList x) := by
  cases c with
  | integer p _ _ => rfl
  | critical r =>
    change criticalLeading x hm r = criticalDenominator P r (bankList x).prod
    rw [bankList_prod, criticalLeading_eq]

noncomputable def denominators {n B : ℕ} (P : SpatialSource n) (initial : List ℤ) : List (Command n B) → List ℤ
  | [] => initial
  | c :: cs => scalarLeading P c (denominators P initial cs) :: denominators P initial cs

theorem denominators_length {n B : ℕ} (P : SpatialSource n) (initial : List ℤ) (cs : List (Command n B)) :
    (denominators P initial cs).length = cs.length + initial.length := by
  induction cs with
  | nil => simp only [denominators, List.length_nil, Nat.zero_add]
  | cons c cs ih => simp only [denominators, List.length_cons, ih]; omega

theorem bankList_step {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (c : Command n B) :
    bankList (IntegralMixedHistoryScript.step x hm c) = scalarLeading P c (bankList x) :: bankList x := by
  unfold bankList
  rw [List.ofFn_succ]
  rw [IntegralMixedHistoryScript.step_denominator_zero, leading_eq]
  congr 1
  congr 1
  funext i
  exact IntegralMixedHistoryScript.step_denominator_succ x hm c i

theorem bankList_continueRun {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B m ι) (cs : List (Command n B)) (h : m + cs.length ≤ S + 1) :
    bankList (continueRun initial cs h) = denominators P (bankList initial) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [continueRun, bankList_step, ih, denominators]
end LeanCanny.Algebra.IntegralMixedDenominatorBits
