/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralIntegerRootBank
public import LeanCanny.Algebra.IntegralScalarRootHistoryBounds
public import LeanCanny.Algebra.IntegralCriticalFactorCeiling
public import LeanCanny.Algebra.CommonIntegerDenominator

/-! # Mixed integer and relative critical scalar histories

The spatial source is immutable. A state retains its actual whole square
sampler, integral coefficient prefix, height bank, and nonzero integer
denominators. Integer births use their original integer polynomials and
actual leading coefficients. Relative critical births construct their
CriticalData from cleared affine expressions over the same bank, retaining
the original spatial degree and the fixed scalar cap.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open LeanCanny.Encoding LeanCanny.Computation IntegralHistorySampler UniformIntegralPrefix FixedWidthPolynomial
open scoped Classical BigOperators

structure SpatialSource (n : ℕ) where
  low : MvPolynomial (Fin (n + 1)) ℤ
  leading : ℤ
  degree : ℕ
  degree_two : 2 ≤ degree
  low_degree : low.totalDegree < degree
  leading_ne_zero : leading ≠ 0

inductive AffineExpr where
  | constant (value : ℤ)
  | reference (index : ℕ)
  | add (left right : AffineExpr)
  | scale (coefficient : ℤ) (body : AffineExpr)

structure CriticalRule (n : ℕ) where
  offset : Fin (n + 1)
  objective : ℕ
  coordinate : ℕ
  scales : Fin (n + 1) → ℤ
  scales_ne_zero : ∀ i, scales i ≠ 0
  heights : Fin (n + 1) → AffineExpr

structure State {n : ℕ} (P : SpatialSource n) (S B m : ℕ) (ι : Type) where
  sampler : Sampler S (2 ^ B) m ι
  bank : HeightBank sampler.scalarPrefix
  denominator_ne_zero : ∀ i, bank.denominator i ≠ 0
  critical_cap : PurePowerReductionBounds.dimension (n + 1) P.degree ≤ 2 ^ B

noncomputable def base {n S B : ℕ} {ι : Type} (P : SpatialSource n)
    (F : Sampler S (2 ^ B) 0 ι) (hcap : PurePowerReductionBounds.dimension (n + 1) P.degree ≤ 2 ^ B) :
    State P S B 0 ι where
  sampler := F
  bank := { numerator := Fin.elim0, denominator := Fin.elim0 }
  denominator_ne_zero := by intro i; exact Fin.elim0 i
  critical_cap := hcap

noncomputable def commonDenominator {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) : ℤ := CommonIntegerDenominator.denominator Finset.univ x.bank.denominator

theorem commonDenominator_ne_zero {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) : commonDenominator x ≠ 0 :=
  CommonIntegerDenominator.denominator_ne_zero _ _ (fun i _ => x.denominator_ne_zero i)

noncomputable def cleared {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (i : Fin m) : x.sampler.scalarPrefix.carrier :=
  CommonIntegerDenominator.numerator Finset.univ x.bank.denominator x.bank.numerator i

noncomputable def expression {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) : AffineExpr → x.sampler.scalarPrefix.carrier
  | .constant c => (commonDenominator x : x.sampler.scalarPrefix.carrier) * (c : _)
  | .reference j => if hj : j < m then cleared x ⟨j, hj⟩ else 0
  | .add a b => expression x a + expression x b
  | .scale c a => (c : x.sampler.scalarPrefix.carrier) * expression x a

noncomputable def data {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) : CriticalData x.sampler.scalarPrefix n where
  heights i := expression x (r.heights i)
  low := P.low
  leading := P.leading
  objective := 2
  scales i := commonDenominator x * r.scales i
  frozen := Finset.univ.filter (fun i => i.val < r.offset.val)
  free := ⟨r.offset.val + r.objective % (n - r.offset.val + 1), by
    have H : r.objective % (n - r.offset.val + 1) < n - r.offset.val + 1 := Nat.mod_lt _ (by omega)
    have HO := r.offset.isLt
    omega⟩
  degree := P.degree
  birth_bound := hm
  degree_two := P.degree_two
  low_degree := P.low_degree
  leading_ne := P.leading_ne_zero
  objective_ne := by decide
  scales_ne i := mul_ne_zero (commonDenominator_ne_zero x) (r.scales_ne_zero i)
  free_not_frozen := by
    intro H
    have HH : r.offset.val + r.objective % (n - r.offset.val + 1) < r.offset.val := (Finset.mem_filter.mp H).2
    omega

noncomputable def family {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) : IntegralHistoryCriticalBits.Family where
  cap _ := S
  width _ := B
  birth _ := m
  ambient _ := n
  free _ := n - r.offset.val
  scalarPrefix _ := x.sampler.scalarPrefix
  data _ := data x hm r
  offset _ := r.offset.val
  fit _ := by have H := r.offset.isLt; omega
  sourceWidth _ := P.degree.size
  degree_lt _ := by change P.degree < 2 ^ P.degree.size; exact Nat.lt_size_self P.degree
  objective _ := ⟨r.objective % (n - r.offset.val + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  coordinate _ := ⟨r.coordinate % (n - r.offset.val + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  coefficientIndex _ := 0
  target _ := 0
  row _ := ⟨0, by change 0 < (2 ^ B) ^ m; exact pow_pos (Nat.two_pow_pos _) _⟩
  col _ := ⟨0, by change 0 < (2 ^ B) ^ m; exact pow_pos (Nat.two_pow_pos _) _⟩
  modulus _ := 1
  modulus_ne_zero _ := by decide

noncomputable def criticalPolynomial {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) : Polynomial x.sampler.scalarPrefix.carrier :=
  (IntegralHistoryCriticalBits.source (family x hm r)).annihilator []

def criticalDegree {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (_x : State P S B m ι) (_hm : m ≤ S) (r : CriticalRule n) : ℕ :=
  PurePowerReductionBounds.dimension (n - r.offset.val + 1) P.degree

noncomputable def criticalLeading {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) : ℤ :=
  IntegralClearedCriticalLeadingBits.integer (IntegralHistoryCriticalBits.source (family x hm r)) []

theorem criticalDegree_cap {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) : criticalDegree x hm r ≤ 2 ^ B :=
  (IntegralCriticalFactorCeiling.dimension_mono (by omega : n - r.offset.val + 1 ≤ n + 1) (Nat.le_refl P.degree)).trans x.critical_cap

theorem criticalLeading_ne_zero {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) : criticalLeading x hm r ≠ 0 :=
  IntegralScalarRootHistoryBounds.integer_nonzero (family x hm r) []

theorem criticalLeading_coefficient {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) :
    (criticalPolynomial x hm r).coeff (criticalDegree x hm r) =
      (criticalLeading x hm r : x.sampler.scalarPrefix.carrier) := by
  have HE : IntegralClearedCriticalBounds.dimension (IntegralHistoryCriticalBits.source (family x hm r)) [] =
      criticalDegree x hm r := rfl
  have H := IntegralClearedCriticalLeadingBits.coefficient (IntegralHistoryCriticalBits.source (family x hm r)) []
  rw [HE] at H
  convert H using 1 <;> rfl

noncomputable def integerStep {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (p : Polynomial ℤ) (hp : p ≠ 0)
    (_hcap : p.natDegree ≤ 2 ^ B) : State P S B (m + 1) (ι ⊕ Unit) where
  sampler := scalarStep x.sampler hm (Nat.two_pow_pos B) (p.map (Int.castRingHom x.sampler.scalarPrefix.carrier)) p.natDegree
  bank := x.bank.rootStep hm (p.map (Int.castRingHom x.sampler.scalarPrefix.carrier)) p.natDegree p.leadingCoeff
  denominator_ne_zero := x.bank.rootStep_denominator_ne_zero hm _ _ _ (Polynomial.leadingCoeff_ne_zero.mpr hp) x.denominator_ne_zero
  critical_cap := x.critical_cap

noncomputable def criticalStep {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) :
    State P S B (m + 1) ((ι ⊕ FlatAffineCriticalStage.Variables (n + 1)) ⊕ Unit) where
  sampler := scalarStep (IntegralHistorySampler.criticalStep x.sampler (data x hm r)) hm (Nat.two_pow_pos B)
    (criticalPolynomial x hm r) (criticalDegree x hm r)
  bank := x.bank.rootStep hm (criticalPolynomial x hm r) (criticalDegree x hm r) (criticalLeading x hm r)
  denominator_ne_zero := x.bank.rootStep_denominator_ne_zero hm _ _ _ (criticalLeading_ne_zero x hm r) x.denominator_ne_zero
  critical_cap := x.critical_cap

theorem integerStep_denominator {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (p : Polynomial ℤ) (hp : p ≠ 0) (hcap : p.natDegree ≤ 2 ^ B) :
    (integerStep x hm p hp hcap).bank.denominator 0 = p.leadingCoeff := rfl

theorem criticalStep_denominator {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) :
    (criticalStep x hm r).bank.denominator 0 = criticalLeading x hm r := rfl

end LeanCanny.Algebra.IntegralMixedHistory
