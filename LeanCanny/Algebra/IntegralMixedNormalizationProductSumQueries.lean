/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeProductTerm
/-! # Finite inverse/raw summands preserve the actual matrix and coefficient -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def productTermAt (F : Family) (key : List Bool) (m k r t h : ℕ) : List Bool :=
  let i : Fin (dimension F key) := ⟨r % dimension F key, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
  let j : Fin (dimension F key) := ⟨t % dimension F key, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
  let v : Fin (dimension F key) := ⟨h % dimension F key, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
  residueBits ((inverseMatrix F key i v * rawCoefficient F key k v j : ℤ) : ZMod m)

theorem productTerm_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    productTermValue P F q = productTermAt F (IntegralMixedVirtualTaskBits.saved P q)
      (modulus P q) (get P .coefficient q) (get P .row q) (get P .col q) (get P .target q) := rfl

noncomputable def productSummand (P : Parameters) (F : Family) (q : List Bool) (h : ℕ) : ZMod (modulus P q) :=
  if hh : h < matrixDimension P F q then
    ((inverseMatrix F (IntegralMixedVirtualTaskBits.saved P q) (topRow P F q) ⟨h, hh⟩ *
      rawCoefficient F (IntegralMixedVirtualTaskBits.saved P q) (get P .coefficient q) ⟨h, hh⟩ (topCol P F q) : ℤ) :
        ZMod (modulus P q)) else 0

def matrixAxes (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  get P .row q < matrixDimension P F q ∧ get P .col q < matrixDimension P F q

def productLoopTask (P : Parameters) :=
  IntegralMixedValueFieldQuery.query P pairFst .normalization .frozenLower .target
    (fun z => Nat.fromBitsLE (pairSnd z))

theorem productLoopTask_FP (P : Parameters) (a : Access P) : productLoopTask P ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a pairFst pairFst_mem_FP .normalization .frozenLower .target
    _ (BinaryFn.fromBits pairSnd_mem_FP)

attribute [local irreducible] productTermAt

theorem productLoop_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (h : ℕ) (hh : h < matrixDimension P F q) :
    productTermValue P F (productLoopTask P (pair q (BinaryNatCode.encode h))) = residueBits (productSummand P F q h) := by
  have HH : h ≤ numericCap P (RankedHistoryTask.root q) := hh.le.trans (dimension_cap P F g q hv)
  unfold productLoopTask
  rw [productTerm_snapshot,
    IntegralMixedValueFieldQuery.query_saved P pairFst .normalization .frozenLower .target _ _ (by decide),
    IntegralMixedValueFieldQuery.query_modulus P pairFst .normalization .frozenLower .target _ _ (by decide),
    IntegralMixedValueFieldQuery.query_field P pairFst .normalization .frozenLower .target _ _ (by decide)
      (by simpa only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using HH),
    IntegralMixedValueFieldQuery.query_other P pairFst .normalization .frozenLower .target _ _ .coefficient (by decide) (by decide),
    IntegralMixedValueFieldQuery.query_other P pairFst .normalization .frozenLower .target _ _ .row (by decide) (by decide),
    IntegralMixedValueFieldQuery.query_other P pairFst .normalization .frozenLower .target _ _ .col (by decide) (by decide)]
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold productTermAt productSummand
  rw [dite_eq_left hh]
  simp only [show dimension F (IntegralMixedVirtualTaskBits.saved P q) = matrixDimension P F q from rfl, Nat.mod_eq_of_lt hh]
  rfl

abbrev ProductTermMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    isPhase .frozenLower q → productAxes P F q → answer q = productTermValue P F q

theorem productLoop_reply (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : ProductTermMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (ha : matrixAxes P F q) (h : ℕ) (hh : h < matrixDimension P F q) :
    answer (productLoopTask P (pair q (BinaryNatCode.encode h))) = residueBits (productSummand P F q h) := by
  let z := pair q (BinaryNatCode.encode h)
  let c := productLoopTask P z
  have HV : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid c productLoopTask
    rw [IntegralMixedValueFieldQuery.query_birth, IntegralMixedValueFieldQuery.query_root, pairFst_pair]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P c = 5 :=
    IntegralMixedValueFieldQuery.query_routine P pairFst .normalization .frozenLower .target _ z
  have HP : isPhase .frozenLower c := IntegralMixedValueFieldQuery.query_phase P pairFst .normalization .frozenLower .target _ z
  have HD : matrixDimension P F c = matrixDimension P F q := by
    apply congrArg (dimension F)
    exact (IntegralMixedValueFieldQuery.query_saved P pairFst .normalization .frozenLower .target _ z (by decide)).trans
      (congrArg (IntegralMixedVirtualTaskBits.saved P) (pairFst_pair _ _))
  have HI : get P .target c = h := by
    have HC := IntegralMixedValueFieldQuery.query_field P pairFst .normalization .frozenLower .target
      (fun z => Nat.fromBitsLE (pairSnd z)) z (by decide)
      (by simpa only [z, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
        (hh.le.trans (dimension_cap P F g q hv)))
    simpa only [c, productLoopTask, z, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using HC
  have HRow : get P .row c = get P .row q := by
    unfold c productLoopTask
    rw [IntegralMixedValueFieldQuery.query_other P pairFst .normalization .frozenLower .target _ z .row (by decide) (by decide), pairFst_pair]
  have HCol : get P .col c = get P .col q := by
    unfold c productLoopTask
    rw [IntegralMixedValueFieldQuery.query_other P pairFst .normalization .frozenLower .target _ z .col (by decide) (by decide), pairFst_pair]
  have HA : productAxes P F c := by
    unfold productAxes
    rw [HI, HRow, HCol, HD]
    exact ⟨ha.1, ha.2, hh⟩
  exact (hx c HV HR HP HA).trans (productLoop_value P F g q hv h hh)

theorem productValue_sum (P : Parameters) (F : Family) (q : List Bool) (ha : matrixAxes P F q) :
    productValue P F q = residueBits (∑ h ∈ Finset.range (matrixDimension P F q), productSummand P F q h) := by
  have HE := IntegralCriticalTotalSnapshotBits.integerEntry_fin
    (inverseMatrix F (IntegralMixedVirtualTaskBits.saved P q) * rawCoefficient F (IntegralMixedVirtualTaskBits.saved P q) (get P .coefficient q))
    (topRow P F q) (topCol P F q)
  have HR : (topRow P F q).val = get P .row q := Nat.mod_eq_of_lt ha.1
  have HT : (topCol P F q).val = get P .col q := Nat.mod_eq_of_lt ha.2
  rw [HR, HT] at HE
  unfold productValue
  rw [HE, Matrix.mul_apply, Int.cast_sum, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  have HH : h.val < matrixDimension P F q := by
    change h.val < FixedWidthPolynomial.count (F.birth (IntegralMixedVirtualTaskBits.saved P q)) (F.width (IntegralMixedVirtualTaskBits.saved P q))
    exact h.isLt
  unfold productSummand
  rw [dite_eq_left HH]

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
