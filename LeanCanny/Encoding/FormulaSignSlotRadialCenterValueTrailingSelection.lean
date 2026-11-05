/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueCoefficient
/-! # Whole-radius zero tests select the literal value certificate trailing coefficient -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValueTrailingSelection
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def specialized (c : List Bool)
    (a : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) → ℝ) :=
  (FormulaSignSlotRadialCenterValuePacking.source c).map
    (Polynomial.mapRingHom (FormulaSignSlotRadialFormalCenter.centerMap
      (FormulaSignSlotRadialCenterValueLayout.original c) a))
noncomputable def bound (c : List Bool) := FormulaSignSlotRadialCenterValuePacking.dimension c + 1
noncomputable def Zero (c : List Bool)
    (a : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) → ℝ) (j r : ℕ) : Prop :=
  (FormulaSignSlotRadialCenterValueCoefficient.polynomial c j r).eval₂ (Int.castRingHom ℝ) a = 0

theorem bound_binary : BinaryFn bound := FormulaSignSlotRadialCenterValuePacking.dimension_binary.add (BinaryFn.const 1)
theorem coefficient (c : List Bool)
    (a : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) → ℝ) (j r : ℕ) :
    ((specialized c a).coeff j).coeff r =
      (FormulaSignSlotRadialCenterValueCoefficient.polynomial c j r).eval₂ (Int.castRingHom ℝ) a := by
  simp only [specialized, Polynomial.coeff_map, Polynomial.coe_mapRingHom]
  rfl

theorem radius_degree (c : List Bool)
    (a : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) → ℝ) (j : ℕ) :
    ((specialized c a).coeff j).natDegree ≤ FormulaSignSlotRadialCenterValuePacking.degree c := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro r hr
  rw [coefficient]
  have HZ : FormulaSignSlotRadialCenterValueCoefficient.polynomial c j r = 0 := by
    rw [FormulaSignSlotRadialCenterValueCoefficient.polynomial_eq]
    exact MvTwoParameterCoefficient.one_eq_zero _ _
      ((FormulaSignSlotRadialCenterValuePacking.source_degree c j).trans_lt hr)
  rw [HZ, MvPolynomial.eval₂_zero]

theorem target_degree (c : List Bool)
    (a : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) → ℝ) :
    (specialized c a).natDegree ≤ bound c := by
  apply Polynomial.natDegree_map_le.trans
  have H := RelativeAffineGridValueGram.degree_le
    (FormulaSignSlotRadialCenterValueFamily.input (FormulaSignSlotRadialCenterValueLayout.original c)
      (fun i => FormulaSignSlotRadialCenterValueLayout.tau c i.val)
      (fun i => FormulaSignSlotRadialCenterValueLayout.degree c i.val))
    (FormulaSignSlotRadialFormalCenter.polynomial (FormulaSignSlotRadialCenterValueLayout.original c))
    (fun i => FormulaSignSlotRadialCenterValueLayout.degree c i.val)
    (FormulaSignSlotRadialCenterValueLayout.testDegree c)
  simpa only [bound, FormulaSignSlotRadialCenterValuePacking.dimension,
    FormulaSignSlotRadialCenterValuePacking.spatial_width, FormulaSignSlotRadialCenterValuePacking.source,
    FormulaSignSlotRadialCenterValueFamily.polynomial, FormulaSignSlotRadialCenterValueLayout.arity,
    FormulaSignSlotRadialFormalInput.spatial, FormulaSignSlotRadialCenterValueLayout.testDegree] using H

theorem radius_zero_iff (c : List Bool)
    (a : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) → ℝ) (j : ℕ) :
    (∀ r < FormulaSignSlotRadialCenterValuePacking.degree c + 1, Zero c a j r) ↔
      (specialized c a).coeff j = 0 := by
  constructor
  · intro H
    ext r
    rw [Polynomial.coeff_zero]
    by_cases hr : r < FormulaSignSlotRadialCenterValuePacking.degree c + 1
    · exact (coefficient c a j r).trans (H r hr)
    · exact coeff_eq_zero_of_natDegree_lt ((radius_degree c a j).trans_lt (by omega))
  · intro H r _
    change _ = 0
    rw [← coefficient, H, Polynomial.coeff_zero]

noncomputable def Guards (c : List Bool)
    (a : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) → ℝ) (ell : ℕ) : Prop :=
  ell ≤ bound c ∧ (∀ j < ell, ∀ r < FormulaSignSlotRadialCenterValuePacking.degree c + 1, Zero c a j r) ∧
    ¬∀ r < FormulaSignSlotRadialCenterValuePacking.degree c + 1, Zero c a ell r

theorem guards_iff (c : List Bool)
    (a : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) → ℝ) (ell : ℕ) :
    Guards c a ell ↔ specialized c a ≠ 0 ∧ ell = (specialized c a).natTrailingDegree := by
  simp_rw [Guards, radius_zero_iff]
  constructor
  · rintro ⟨_, HL, HNZ⟩
    have H : specialized c a ≠ 0 := by intro H; exact HNZ (by rw [H, Polynomial.coeff_zero])
    refine ⟨H, Nat.le_antisymm ?_ (natTrailingDegree_le_of_ne_zero HNZ)⟩
    by_contra HB
    exact (coeff_natTrailingDegree_ne_zero.mpr H) (HL _ (by omega))
  · rintro ⟨H, rfl⟩
    exact ⟨(natTrailingDegree_le_natDegree _).trans (target_degree c a),
      fun _ hj => coeff_eq_zero_of_lt_natTrailingDegree hj, coeff_natTrailingDegree_ne_zero.mpr H⟩

theorem specialization (c : List Bool)
    (a : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) → ℝ)
    (h : FormulaSignSlotRadialCenterValueFamily.Guards (FormulaSignSlotRadialCenterValueLayout.original c) a
      (fun i => FormulaSignSlotRadialCenterValueLayout.tau c i.val)
      (fun i => FormulaSignSlotRadialCenterValueLayout.degree c i.val)) :
    specialized c a = FormulaSignSlotRadialValueCertificate.polynomial
      (FormulaSignSlotRadialCenterValueLayout.original c) a :=
  FormulaSignSlotRadialCenterValueFamily.specialization _ a _ _ h

theorem guards_actual (c : List Bool)
    (a : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) → ℝ) (ell : ℕ)
    (h : FormulaSignSlotRadialCenterValueFamily.Guards (FormulaSignSlotRadialCenterValueLayout.original c) a
      (fun i => FormulaSignSlotRadialCenterValueLayout.tau c i.val)
      (fun i => FormulaSignSlotRadialCenterValueLayout.degree c i.val)) :
    Guards c a ell ↔ FormulaSignSlotRadialValueCertificate.polynomial
      (FormulaSignSlotRadialCenterValueLayout.original c) a ≠ 0 ∧
        ell = (FormulaSignSlotRadialValueCertificate.polynomial
          (FormulaSignSlotRadialCenterValueLayout.original c) a).natTrailingDegree := by
  rw [guards_iff, specialization c a h]

theorem trailing_coefficient (c : List Bool)
    (a : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) → ℝ) (ell r : ℕ)
    (h : FormulaSignSlotRadialCenterValueFamily.Guards (FormulaSignSlotRadialCenterValueLayout.original c) a
      (fun i => FormulaSignSlotRadialCenterValueLayout.tau c i.val)
      (fun i => FormulaSignSlotRadialCenterValueLayout.degree c i.val)) (hG : Guards c a ell) :
    (FormulaSignSlotRadialCenterValueCoefficient.polynomial c ell r).eval₂ (Int.castRingHom ℝ) a =
      ((FormulaSignSlotRadialValueCertificate.polynomial
        (FormulaSignSlotRadialCenterValueLayout.original c) a).trailingCoeff).coeff r := by
  have HE := (guards_actual c a ell h).mp hG
  rw [← coefficient, specialization c a h, HE.2]
  rfl

theorem exists_guards (c : List Bool)
    (a : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) → ℝ)
    (h : FormulaSignSlotRadialCenterValueFamily.Guards (FormulaSignSlotRadialCenterValueLayout.original c) a
      (fun i => FormulaSignSlotRadialCenterValueLayout.tau c i.val)
      (fun i => FormulaSignSlotRadialCenterValueLayout.degree c i.val))
    (r : ℝ) (hr : r ∉ FormulaSignSlotRadialParameterEliminant.bad
      (FormulaSignSlotRadialCenterValueLayout.original c) a)
    (x : Fin (N (FormulaSignSlotRadialCenterValueLayout.original c) +
      d (FormulaSignSlotRadialCenterValueLayout.original c) + 1) → ℝ)
    (hx : x ∈ FormulaSignSlotRadialParameterGrid.grid (FormulaSignSlotRadialCenterValueLayout.original c) a r) :
    ∃ ell ≤ bound c, Guards c a ell := by
  have HN := FormulaSignSlotRadialValueCertificate.ne_zero _ a r hr x hx
  have HG := (guards_actual c a _ h).mpr ⟨HN, rfl⟩
  exact ⟨_, HG.1, HG⟩

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValueTrailingSelection
