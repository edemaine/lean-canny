/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedExceptionalBounds
public import LeanCanny.Geometry.AlgebraicBranchZero

/-! # The selected equation-value trailing cut and exact grid pruning

An explicit bounded coefficient index is validated on the CURRENT old
component. The chosen relative coefficient is the exact trailing factor
of the constructed relative value certificate. Its avoidance makes the
actual original-source/gradient zero tests constant on connected grid
branches, so extraneous Cartesian combinations are pruned exactly.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueTrailing
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedCriticalSweep
open Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

abbrev ChoiceBound (P : SpatialSource n) (r : Rule n) := IntegralMixedGridValue.dimension P r + 2

noncomputable def selectedValue (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :=
  (IntegralMixedGridValue.polynomial x hm r i).map (Polynomial.mapRingHom φ.toRingHom)

def Valid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (k : Fin (ChoiceBound P r)) : Prop :=
  (∀ l < k.val, ((IntegralMixedGridValue.polynomial x hm r i).coeff l).map φ.toRingHom = 0) ∧
    ((IntegralMixedGridValue.polynomial x hm r i).coeff k.val).map φ.toRingHom ≠ 0

noncomputable def factor (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (k : Fin (ChoiceBound P r)) :=
  (IntegralMixedGridValue.polynomial x hm r i).coeff k.val

theorem valid_iff (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (k : Fin (ChoiceBound P r)) : Valid x hm r i φ k ↔ k.val = (selectedValue x hm r i φ).natTrailingDegree := by
  have HP : selectedValue x hm r i φ ≠ 0 := IntegralMixedGridValue.selected_ne_zero x hm r i φ
  have HC (l : ℕ) : (selectedValue x hm r i φ).coeff l =
      ((IntegralMixedGridValue.polynomial x hm r i).coeff l).map φ.toRingHom := Polynomial.coeff_map _ _
  constructor
  · rintro ⟨HL, HT⟩
    apply Nat.le_antisymm
    · apply Polynomial.le_natTrailingDegree HP
      intro l hl
      rw [HC]
      exact HL l hl
    · apply Polynomial.natTrailingDegree_le_of_ne_zero
      rw [HC]
      exact HT
  · intro H
    constructor
    · intro l hl
      rw [H] at hl
      have HE := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hl
      rw [HC] at HE
      exact HE
    · have HE := Polynomial.coeff_natTrailingDegree_ne_zero.mpr HP
      rw [← H, HC] at HE
      exact HE

theorem exists_valid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    ∃ k : Fin (ChoiceBound P r), Valid x hm r i φ k := by
  have HD : (selectedValue x hm r i φ).natTrailingDegree < ChoiceBound P r :=
    (Polynomial.natTrailingDegree_le_natDegree _).trans_lt (Nat.lt_succ_of_le
      (Polynomial.natDegree_map_le.trans (IntegralMixedGridValue.degree_le x hm r i)))
  exact ⟨⟨_, HD⟩, (valid_iff x hm r i φ ⟨_, HD⟩).mpr rfl⟩

theorem factor_specialization (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (k : Fin (ChoiceBound P r)) (hk : Valid x hm r i φ k) :
    (factor x hm r i k).map φ.toRingHom = (selectedValue x hm r i φ).trailingCoeff := by
  have HE := (valid_iff x hm r i φ k).mp hk
  change _ = (selectedValue x hm r i φ).coeff (selectedValue x hm r i φ).natTrailingDegree
  rw [← HE]
  exact (Polynomial.coeff_map (p := IntegralMixedGridValue.polynomial x hm r i) (Polynomial.mapRingHom φ.toRingHom) k.val).symm

theorem factor_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (k : Fin (ChoiceBound P r)) :
    (factor x hm r i k).natDegree ≤ IntegralMixedExceptionalBounds.valueCap (n + 1) P.degree :=
  IntegralMixedExceptionalBounds.value_coefficient_degree x hm r i k.val

theorem finite_cuts (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (k : Fin (ChoiceBound P r)) (hk : Valid x hm r i φ k) :
    {t : ℝ | (factor x hm r i k).eval₂ φ.toRingHom t = 0}.Finite := by
  simpa only [factor, Polynomial.IsRoot, Polynomial.eval_map] using Polynomial.finite_setOfPred_isRoot hk.2

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]

theorem original_row_zero_iff (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (k : Fin (ChoiceBound P r)) (hk : Valid x hm r i φ k)
    (parameter : X → ℝ) (z : X → Fin (n - r.critical.offset.val + 1) → ℝ)
    (ht : Continuous parameter) (hz : Continuous z)
    (hgrid : ∀ w j, (selected x hm r j φ).eval₂ (Polynomial.evalRingHom (parameter w)) (z w j) = 0)
    (havoid : ∀ w, (factor x hm r i k).eval₂ φ.toRingHom (parameter w) ≠ 0) (a b : X) :
    (IntegralMixedSweepRows.integerRow P r i).eval₂ (Int.castRingHom ℝ)
      (IntegralMixedSweepRows.point x hm r φ (parameter a) (z a)) = 0 ↔
    (IntegralMixedSweepRows.integerRow P r i).eval₂ (Int.castRingHom ℝ)
      (IntegralMixedSweepRows.point x hm r φ (parameter b) (z b)) = 0 := by
  let q := (IntegralMixedSweepRows.row x hm r i).map (Polynomial.mapRingHom φ.toRingHom)
  let f := fun w => (IntegralMixedSweepRows.row x hm r i).eval₂ (evaluation x φ (parameter w)) (z w)
  have HF : Continuous f := by
    have H := (LeanCanny.Geometry.PolynomialRootFamily.contDiff_eval q 1).continuous.comp (ht.prodMk hz)
    convert H using 1
    funext w
    dsimp only [f, q, Function.comp_apply]
    rw [MvPolynomial.eval₂_map]
    rfl
  have Hzero : f a = 0 ↔ f b = 0 := by
    apply LeanCanny.Geometry.AlgebraicBranchZero.zero_iff (selectedValue x hm r i φ) parameter f ht HF
    · intro w
      exact IntegralMixedGridValue.root x hm r i φ (parameter w) (z w) (hgrid w)
    · intro w
      rw [← factor_specialization x hm r i φ k hk, Polynomial.eval_map]
      exact havoid w
  exact (IntegralMixedSweepRows.row_zero_iff x hm r i φ (parameter a) (z a)).symm.trans
    (Hzero.trans (IntegralMixedSweepRows.row_zero_iff x hm r i φ (parameter b) (z b)))

end LeanCanny.Algebra.IntegralMixedValueTrailing
