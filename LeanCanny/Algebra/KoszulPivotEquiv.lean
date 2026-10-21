/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulPivotBasis
public import Mathlib.LinearAlgebra.Isomorphisms

/-! # The homotopy identifies adjacent monomial summands

In every degree, the kernel of the normalized homotopy is the pivot
summand. Its restriction to the complementary nonpivot summand is therefore
an equivalence onto the pivot summand in the next degree. The projection
onto the nonpivot summand preserves homotopy images and canonical nonpivot
coordinates. All constructions are over the original coefficient ring.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem homotopy_kernel_eq_pivotSpan (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    LinearMap.ker (weightedHomotopy (R := R) d W hW k) = pivotSpan (R := R) d W k := by
  cases k with
  | zero =>
    have hz : LinearMap.ker (weightedHomotopy (R := R) d W hW 0) = ⊥ :=
      LinearMap.ker_eq_bot.mpr (weightedHomotopy_zero_injective d W hW)
    apply le_antisymm
    · rw [hz]
      exact bot_le
    · exact pivotSpan_le_homotopy_kernel d W hW 0
  | succ k =>
    exact (weightedHomotopy_exact d W hW k).trans (homotopy_range_eq_pivotSpan d W hW k)

noncomputable def nonpivotProjection (d : Fin n → ℕ) (W k : ℕ) :
    space (R := R) d (Macaulay.level d) W k →ₗ[R] nonpivotSpan (R := R) d W k :=
  (nonpivotSpan d W k).projectionOnto (pivotSpan d W k) (pivot_nonpivot_isCompl d W k).symm

theorem homotopy_nonpivotProjection (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (x : space (R := R) d (Macaulay.level d) W k) :
    weightedHomotopy (R := R) d W hW k (nonpivotProjection d W k x) =
      weightedHomotopy (R := R) d W hW k x := by
  have hm := Submodule.sub_projection_mem (pivot_nonpivot_isCompl (R := R) d W k).symm x
  have hz := pivotSpan_le_homotopy_kernel d W hW k hm
  change weightedHomotopy (R := R) d W hW k (x - (nonpivotProjection d W k x :
    space (R := R) d (Macaulay.level d) W k)) = 0 at hz
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

noncomputable def nonpivotHomotopyEquiv (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    nonpivotSpan (R := R) d W k ≃ₗ[R] pivotSpan (R := R) d W (k + 1) :=
  (Submodule.quotientEquivOfIsCompl
    (LinearMap.ker (weightedHomotopy (R := R) d W hW k)) (nonpivotSpan d W k)
      (by rw [homotopy_kernel_eq_pivotSpan]; exact pivot_nonpivot_isCompl d W k)).symm.trans
    ((weightedHomotopy (R := R) d W hW k).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (homotopy_range_eq_pivotSpan d W hW k)))

theorem nonpivotHomotopyEquiv_apply (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (x : nonpivotSpan (R := R) d W k) :
    (nonpivotHomotopyEquiv (R := R) d W hW k x : space (R := R) d (Macaulay.level d) W (k + 1)) =
      weightedHomotopy (R := R) d W hW k x.val := rfl

theorem monomialSubsetBasis_repr (d : Fin n → ℕ) (W k : ℕ)
    (s : Set (CanonicalIndex d (Macaulay.level d) W k))
    (x : Submodule.span R ((canonicalBasis (R := R) d (Macaulay.level d) W k) '' s)) (a : s) :
    (monomialSubsetBasis (R := R) d W k s).repr x a =
      (canonicalBasis (R := R) d (Macaulay.level d) W k).repr x.val a.val := by
  have he : (Finsupp.lapply a).comp (monomialSubsetBasis (R := R) d W k s).repr.toLinearMap =
      (Finsupp.lapply a.val).comp ((canonicalBasis (R := R) d (Macaulay.level d) W k).repr.toLinearMap.comp
        (Submodule.span R ((canonicalBasis (R := R) d (Macaulay.level d) W k) '' s)).subtype) := by
    apply (monomialSubsetBasis (R := R) d W k s).ext
    intro j
    change (monomialSubsetBasis (R := R) d W k s).repr (monomialSubsetBasis (R := R) d W k s j) a =
      (canonicalBasis (R := R) d (Macaulay.level d) W k).repr
        (monomialSubsetBasis (R := R) d W k s j : space (R := R) d (Macaulay.level d) W k) a.val
    rw [monomialSubsetBasis_apply, Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]
    simp only [Subtype.val_injective.eq_iff]
  exact LinearMap.congr_fun he x

theorem pivotBasis_apply (d : Fin n → ℕ) (W k : ℕ)
    (a : {a : CanonicalIndex d (Macaulay.level d) W k // HasPivot d W k a}) :
    (pivotBasis (R := R) d W k a : space (R := R) d (Macaulay.level d) W k) =
      canonicalBasis (R := R) d (Macaulay.level d) W k a.val :=
  monomialSubsetBasis_apply (R := R) d W k {a | HasPivot d W k a} a

theorem nonpivotBasis_apply (d : Fin n → ℕ) (W k : ℕ)
    (a : {a : CanonicalIndex d (Macaulay.level d) W k // ¬HasPivot d W k a}) :
    (nonpivotBasis (R := R) d W k a : space (R := R) d (Macaulay.level d) W k) =
      canonicalBasis (R := R) d (Macaulay.level d) W k a.val :=
  monomialSubsetBasis_apply (R := R) d W k {a | ¬HasPivot d W k a} a

theorem pivotBasis_repr (d : Fin n → ℕ) (W k : ℕ)
    (x : pivotSpan (R := R) d W k)
    (a : {a : CanonicalIndex d (Macaulay.level d) W k // HasPivot d W k a}) :
    (pivotBasis (R := R) d W k).repr x a =
      (canonicalBasis (R := R) d (Macaulay.level d) W k).repr x.val a.val :=
  monomialSubsetBasis_repr (R := R) d W k {a | HasPivot d W k a} x a

theorem nonpivotBasis_repr (d : Fin n → ℕ) (W k : ℕ)
    (x : nonpivotSpan (R := R) d W k)
    (a : {a : CanonicalIndex d (Macaulay.level d) W k // ¬HasPivot d W k a}) :
    (nonpivotBasis (R := R) d W k).repr x a =
      (canonicalBasis (R := R) d (Macaulay.level d) W k).repr x.val a.val :=
  monomialSubsetBasis_repr (R := R) d W k {a | ¬HasPivot d W k a} x a

theorem nonpivotProjection_repr (d : Fin n → ℕ) (W k : ℕ)
    (x : space (R := R) d (Macaulay.level d) W k)
    (a : {a : CanonicalIndex d (Macaulay.level d) W k // ¬HasPivot d W k a}) :
    (nonpivotBasis (R := R) d W k).repr (nonpivotProjection d W k x) a =
      (canonicalBasis (R := R) d (Macaulay.level d) W k).repr x a.val := by
  have hm := Submodule.sub_projection_mem (pivot_nonpivot_isCompl (R := R) d W k).symm x
  have hs := (canonicalBasis (R := R) d (Macaulay.level d) W k).mem_span_image.mp hm
  have hz : (canonicalBasis (R := R) d (Macaulay.level d) W k).repr
      (x - (nonpivotProjection d W k x : space (R := R) d (Macaulay.level d) W k)) a.val = 0 := by
    by_contra hne
    exact a.property (hs (Finsupp.mem_support_iff.mpr hne))
  rw [map_sub, Finsupp.sub_apply, sub_eq_zero] at hz
  rw [nonpivotBasis_repr]
  exact hz.symm

end LeanCanny.Algebra.KoszulWeighted
