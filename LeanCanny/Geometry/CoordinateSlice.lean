/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.HypersurfaceSweep
public import LeanCanny.Geometry.PolynomialCalculus
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.SetTheory.Cardinal.NatCard

/-! # A hypersurface sweep fiber as a polynomial equation in fewer coordinates

Replace the swept coordinate by a polynomial parameter. Evaluating that
parameter gives exactly the original polynomial on the corresponding slice.
The fixed hypersurface's sweep fiber is homeomorphic to this equation in the
remaining coordinates, so recursive path tests retain their original meaning.
-/

@[expose] public section

namespace LeanCanny.Geometry.CoordinateSlice
open MvPolynomial Set Topology

variable {ι : Type} [DecidableEq ι]

abbrev Index (base : ι) := {i : ι // i ≠ base}

def restore {Y : Type*} (base : ι) (t : Y) (x : Index base → Y) : ι → Y :=
  fun i => if hi : i = base then t else x ⟨i, hi⟩

theorem restore_base {Y : Type*} (base : ι) (t : Y) (x : Index base → Y) :
    restore base t x base = t := by simp [restore]

theorem restore_other {Y : Type*} (base : ι) (t : Y) (x : Index base → Y) (j : Index base) :
    restore base t x j.val = x j := by simp [restore, j.property]

theorem restore_coordinates {Y : Type*} (base : ι) (t : Y) (x : ι → Y) (hx : x base = t) :
    restore base t (fun j => x j.val) = x := by
  funext i
  by_cases hi : i = base
  · simp [restore, hi, hx]
  · simp only [restore, dite_eq_right hi]

variable {R : Type*} [CommRing R]

noncomputable def family (base : ι) :
    MvPolynomial ι R →+* MvPolynomial (Index base) (Polynomial R) :=
  eval₂Hom (MvPolynomial.C.comp Polynomial.C)
    (fun i => if hi : i = base then MvPolynomial.C Polynomial.X else MvPolynomial.X ⟨i, hi⟩)

theorem eval_family (base : ι) (p : MvPolynomial ι R) (φ : R →+* ℝ) (t : ℝ) (x : Index base → ℝ) :
    (family base p).eval₂ (Polynomial.eval₂RingHom φ t) x = p.eval₂ φ (restore base t x) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [family]
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, eval₂_mul, hp, eval₂_mul, eval₂_X]
    congr 1
    by_cases hi : i = base <;> simp [family, restore, hi]

theorem continuous_restore (base : ι) (t : ℝ) : Continuous (restore base t : (Index base → ℝ) → ι → ℝ) := by
  apply continuous_pi
  intro i
  by_cases hi : i = base
  · simpa only [restore, dite_eq_left hi] using (continuous_const : Continuous (fun _ : Index base → ℝ => t))
  · simpa only [restore, dite_eq_right hi] using (continuous_apply (⟨i, hi⟩ : Index base))

theorem isProperMap_restore (base : ι) (t : ℝ) : IsProperMap (restore base t : (Index base → ℝ) → ι → ℝ) := by
  let rest : (ι → ℝ) → Index base → ℝ := fun x j => x j.val
  have hrest : Continuous rest := continuous_pi (fun j => continuous_apply j.val)
  have hcomp : rest ∘ restore base t = id := by
    funext x j
    exact restore_other base t x j
  have hemb : IsEmbedding (restore base t : (Index base → ℝ) → ι → ℝ) :=
    IsEmbedding.of_comp (continuous_restore base t) hrest (by rw [hcomp]; exact IsEmbedding.id)
  have hrange : range (restore base t : (Index base → ℝ) → ι → ℝ) = {x | x base = t} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact restore_base base t y
    · intro hx
      exact ⟨rest x, restore_coordinates base t x hx⟩
  exact (show IsClosedEmbedding (restore base t : (Index base → ℝ) → ι → ℝ) from
    ⟨hemb, hrange ▸ isClosed_eq (continuous_apply base) continuous_const⟩).isProperMap

theorem isProperMap_family (base : ι) (p : MvPolynomial ι R) (φ : R →+* ℝ) (t : ℝ)
    (hp : IsProperMap (fun x => p.eval₂ φ x)) :
    IsProperMap (fun x : Index base → ℝ => (family base p).eval₂ (Polynomial.eval₂RingHom φ t) x) := by
  have he : (fun x : Index base → ℝ => (family base p).eval₂ (Polynomial.eval₂RingHom φ t) x) =
      (fun x => p.eval₂ φ x) ∘ restore base t := funext (eval_family base p φ t)
  rw [he]
  exact hp.comp (isProperMap_restore base t)

section Derivatives
variable [Fintype ι]

noncomputable def tangent (base : ι) : (Index base → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => if hi : i = base then 0 else ContinuousLinearMap.proj ⟨i, hi⟩)

theorem hasFDerivAt_restore (base : ι) (t : ℝ) (x : Index base → ℝ) :
    HasFDerivAt (restore base t) (tangent base) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i = base
  · simpa [restore, tangent, hi] using (hasFDerivAt_const t x)
  · simpa [restore, tangent, hi] using (hasFDerivAt_apply (𝕜 := ℝ) (⟨i, hi⟩ : Index base) x)

/-- Regularity of the combined hypersurface/sweep map is precisely strong
enough to make the remaining-coordinate level equation regular. -/
theorem surjective_fderiv_family (base : ι) (p : MvPolynomial ι R) (φ : R →+* ℝ)
    (t : ℝ) (x : Index base → ℝ)
    (hregular : Function.Surjective (fderiv ℝ
      (HypersurfaceSweep.combined (fun y => p.eval₂ φ y) (fun y => y base)) (restore base t x))) :
    Function.Surjective (fderiv ℝ
      (fun y : Index base → ℝ => (family base p).eval₂ (Polynomial.eval₂RingHom φ t) y) x) := by
  have hder := PolynomialCalculus.hasFDerivAt φ p (restore base t x)
  change Function.Surjective (fderiv ℝ (fun y : ι → ℝ => (p.eval₂ φ y, y base)) (restore base t x)) at hregular
  rw [(hder.prodMk (hasFDerivAt_apply (𝕜 := ℝ) base (restore base t x))).fderiv] at hregular
  have he : (fun y : Index base → ℝ => (family base p).eval₂ (Polynomial.eval₂RingHom φ t) y) =
      (fun y => p.eval₂ φ (restore base t y)) := funext (eval_family base p φ t)
  rw [he]
  change Function.Surjective (fderiv ℝ ((fun y => p.eval₂ φ y) ∘ restore base t) x)
  rw [(hder.comp x (hasFDerivAt_restore base t x)).fderiv]
  intro a
  obtain ⟨v, hv⟩ := hregular (a, 0)
  have hvbase : v base = 0 := congrArg Prod.snd hv
  have hvt : tangent base (fun j => v j.val) = v := by
    funext i
    by_cases hi : i = base
    · simpa [tangent, hi] using hvbase.symm
    · simp [tangent, hi]
  refine ⟨fun j => v j.val, ?_⟩
  change PolynomialCalculus.derivative φ p (restore base t x) (tangent base (fun j => v j.val)) = a
  rw [hvt]
  exact congrArg Prod.fst hv

end Derivatives

/-- This is the actual reduction in dimension of a coordinate-sweep fiber.
It includes irrational levels and sweep coordinates, and empty fibers. -/
noncomputable def fiberHomeomorph (p : MvPolynomial ι R) (φ : R →+* ℝ) (base : ι) (c t : ℝ) :
    ((HypersurfaceSweep.projection (fun x => p.eval₂ φ x) (fun x => x base) c) ⁻¹' {t}) ≃ₜ
      {x : Index base → ℝ | (family base p).eval₂ (Polynomial.eval₂RingHom φ t) x = c} where
  toFun := fun x => ⟨fun j => x.val.val j.val, by
    change (family base p).eval₂ (Polynomial.eval₂RingHom φ t) (fun j => x.val.val j.val) = c
    exact (eval_family base p φ t (fun j => x.val.val j.val)).trans
      ((congrArg (fun y => p.eval₂ φ y) (restore_coordinates base t x.val.val x.property)).trans x.val.property)⟩
  invFun := fun x => ⟨⟨restore base t x.val, by
    change p.eval₂ φ (restore base t x.val) = c
    exact (eval_family base p φ t x.val).symm.trans x.property⟩,
    restore_base base t x.val⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact restore_coordinates base t x.val.val x.property
  right_inv := by
    intro x
    apply Subtype.ext
    funext j
    exact restore_other base t x.val j
  continuous_toFun := by
    exact (continuous_pi fun j => (continuous_apply j.val).comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := by
    exact (((continuous_restore base t).comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem card_index_add_one [Finite ι] (base : ι) : Nat.card (Index base) + 1 = Nat.card ι := by
  simpa only [Finite.card_option] using Nat.card_congr (Equiv.optionSubtypeNe base)

end LeanCanny.Geometry.CoordinateSlice
