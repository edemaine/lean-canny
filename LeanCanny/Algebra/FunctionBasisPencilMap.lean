/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FunctionBasisPencil

/-! # Changing fields in the weighted Gram separation test

The pencil splits already over the source field. An injective coefficient
map therefore introduces no additional roots. In particular, the rational
separation criterion agrees with counting real roots of the integer pencil.
-/

@[expose] public section
namespace LeanCanny.Algebra.FunctionBasisPencil
open Polynomial
open scoped Classical BigOperators

variable {R S ι : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Fintype ι] [DecidableEq ι]

theorem mapped_roots (f : R →+* S) (hf : Function.Injective f) (A : Matrix ι ι R) (v : ι → R)
    (hA : A.det ≠ 0) : ((pencil A v).det.map f).roots = Finset.univ.val.map (f ∘ v) := by
  have hg : f (gram A).det ≠ 0 := by
    intro hz
    have hn : (gram A).det ≠ 0 := by
      rw [gram, Matrix.det_mul, Matrix.det_transpose]
      exact mul_ne_zero hA hA
    exact hn (hf (hz.trans (map_zero f).symm))
  rw [determinant, Polynomial.map_mul, Polynomial.map_C, roots_C_mul _ hg]
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have he : (∏ i, ((X : S[X]) - C (f (v i)))) =
      ((Finset.univ.val.map (f ∘ v)).map (fun z => X - C z)).prod := by
    rw [Multiset.map_map]
    rfl
  rw [he, roots_multiset_prod_X_sub_C]

variable [DecidableEq S]

theorem mapped_rootCount_eq_card_iff (f : R →+* S) (hf : Function.Injective f)
    (A : Matrix ι ι R) (v : ι → R) (hA : A.det ≠ 0) :
    ((pencil A v).det.map f).roots.toFinset.card = Fintype.card ι ↔ Function.Injective v := by
  have hr : ((pencil A v).det.map f).roots.toFinset = Finset.univ.image (f ∘ v) := by
    rw [mapped_roots f hf A v hA]
    rfl
  rw [hr, ← Finset.card_univ, Finset.card_image_iff]
  rw [Finset.coe_univ, Set.injOn_univ]
  exact ⟨fun h x y he => h (congrArg f he), fun h => hf.comp h⟩

end LeanCanny.Algebra.FunctionBasisPencil
