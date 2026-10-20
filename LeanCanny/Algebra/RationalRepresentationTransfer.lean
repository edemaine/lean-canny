/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteSystemCoordinates

/-! # Sound rational decoding in arbitrary extension fields

A representation proved over an algebraic closure remains sound at eliminant
roots in any extension of the input field, including the reals. Embed both
fields into an algebraic closure of the target; splitting lifts each parameter
root back to the source. Polynomial evaluation and rational decoding commute
with the embeddings. Conversely, solutions with algebraic coordinates are
recovered from parameter roots in their own field. Coefficient and space bounds
are not supplied here.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteSystemCoordinates
open Polynomial AsymmetricProjection

variable {ι τ K L : Type*} [Fintype ι] [Field K] [Field L] [Algebra K L]

namespace Representation
variable {p : τ → MvPolynomial ι K}

noncomputable def decodeOver {E : Type*} [Field E] [Algebra K E]
    (r : Representation (L := L) p) (θ : E) : ι → E := fun j =>
  Polynomial.aeval θ (r.numerator j) / Polynomial.aeval θ (r.denominator j)

theorem map_decodeOver {E F : Type*} [Field E] [Field F] [Algebra K E] [Algebra K F]
    (r : Representation (L := L) p) (f : E →ₐ[K] F) (θ : E) :
    (fun j => f (r.decodeOver θ j)) = r.decodeOver (f θ) := by
  funext j
  simp [decodeOver, Polynomial.aeval_algHom_apply]

omit [Fintype ι] in
private theorem map_zeroSet {E F : Type*} [Field E] [Field F] [Algebra K E] [Algebra K F]
    (f : E →ₐ[K] F) (x : ι → E) (hx : x ∈ zeroSet (L := E) p) :
    (fun j => f (x j)) ∈ zeroSet (L := F) p := by
  intro j
  change MvPolynomial.aeval (fun i => f (x i)) (p j) = 0
  have he : MvPolynomial.aeval x (p j) = 0 := hx j
  have hm := MvPolynomial.comp_aeval_apply (f := x) f (p j)
  exact hm.symm.trans ((congrArg f he).trans (map_zero f))

omit [Fintype ι] in
private theorem lift_root {F : Type*} [Field F] [Algebra K F] (q : K[X]) (hq : q.Monic)
    (hs : (q.map (algebraMap K L)).Splits) (f : L →ₐ[K] F) (θ : F)
    (hθ : Polynomial.aeval θ q = 0) :
    ∃ a : L, Polynomial.aeval a q = 0 ∧ f a = θ := by
  have hm : θ ∈ q.rootSet F := hq.mem_rootSet.mpr hθ
  rw [← hs.image_rootSet f] at hm
  obtain ⟨a, ha, he⟩ := hm
  exact ⟨a, hq.mem_rootSet.mp ha, he⟩

theorem decodeOver_sound_of_embedding [IsAlgClosed L]
    {F : Type*} [Field F] [Algebra K F] (r : Representation (L := L) p)
    (f : L →ₐ[K] F) (θ : F) (hθ : Polynomial.aeval θ r.polynomial = 0) :
    r.decodeOver θ ∈ zeroSet (L := F) p ∧
      projection r.direction (r.decodeOver θ) = θ ∧
      ∀ j, Polynomial.aeval θ (r.denominator j) ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := lift_root r.polynomial r.monic (IsAlgClosed.splits _) f θ hθ
  have hr := r.decode_of_root a ha
  have hdecode : (fun j => f (r.decode a j)) = r.decodeOver (f a) := r.map_decodeOver f a
  refine ⟨?_, ?_, ?_⟩
  · rw [← hdecode]
    exact map_zeroSet f (r.decode a) hr.1
  · rw [← hdecode]
    have he : projection r.direction (fun j => f (r.decode a j)) =
        f (projection r.direction (r.decode a)) := by simp [projection]
    rw [he, hr.2.1]
  · intro j
    rw [Polynomial.aeval_algHom_apply]
    exact fun hz => hr.2.2 j (f.injective (hz.trans (map_zero f).symm))

/-- Algebraic-closure representations decode soundly in every extension field.
No Galois or algebraicity hypothesis is required of the target extension. -/
theorem decodeOver_sound [IsAlgClosure K L]
    {E : Type*} [Field E] [Algebra K E] (r : Representation (L := L) p)
    (θ : E) (hθ : Polynomial.aeval θ r.polynomial = 0) :
    r.decodeOver θ ∈ zeroSet (L := E) p ∧
      projection r.direction (r.decodeOver θ) = θ ∧
      ∀ j, Polynomial.aeval θ (r.denominator j) ≠ 0 := by
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let i : E →ₐ[K] AlgebraicClosure E := IsScalarTower.toAlgHom K E (AlgebraicClosure E)
  let f : L →ₐ[K] AlgebraicClosure E := IsAlgClosed.lift
  have hroot : Polynomial.aeval (i θ) r.polynomial = 0 := by
    rw [Polynomial.aeval_algHom_apply, hθ, map_zero]
  have hs := r.decodeOver_sound_of_embedding f (i θ) hroot
  have hdecode := r.map_decodeOver i θ
  refine ⟨?_, ?_, ?_⟩
  · intro j
    change MvPolynomial.aeval (r.decodeOver θ) (p j) = 0
    have hj : MvPolynomial.aeval (fun a => i (r.decodeOver θ a)) (p j) = 0 := by
      rw [hdecode]
      exact hs.1 j
    have hm := MvPolynomial.comp_aeval_apply (f := r.decodeOver θ) i (p j)
    exact i.injective ((hm.trans hj).trans (map_zero i).symm)
  · apply i.injective
    calc
      i (projection r.direction (r.decodeOver θ)) =
          projection r.direction (fun j => i (r.decodeOver θ j)) := by simp [projection]
      _ = projection r.direction (r.decodeOver (i θ)) := congrArg (projection r.direction) hdecode
      _ = i θ := hs.2.1
  · intro j hz
    apply hs.2.2 j
    rw [Polynomial.aeval_algHom_apply, hz, map_zero]

/-- Completeness holds in every algebraic target extension. -/
theorem complete_at_solution [IsAlgClosure K L]
    {E : Type*} [Field E] [Algebra K E] [Algebra.IsAlgebraic K E]
    (r : Representation (L := L) p) (x : ι → E) (hx : x ∈ zeroSet (L := E) p) :
    Polynomial.aeval (projection r.direction x) r.polynomial = 0 ∧
      r.decodeOver (projection r.direction x) = x := by
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let f : E →ₐ[K] L := IsAlgClosed.lift
  have hxL := map_zeroSet f x hx
  have hproj : projection r.direction (fun j => f (x j)) = f (projection r.direction x) := by
    simp [projection]
  have hroot := (r.roots _).mpr ⟨fun j => f (x j), hxL, rfl⟩
  rw [hproj, Polynomial.aeval_algHom_apply] at hroot
  refine ⟨f.injective (hroot.trans (map_zero f).symm), ?_⟩
  have hd : r.decodeOver (f (projection r.direction x)) = fun j => f (x j) := by
    rw [← hproj]
    exact r.decode_projection _ hxL
  have hm := (r.map_decodeOver f (projection r.direction x)).trans hd
  funext j
  exact f.injective (congrFun hm j)

/-- Only the coordinates of the solution need be algebraic over K; the rest of
the target field may contain transcendental elements. -/
theorem complete_at_algebraic_solution [IsAlgClosure K L]
    {E : Type*} [Field E] [Algebra K E] (r : Representation (L := L) p)
    (x : ι → E) (hx : x ∈ zeroSet (L := E) p) (halg : ∀ j, IsAlgebraic K (x j)) :
    Polynomial.aeval (projection r.direction x) r.polynomial = 0 ∧
      r.decodeOver (projection r.direction x) = x := by
  let F := IntermediateField.adjoin K (Set.range x)
  let : Algebra.IsAlgebraic K F := IntermediateField.isAlgebraic_adjoin (by
    rintro _ ⟨j, rfl⟩
    exact (halg j).isIntegral)
  let xF : ι → F := fun j => ⟨x j, IntermediateField.subset_adjoin K _ (Set.mem_range_self j)⟩
  let i : F →ₐ[K] E := F.val
  have hxF : xF ∈ zeroSet (L := F) p := by
    intro j
    change MvPolynomial.aeval xF (p j) = 0
    have hm := MvPolynomial.comp_aeval_apply (f := xF) i (p j)
    have he : MvPolynomial.aeval (fun a => i (xF a)) (p j) = 0 := hx j
    exact i.injective ((hm.trans he).trans (map_zero i).symm)
  have hc := r.complete_at_solution xF hxF
  have hproj : i (projection r.direction xF) = projection r.direction x := by
    simp [projection, i, xF]
  refine ⟨?_, ?_⟩
  · rw [← hproj, Polynomial.aeval_algHom_apply, hc.1, map_zero]
  · have hm := r.map_decodeOver i (projection r.direction xF)
    rw [hproj, hc.2] at hm
    exact hm.symm

theorem decodeOver_injective_on_roots [IsAlgClosure K L]
    {E : Type*} [Field E] [Algebra K E] (r : Representation (L := L) p) :
    Set.InjOn (r.decodeOver (E := E)) {θ : E | Polynomial.aeval θ r.polynomial = 0} := by
  intro θ hθ η hη he
  have ht := (r.decodeOver_sound θ hθ).2.1
  have hu := (r.decodeOver_sound η hη).2.1
  exact ht.symm.trans ((congrArg (projection r.direction) he).trans hu)

/-- Over an algebraic target extension, parameter roots and full solutions
are in bijection, even if the target extension is not Galois. -/
noncomputable def rootEquivOver [IsAlgClosure K L]
    {E : Type*} [Field E] [Algebra K E] [Algebra.IsAlgebraic K E]
    (r : Representation (L := L) p) :
    {θ : E // Polynomial.aeval θ r.polynomial = 0} ≃ zeroSet (L := E) p where
  toFun θ := ⟨r.decodeOver θ.val, (r.decodeOver_sound θ.val θ.property).1⟩
  invFun x := ⟨projection r.direction x.val, (r.complete_at_solution x.val x.property).1⟩
  left_inv θ := Subtype.ext (r.decodeOver_sound θ.val θ.property).2.1
  right_inv x := Subtype.ext (r.complete_at_solution x.val x.property).2

end Representation
end LeanCanny.Algebra.FiniteSystemCoordinates
