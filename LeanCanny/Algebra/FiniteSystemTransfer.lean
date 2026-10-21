/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalRepresentationTransfer
public import LeanCanny.Algebra.FiniteZeroLocus

/-! # Complete finite-system decoding in arbitrary extension fields

A finite full zero set over an algebraically closed field has no additional
solutions in larger fields. The evaluation kernel of any putative new solution
is prime above the system ideal, hence maximal, and is a point ideal. Applying
this in a common algebraically closed overfield removes the algebraic-coordinate
hypothesis from completeness of rational univariate representations.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteSystemCoordinates
open MvPolynomial
open scoped Classical

variable {ι τ K L : Type*} [Fintype ι] [Field K] [Field L] [Algebra K L]

omit [Fintype ι] in
/-- An embedding into a field with finitely many solutions bounds the source zero set. -/
theorem finite_zeroSet_of_embedding
    {E : Type*} [Field E] [Algebra K E]
    (p : τ → MvPolynomial ι K) (f : L →ₐ[K] E)
    (hf : (zeroSet (L := E) p).Finite) : (zeroSet (L := L) p).Finite := by
  apply Set.Finite.of_injOn (f := fun x j => f (x j)) ?_ ?_ hf
  · intro x hx j
    have hm := MvPolynomial.comp_aeval_apply (f := x) f (p j)
    exact hm.symm.trans ((congrArg f (hx j)).trans (map_zero f))
  · intro x _ y _ h
    funext j
    exact f.injective (congrFun h j)

theorem exists_solution_lift_of_finite [IsAlgClosed L]
    {E : Type*} [Field E] [Algebra K E]
    (p : τ → MvPolynomial ι K) (hf : (zeroSet (L := L) p).Finite)
    (f : L →ₐ[K] E) (x : ι → E) (hx : x ∈ zeroSet (L := E) p) :
    ∃ y ∈ zeroSet (L := L) p, ∀ i, f (y i) = x i := by
  let q : τ → MvPolynomial ι L := fun j => (p j).map (algebraMap K L)
  let I : Ideal (MvPolynomial ι L) := Ideal.span (Set.range q)
  let e : MvPolynomial ι L →+* E := eval₂Hom (f : L →+* E) x
  let P := RingHom.ker e
  have he (j : τ) : e (q j) = 0 := by
    change eval₂ (f : L →+* E) x ((p j).map (algebraMap K L)) = 0
    rw [eval₂_map]
    rw [f.comp_algebraMap]
    exact hx j
  have hIP : I ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact he j
  have hzero : MvPolynomial.zeroLocus L I = zeroSet (L := L) p := by
    ext y
    change y ∈ MvPolynomial.zeroLocus L (Ideal.span (Set.range q)) ↔ _
    rw [MvPolynomial.zeroLocus_span]
    simp only [Set.mem_ofPred_eq, Set.forall_mem_range, MvPolynomial.aeval_eq_eval]
    change (∀ j, eval y ((p j).map (algebraMap K L)) = 0) ↔ _
    simp only [eval_map]
    rfl
  let : P.IsPrime := RingHom.ker_isPrime e
  have hmax : P.IsMaximal := FiniteZeroLocus.isMaximal_of_finite_zeroLocus I P
    (hzero.symm ▸ hf) hIP
  obtain ⟨y, hy⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal L hmax
  refine ⟨y, ?_, ?_⟩
  · intro j
    have hm : q j ∈ P := hIP (Ideal.subset_span (Set.mem_range_self j))
    rw [hy, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hm
    exact (eval_map (algebraMap K L) y (p j)).symm.trans hm
  · intro i
    have hm : X i - C (y i) ∈ P := by
      rw [hy, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    have hz : x i - f (y i) = 0 := by
      change e (X i - C (y i)) = 0 at hm
      have heval := (map_sub e (X i) (C (y i))).symm.trans hm
      rw [show e (X i) = x i from eval₂Hom_X' _ _ _,
        show e (C (y i)) = f (y i) from
          (eval₂Hom_C _ _ _).trans (congrFun (AlgHom.coe_toRingHom f) _)] at heval
      exact heval
    exact (sub_eq_zero.mp hz).symm

namespace Representation
variable {p : τ → MvPolynomial ι K}

/-- Finiteness replaces the separate algebraicity hypothesis on a solution. -/
theorem complete_of_finite [IsAlgClosure K L]
    {E : Type*} [Field E] [Algebra K E]
    (r : Representation (L := L) p) (hf : (zeroSet (L := L) p).Finite)
    (x : ι → E) (hx : x ∈ zeroSet (L := E) p) :
    Polynomial.aeval (AsymmetricProjection.projection r.direction x) r.polynomial = 0 ∧
      r.decodeOver (AsymmetricProjection.projection r.direction x) = x := by
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let i : E →ₐ[K] AlgebraicClosure E := IsScalarTower.toAlgHom K E (AlgebraicClosure E)
  let f : L →ₐ[K] AlgebraicClosure E := IsAlgClosed.lift
  have hxF : (fun j => i (x j)) ∈ zeroSet (L := AlgebraicClosure E) p := by
    intro j
    have hm := MvPolynomial.comp_aeval_apply (f := x) i (p j)
    exact hm.symm.trans ((congrArg i (hx j)).trans (map_zero i))
  obtain ⟨y, hy, hxy⟩ := exists_solution_lift_of_finite p hf f (fun j => i (x j)) hxF
  have hproj : f (AsymmetricProjection.projection r.direction y) =
      i (AsymmetricProjection.projection r.direction x) := by
    simp only [AsymmetricProjection.projection, map_sum, map_mul, map_natCast, hxy]
  have hr := (r.roots _).mpr ⟨y, hy, rfl⟩
  have hroot : Polynomial.aeval (i (AsymmetricProjection.projection r.direction x)) r.polynomial = 0 := by
    rw [← hproj, Polynomial.aeval_algHom_apply, hr, map_zero]
  refine ⟨i.injective ((Polynomial.aeval_algHom_apply i _ _).symm.trans
    (hroot.trans (map_zero i).symm)), ?_⟩
  have hd : r.decodeOver (i (AsymmetricProjection.projection r.direction x)) = fun j => i (x j) := by
    rw [← hproj, ← r.map_decodeOver f]
    change (fun j => f (r.decode (AsymmetricProjection.projection r.direction y) j)) = _
    rw [r.decode_projection y hy]
    exact funext hxy
  have hm := (r.map_decodeOver i (AsymmetricProjection.projection r.direction x)).trans hd
  funext j
  exact i.injective (congrFun hm j)

/-- All parameter roots and all solutions correspond in any target extension. -/
noncomputable def rootEquivOfFinite [IsAlgClosure K L]
    {E : Type*} [Field E] [Algebra K E]
    (r : Representation (L := L) p) (hf : (zeroSet (L := L) p).Finite) :
    {θ : E // Polynomial.aeval θ r.polynomial = 0} ≃ zeroSet (L := E) p where
  toFun θ := ⟨r.decodeOver θ.val, (r.decodeOver_sound θ.val θ.property).1⟩
  invFun x := ⟨AsymmetricProjection.projection r.direction x.val,
    (r.complete_of_finite hf x.val x.property).1⟩
  left_inv θ := Subtype.ext (r.decodeOver_sound θ.val θ.property).2.1
  right_inv x := Subtype.ext (r.complete_of_finite hf x.val x.property).2

theorem exists_solution_iff [IsAlgClosure K L]
    {E : Type*} [Field E] [Algebra K E]
    (r : Representation (L := L) p) (hf : (zeroSet (L := L) p).Finite) (P : (ι → E) → Prop) :
    (∃ x ∈ zeroSet (L := E) p, P x) ↔
      ∃ θ : E, Polynomial.aeval θ r.polynomial = 0 ∧ P (r.decodeOver θ) := by
  constructor
  · rintro ⟨x, hx, hP⟩
    have hc := r.complete_of_finite hf x hx
    exact ⟨AsymmetricProjection.projection r.direction x, hc.1, hc.2.symm ▸ hP⟩
  · rintro ⟨θ, hθ, hP⟩
    exact ⟨r.decodeOver θ, (r.decodeOver_sound θ hθ).1, hP⟩

end Representation
end LeanCanny.Algebra.FiniteSystemCoordinates
