/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ValidatedSquarefreeSpecialization
public import Mathlib.RingTheory.Localization.FractionRing
/-! # Root-preserving squarefree preprocessing over a characteristic-zero domain

The fraction field chooses a principal-subresultant index once. All actual
polynomial arithmetic remains over the original ring. Its leading coefficient
and selected subresultant give a nonzero exceptional element; every field
specialization avoiding it preserves roots and gives a separable polynomial.
-/
@[expose] public section
namespace LeanCanny.Algebra.DomainSquarefree
open Polynomial PrincipalSubresultant
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Matrix.det
variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
noncomputable def embedding : R →+* FractionRing R := algebraMap _ _
omit [IsDomain R] [CharZero R] in
theorem embedding_injective : Function.Injective (embedding (R := R)) := IsFractionRing.injective _ _

theorem exists_valid (p : Polynomial R) (h : p.natDegree≠0) :
    ∃ k : Fin p.natDegree, ValidatedSquarefreeSpecialization.Valid embedding p p.natDegree k.val :=
  ValidatedSquarefreeSpecialization.exists_valid (L := FractionRing R) embedding p p.natDegree
    (Polynomial.natDegree_map_eq_of_injective embedding_injective p) (Nat.pos_of_ne_zero h)

noncomputable def index (p : Polynomial R) : ℕ :=
  if h : p.natDegree=0 then 0 else (Classical.choose (exists_valid p h)).val

theorem valid_fraction (p : Polynomial R) (h : p.natDegree≠0) :
    ValidatedSquarefreeSpecialization.Valid embedding p p.natDegree (index p) := by
  rw [index,dite_eq_right h]
  exact Classical.choose_spec (exists_valid p h)

noncomputable def polynomial (p : Polynomial R) : Polynomial R :=
  if p.natDegree=0 then 1 else ValidatedSquarefreeSpecialization.polynomial p p.natDegree (index p)

noncomputable def exceptional (p : Polynomial R) : R :=
  p.leadingCoeff * if p.natDegree=0 then 1 else psc p p.derivative p.natDegree (p.natDegree-1) (index p)

theorem exceptional_ne_zero (p : Polynomial R) (hp : p≠0) : exceptional p≠0 := by
  apply mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp)
  split_ifs with h
  · exact one_ne_zero
  · intro H
    have HV := (valid_fraction p h).selected
    exact HV (by rw [H,map_zero])

variable {L : Type*} [Field L] [CharZero L]
omit [CharZero L] in
theorem valid_specialization (φ : R →+* L) (p : Polynomial R) (h : p.natDegree≠0)
    (he : φ (exceptional p)≠0) :
    ValidatedSquarefreeSpecialization.Valid φ p p.natDegree (index p) := by
  have HV := valid_fraction p h
  have HE : φ p.leadingCoeff≠0 ∧ φ (psc p p.derivative p.natDegree (p.natDegree-1) (index p))≠0 := by
    simpa only [exceptional,ite_eq_right h,map_mul,mul_ne_zero_iff] using he
  refine ⟨HV.index_lt,HE.1,?_,HE.2⟩
  intro j hj
  have HZ : psc p p.derivative p.natDegree (p.natDegree-1) j=0 :=
    embedding_injective (by simpa only [map_zero] using HV.lower j hj)
  rw [HZ,map_zero]

omit [CharZero L] in
theorem constant_specialization (φ : R →+* L) (p : Polynomial R) (h : p.natDegree=0)
    (he : φ (exceptional p)≠0) (x : L) : p.eval₂ φ x≠0 := by
  have HL : φ p.leadingCoeff≠0 := by
    simpa only [exceptional,ite_eq_left h,mul_one] using he
  have HP : p=C p.leadingCoeff := by
    simpa only [Polynomial.leadingCoeff,h] using Polynomial.eq_C_of_natDegree_eq_zero h
  rw [HP,Polynomial.eval₂_C]
  exact HL

theorem roots_iff (φ : R →+* L) (p : Polynomial R) (he : φ (exceptional p)≠0) (x : L) :
    (polynomial p).eval₂ φ x=0 ↔ p.eval₂ φ x=0 := by
  by_cases h : p.natDegree=0
  · rw [polynomial,ite_eq_left h]
    simp only [Polynomial.eval₂_one,one_ne_zero,false_iff]
    exact constant_specialization φ p h he x
  · rw [polynomial,ite_eq_right h]
    exact ValidatedSquarefreeSpecialization.roots_iff φ p p.natDegree (index p) le_rfl (valid_specialization φ p h he) x

theorem separable (φ : R →+* L) (p : Polynomial R) (he : φ (exceptional p)≠0) :
    ((polynomial p).map φ).Separable := by
  by_cases h : p.natDegree=0
  · simp only [polynomial,ite_eq_left h,Polynomial.map_one]
    exact Polynomial.separable_one
  · rw [polynomial,ite_eq_right h]
    exact ValidatedSquarefreeSpecialization.separable φ p p.natDegree (index p) le_rfl (valid_specialization φ p h he)
theorem polynomial_ne_zero (p : Polynomial R) (hp : p≠0) : polynomial p≠0 := by
  have HE : embedding (exceptional p)≠0 := by
    intro HZ
    exact exceptional_ne_zero p hp (embedding_injective (by simpa only [map_zero] using HZ))
  have HN := (separable embedding p HE).ne_zero
  intro HZ
  exact HN (by rw [HZ,Polynomial.map_zero])
end LeanCanny.Algebra.DomainSquarefree
