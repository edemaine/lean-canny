/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularJacobianParameters
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The actual generic tube singular ideal is the unit ideal

A maximal quotient would be a field extension containing a singular root,
contradicting generic nonsingularity. This supplies an ideal identity, with no
degree bound on its multipliers.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRegularSingularIdeal
open LeanCanny.Algebra Geometry MvPolynomial
open TubeEncoding TubeProjectionEncoding TubeRegularJacobianGeneric
open TubeRegularJacobianParameters LevelProjectionSpecialization
open scoped Classical
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000

section Transport
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem map_specialize (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* F)
    (p : MvPolynomial (TubeRegularSource.Variable bits) ℤ) :
    (specialize bits φ p).map (algebraMap F E) =
      specialize bits ((algebraMap F E).comp φ) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [specialize_C, Int.coe_castRingHom, map_intCast]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, specialize_X, substitution]
    exact congrArg (fun q => specialize bits ((algebraMap F E).comp φ) p * q)
      (MvPolynomial.map_map φ (algebraMap F E) (TubeMacaulay.image (TubeIndexed.arity bits) i))

theorem eval_specialize_tower (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* F)
    (z : Option (TubeSource.Coordinate bits) → E)
    (p : MvPolynomial (TubeRegularSource.Variable bits) ℤ) :
    aeval z (specialize bits φ p) = p.eval₂ (Int.castRingHom E)
      (nativeAssignment bits ((algebraMap F E).comp φ) z) := by
  rw [← eval_specialize, ← map_specialize]
  simp only [aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_map, RingHom.id_comp]

end Transport

section Generic
variable {K : Type*} [Field K]

abbrev ParameterFieldAt (K : Type*) [Field K] (bits : List Bool) :=
  ParameterField K (TubePolynomial.base (Fin (CompactSource.term bits).arity))

noncomputable def row (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (epsilon delta : K) (i : TubeRegularSource.Index bits) :
    MvPolynomial (Option (TubeSource.Coordinate bits)) (ParameterFieldAt K bits) :=
  specialize bits (genericMap (L := ParameterFieldAt K bits) bits epsilon delta)
    (TubeRegularSource.polynomial bits s i)

noncomputable def determinant (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (epsilon delta : K) :
    MvPolynomial (Option (TubeSource.Coordinate bits)) (ParameterFieldAt K bits) :=
  specialize bits (genericMap (L := ParameterFieldAt K bits) bits epsilon delta)
    (TubeRegularJacobianBudget.polynomial bits s)

noncomputable def ideal (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (epsilon delta : K) :
    Ideal (MvPolynomial (Option (TubeSource.Coordinate bits)) (ParameterFieldAt K bits)) :=
  Ideal.span (Set.range (row bits s epsilon delta) ∪ {determinant bits s epsilon delta})

theorem genericMap_comp {E : Type*} [Field E] [Algebra K E]
    (bits : List Bool) (epsilon delta : K) [Algebra (ParameterFieldAt K bits) E]
    [IsScalarTower K (ParameterFieldAt K bits) E] :
    (algebraMap (ParameterFieldAt K bits) E).comp
        (genericMap (L := ParameterFieldAt K bits) bits epsilon delta) =
      genericMap (L := E) bits epsilon delta := by
  apply MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
  intro i
  unfold genericMap parameterMap
  rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  rcases i with i | (_ | b)
  · rfl
  · rfl
  · cases b <;>
      simp only [Sum.elim_inr, Option.elim_some, Bool.false_eq_true, ite_false, ite_true]
    all_goals exact (IsScalarTower.algebraMap_apply K (ParameterFieldAt K bits) E _).symm

theorem ideal_eq_top [CharZero K] (bits : List Bool)
    (s : Finset (PerturbedSource.Index bits)) (epsilon delta : K) :
    ideal bits s epsilon delta = ⊤ := by
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (ideal bits s epsilon delta) h
  have : M.IsMaximal := hM
  let E := (MvPolynomial (Option (TubeSource.Coordinate bits)) (ParameterFieldAt K bits)) ⧸ M
  let : Field E := Ideal.Quotient.field M
  let z : Option (TubeSource.Coordinate bits) → E := fun i => Ideal.Quotient.mk M (X i)
  have he (p : MvPolynomial (Option (TubeSource.Coordinate bits)) (ParameterFieldAt K bits)) :
      aeval z p = Ideal.Quotient.mk M p := by
    have h := MvPolynomial.aeval_unique (Ideal.Quotient.mkₐ (ParameterFieldAt K bits) M)
    exact (congrArg (fun f => f p) h).symm
  have hz (i : TubeRegularSource.Index bits) :
      (TubeRegularSource.polynomial bits s i).eval₂ (Int.castRingHom E)
        (nativeAssignment bits (genericMap (L := E) bits epsilon delta) z) = 0 := by
    rw [← genericMap_comp bits epsilon delta, ← eval_specialize_tower, he]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hle (Ideal.subset_span (Or.inl (Set.mem_range_self i)))
  have hdet : (TubeRegularJacobianBudget.polynomial bits s).eval₂ (Int.castRingHom E)
      (nativeAssignment bits (genericMap (L := E) bits epsilon delta) z) = 0 := by
    rw [← genericMap_comp bits epsilon delta, ← eval_specialize_tower, he]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hle (Ideal.subset_span (Or.inr (Set.mem_singleton _)))
  exact generic_determinant_ne_zero bits s epsilon delta z hz hdet

end Generic
end LeanCanny.ETR.TubeRegularSingularIdeal
