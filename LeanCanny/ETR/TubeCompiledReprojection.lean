/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCompiledAffineLift

/-! # Changing the extra projection preserves compiled affine solutions

Every compiled root consists of its spatial tuple and the uniquely determined
linear projection. Decoding the tuple and lifting with another projection gives
a bijection of the full affine root sets, including singular roots.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCompiledAffineRoots
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical BigOperators
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det
variable {K : Type*} [Field K]

omit [Field K] in
theorem spatialPoint_decodedPoint (bits : List Bool) (z : Fin (TubeParameter.spatialCount bits) → K) :
    spatialPoint bits (decodedPoint bits z) = fun j => z j.succ := by
  funext j
  change z ((TubeMacaulay.coordinateEquiv (TubeIndexed.arity bits))
    ((TubeMacaulay.coordinateEquiv (TubeIndexed.arity bits)).symm j)).succ = z j.succ
  rw [Equiv.apply_symm_apply]

variable (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
  (ell : List Bool → ℕ → ℤ) (c : List Bool) (epsilon : K)

theorem projection_eq_of_compiled (z : Fin (TubeParameter.spatialCount (source c)) → K)
    (hz : ∀ i, MvPolynomial.eval z
      (TubeCharacteristicQuotient.finiteSystem source active n d ell c epsilon i) = 0) :
    z (TubeCharacteristicQuotient.finiteParameterIndex (source c)) =
      ∑ j : Fin (pointCount (TubeIndexed.arity (source c)) + 1),
        (Int.castRingHom K) (ell c (j.val + 1)) * z j.succ := by
  have h := hz (TubeCharacteristicQuotient.finiteParameterIndex (source c))
  rw [TubeCharacteristicQuotient.eval_finiteSystem] at h
  simp_rw [TubeCharacteristicQuotient.eval_finiteChartVariables] at h
  exact sub_eq_zero.mp ((eval_projection_row source active n d ell c epsilon _ _).symm.trans h)

theorem compiledPoint_decodedPoint (z : Fin (TubeParameter.spatialCount (source c)) → K)
    (hz : ∀ i, MvPolynomial.eval z
      (TubeCharacteristicQuotient.finiteSystem source active n d ell c epsilon i) = 0) :
    compiledPoint (source c) (ell c) (decodedPoint (source c) z) = z := by
  unfold compiledPoint
  rw [spatialPoint_decodedPoint]
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  exact (projection_eq_of_compiled source active n d ell c epsilon z hz).symm

theorem tail_injective_on_roots : Set.InjOn
    (fun z : Fin (TubeParameter.spatialCount (source c)) → K =>
      fun j : Fin (pointCount (TubeIndexed.arity (source c)) + 1) => z j.succ)
    {z | ∀ i, MvPolynomial.eval z
      (TubeCharacteristicQuotient.finiteSystem source active n d ell c epsilon i) = 0} := by
  intro z hz w hw he
  have h0 := (projection_eq_of_compiled source active n d ell c epsilon z hz).trans
    ((congrArg (fun y => ∑ j, (Int.castRingHom K) (ell c (j.val + 1)) * y j) he).trans
      (projection_eq_of_compiled source active n d ell c epsilon w hw).symm)
  funext i
  exact Fin.cases h0 (fun j => congrFun he j) i

/-- The predicate form avoids requiring a stored enumeration of the zero set. -/
def RootSet : Set (Fin (TubeParameter.spatialCount (source c)) → K) :=
  {z | ∀ i, MvPolynomial.eval z
    (TubeCharacteristicQuotient.finiteSystem source active n d ell c epsilon i) = 0}

noncomputable def reprojectEquiv (ell' : List Bool → ℕ → ℤ)
    (hd : ∀ i, i < TubeParameter.parameterCount (source c) →
      (d c i).eval₂ (Int.castRingHom K) epsilon ≠ 0) :
    RootSet source active n d ell c epsilon ≃ RootSet source active n d ell' c epsilon where
  toFun z := ⟨compiledPoint (source c) (ell' c) (decodedPoint (source c) z.val),
    compiled_root_of_spatial source active n d ell' c epsilon hd _
      (spatial_roots_of_compiled source active n d ell c epsilon hd z.val z.property)⟩
  invFun z := ⟨compiledPoint (source c) (ell c) (decodedPoint (source c) z.val),
    compiled_root_of_spatial source active n d ell c epsilon hd _
      (spatial_roots_of_compiled source active n d ell' c epsilon hd z.val z.property)⟩
  left_inv z := Subtype.ext (by
    change compiledPoint (source c) (ell c) (decodedPoint (source c)
      (compiledPoint (source c) (ell' c) (decodedPoint (source c) z.val))) = z.val
    rw [decodedPoint_compiledPoint]
    exact compiledPoint_decodedPoint source active n d ell c epsilon z.val z.property)
  right_inv z := Subtype.ext (by
    change compiledPoint (source c) (ell' c) (decodedPoint (source c)
      (compiledPoint (source c) (ell c) (decodedPoint (source c) z.val))) = z.val
    rw [decodedPoint_compiledPoint]
    exact compiledPoint_decodedPoint source active n d ell' c epsilon z.val z.property)

/-- A coordinate direction is represented in the same integer reader format. -/
def coordinateDirection (j : ℕ) (i : ℕ) : ℤ := if i = j + 1 then 1 else 0

theorem coordinate_projection (bits : List Bool)
    (j : Fin (pointCount (TubeIndexed.arity bits) + 1))
    (z : Fin (TubeParameter.spatialCount bits) → K) :
    compiledPoint bits (coordinateDirection j.val) (decodedPoint bits z)
      (TubeCharacteristicQuotient.finiteParameterIndex bits) = z j.succ := by
  unfold compiledPoint
  rw [spatialPoint_decodedPoint]
  change (∑ i : Fin (pointCount (TubeIndexed.arity bits) + 1),
    (Int.castRingHom K) (coordinateDirection j.val (i.val + 1)) * z i.succ) = z j.succ
  simp [coordinateDirection]
  simp only [← Fin.ext_iff]
  simp

end LeanCanny.ETR.TubeCompiledAffineRoots
