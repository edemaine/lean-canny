/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteComplexSurjectivity
public import LeanCanny.Algebra.KoszulWeightedContraction
public import LeanCanny.Algebra.KoszulGenericExact
public import LeanCanny.Algebra.MacaulayQuotientSurjectivity

/-! # Positive weighted Koszul exactness gives the sharp Macaulay target

The coordinate-power complex is an exact reference on the same finite
weighted pieces. Rank comparison shows that positive-degree exactness for
the input complex forces degree-zero surjectivity. Canonical coordinates
then give full Macaulay row surjectivity and a unit polynomial quotient.
Exactness from absence of projective roots is proved in `KoszulWeightedExact`.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {K : Type*} [Field K]

theorem zero_surjective_of_weighted_exact (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hex : ∀ k, LinearMap.ker (differential p d (Macaulay.level d) W hp hW k) =
      LinearMap.range (differential p d (Macaulay.level d) W hp hW (k + 1))) :
    Function.Surjective (differential p d (Macaulay.level d) W hp hW 0) := by
  let V : ℕ → Type _ := fun k => ↥(space (R := K) d (Macaulay.level d) W k)
  let : Subsingleton (V (n + 1)) := Submodule.subsingleton_iff_eq_bot.mpr
    (space_eq_bot_of_lt d (Macaulay.level d) W (n + 1) (Nat.lt_succ_self n))
  exact FiniteComplexSurjectivity.surjective_of_exact V
    (differential p d (Macaulay.level d) W hp hW)
    (differential (Macaulay.powers (R := K) d) d (Macaulay.level d) W (powers_homogeneous d) hW)
    hex (powers_weighted_exact d W hW) n (powers_weighted_zero_surjective d W hW)

theorem fullMatrix_surjective_of_weighted_zero_surjective (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hs : Function.Surjective (differential p d (Macaulay.level d) W hp hW 0)) :
    Function.Surjective (fun v => Matrix.vecMul v (Macaulay.fullMatrix p d W)) := by
  intro v
  let es := macaulaySourceEquiv d W
  let et := macaulayTargetEquiv d W
  let x := (canonicalBasis (R := K) d (Macaulay.level d) W 0).equivFun.symm (v ∘ et.symm)
  obtain ⟨y, hy⟩ := hs x
  let w := (canonicalBasis (R := K) d (Macaulay.level d) W 1).equivFun y
  let M := canonicalMatrix p d (Macaulay.level d) W hp hW 0
  have hw : Matrix.vecMul w M = v ∘ et.symm := by
    have he := canonicalMatrix_vecMul_coordinates p d (Macaulay.level d) W hp hW 0 y
    rw [hy] at he
    exact he.trans (LinearEquiv.apply_symm_apply _ _)
  refine ⟨w ∘ es, ?_⟩
  have hm : M.submatrix es et = Macaulay.fullMatrix p d W := canonicalMatrix_macaulay p d W hp hW
  have he := Matrix.submatrix_vecMul_equiv M (w ∘ es) es et
  have hc : (w ∘ es) ∘ es.symm = w := by funext a; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [hm, hc, hw] at he
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using he

theorem fullMatrix_surjective_of_weighted_exact (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hex : ∀ k, LinearMap.ker (differential p d (Macaulay.level d) W hp hW k) =
      LinearMap.range (differential p d (Macaulay.level d) W hp hW (k + 1))) :
    Function.Surjective (fun v => Matrix.vecMul v (Macaulay.fullMatrix p d W)) :=
  fullMatrix_surjective_of_weighted_zero_surjective p d W hp hW (zero_surjective_of_weighted_exact p d W hp hW hex)

end LeanCanny.Algebra.KoszulWeighted

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {K : Type*} [Field K]

theorem polynomialValue_isUnit_of_weighted_exact (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hex : ∀ k, LinearMap.ker (KoszulWeighted.differential p d (Macaulay.level d) W hp hW k) =
      LinearMap.range (KoszulWeighted.differential p d (Macaulay.level d) W hp hW (k + 1))) :
    IsUnit (polynomialValue d W hdegree hW p) :=
  polynomialValue_isUnit_of_fullMatrix_surjective d W hdegree hW p hp hd
    (KoszulWeighted.fullMatrix_surjective_of_weighted_exact p d W hp hW hex)

end LeanCanny.Algebra.MacaulayUniversal
