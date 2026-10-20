/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AsymmetricBaseCoordinates
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Data.Set.Card

/-! # Rational representations of full finite polynomial zero sets

A finite full zero set in a characteristic-zero Galois extension has a bounded
integer projection and a rational univariate representation over the input field.
In particular, this applies in an algebraic closure without a supplied finite
Galois ambient field. These are algebraic existence results; computing the
representation and bounding its coefficient sizes remain open.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteSystemCoordinates
open Polynomial AsymmetricProjection

variable {ι τ K L : Type*} [Fintype ι] [Field K] [Field L] [Algebra K L]

def zeroSet (p : τ → MvPolynomial ι K) : Set (ι → L) :=
  {x | ∀ j, MvPolynomial.eval₂ (algebraMap K L) x (p j) = 0}

/-- A rational univariate representation with no extra parameter roots in L. -/
structure Representation (p : τ → MvPolynomial ι K) where
  direction : ι → ℕ
  polynomial : K[X]
  numerator : ι → K[X]
  denominator : ι → K[X]
  direction_le : ∀ i, direction i ≤ (Fintype.card ι + 1) * (zeroSet (L := L) p).ncard ^ 4
  projection_injective : Set.InjOn (projection (K := L) direction) (zeroSet (L := L) p)
  monic : polynomial.Monic
  separable : polynomial.Separable
  degree_eq : polynomial.natDegree = (zeroSet (L := L) p).ncard
  roots : ∀ θ : L, Polynomial.aeval θ polynomial = 0 ↔ ∃ x ∈ zeroSet (L := L) p, projection direction x = θ
  numerator_degree : ∀ j, (numerator j).natDegree ≤ 1 + max 1 (((zeroSet (L := L) p).ncard - 1) * (zeroSet (L := L) p).ncard)
  denominator_degree : ∀ j, (denominator j).natDegree ≤ max 1 (((zeroSet (L := L) p).ncard - 1) * (zeroSet (L := L) p).ncard)
  coordinates : ∀ j, ∀ x ∈ zeroSet (L := L) p, Polynomial.aeval (projection direction x) (denominator j) ≠ 0 ∧
    Polynomial.aeval (projection direction x) (numerator j) /
      Polynomial.aeval (projection direction x) (denominator j) = x j

theorem nonempty_representation [IsGalois K L] [CharZero L]
    (p : τ → MvPolynomial ι K) (hfinite : (zeroSet (L := L) p).Finite) :
    Nonempty (Representation (L := L) p) := by
  classical
  let s := hfinite.toFinset
  have hs : VectorGaloisDescent.Stable (K := K) s :=
    VectorGaloisDescent.stable_of_zero_set p s (by
      intro x
      exact hfinite.mem_toFinset)
  obtain ⟨k, c, q, num, den, _hk, _hkb, hc, hproj, hmonic, hsep, hdeg, hroots, hcoord⟩ :=
    AsymmetricBaseCoordinates.exists_bounded_coordinates s hs
  have hcard : s.card = (zeroSet (L := L) p).ncard := (Set.ncard_eq_toFinset_card _ hfinite).symm
  refine ⟨{
    direction := c
    polynomial := q
    numerator := num
    denominator := den
    direction_le := fun i => (hc i).trans_eq (by rw [hcard])
    projection_injective := ?_
    monic := hmonic
    separable := hsep
    degree_eq := hdeg.trans hcard
    roots := ?_
    numerator_degree := fun j => (hcoord j).1.trans_eq (by rw [hcard])
    denominator_degree := fun j => (hcoord j).2.1.trans_eq (by rw [hcard])
    coordinates := ?_ }⟩
  · simpa only [s, Set.Finite.coe_toFinset] using hproj
  · intro θ
    simpa only [s, Set.Finite.mem_toFinset] using hroots θ
  · intro j x hx
    exact (hcoord j).2.2 x (hfinite.mem_toFinset.mpr hx)

theorem nonempty_algebraicClosure_representation [CharZero K]
    (p : τ → MvPolynomial ι K) (hfinite : (zeroSet (L := AlgebraicClosure K) p).Finite) :
    Nonempty (Representation (L := AlgebraicClosure K) p) :=
  nonempty_representation p hfinite

namespace Representation
variable {p : τ → MvPolynomial ι K}

noncomputable def decode (r : Representation (L := L) p) (θ : L) : ι → L := fun j =>
  Polynomial.aeval θ (r.numerator j) / Polynomial.aeval θ (r.denominator j)

theorem decode_projection (r : Representation (L := L) p) (x : ι → L) (hx : x ∈ zeroSet (L := L) p) :
    r.decode (projection r.direction x) = x := by
  funext j
  exact (r.coordinates j x hx).2

theorem decode_of_root (r : Representation (L := L) p) (θ : L) (hθ : Polynomial.aeval θ r.polynomial = 0) :
    r.decode θ ∈ zeroSet (L := L) p ∧ projection r.direction (r.decode θ) = θ ∧
      ∀ j, Polynomial.aeval θ (r.denominator j) ≠ 0 := by
  obtain ⟨x, hx, he⟩ := (r.roots θ).mp hθ
  rw [← he, r.decode_projection x hx]
  exact ⟨hx, rfl, fun j => (r.coordinates j x hx).1⟩

/-- The representation gives a bijection between eliminant roots and solutions. -/
noncomputable def rootEquiv (r : Representation (L := L) p) :
    {θ : L // Polynomial.aeval θ r.polynomial = 0} ≃ zeroSet (L := L) p where
  toFun θ := ⟨r.decode θ.val, (r.decode_of_root θ.val θ.property).1⟩
  invFun x := ⟨projection r.direction x.val, (r.roots _).mpr ⟨x.val, x.property, rfl⟩⟩
  left_inv θ := Subtype.ext (r.decode_of_root θ.val θ.property).2.1
  right_inv x := Subtype.ext (r.decode_projection x.val x.property)

end Representation
end LeanCanny.Algebra.FiniteSystemCoordinates
