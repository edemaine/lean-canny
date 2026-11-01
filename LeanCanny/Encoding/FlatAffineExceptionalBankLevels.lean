/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalParentBank

/-! # Actual affine levels in the constructed integral parent bank

Common denominator clearing turns every retained spatial coordinate into
an algebra element. Integer affine combinations and midpoint sums therefore
recover the actual old levels. Adding the exceptional numerator freezes
the same selected scalar, with no new algebraic coefficient premise.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalParentBank
open LeanCanny.Algebra LeanCanny.Computation MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births)
open scoped Classical BigOperators
attribute [local irreducible] SquareSampleCompleteVertices.candidate

def spatialIndex (F : Inputs) (u : List Bool) (t : Fin (F.depth u)) (i : Fin (arity F u)) : Fin (births F u) :=
  (FlatAffinePowerTower.current t i).castSucc.succ

def exceptionalIndex (F : Inputs) (u : List Bool) : Fin (births F u) := ⟨0, Nat.zero_lt_succ _⟩

noncomputable def heightNumerator (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (t : Fin (F.depth u)) (a : Fin (arity F u) → ℤ) : (bank F C h S u hm).sampler.scalarPrefix.carrier :=
  ∑ i, (a i : (bank F C h S u hm).sampler.scalarPrefix.carrier) * cleared F C h S u hm (spatialIndex F u t i)

noncomputable def levelNumerator (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1) :
    FlatAffineCriticalTower.Level (arity F u) (F.depth u) ℤ → (bank F C h S u hm).sampler.scalarPrefix.carrier
  | .constant c => (denominator F C h S u hm : (bank F C h S u hm).sampler.scalarPrefix.carrier) * (c : _)
  | .height t a => heightNumerator F C h S u hm t a
  | .midpoint l r a => heightNumerator F C h S u hm l a + heightNumerator F C h S u hm r a

noncomputable def shiftedNumerator (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (j : Fin (arity F u)) : (bank F C h S u hm).sampler.scalarPrefix.carrier :=
  levelNumerator F C h S u hm (FlatAffineFullSourceTower.level F u (F.depth u) j) +
    if j = h u then cleared F C h S u hm (exceptionalIndex F u) else 0

noncomputable def ancestorValues (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v) :
    FlatAffineCriticalTower.Ancestors (arity F u) (F.depth u) → ℝ :=
  (FlatAffineExceptionalSliceFrame.parent F C u v hv).val ∘
    TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)

theorem spatial_values (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (t : Fin (F.depth u)) (i : Fin (arity F u)) :
    values F C h u v a hv (spatialIndex F u t i) =
      ancestorValues F C u v hv (FlatAffineCriticalTower.oldAmbient (F.depth u) t i) := by
  have HI : TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)
      (FlatAffineCriticalTower.oldAmbient (F.depth u) t i) = FlatAffinePowerTower.current t i := by
    apply Fin.ext
    exact (FlatAffineCriticalTower.oldAmbient_index (F.depth u) t i).trans (by
      change t.val * stageWidth F u + i.val = i.val + stageWidth F u * t.val
      ac_rfl)
  have HE := FlatAffineCompleteVertices.ambient_coordinate F (parentCone F C) u v hv t i
  change (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F C)) u v hv).val
    (FlatAffinePowerTower.current t i).castSucc =
      (FlatAffineExceptionalSliceFrame.parent F C u v hv).val
        (TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)
          (FlatAffineCriticalTower.oldAmbient (F.depth u) t i))
  rw [HI]
  exact HE.symm

theorem heightNumerator_eval (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S + 1)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (φ : (bank F C h S u hm).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (H : ∀ i, φ ((bank F C h S u hm).bank.numerator i) /
      ((bank F C h S u hm).bank.denominator i : ℝ) = values F C h u v a hv i)
    (t : Fin (F.depth u)) (b : Fin (arity F u) → ℤ) :
    φ (heightNumerator F C h S u hm t b) = (denominator F C h S u hm : ℝ) *
      ∑ i, (b i : ℝ) * ancestorValues F C u v hv (FlatAffineCriticalTower.oldAmbient (F.depth u) t i) := by
  simp only [heightNumerator, map_sum, map_mul, map_intCast, cleared_recover F C h S u v a hm hv φ H, spatial_values]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem levelNumerator_eval (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S + 1)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (φ : (bank F C h S u hm).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (H : ∀ i, φ ((bank F C h S u hm).bank.numerator i) /
      ((bank F C h S u hm).bank.denominator i : ℝ) = values F C h u v a hv i)
    (b : FlatAffineCriticalTower.Level (arity F u) (F.depth u) ℤ) :
    φ (levelNumerator F C h S u hm b) = (denominator F C h S u hm : ℝ) *
      b.polynomial.eval₂ (Int.castRingHom ℝ) (ancestorValues F C u v hv) := by
  cases b with
  | constant c =>
    simp only [levelNumerator, FlatAffineCriticalTower.Level.polynomial, eval₂_C, map_mul, map_intCast, Int.coe_castRingHom]
  | height t b =>
    rw [levelNumerator, FlatAffineCriticalTower.Level.eval_height]
    exact heightNumerator_eval F C h S u v a hm hv φ H t b
  | midpoint l r b =>
    rw [levelNumerator, map_add, heightNumerator_eval F C h S u v a hm hv φ H l b,
      heightNumerator_eval F C h S u v a hm hv φ H r b, FlatAffineCriticalTower.Level.eval_midpoint]
    simp only [Int.coe_castRingHom]
    ring

theorem shiftedNumerator_eval (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S + 1)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (φ : (bank F C h S u hm).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (H : ∀ i, φ ((bank F C h S u hm).bank.numerator i) /
      ((bank F C h S u hm).bank.denominator i : ℝ) = values F C h u v a hv i)
    (j : Fin (arity F u)) :
    φ (shiftedNumerator F C h S u hm j) = (denominator F C h S u hm : ℝ) *
      ((FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial.eval₂ (Int.castRingHom ℝ)
        (ancestorValues F C u v hv) + if j = h u then FlatAffineExceptionalSliceFrame.scalar F C h u a else 0) := by
  have HE : values F C h u v a hv (exceptionalIndex F u) = FlatAffineExceptionalSliceFrame.scalar F C h u a := rfl
  by_cases hj : j = h u
  · rw [shiftedNumerator, ite_eq_left hj, map_add, levelNumerator_eval F C h S u v a hm hv φ H,
      cleared_recover F C h S u v a hm hv φ H, HE, ite_eq_left hj]
    ring
  · rw [shiftedNumerator, ite_eq_right hj, add_zero, levelNumerator_eval F C h S u v a hm hv φ H,
      ite_eq_right hj, add_zero]

end LeanCanny.Encoding.FlatAffineExceptionalParentBank
