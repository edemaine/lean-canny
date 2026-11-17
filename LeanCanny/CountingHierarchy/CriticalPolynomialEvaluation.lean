/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CriticalNumericEvaluation
public import LeanCanny.CountingHierarchy.PartialDerivativeEvaluation

/-! # Uniform evaluators for the actual deformed objective and lower relations -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

@[expose] noncomputable def criticalLowerValue (p n ell u i : ℕ) (z : List ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  modularSub p (powMod p (criticalCenterResidue p ell i) ell)
    (u * firstPartialResidue p n i z value)

@[expose] noncomputable def criticalObjectiveValue (p n ell u : ℕ) (z : List ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  (criticalPotentialResidue p n ell z + (ell + 1) * u * value z) % p

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}

theorem criticalLowerValue_mem (E : Decoder enc) {p n ell u i : α → ℕ}
    {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hi : ComputableInPolyTime i enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => criticalLowerValue (p w) (n w) (ell w) (u w) (i w) (z w) (fun y => value (w, y))) ∈
      CountingFunction (a + 1) enc encNat := by
  have hcenter := criticalCenterResidue_polyTime hp hell hi
  have hc := computableInPolyTime_powMod hp hcenter hell
  have hd := firstPartialResidue_mem E hp hn hi hz hv
  exact modularSub_mem (CountingFunction.of_polyTime hp) (CountingFunction.of_polyTime hc)
    (CountingFunction.nat_mul (CountingFunction.of_polyTime hu) hd)

theorem criticalObjectiveValue_mem {p n ell u : α → ℕ}
    {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => criticalObjectiveValue (p w) (n w) (ell w) (u w) (z w) (fun y => value (w, y))) ∈
      CountingFunction a enc encNat := by
  have hpotential := criticalPotentialResidue_mem (a := a) hp hn hell hz
  have hscale := ComputableInPolyTime.binary_mul' (ComputableInPolyTime.binary_add' hell (.const 1)) hu
  have hvalue := CountingFunction.preprocess hv (ComputableInPolyTime.id'.prod hz)
  have hterm := CountingFunction.nat_mul (CountingFunction.of_polyTime hscale) hvalue
  have hsum := CountingFunction.map (CountingFunction.prod hpotential hterm) ComputableInPolyTime.binary_add
  exact CountingFunction.nat_mod hsum (CountingFunction.of_polyTime hp)

theorem criticalLowerValue_cast {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) (ZMod p)) (ell u : ℕ) (i : Fin n) (z : List ℕ)
    (value : List ℕ → ℕ) (hF : F.totalDegree < p - 1) (hp : 3 < p)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun j : Fin n => ((y[j.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (criticalLowerValue p n ell u i.val z value : ZMod p) =
      eval (fun j : Fin n => ((z[j.val]?.getD 0 : ℕ) : ZMod p))
        (criticalLower ell (fun j : Fin n => ((separatedCenters ell j : ℕ) : ZMod p)) (u : ZMod p) F i) := by
  rw [criticalLowerValue, modularSub_cast (Fact.out : p.Prime).pos,
    powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod, Nat.cast_pow,
    criticalCenterResidue_cast]
  simp only [Nat.cast_mul]
  rw [firstPartialResidue_cast F i z value hF hp hv,
    criticalLower, map_sub, map_mul, eval_C, eval_C]
  simp only [separatedCenters, Nat.cast_pow, Nat.cast_mul]

theorem criticalObjectiveValue_cast {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) (ZMod p)) (ell u : ℕ) (z : List ℕ) (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun j : Fin n => ((y[j.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (criticalObjectiveValue p n ell u z value : ZMod p) =
      eval (fun j : Fin n => ((z[j.val]?.getD 0 : ℕ) : ZMod p))
        (deformedPolynomial ell (fun j : Fin n => ((separatedCenters ell j : ℕ) : ZMod p)) (u : ZMod p) F) := by
  rw [criticalObjectiveValue, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
    criticalPotentialResidue_cast, hv, deformedPolynomial, map_add, map_mul, eval_C]

end LeanCanny.CountingHierarchy
