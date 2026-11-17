/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledCoordinateProgram
public import LeanCanny.CountingHierarchy.CandidateCoordinateBounds

/-! # Uniform controlled families of addressed coordinate candidates -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial Polynomial

@[fun_prop] theorem coordinateCharacteristicMassExponent_polyTime {α : Type} {enc : α ↪ List Bool}
    {n d b : α → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => coordinateCharacteristicMassExponent (n w) (d w) (b w)) enc encNat :=
  quotientCharMassExponent_polyTime hn hd (ComputableInPolyTime.const 1) (ComputableInPolyTime.const 0)
    (relativeRelationMassExponent_polyTime hd hb)

namespace Controlled

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}

noncomputable def coordinateCandidateOfDegree (C : Controlled F enc a) (E : Decoder enc)
    (d : α → ℕ) (hd : ComputableInPolyTime d enc encNat) (hpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (i : (w : α) → Fin (n w))
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat)
    (j : α → ℕ) (hj : ComputableInPolyTime j enc encNat) :
    Controlled (fun w => liftUnivariate
      ((Bivariate.swap (parametricCoordinatePolynomial (d w) (F w) (hF w) (i w))).coeff (j w))) enc (a + 11) :=
  univariate _ (fun w => (d w + 1) ^ n w)
    (fun w => coordinateCharacteristicMassExponent (n w) (d w) (C.massExponent w))
    (C.coordinateCutoff d j)
    (ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_add' hd (.const 1)) C.arity_computable)
    (coordinateCharacteristicMassExponent_polyTime C.arity_computable hd C.mass_computable)
    (C.coordinateCutoff_polyTime hd hj)
    (fun w => coordinateCandidate_degree_le (d w) (F w) (hF w) (i w) (j w))
    (fun w => coordinateCandidate_mass_le (d w) (C.massExponent w) (hpos w) (F w) (hF w) (C.mass_le w) (i w) (j w))
    (C.coordinateProgram d (fun w => (i w).val) j) (C.coordinateProgram_mem E hd hi hj)
    (fun w p t hp hc => C.coordinateProgram_eq d j i w p t hp hc (hpos w) (hF w))

noncomputable def addressedCandidate (C : Controlled F enc a) (E : Decoder enc)
    (i : (w : α) → Fin (n w)) (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat)
    (j : α → ℕ) (hj : ComputableInPolyTime j enc encNat) :
    Controlled (fun w => liftUnivariate
      (addressedCandidateCoordinate (F w) (C.degreeBound w) (C.degree_le w) (i w) (j w))) enc (a + 11) := by
  let d := fun w => 2 * (C.degreeBound w + 1)
  have hd : ComputableInPolyTime d enc encNat := ComputableInPolyTime.binary_mul' (.const 2)
    (ComputableInPolyTime.binary_add' C.degree_computable (.const 1))
  have hF (w : α) : (F w ^ 2).totalDegree ≤ d w + 1 := by
    have := C.degree_le w
    exact (MvPolynomial.totalDegree_pow _ _).trans (by dsimp only [d]; nlinarith)
  exact (C.pow (fun _ => 2) (ComputableInPolyTime.const 2)).coordinateCandidateOfDegree E d hd
    (fun _ => by dsimp only [d]; omega) hF i hi j hj

end Controlled
end LeanCanny.CountingHierarchy
