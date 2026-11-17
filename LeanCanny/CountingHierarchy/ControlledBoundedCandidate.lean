/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledCoordinateCandidate
public import LeanCanny.CountingHierarchy.ControlledBounds

/-! # Common source-only budgets for all bounded coordinate candidate indices -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

def candidateDegree (n D : ℕ) : ℕ := (2 * (D + 1) + 1) ^ n

def candidateMassExponent (n D b : ℕ) : ℕ := coordinateCharacteristicMassExponent n (2 * (D + 1)) (2 * b)

def candidateIndexBound (n D : ℕ) : ℕ := coordinateParameterDegreeBound n (2 * (D + 1))

def candidatePrimeCutoff (n D cutoff : ℕ) : ℕ :=
  max cutoff (max (criticalCoefficientPrimeCutoff n (2 * (D + 1))) (candidateIndexBound n D + 1))

@[fun_prop] theorem candidateDegree_polyTime {α : Type} {enc : α ↪ List Bool} {n D : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hD : ComputableInPolyTime D enc encNat) :
    ComputableInPolyTime (fun w => candidateDegree (n w) (D w)) enc encNat :=
  ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' (.const 2) (ComputableInPolyTime.binary_add' hD (.const 1))) (.const 1)) hn

@[fun_prop] theorem candidateMassExponent_polyTime {α : Type} {enc : α ↪ List Bool} {n D b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hD : ComputableInPolyTime D enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => candidateMassExponent (n w) (D w) (b w)) enc encNat :=
  coordinateCharacteristicMassExponent_polyTime hn
    (ComputableInPolyTime.binary_mul' (.const 2) (ComputableInPolyTime.binary_add' hD (.const 1)))
    (ComputableInPolyTime.binary_mul' (.const 2) hb)

@[fun_prop] theorem candidateIndexBound_polyTime {α : Type} {enc : α ↪ List Bool} {n D : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hD : ComputableInPolyTime D enc encNat) :
    ComputableInPolyTime (fun w => candidateIndexBound (n w) (D w)) enc encNat :=
  coordinateParameterDegreeBound_polyTime hn
    (ComputableInPolyTime.binary_mul' (.const 2) (ComputableInPolyTime.binary_add' hD (.const 1)))

@[fun_prop] theorem candidatePrimeCutoff_polyTime {α : Type} {enc : α ↪ List Bool} {n D cutoff : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hD : ComputableInPolyTime D enc encNat)
    (hc : ComputableInPolyTime cutoff enc encNat) :
    ComputableInPolyTime (fun w => candidatePrimeCutoff (n w) (D w) (cutoff w)) enc encNat :=
  ComputableInPolyTime.binary_max' hc (ComputableInPolyTime.binary_max'
    (criticalCoefficientPrimeCutoff_polyTime hn
      (ComputableInPolyTime.binary_mul' (.const 2) (ComputableInPolyTime.binary_add' hD (.const 1))))
    (ComputableInPolyTime.binary_add' (candidateIndexBound_polyTime hn hD) (.const 1)))

namespace Controlled

noncomputable def boundedCandidate {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) (i : (w : α) → Fin (n w))
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat)
    (j : α → ℕ) (hj : ComputableInPolyTime j enc encNat)
    (hchoice : ∀ w, j w ≤ candidateIndexBound (n w) (C.degreeBound w)) :
    Controlled (fun w => liftUnivariate
      (addressedCandidateCoordinate (F w) (C.degreeBound w) (C.degree_le w) (i w) (j w))) enc (a + 11) := by
  let CC := C.addressedCandidate E i hi j hj
  exact CC.withBounds (fun w => candidateDegree (n w) (C.degreeBound w))
    (fun w => candidateMassExponent (n w) (C.degreeBound w) (C.massExponent w))
    (fun w => candidatePrimeCutoff (n w) (C.degreeBound w) (C.cutoff w))
    (candidateDegree_polyTime C.arity_computable C.degree_computable)
    (candidateMassExponent_polyTime C.arity_computable C.degree_computable C.mass_computable)
    (candidatePrimeCutoff_polyTime C.arity_computable C.degree_computable C.cutoff_computable)
    (fun w => (liftUnivariate_degree_le _).trans
      (addressedCandidateCoordinate_degree_le (F w) (C.degreeBound w) (C.degree_le w) (i w) (j w)))
    (fun w => (liftUnivariate_mass_le _).trans
      (addressedCandidateCoordinate_mass_le (F w) (C.degreeBound w) (C.massExponent w) (C.degree_le w) (C.mass_le w) (i w) (j w)))
    (fun w => by
      change max (C.cutoff w) (max (criticalCoefficientPrimeCutoff (n w) (2 * (C.degreeBound w + 1)))
        (max (candidateIndexBound (n w) (C.degreeBound w)) (j w) + 1)) ≤ _
      unfold candidatePrimeCutoff
      apply max_le_max le_rfl
      apply max_le_max le_rfl
      exact Nat.add_le_add_right (max_le le_rfl (hchoice w)) 1)

end Controlled
end LeanCanny.CountingHierarchy
