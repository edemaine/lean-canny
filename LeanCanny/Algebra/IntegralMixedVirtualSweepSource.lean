/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCutSource
public import LeanCanny.Algebra.IntegralMixedCutNilpotent
public import LeanCanny.Algebra.PurePowerAnnihilatorMap

/-! # Actual virtual swept sources for the native critical subroutine

The old algebra is extended only as a coefficient algebra by a formal
nilpotent. Its canonical basis, original integer spatial source, integer
coordinate denominator and swept retained heights build an actual Euler
source. The constructed relative annihilator is exactly the nilpotent
image of the old relative coordinate polynomial. No physical sampler
birth, fake prefix interpretation or supplied annihilator is required.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualSweepSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource Polynomial
open scoped Classical

structure Indices (F : Family) where
  coordinate : (q : List Bool) → Fin (F.ambient q - (F.rule q).critical.offset.val + 1)
  coefficientIndex : List Bool → ℕ
  target : List Bool → ℕ
  row : (q : List Bool) → Fin (count (F.birth q + 1) (F.width q))
  col : (q : List Bool) → Fin (count (F.birth q + 1) (F.width q))
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ q, modulus q ≠ 0

abbrev Coefficient (F : Family) (q : List Bool) :=
  AdjoinRoot (X ^ (2 ^ F.width q) : Polynomial (F.state q).sampler.scalarPrefix.carrier)

noncomputable def denominator (F : Family) (q : List Bool) : ℤ :=
  CoordinateFrozenCriticalElimination.denominator
    (data (F.state q) (F.birth_bound q) (F.rule q).critical).scales

noncomputable def height (F : Family) (q : List Bool) (j : ℕ) : Coefficient F q :=
  AdjoinRoot.mk (X ^ (2 ^ F.width q))
    (CoordinateFrozenCriticalElimination.numerators
      (data (F.state q) (F.birth_bound q) (F.rule q).critical).scales (heights (F.state q) (F.rule q)) j)

noncomputable def original (F : Family) (I : Indices F) : IntegralClearedCoefficientBits.Source where
  arity q := F.ambient q + 1
  free q := F.ambient q - (F.rule q).critical.offset.val + 1
  offset q := (F.rule q).critical.offset.val
  fit q := (fit (F.rule q)).le
  sourceWidth q := (F.spatial q).degree.size
  targetWidth _ := 0
  rank q := count (F.birth q + 1) (F.width q)
  carrier q := Coefficient F q
  ring _ := inferInstance
  basis q := (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
  polynomial q := (F.spatial q).low.map (Int.castRingHom _)
  support q _e he j :=
    ((MvPolynomial.monomial_le_degreeOf j he).trans (MvPolynomial.degreeOf_le_totalDegree _ _)).trans_lt
      (((PolynomialMapDegree.degree_le _ (F.spatial q).low).trans_lt (F.spatial q).low_degree).trans (Nat.lt_size_self _))
  denominator := denominator F
  height := height F
  allowance q := (F.spatial q).degree
  target := I.target
  row := I.row
  col := I.col
  modulus := I.modulus
  modulus_ne_zero := I.modulus_ne_zero

noncomputable def euler (F : Family) (I : Indices F) : IntegralEulerBits.Source where
  toGradient := {
    toFrozen := { toSource := original F I, leading q := (F.spatial q).leading }
    free_pos _ := Nat.zero_lt_succ _
    degree q := (F.spatial q).degree
    degree_pos q := by have H := (F.spatial q).degree_two; omega
    degree_le q := by
      let := (original F I).ring q
      exact ((PolynomialMapDegree.degree_le _ (F.spatial q).low).trans_lt (F.spatial q).low_degree).le
    degree_lt q := Nat.lt_size_self _ }
  objective q := objective (F.rule q)

noncomputable def source (F : Family) (I : Indices F) : IntegralClearedCriticalBits.Source :=
  IntegralCanonicalCriticalBits.source (euler F I) I.coordinate I.coefficientIndex

theorem euler_lower (F : Family) (I : Indices F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) :
    (euler F I).lowerPolynomial q j =
      ClearedCoordinateCritical.lower (F.spatial q).degree (denominator F q : Coefficient F q)
        (height F q) (F.rule q).critical.offset.val (fit (F.rule q)).le
        ((F.spatial q).low.map (Int.castRingHom (Coefficient F q)))
        ((F.spatial q).leading : Coefficient F q) (objective (F.rule q)) j := by
  have HG (i : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) :
      IntegralCriticalGradientBits.polynomial (euler F I).toGradient q i =
        ClearedCoordinateCritical.gradientLower (F.spatial q).degree
          (denominator F q : Coefficient F q) (height F q)
          (F.rule q).critical.offset.val (fit (F.rule q)).le
          ((F.spatial q).low.map (Int.castRingHom (Coefficient F q))) i := rfl
  unfold IntegralEulerBits.Source.lowerPolynomial ClearedCoordinateCritical.lower PurePowerEulerReduction.lower
  change (if j = objective (F.rule q) then (euler F I).objectivePolynomial q else _) = _
  split_ifs
  · unfold IntegralEulerBits.Source.objectivePolynomial PurePowerEulerReduction.objectiveLower
    rw [IntegralEulerBits.sumPolynomial_eq_erase]
    rfl
  · exact HG j

theorem annihilator_cleared (F : Family) (I : Indices F) (q : List Bool) :
    (source F I).annihilator q =
      ClearedCoordinateCritical.annihilator (F.spatial q).degree
        (denominator F q : Coefficient F q) (height F q)
        (F.rule q).critical.offset.val (fit (F.rule q)).le
        ((F.spatial q).low.map (Int.castRingHom (Coefficient F q)))
        ((F.spatial q).leading : Coefficient F q) (objective (F.rule q)) (I.coordinate q) := by
  have HL : (source F I).toEuler.lowerPolynomial q =
      ClearedCoordinateCritical.lower (F.spatial q).degree
        (denominator F q : Coefficient F q) (height F q)
        (F.rule q).critical.offset.val (fit (F.rule q)).le
        ((F.spatial q).low.map (Int.castRingHom (Coefficient F q)))
        ((F.spatial q).leading : Coefficient F q) (objective (F.rule q)) := by
    funext j
    exact (IntegralCanonicalCriticalBits.normalized_lower (euler F I) q j).trans (euler_lower F I q j)
  have HD : (fun j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1) =>
      IntegralClearedCriticalBits.rowDegree (source F I).toEuler q j.val) =
        FermatCoordinateCriticalReduction.degrees (objective (F.rule q)) (F.spatial q).degree := by
    funext j
    simp only [IntegralClearedCriticalBits.rowDegree, IntegralEulerBits.objectiveRank, source,
      IntegralCanonicalCriticalBits.source, IntegralCanonicalCriticalBits.normalized, euler, original,
      FermatCoordinateCriticalReduction.degrees, Fin.ext_iff]
    rfl
  rw [IntegralClearedCriticalBits.annihilator_eq]
  unfold ClearedCoordinateCritical.annihilator
  congr 1
  simp only [source, IntegralCanonicalCriticalBits.source, IntegralCanonicalCriticalBits.normalized,
    euler, original]
  change (((F.spatial q).leading * denominator F q ^ (F.spatial q).degree * (F.spatial q).degree : ℤ) : Coefficient F q) = _
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]

theorem annihilator_eq (F : Family) (I : Indices F) (q : List Bool) :
    (source F I).annihilator q =
      (coordinate (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q)).map
        (AdjoinRoot.mk (X ^ (2 ^ F.width q))) := by
  rw [annihilator_cleared]
  unfold coordinate CoordinateFrozenCriticalElimination.polynomial
  rw [PurePowerAnnihilatorMap.cleared]
  have HP :
      ((F.spatial q).low.map (Int.castRingHom (Polynomial (F.state q).sampler.scalarPrefix.carrier))).map
        (AdjoinRoot.mk (X ^ (2 ^ F.width q))) =
      (F.spatial q).low.map (Int.castRingHom (Coefficient F q)) := by
    rw [MvPolynomial.map_map]
    congr 1
  simp only [map_intCast, HP]
  rfl

theorem value_eq (F : Family) (I : Indices F) (q : List Bool) :
    (source F I).value q = residueBits ((Algebra.leftMulMatrix
      (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      (AdjoinRoot.mk (X ^ (2 ^ F.width q))
        ((coordinate (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q)).coeff (I.coefficientIndex q)))
      (I.row q) (I.col q) : ℤ) : ZMod (I.modulus q)) := by
  let read (p : Polynomial (Coefficient F q)) : List Bool := residueBits ((Algebra.leftMulMatrix
    (IntegralMixedCutNilpotent.basis (F.state q)).finBasis (p.coeff (I.coefficientIndex q))
      (I.row q) (I.col q) : ℤ) : ZMod (I.modulus q))
  have HV : (source F I).value q = read ((source F I).annihilator q) := rfl
  rw [HV, annihilator_eq]
  change read ((coordinate (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q)).map
    (AdjoinRoot.mk (X ^ (2 ^ F.width q)))) = _
  simp only [read, Polynomial.coeff_map]

end LeanCanny.Algebra.IntegralMixedVirtualSweepSource
