/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCanonicalCriticalSpace
public import LeanCanny.Algebra.IntegralHistoryRelativeCritical
public import LeanCanny.Algebra.FixedWidthCommonDenominatorSpace

/-! # Original native critical sources from actual retained histories

The carrier, basis, source, common denominator, and retained numerators
come from the sampler's critical data. Spatial arities are successors by
construction, so its relative polynomial can be compared directly with
the critical candidate used to extend the same physical parent tuple.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralHistoryCriticalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family where
  cap : List Bool → ℕ
  width : List Bool → ℕ
  birth : List Bool → ℕ
  ambient : List Bool → ℕ
  free : List Bool → ℕ
  scalarPrefix : ∀ c, UniformIntegralPrefix.Prefix (cap c) (2 ^ width c) (birth c)
  data : ∀ c, IntegralHistorySampler.CriticalData (scalarPrefix c) (ambient c)
  offset : List Bool → ℕ
  fit : ∀ c, offset c + (free c + 1) = ambient c + 1
  sourceWidth : List Bool → ℕ
  degree_lt : ∀ c, (data c).degree < 2 ^ sourceWidth c
  objective : ∀ c, Fin (free c + 1)
  coordinate : ∀ c, Fin (free c + 1)
  coefficientIndex : List Bool → ℕ
  target : List Bool → ℕ
  row : ∀ c, Fin (count (birth c) (width c))
  col : ∀ c, Fin (count (birth c) (width c))
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def original (F : Family) : IntegralClearedCoefficientBits.Source where
  arity c := F.ambient c + 1
  free c := F.free c + 1
  offset := F.offset
  fit c := (F.fit c).le
  sourceWidth := F.sourceWidth
  targetWidth _ := 0
  rank c := count (F.birth c) (F.width c)
  carrier c := (F.scalarPrefix c).carrier
  ring c := (F.scalarPrefix c).ring
  basis c := (F.scalarPrefix c).basis.finBasis
  polynomial c := (F.data c).low.map (Int.castRingHom (F.scalarPrefix c).carrier)
  support c e he i := by
    exact ((MvPolynomial.monomial_le_degreeOf i he).trans (MvPolynomial.degreeOf_le_totalDegree _ i)).trans_lt
      (((PolynomialMapDegree.degree_le _ (F.data c).low).trans_lt (F.data c).low_degree).trans (F.degree_lt c))
  denominator c := CoordinateFrozenCriticalElimination.denominator (F.data c).scales
  height c := CoordinateFrozenCriticalElimination.numerators (F.data c).scales (F.data c).heights
  allowance c := (F.data c).degree
  target := F.target
  row := F.row
  col := F.col
  modulus := F.modulus
  modulus_ne_zero := F.modulus_ne_zero

noncomputable def euler (F : Family) : IntegralEulerBits.Source where
  toGradient := {
    toFrozen := { toSource := original F, leading c := (F.data c).leading }
    free_pos c := Nat.zero_lt_succ _
    degree c := (F.data c).degree
    degree_pos c := by have := (F.data c).degree_two; omega
    degree_le c := by
      let := (original F).ring c
      let := (F.scalarPrefix c).ring
      exact ((PolynomialMapDegree.degree_le (Int.castRingHom (F.scalarPrefix c).carrier) (F.data c).low).trans_lt (F.data c).low_degree).le
    degree_lt := F.degree_lt }
  objective := F.objective

noncomputable def source (F : Family) : IntegralClearedCriticalBits.Source :=
  IntegralCanonicalCriticalBits.source (euler F) F.coordinate F.coefficientIndex

theorem euler_lower (F : Family) (c : List Bool) (i : Fin (F.free c + 1)) :
    (euler F).lowerPolynomial c i =
      ClearedCoordinateCritical.lower (F.data c).degree
        (CoordinateFrozenCriticalElimination.denominator (F.data c).scales : (F.scalarPrefix c).carrier)
        (CoordinateFrozenCriticalElimination.numerators (F.data c).scales (F.data c).heights)
        (F.offset c) (F.fit c).le ((F.data c).low.map (Int.castRingHom (F.scalarPrefix c).carrier))
        ((F.data c).leading : (F.scalarPrefix c).carrier) (F.objective c) i := by
  have HG (j : Fin (F.free c + 1)) : IntegralCriticalGradientBits.polynomial (euler F).toGradient c j =
      ClearedCoordinateCritical.gradientLower (F.data c).degree
        (CoordinateFrozenCriticalElimination.denominator (F.data c).scales : (F.scalarPrefix c).carrier)
        (CoordinateFrozenCriticalElimination.numerators (F.data c).scales (F.data c).heights)
        (F.offset c) (F.fit c).le ((F.data c).low.map (Int.castRingHom (F.scalarPrefix c).carrier)) j := by rfl
  unfold IntegralEulerBits.Source.lowerPolynomial ClearedCoordinateCritical.lower PurePowerEulerReduction.lower
  change (if i = F.objective c then (euler F).objectivePolynomial c else _) = _
  split_ifs
  · unfold IntegralEulerBits.Source.objectivePolynomial PurePowerEulerReduction.objectiveLower
    rw [IntegralEulerBits.sumPolynomial_eq_erase]
    simp only [HG]
    rfl
  · exact HG i

theorem annihilator_eq (F : Family) (c : List Bool) :
    (source F).annihilator c = CoordinateFrozenCriticalElimination.polynomial (F.data c).degree
      (F.data c).scales (F.data c).heights (F.offset c) (F.fit c)
      ((F.data c).low.map (Int.castRingHom (F.scalarPrefix c).carrier))
      ((F.data c).leading : (F.scalarPrefix c).carrier) (F.objective c) (F.coordinate c) := by
  let := (source F).ring c
  have HL : (source F).toEuler.lowerPolynomial c =
      ClearedCoordinateCritical.lower (F.data c).degree
        (CoordinateFrozenCriticalElimination.denominator (F.data c).scales : (F.scalarPrefix c).carrier)
        (CoordinateFrozenCriticalElimination.numerators (F.data c).scales (F.data c).heights)
        (F.offset c) (F.fit c).le ((F.data c).low.map (Int.castRingHom (F.scalarPrefix c).carrier))
        ((F.data c).leading : (F.scalarPrefix c).carrier) (F.objective c) := by
    funext i
    exact (IntegralCanonicalCriticalBits.normalized_lower (euler F) c i).trans (euler_lower F c i)
  have HD : (fun i : Fin (F.free c + 1) => IntegralClearedCriticalBits.rowDegree (source F).toEuler c i.val) =
      FermatCoordinateCriticalReduction.degrees (F.objective c) (F.data c).degree := by
    funext i
    simp only [IntegralClearedCriticalBits.rowDegree, IntegralEulerBits.objectiveRank, source,
      IntegralCanonicalCriticalBits.source, IntegralCanonicalCriticalBits.normalized, euler, original,
      FermatCoordinateCriticalReduction.degrees, Fin.ext_iff]
  rw [IntegralClearedCriticalBits.annihilator_eq]
  unfold CoordinateFrozenCriticalElimination.polynomial ClearedCoordinateCritical.annihilator
  congr 1
  simp only [source, IntegralCanonicalCriticalBits.source, IntegralCanonicalCriticalBits.normalized,
      euler, original, Int.cast_mul, Int.cast_pow, Int.cast_natCast]

noncomputable def value (F : Family) (c : List Bool) : List Bool :=
  residueBits ((Algebra.leftMulMatrix (F.scalarPrefix c).basis.finBasis
    ((CoordinateFrozenCriticalElimination.polynomial (F.data c).degree
      (F.data c).scales (F.data c).heights (F.offset c) (F.fit c)
      ((F.data c).low.map (Int.castRingHom (F.scalarPrefix c).carrier))
      ((F.data c).leading : (F.scalarPrefix c).carrier) (F.objective c) (F.coordinate c)).coeff
      (F.coefficientIndex c)) (F.row c) (F.col c) : ℤ) : ZMod (F.modulus c))

theorem value_eq (F : Family) (c : List Bool) : (source F).value c = value F c := by
  let reader (p : Polynomial (F.scalarPrefix c).carrier) : List Bool :=
    residueBits ((Algebra.leftMulMatrix (F.scalarPrefix c).basis.finBasis (p.coeff (F.coefficientIndex c))
      (F.row c) (F.col c) : ℤ) : ZMod (F.modulus c))
  exact congrArg reader (annihilator_eq F c)

theorem evaluator (F : Family) (a : IntegralEulerBits.Access (euler F))
    (hi : BinaryFn (fun c => (F.coordinate c).val)) (hk : BinaryFn F.coefficientIndex)
    (EC : SpaceFunction a.coefficient) (EH : SpaceFunction a.height)
    (EQ : SpaceFunction a.denominator) (EA : SpaceFunction a.leading) : SpaceFunction (value F) :=
  (IntegralCanonicalCriticalBits.evaluator (euler F) a F.coordinate F.coefficientIndex hi hk EC EH EQ EA).congr
    (funext (value_eq F))

end LeanCanny.Algebra.IntegralHistoryCriticalBits
