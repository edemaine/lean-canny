/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalScriptGenerator

/-! # Query fields for actual creating critical polynomials

A caller selects a family at each input word. Its data at the empty word
fix the actual old algebra, basis, and creating polynomial. Query fields
change only the coefficient, target exponent, matrix indices, and modulus.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScriptQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Families := List Bool → IntegralHistoryCriticalBits.Family

structure Queries (F : Families) where
  coefficientIndex : List Bool → ℕ
  target : List Bool → ℕ
  row : ∀ c, Fin (count ((F c).birth []) ((F c).width []))
  col : ∀ c, Fin (count ((F c).birth []) ((F c).width []))
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def family (F : Families) (q : Queries F) : IntegralHistoryCriticalBits.Family where
  cap c := (F c).cap []
  width c := (F c).width []
  birth c := (F c).birth []
  ambient c := (F c).ambient []
  free c := (F c).free []
  scalarPrefix c := (F c).scalarPrefix []
  data c := (F c).data []
  offset c := (F c).offset []
  fit c := (F c).fit []
  sourceWidth c := (F c).sourceWidth []
  degree_lt c := (F c).degree_lt []
  objective c := (F c).objective []
  coordinate c := (F c).coordinate []
  coefficientIndex := q.coefficientIndex
  target := q.target
  row := q.row
  col := q.col
  modulus := q.modulus
  modulus_ne_zero := q.modulus_ne_zero

noncomputable def source (F : Families) (q : Queries F) := IntegralHistoryCriticalBits.source (family F q)

-- These identities preserve the actual algebra, rather than constructing
-- an isomorphic algebra with a new query-dependent scalar extension.
theorem carrier (F : Families) (q : Queries F) (c : List Bool) :
    (source F q).carrier c = (IntegralHistoryCriticalBits.source (F c)).carrier [] := rfl

theorem basis (F : Families) (q : Queries F) (c : List Bool) :
    (source F q).basis c = (IntegralHistoryCriticalBits.source (F c)).basis [] := rfl

theorem original_polynomial (F : Families) (q : Queries F) (c : List Bool) :
    (IntegralHistoryCriticalBits.original (family F q)).polynomial c =
      (IntegralHistoryCriticalBits.original (F c)).polynomial [] := rfl

/-- Original integer coefficients act diagonally in the actual old basis. -/
theorem original_coefficient_matrix (F : Families) (q : Queries F) (c : List Bool)
    (e : (Fin ((F c).ambient [] + 1)) →₀ ℕ)
    (r t : Fin (count ((F c).birth []) ((F c).width []))) :
    letI := (IntegralHistoryCriticalBits.original (family F q)).ring c
    Algebra.leftMulMatrix ((IntegralHistoryCriticalBits.original (family F q)).basis c)
      (((IntegralHistoryCriticalBits.original (family F q)).polynomial c).coeff e) r t =
      if r = t then ((F c).data []).low.coeff e else 0 := by
  let := (IntegralHistoryCriticalBits.original (family F q)).ring c
  change Algebra.leftMulMatrix ((IntegralHistoryCriticalBits.original (family F q)).basis c)
    ((((F c).data []).low.map (Int.castRingHom ((IntegralHistoryCriticalBits.original (family F q)).carrier c))).coeff e) r t = _
  rw [MvPolynomial.coeff_map]
  change Algebra.leftMulMatrix ((IntegralHistoryCriticalBits.original (family F q)).basis c)
    ((((F c).data []).low.coeff e : ℤ) : (IntegralHistoryCriticalBits.original (family F q)).carrier c) r t = _
  simp only [map_intCast, Matrix.intCast_apply, Int.cast_id]

theorem original_height (F : Families) (q : Queries F) (c : List Bool) (i : ℕ) :
    (IntegralHistoryCriticalBits.original (family F q)).height c i =
      (IntegralHistoryCriticalBits.original (F c)).height [] i := rfl

theorem original_denominator (F : Families) (q : Queries F) (c : List Bool) :
    (IntegralHistoryCriticalBits.original (family F q)).denominator c =
      (IntegralHistoryCriticalBits.original (F c)).denominator [] := rfl

theorem original_leading (F : Families) (q : Queries F) (c : List Bool) :
    (IntegralHistoryCriticalBits.euler (family F q)).leading c =
      (IntegralHistoryCriticalBits.euler (F c)).leading [] := rfl

theorem annihilator (F : Families) (q : Queries F) (c : List Bool) :
    (source F q).annihilator c = (IntegralHistoryCriticalBits.source (F c)).annihilator [] := rfl

theorem leading_integer (F : Families) (q : Queries F) (c : List Bool) :
    IntegralClearedCriticalLeadingBits.integer (source F q) c =
      IntegralClearedCriticalLeadingBits.integer (IntegralHistoryCriticalBits.source (F c)) [] := rfl

theorem degree (F : Families) (q : Queries F) (c : List Bool) :
    IntegralScalarRootHistoryBounds.degree (family F q) c =
      IntegralScalarRootHistoryBounds.degree (F c) [] := rfl

theorem value (F : Families) (q : Queries F) (c : List Bool) :
    letI := (IntegralHistoryCriticalBits.source (F c)).ring []
    (source F q).value c = residueBits
      ((Algebra.leftMulMatrix ((IntegralHistoryCriticalBits.source (F c)).basis [])
        (((IntegralHistoryCriticalBits.source (F c)).annihilator []).coeff (q.coefficientIndex c))
        (q.row c) (q.col c) : ℤ) : ZMod (q.modulus c)) := rfl

theorem top_value (F : Families) (q : Queries F) (c : List Bool)
    (hk : q.coefficientIndex c = IntegralClearedCriticalBounds.dimension (IntegralHistoryCriticalBits.source (F c)) []) :
    (source F q).value c = residueBits
      ((if q.row c = q.col c then
        IntegralClearedCriticalLeadingBits.integer (IntegralHistoryCriticalBits.source (F c)) [] else 0 : ℤ) : ZMod (q.modulus c)) := by
  let := (IntegralHistoryCriticalBits.source (F c)).ring []
  rw [value, hk, IntegralClearedCriticalLeadingBits.coefficient]
  simp only [map_intCast, Matrix.intCast_apply, Int.cast_id]

theorem leading_value (F : Families) (q : Queries F) (c : List Bool) :
    IntegralClearedCriticalLeadingBits.value (source F q) c = residueBits
      (IntegralClearedCriticalLeadingBits.integer (IntegralHistoryCriticalBits.source (F c)) [] : ZMod (q.modulus c)) := rfl


/-- Query the creating polynomial used by the actual scalar generator. -/
structure GeneratorQueries (F : IntegralCriticalScriptGeneratorBits.Queries) where
  coefficientIndex : List Bool → ℕ
  target : List Bool → ℕ
  row : ∀ c, Fin (count ((older (F.rules c) (F.selected c)).length) (F.width c))
  col : ∀ c, Fin (count ((older (F.rules c) (F.selected c)).length) (F.width c))

noncomputable def birthFamilies (F : IntegralCriticalScriptGeneratorBits.Queries) : Families :=
  IntegralCriticalScriptGeneratorBits.birthSource F

def GeneratorQueries.toQueries {F : IntegralCriticalScriptGeneratorBits.Queries} (q : GeneratorQueries F) : Queries (birthFamilies F) where
  coefficientIndex := q.coefficientIndex
  target := q.target
  row := q.row
  col := q.col
  modulus := F.modulus
  modulus_ne_zero := F.modulus_ne_zero

noncomputable def generatorFamily (F : IntegralCriticalScriptGeneratorBits.Queries) (q : GeneratorQueries F) :=
  family (birthFamilies F) q.toQueries

noncomputable def generatorSource (F : IntegralCriticalScriptGeneratorBits.Queries) (q : GeneratorQueries F) :=
  source (birthFamilies F) q.toQueries

theorem generator_polynomial (F : IntegralCriticalScriptGeneratorBits.Queries) (q : GeneratorQueries F) (c : List Bool) :
    (generatorSource F q).annihilator c = (IntegralCriticalScriptGeneratorBits.generatorFamily F).polynomial c := rfl

theorem generator_leading (F : IntegralCriticalScriptGeneratorBits.Queries) (q : GeneratorQueries F) (c : List Bool) :
    IntegralClearedCriticalLeadingBits.integer (generatorSource F q) c = IntegralCriticalScriptGeneratorBits.leading F c := rfl

theorem generator_value (F : IntegralCriticalScriptGeneratorBits.Queries) (q : GeneratorQueries F) (c : List Bool) :
    (generatorSource F q).value c = residueBits
      ((IntegralCriticalScriptGeneratorBits.generatorFamily F).coefficient c (q.coefficientIndex c) (q.row c) (q.col c)) := rfl

variable {S B n W D C : ℕ}

theorem past_older (rules : List (Command n W D C)) (i : Fin rules.length) :
    past rules (older rules i).length = older rules i := by
  have HI := i.isLt
  have HL : (older rules i).length ≤ rules.length := by rw [older_length]; omega
  unfold past
  rw [min_eq_left HL, older_length]
  change rules.drop (rules.length - (rules.length - 1 - i.val)) = rules.drop (i.val + 1)
  congr 1
  omega

theorem birthState_heq_stateAt (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length) :
    HEq (birthState rules h hN i) (stateAt rules h hN (older rules i).length) := by
  have HC (a b : List (Command n W D C)) (ha : a.length ≤ S + 1) (hb : b.length ≤ S + 1)
      (he : a = b) : HEq (run a ha hN) (run b hb hN) := by subst b; rfl
  exact HC _ _ _ _ (past_older rules i).symm

theorem birthCarrier_stateAt (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length) :
    (birthState rules h hN i).scalarPrefix.carrier =
      (stateAt rules h hN (older rules i).length).scalarPrefix.carrier := by
  have HC (a b : List (Command n W D C)) (ha : a.length ≤ S + 1) (hb : b.length ≤ S + 1)
      (he : a = b) : (run a ha hN).scalarPrefix.carrier = (run b hb hN).scalarPrefix.carrier := by subst b; rfl
  exact HC _ _ _ _ (past_older rules i).symm

theorem birthBasis_heq_stateAt (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length) :
    HEq (birthState rules h hN i).scalarPrefix.basis.finBasis
      (stateAt rules h hN (older rules i).length).scalarPrefix.basis.finBasis := by
  have HC (a b : List (Command n W D C)) (ha : a.length ≤ S + 1) (hb : b.length ≤ S + 1)
      (he : a = b) : HEq (run a ha hN).scalarPrefix.basis.finBasis (run b hb hN).scalarPrefix.basis.finBasis := by subst b; rfl
  exact HC _ _ _ _ (past_older rules i).symm

theorem birthFamily_stateAt (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length) :
    IntegralCriticalScript.family (stateAt rules h hN (older rules i).length)
      (by rw [past_older]; exact older_bound rules h i) (chosen rules i) = birthFamily rules h hN i := by
  have HC (a b : List (Command n W D C)) (ha : a.length ≤ S) (hb : b.length ≤ S) (he : a = b) :
      IntegralCriticalScript.family (run a (ha.trans (Nat.le_add_right S 1)) hN) ha (chosen rules i) =
        IntegralCriticalScript.family (run b (hb.trans (Nat.le_add_right S 1)) hN) hb (chosen rules i) := by
    subst b
    rfl
  exact HC _ _ _ _ (past_older rules i)


/-- The query source preserves the denominator used at the creating command. -/
theorem birth_denominator (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length) :
    (IntegralHistoryCriticalBits.original (birthFamily rules h hN i)).denominator [] =
      CoordinateFrozenCriticalElimination.denominator
        (fun j => (birthState rules h hN i).bank.selectedDenominator ((chosen rules i).select (older rules i).length j)) := rfl

/-- The height is the actual common-denominator-cleared selected numerator. -/
theorem birth_height (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length) (j : ℕ) :
    (IntegralHistoryCriticalBits.original (birthFamily rules h hN i)).height [] j =
      CoordinateFrozenCriticalElimination.numerators
        (fun k => (birthState rules h hN i).bank.selectedDenominator ((chosen rules i).select (older rules i).length k))
        (fun k => (birthState rules h hN i).bank.selectedNumerator ((chosen rules i).select (older rules i).length k)) j := rfl

end LeanCanny.Algebra.IntegralCriticalScriptQueryBits
