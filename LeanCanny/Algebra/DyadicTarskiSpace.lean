/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DyadicPolynomialSpace
public import LeanCanny.Algebra.TarskiQueryPSPACE

/-! # Tarski queries at a dyadic parameter from original bivariate readers

Both parameterized polynomials are specialized coefficientwise. Positive
denominator-clearing factors preserve the roots and query signs. This computes
the query at the selected parameter; eventual constancy as beta tends to zero
requires additional bounds on the polynomials governing root-sign changes.
-/

@[expose] public section

namespace LeanCanny.Algebra.RootSignQueries
open Polynomial

theorem tarskiQuery_C_mul (p q : ℝ[X]) (a b : ℝ) (ha : a ≠ 0) (hb : 0 < b) :
    tarskiQuery (C a * p) (C b * q) = tarskiQuery p q := by
  classical
  simp only [tarskiQuery, roots_C_mul p ha, signSum, eval_mul, eval_C,
    sign_mul, sign_pos hb, one_mul]

end LeanCanny.Algebra.RootSignQueries

namespace LeanCanny.Algebra.DyadicTarskiBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation
open DyadicPolynomialBits

noncomputable def family (F G : Family) : IntegerTarskiSeedBits.Family where
  head := F.specialized
  query := G.specialized
  degree := BinaryNat.succ ∘ F.degree
  queryBound := G.degree
  headMass := massCode F
  queryMass := massCode G
  degree_pos c := by simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]; omega
  head_degree c := by
    simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
    exact (specialized_degree F c).trans (Nat.le_succ _)
  query_degree := specialized_degree G
  head_mass := specialized_mass F
  query_mass := specialized_mass G

theorem controls (F G : Family) (hF : ControlsPolyTime F) (hG : ControlsPolyTime G) :
    IntegerTarskiSeedBits.ControlsPolyTime (family F G) := by
  have hd := mem_FP_comp hF.degree BinaryNat.succ_mem_FP
  exact ⟨hd, hG.degree, massCode_mem_FP F hF, massCode_mem_FP G hG⟩

noncomputable def access (F G : Family) : IntegerTarskiSeedBits.Access (family F G) where
  headCoefficient := F.residue
  queryCoefficient := G.residue
  head_eq c i m hm := residue_packet F c i m hm
  query_eq c i m hm := residue_packet G c i m hm

/-- The parameter exponents may have different raw encodings but the same value. -/
def SameParameter (F G : Family) : Prop :=
  ∀ c, Nat.fromBitsLE (F.exponent c) = Nat.fromBitsLE (G.exponent c)

noncomputable def value (F G : Family) (c : List Bool) : ℤ := RootSignQueries.tarskiQuery
  ((F.polynomial c).map (DyadicPolynomial.evalHom (Nat.fromBitsLE (F.exponent c))))
  ((G.polynomial c).map (DyadicPolynomial.evalHom (Nat.fromBitsLE (F.exponent c))))

theorem family_value (F G : Family) (h : SameParameter F G) (c : List Bool) :
    TarskiQueryBits.value (family F G) c = value F G c := by
  change RootSignQueries.tarskiQuery
    ((DyadicPolynomial.specialize (F.polynomial c) _ _).map (Int.castRingHom ℝ))
    ((DyadicPolynomial.specialize (G.polynomial c) _ _).map (Int.castRingHom ℝ)) = _
  rw [DyadicPolynomial.map_specialize _ _ _ (F.coefficient_degree c),
    DyadicPolynomial.map_specialize _ _ _ (G.coefficient_degree c)]
  rw [RootSignQueries.tarskiQuery_C_mul _ _ _ _
    (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
    (pow_pos (by norm_num : (0 : ℝ) < 2) _), ← h c]
  rfl

/-- Only the original bivariate coefficient routines are external subroutines. -/
noncomputable def evaluator {F G : Family} (a : Access F) (b : Access G)
    (hF : ControlsPolyTime F) (hG : ControlsPolyTime G) (h : SameParameter F G)
    (P : SpaceFunction a.coefficient) (Q : SpaceFunction b.coefficient) :
    SpaceFunction (fun c => SignStatisticBits.integerCode (value F G c)) := by
  let E := TarskiQueryBits.evaluator (access F G) (controls F G hF hG)
    (residueEvaluator a hF P) (residueEvaluator b hG Q)
  exact E.congr (funext fun c => congrArg SignStatisticBits.integerCode (family_value F G h c))

def positiveLanguage (F G : Family) : Language := {c | 0 < value F G c}

theorem positiveLanguage_mem_PSPACE {F G : Family} (a : Access F) (b : Access G)
    (hF : ControlsPolyTime F) (hG : ControlsPolyTime G) (h : SameParameter F G)
    (P : SpaceFunction a.coefficient) (Q : SpaceFunction b.coefficient) :
    positiveLanguage F G ∈ PSPACE := by
  have he : TarskiQueryBits.positiveLanguage (family F G) = positiveLanguage F G := by
    ext c
    change 0 < TarskiQueryBits.value (family F G) c ↔ 0 < value F G c
    rw [family_value F G h c]
  rw [← he]
  exact TarskiQueryBits.positiveLanguage_mem_PSPACE (access F G) (controls F G hF hG)
    (residueEvaluator a hF P) (residueEvaluator b hG Q)

end LeanCanny.Algebra.DyadicTarskiBits
