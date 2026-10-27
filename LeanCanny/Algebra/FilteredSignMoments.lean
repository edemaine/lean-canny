/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FilteredSignPatternEnumeration
public import LeanCanny.Algebra.IntegerSmallProductSpace
public import Mathlib.Data.Int.NatAbs

/-! # Native signed moments over roots satisfying sign constraints

Only polynomially many selected features are supplied. Enumerating their
ternary sign patterns, with a streaming signed sum, computes a moment on the
accepted root set without retaining the patterns or all the roots.
-/

@[expose] public section
namespace LeanCanny.Algebra.FilteredSignMomentBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation SignPatternBits
open LeanCanny.Encoding.Brackets
open scoped Classical BigOperators

def factorWord (p : List Bool) : List Bool :=
  if pairSnd p = [] then SignStatisticBits.integerCode 1
  else if pairFst p = [] then SignStatisticBits.integerCode 0
  else if pairFst p = [true] then SignStatisticBits.integerCode 1
  else if pairSnd p = [true] then SignStatisticBits.integerCode (-1)
  else SignStatisticBits.integerCode 1

theorem factorWord_FP : factorWord ∈ FP := by
  have h0 := stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [])
  have hs0 := stringEq_fppred pairFst_mem_FP (constFn_mem_FP [])
  have hs1 := stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])
  have he1 := stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true])
  exact h0.ite_mem_FP (constFn_mem_FP _) (hs0.ite_mem_FP (constFn_mem_FP _)
    (hs1.ite_mem_FP (constFn_mem_FP _) (he1.ite_mem_FP (constFn_mem_FP _) (constFn_mem_FP _))))

theorem factorWord_codes (s e : Fin 3) :
    factorWord (pair (BinaryNatCode.encode s.val) (BinaryNatCode.encode e.val)) =
      SignStatisticBits.integerCode ((SignType.fin3Equiv.symm s : ℤ) ^ e.val) := by
  fin_cases s <;> fin_cases e <;> rfl

theorem factor_abs_le (s : SignType) (e : Fin 3) : ((s : ℤ) ^ e.val).natAbs ≤ 2 := by
  cases s <;> fin_cases e <;> decide

theorem sign_power_abs_le_one (s : SignType) (e : Fin 3) : ((s : ℤ) ^ e.val).natAbs ≤ 1 := by
  cases s <;> fin_cases e <;> decide

/-- A summand context is `pair (pair source exponents) patternRank`. -/
def context (q : List Bool) : List Bool := pairFst (pairFst q)
def exponents (q : List Bool) : List Bool := pairSnd (pairFst q)
def patternQuery (q : List Bool) : List Bool := pair (context q) (pairSnd q)

theorem context_FP : context ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem exponents_FP : exponents ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem patternQuery_FP : patternQuery ∈ FP := mem_FP_pair context_FP pairSnd_mem_FP

noncomputable def factor (G : Family) (q : List Bool) (i : ℕ) : ℤ :=
  (enumeratedSign (Nat.fromBitsLE (G.count (context q))) (Nat.fromBitsLE (pairSnd q)) i : ℤ) ^
    (Ternary.exponent (Nat.fromBitsLE (G.count (context q))) (Nat.fromBitsLE (exponents q)) i).val

def factorBits (G : Family) (p : List Bool) : List Bool :=
  factorWord (pair
    (Ternary.digit (G.count (context (pairFst p))) (pairSnd (pairFst p)) (pairSnd p))
    (Ternary.digit (G.count (context (pairFst p))) (exponents (pairFst p)) (pairSnd p)))

theorem factorBits_FP {G : Family} (hG : ControlsPolyTime G) : factorBits G ∈ FP := by
  have hsource : (context ∘ pairFst) ∈ FP := mem_FP_comp pairFst_mem_FP context_FP
  have hk : (G.count ∘ (context ∘ pairFst)) ∈ FP := mem_FP_comp hsource hG.count
  have hu := hG.countUnary.comp hsource
  exact mem_FP_comp (mem_FP_pair
    (Ternary.digit_mem_FP hk (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP hu)
    (Ternary.digit_mem_FP hk (mem_FP_comp (f := pairFst) (g := exponents)
      pairFst_mem_FP exponents_FP) pairSnd_mem_FP hu)) factorWord_FP

theorem factorBits_packet (G : Family) (q : List Bool) (i : ℕ) :
    factorBits G (pair q (BinaryNatCode.encode i)) = SignStatisticBits.integerCode (factor G q i) := by
  simp only [factorBits, pairFst_pair, pairSnd_pair, Ternary.digit_exponent,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact factorWord_codes _ _

noncomputable def patternWeight (G : Family) (q : List Bool) : ℤ :=
  IntegerSmallProductBits.product (factor G q) (Nat.fromBitsLE (G.count (context q)))

theorem patternWeightEvaluator {G : Family} (hG : ControlsPolyTime G) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (patternWeight G q)) :=
  IntegerSmallProductBits.evaluator (SpaceFunction.ofFP (factorBits G) (factorBits_FP hG))
    (G.count ∘ context) (mem_FP_comp context_FP hG.count) (hG.countUnary.comp context_FP)
    (factor G) (factorBits_packet G) (fun _ _ => factor_abs_le _ _)

def signedNatural (w : List Bool) : List Bool := pair w []
theorem signedNatural_FP : signedNatural ∈ FP := mem_FP_pair id_mem_FP (constFn_mem_FP [])
theorem signedNatural_encode (n : ℕ) :
    signedNatural (BinaryNatCode.encode n) = SignStatisticBits.integerCode (n : ℤ) := by
  simp [signedNatural, SignStatisticBits.integerCode]
  rfl

noncomputable def summand (F G : Family) (q : List Bool) : ℤ :=
  patternWeight G q * (rootCount ((F.comp pairFst).append G.enumerate) (patternQuery q) : ℤ)

theorem summandEvaluator {F G : Family} (A : Access F) (B : Access G)
    (hF : ControlsPolyTime F) (hG : ControlsPolyTime G) (hs : A.pattern ∈ FP)
    (H : SpaceFunction A.rootCoefficient) (P : SpaceFunction A.polynomialCoefficient)
    (Q : SpaceFunction B.polynomialCoefficient) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (summand F G q)) := by
  have Hr : SpaceFunction (A.comp pairFst).rootCoefficient :=
    H.precompose (compQuery pairFst) (compQuery_FP pairFst_mem_FP)
  have Pr : SpaceFunction (A.comp pairFst).polynomialCoefficient :=
    P.precompose (compQuery pairFst) (compQuery_FP pairFst_mem_FP)
  have Qr : SpaceFunction B.enumerate.polynomialCoefficient :=
    Q.precompose (compQuery pairFst) (compQuery_FP pairFst_mem_FP)
  have hsr : (A.comp pairFst).pattern ∈ FP := by
    change (A.pattern ∘ compPattern pairFst) ∈ FP
    exact mem_FP_comp (compPattern_FP pairFst_mem_FP) hs
  have C := appendCountEvaluator (A.comp pairFst) B.enumerate (comp_controls hF pairFst_mem_FP)
    (enumerate_controls hG) hsr (enumeratedPattern_FP hG) Hr Pr Qr
  have N := (C.precompose patternQuery patternQuery_FP).postcompose signedNatural signedNatural_FP
  have W := (patternWeightEvaluator hG).withInput
  have V := (N.precompose pairFst pairFst_mem_FP).withInput
  have E := (W.chain V).postcompose SignPatternBits.termOutput SignPatternBits.termOutput_mem_FP
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, SignPatternBits.termOutput, pairFst_pair, pairSnd_pair,
    signedNatural_encode, IntegerSumBits.multiply_codes, summand]

noncomputable def moment (F G : Family) (q : List Bool) : ℤ :=
  ∑ x ∈ acceptedRoots F (pairFst q),
    ∏ i ∈ Finset.range (Nat.fromBitsLE (G.count (pairFst q))),
      (SignType.sign (((G.polynomial (pairFst q) i).map (algebraMap ℤ ℝ)).eval x) : ℤ) ^
        (Ternary.exponent (Nat.fromBitsLE (G.count (pairFst q))) (Nat.fromBitsLE (pairSnd q)) i).val

theorem moment_no_features (F G : Family) (q : List Bool)
    (h : Nat.fromBitsLE (G.count (pairFst q)) = 0) :
    moment F G q = (rootCount F (pairFst q) : ℤ) := by
  simp only [moment, h, Finset.range_zero, Finset.prod_empty, Finset.sum_const,
    nsmul_eq_mul, mul_one, rootCount_eq_card]

theorem moment_abs_le_count (F G : Family) (q : List Bool) :
    (moment F G q).natAbs ≤ rootCount F (pairFst q) := by
  rw [moment, rootCount_eq_card]
  calc
    _ ≤ ∑ x ∈ acceptedRoots F (pairFst q),
        (∏ i ∈ Finset.range (Nat.fromBitsLE (G.count (pairFst q))),
          (SignType.sign (((G.polynomial (pairFst q) i).map (algebraMap ℤ ℝ)).eval x) : ℤ) ^
            (Ternary.exponent (Nat.fromBitsLE (G.count (pairFst q))) (Nat.fromBitsLE (pairSnd q)) i).val).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _x ∈ acceptedRoots F (pairFst q), 1 := by
      apply Finset.sum_le_sum
      intro x _
      change Int.natAbsHom _ ≤ 1
      rw [map_prod]
      calc
        _ ≤ ∏ _i ∈ Finset.range (Nat.fromBitsLE (G.count (pairFst q))), (1 : ℕ) :=
          Finset.prod_le_prod (fun _ _ => sign_power_abs_le_one _ _)
        _ = 1 := by simp
    _ = _ := by simp

theorem sum_eq_moment (F G : Family) (q : List Bool) :
    (∑ r ∈ Finset.range (3 ^ Nat.fromBitsLE (G.count (pairFst q))),
      summand F G (pair q (BinaryNatCode.encode r))) = moment F G q := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [summand, patternQuery, context, pairFst_pair, pairSnd_pair, enumeratedCount_eq]
  let k := Nat.fromBitsLE (G.count (pairFst q))
  let w (sigma : Fin k → SignType) : ℤ :=
    ∏ i, (sigma i : ℤ) ^ (Ternary.exponent k (Nat.fromBitsLE (pairSnd q)) i.val).val
  have hw (r : Fin (3 ^ k)) : patternWeight G (pair q (BinaryNatCode.encode r.val)) = w (patternEquiv k r) := by
    simp only [patternWeight, IntegerSmallProductBits.product, factor, context, exponents,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, w, patternEquiv_apply]
    exact (Fin.prod_univ_eq_prod_range _ _).symm
  simp_rw [hw]
  have he (r : Fin (3 ^ k)) : (fun i : Fin k => enumeratedSign k r.val i.val) = patternEquiv k r := by
    funext i
    exact (patternEquiv_apply k r i).symm
  change (∑ r : Fin (3 ^ k), w (patternEquiv k r) *
    (RootSignQueries.signCount (acceptedRoots F (pairFst q))
      (fun i : Fin k => (G.polynomial (pairFst q) i.val).map (algebraMap ℤ ℝ))
      (fun i => enumeratedSign k r.val i.val) : ℤ)) = _
  simp_rw [he]
  have hsum := Equiv.sum_comp (patternEquiv k) (fun sigma : Fin k → SignType =>
    w sigma * (RootSignQueries.signCount (acceptedRoots F (pairFst q))
      (fun i : Fin k => (G.polynomial (pairFst q) i.val).map (algebraMap ℤ ℝ)) sigma : ℤ))
  refine hsum.trans ?_
  have hp := RootSignQueries.sum_pattern_counts (acceptedRoots F (pairFst q))
    (fun i : Fin k => (G.polynomial (pairFst q) i.val).map (algebraMap ℤ ℝ)) w
  trans ∑ x ∈ acceptedRoots F (pairFst q),
    w (fun i : Fin k => SignType.sign (((G.polynomial (pairFst q) i.val).map (algebraMap ℤ ℝ)).eval x))
  · refine Eq.trans ?_ hp
    apply Finset.sum_congr
    · ext sigma
      simp only [Finset.mem_univ]
    · intro sigma _
      rfl
  unfold moment
  apply Finset.sum_congr rfl
  intro x _
  exact Fin.prod_univ_eq_prod_range
    (fun i => (SignType.sign (((G.polynomial (pairFst q) i).map (algebraMap ℤ ℝ)).eval x) : ℤ) ^
      (Ternary.exponent k (Nat.fromBitsLE (pairSnd q)) i).val) k

theorem evaluator {F G : Family} (A : Access F) (B : Access G)
    (hF : ControlsPolyTime F) (hG : ControlsPolyTime G) (hs : A.pattern ∈ FP)
    (H : SpaceFunction A.rootCoefficient) (P : SpaceFunction A.polynomialCoefficient)
    (Q : SpaceFunction B.polynomialCoefficient) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment F G q)) := by
  have E := IntegerSumBits.evaluator (summandEvaluator A B hF hG hs H P Q)
    (fun q => Ternary.count (G.count (pairFst q)))
    (Ternary.count_mem_FP (mem_FP_comp pairFst_mem_FP hG.count) (hG.countUnary.comp pairFst_mem_FP))
    (fun q r => summand F G (pair q (BinaryNatCode.encode r))) (fun _ _ => rfl)
  refine E.congr (funext fun q => ?_)
  simp only [Ternary.count_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact congrArg SignStatisticBits.integerCode (by simpa only [BinaryNatCode.encode] using sum_eq_moment F G q)

end LeanCanny.Algebra.FilteredSignMomentBits
