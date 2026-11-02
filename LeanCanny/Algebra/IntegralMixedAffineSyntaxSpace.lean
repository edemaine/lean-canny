/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedAffineCoefficientSpace
public import LeanCanny.Computation.SpaceFunctionChain
/-! # Space-generated original affine syntax composes with a uniform term reader -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedAffineCode
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def syntaxDimension := ETR.CollectedCoefficient.dimension pairFst
noncomputable def constantReader := ETR.SizedCollectedCoefficient.value syntaxDimension (fun _ => 1) pairFst (zeroTarget syntaxDimension) pairSnd

theorem constantReader_space : SpaceFunction constantReader :=
  ETR.SizedCollectedCoefficient.evaluator (ETR.CollectedCoefficient.dimension_unary pairFst_mem_FP)
    (UnaryFn.const 1) pairFst_mem_FP (zeroTarget_FP _ (ETR.CollectedCoefficient.dimension_unary pairFst_mem_FP)) pairSnd_mem_FP
    (ETR.CollectedCoefficient.arity_le_dimension pairFst)

theorem constantReader_packet (e : IntegralMixedHistory.AffineExpr) (m : List Bool) :
    constantReader (pair (encode e) m) = residueBits (IntegralMixedAffineCoefficients.constantCoefficient e : ZMod (Nat.fromBitsLE m + 1)) := by
  unfold constantReader ETR.SizedCollectedCoefficient.value
  rw [zero_exponent]
  have HC : ((ETR.TermView.term (pairFst (pair (encode e) m))).finitePolynomial
      (syntaxDimension (pair (encode e) m))).coeff 0 = IntegralMixedAffineCoefficients.constantCoefficient e := by
    rw [pairFst_pair, encode, ETR.TermView.term_toBits, constant_coefficient]
  exact congrArg₂ (fun (z : ℤ) (n : ℕ) => residueBits (z : ZMod n)) HC
    (congrArg (fun w => Nat.fromBitsLE w + 1) (pairSnd_pair _ _))

def syntaxIndex (q : List Bool) := Nat.fromBitsLE (pairFst (pairSnd q))
def syntaxModulus (q : List Bool) := pairSnd (pairSnd q)
noncomputable def referenceReader (q : List Bool) :=
  if syntaxIndex q < syntaxDimension q then
    ETR.SizedCollectedCoefficient.value syntaxDimension (fun _ => 1) pairFst (unitTarget syntaxDimension syntaxIndex) syntaxModulus q else []

theorem referenceReader_space : SpaceFunction referenceReader := by
  have HN := ETR.CollectedCoefficient.dimension_unary pairFst_mem_FP
  have HJ : BinaryFn syntaxIndex := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have HV := ETR.SizedCollectedCoefficient.evaluator HN (UnaryFn.const 1) pairFst_mem_FP (unitTarget_FP _ _ HN HJ)
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (ETR.CollectedCoefficient.arity_le_dimension pairFst)
  have HP := HJ.lt (BinaryFn.ofUnary HN)
  exact (SpaceFunction.branch _ HP.flag_mem_FP HV (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
    (funext fun q => by simp only [referenceReader, decide_eq_true_eq]; rfl)

theorem referenceReader_packet (e : IntegralMixedHistory.AffineExpr) (i : ℕ) (m : List Bool) :
    referenceReader (pair (encode e) (pair (BinaryNatCode.encode i) m)) =
      residueBits (IntegralMixedAffineCoefficients.referenceCoefficient e i : ZMod (Nat.fromBitsLE m + 1)) := by
  let q := pair (encode e) (pair (BinaryNatCode.encode i) m)
  have HJ : syntaxIndex q = i := by simp only [syntaxIndex, q, pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HM : Nat.fromBitsLE (syntaxModulus q) + 1 = Nat.fromBitsLE m + 1 := by simp only [syntaxModulus, q, pairSnd_pair]
  have HT : ETR.TermView.term (pairFst q) = term e := by rw [show pairFst q = encode e from pairFst_pair _ _, encode, ETR.TermView.term_toBits]
  have HA := ETR.CollectedCoefficient.arity_le_dimension pairFst q
  rw [HT] at HA
  by_cases hi : syntaxIndex q < syntaxDimension q
  · change (if syntaxIndex q < syntaxDimension q then _ else _) = _
    rw [ite_eq_left hi]
    unfold ETR.SizedCollectedCoefficient.value
    rw [unit_exponent _ _ q hi]
    have HC : ((ETR.TermView.term (pairFst q)).finitePolynomial (syntaxDimension q)).coeff
        (Finsupp.single (⟨syntaxIndex q, hi⟩ : Fin (syntaxDimension q)) 1) = IntegralMixedAffineCoefficients.referenceCoefficient e i := by
      rw [HT, reference_coefficient]
      exact congrArg (IntegralMixedAffineCoefficients.referenceCoefficient e) HJ
    exact congrArg₂ (fun (z : ℤ) (n : ℕ) => residueBits (z : ZMod n)) HC HM
  · change (if syntaxIndex q < syntaxDimension q then _ else _) = _
    rw [ite_eq_right hi]
    have HZ := reference_outside e (syntaxDimension q) i HA (by rw [HJ] at hi; omega)
    rw [HZ]
    simpa only [ArithmeticBits.zero, Int.cast_zero] using ArithmeticBits.zero_residueBits (Nat.fromBitsLE m + 1)

theorem constant_space_fromSpace (E : List Bool → IntegralMixedHistory.AffineExpr) (source mod : List Bool → List Bool)
    (hs : SpaceFunction source) (hm : mod ∈ FP) (he : ∀ q, source q = encode (E q)) :
    SpaceFunction (fun q => residueBits (IntegralMixedAffineCoefficients.constantCoefficient (E q) : ZMod (Nat.fromBitsLE (mod q) + 1))) := by
  have H := (hs.pairOutputs (SpaceFunction.ofFP _ hm)).chain constantReader_space
  apply H.congr
  funext q
  change constantReader (pair (source q) (mod q)) = _
  rw [he q]
  exact constantReader_packet (E q) (mod q)

theorem reference_space_fromSpace (E : List Bool → IntegralMixedHistory.AffineExpr) (source mod : List Bool → List Bool)
    (J : List Bool → ℕ) (hs : SpaceFunction source) (hm : mod ∈ FP) (hJ : BinaryFn J) (he : ∀ q, source q = encode (E q)) :
    SpaceFunction (fun q => residueBits (IntegralMixedAffineCoefficients.referenceCoefficient (E q) (J q) : ZMod (Nat.fromBitsLE (mod q) + 1))) := by
  have HQ := hs.pairOutputs ((SpaceFunction.ofFP _ hJ.bits_mem_FP).pairOutputs (SpaceFunction.ofFP _ hm))
  have H := HQ.chain referenceReader_space
  apply H.congr
  funext q
  change referenceReader (pair (source q) (pair (BinaryNatCode.encode (J q)) (mod q))) = _
  rw [he q]
  exact referenceReader_packet (E q) (J q) (mod q)
end LeanCanny.Algebra.IntegralMixedAffineCode
