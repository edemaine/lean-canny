/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialBankCenterPolynomial
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQBankProducts
/-! # Native sparse numerators at actual chronological center references

Reference lookup and exponent guards run before the original current-Q
cofactor query. No division modulo the caller modulus occurs.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialBankCenterNumerator
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower FixedWidthPolynomial
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedBankSnapshotBits (atKey packet)
open FormulaSignSlotRadialBankCenterPolynomial (key reference numerator width)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def context (q : List Bool) := pairFst (pairFst q)
def indexWord (q : List Bool) := pairFst (pairSnd (pairFst q))
def target (q : List Bool) := pairSnd (pairSnd (pairFst q))
def refWord (refs : List Bool → List Bool) (q : List Bool) :=
  WordList.reader (pair (refs (pairFst (context q))) (indexWord q))
noncomputable def count (B : Bank) (q : List Bool) := (atKey B.parameters B.plan B.data (key B (context q))).count
def requested (refs : List Bool → List Bool) (q : List Bool) := Nat.fromBitsLE (refWord refs q)
noncomputable def clipped (B : Bank) (refs : List Bool → List Bool) (q : List Bool) := min (requested refs q) (count B q)
noncomputable def newest (B : Bank) (refs : List Bool → List Bool) (q : List Bool) := count B q - 1 - clipped B refs q
noncomputable def power (B : Bank) (refs : List Bool → List Bool) (q : List Bool) :=
  UniformIntegralPowerSchedule.birth (B.parameters.cap (pairFst (key B (context q))) + 1)
    (2 ^ B.parameters.width (pairFst (key B (context q)))) (clipped B refs q)
noncomputable def encodedDegree (B : Bank) (source refs : List Bool → List Bool) (q : List Bool) :=
  power B refs q * 2 ^ (newest B refs q * width B source (context q))

theorem context_FP : context ∈ FP := by polytime [context]
theorem indexWord_FP : indexWord ∈ FP := by polytime [indexWord]
theorem target_FP : target ∈ FP := by polytime [target]
theorem key_context_FP (B : Bank) (h : IntegralFramedBankQuery.Access B) :
    (fun q => key B (context q)) ∈ FP :=
  mem_FP_comp (f := context) (g := key B) context_FP (FormulaSignSlotRadialBankCenterPolynomial.key_FP B h)
theorem refWord_FP (refs : List Bool → List Bool) (hr : refs ∈ FP) : refWord refs ∈ FP :=
  mem_FP_comp (mem_FP_pair (mem_FP_comp (mem_FP_comp context_FP pairFst_mem_FP) hr) indexWord_FP) WordList.reader_FP
theorem requested_binary (refs : List Bool → List Bool) (hr : refs ∈ FP) : BinaryFn (requested refs) :=
  BinaryFn.fromBits (refWord_FP refs hr)
theorem count_unary (B : Bank) (h : IntegralFramedBankQuery.Access B) : UnaryFn (count B) :=
  (IntegralMixedFramedBankSnapshotBits.count_unary B.parameters h.parameters B.plan B.data).comp
    (key_context_FP B h)
theorem clipped_unary (B : Bank) (h : IntegralFramedBankQuery.Access B) (refs : List Bool → List Bool) (hr : refs ∈ FP) :
    UnaryFn (clipped B refs) := UnaryFn.fromBitsLE_min (refWord_FP refs hr) (count_unary B h)
theorem newest_unary (B : Bank) (h : IntegralFramedBankQuery.Access B) (refs : List Bool → List Bool) (hr : refs ∈ FP) :
    UnaryFn (newest B refs) := ((count_unary B h).sub (UnaryFn.const 1)).sub (clipped_unary B h refs hr)
theorem power_binary (B : Bank) (h : IntegralFramedBankQuery.Access B) (refs : List Bool → List Bool) (hr : refs ∈ FP) :
    BinaryFn (power B refs) := by
  have HK : (fun q => pairFst (key B (context q))) ∈ FP :=
    mem_FP_comp (f := fun q => key B (context q)) (g := pairFst) (key_context_FP B h) pairFst_mem_FP
  exact UniformIntegralPowerSchedule.birth_binary (UnaryFn.add (h.parameters.cap.comp HK) (UnaryFn.const 1))
    ((BinaryFn.const 2).powUnary (h.parameters.width.comp HK)) (clipped_unary B h refs hr)
theorem encodedDegree_binary (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (source refs : List Bool → List Bool) (hs : source ∈ FP) (hr : refs ∈ FP) : BinaryFn (encodedDegree B source refs) :=
  (power_binary B h refs hr).mul ((BinaryFn.const 2).powUnary
    ((newest_unary B h refs hr).mul ((FormulaSignSlotRadialBankCenterPolynomial.width_unary B h source hs).comp context_FP)))

noncomputable def Selected (B : Bank) (source refs : List Bool → List Bool) (q : List Bool) : Prop :=
  requested refs q < count B q ∧ Nat.fromBitsLE (target q) = encodedDegree B source refs q
theorem selected_FP (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (source refs : List Bool → List Bool) (hs : source ∈ FP) (hr : refs ∈ FP) : FPPred (Selected B source refs) :=
  ((requested_binary refs hr).lt (BinaryFn.ofUnary (count_unary B h))).and
    ((BinaryFn.fromBits target_FP).eq (encodedDegree_binary B h source refs hs hr))

noncomputable def cofactorQuery (B : Bank) (refs : List Bool → List Bool) (q : List Bool) :=
  packet (key B (context q)) (pairSnd q) (newest B refs q) 0
theorem cofactorQuery_FP (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (refs : List Bool → List Bool) (hr : refs ∈ FP) : cofactorQuery B refs ∈ FP :=
  mem_FP_pair (mem_FP_pair (key_context_FP B h) pairSnd_mem_FP)
    (mem_FP_pair (BinaryFn.ofUnary (newest_unary B h refs hr)).bits_mem_FP (constFn_mem_FP (BinaryNatCode.encode 0)))

noncomputable def cofactor (B : Bank) (refs : List Bool → List Bool) : List Bool → List Bool :=
  IntegralMixedFramedBankProductBits.value B.parameters B.plan B.data IntegralMixedFramedBankDenominatorBits.index ∘
    cofactorQuery B refs
theorem cofactor_evaluator (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (refs : List Bool → List Bool) (hr : refs ∈ FP) : SpaceFunction (cofactor B refs) :=
  (IntegralMixedFramedCurrentQBankProductBits.evaluator B.parameters h.parameters B.plan B.data
    h.liftedData h.controls h.bounds IntegralMixedFramedBankDenominatorBits.index
      IntegralMixedFramedBankDenominatorBits.index_binary).precompose (cofactorQuery B refs) (cofactorQuery_FP B h refs hr)

theorem cofactor_actual (B : Bank) (refs : List Bool → List Bool) (q : List Bool) : cofactor B refs q =
    residueBits (((atKey B.parameters B.plan B.data (key B (context q))).cofactor (newest B refs q) : ℤ) :
      ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have HI := IntegralMixedFramedBankSnapshotBits.cofactor_packet B.parameters B.plan B.data
    (key B (context q)) (pairSnd q) (newest B refs q) 0
  have HM : IntegralMixedFramedCompanionQueryBits.callerModulus (cofactorQuery B refs q) =
      Nat.fromBitsLE (pairSnd q) + 1 := by
    simp only [cofactorQuery, IntegralMixedFramedCompanionQueryBits.callerModulus, packet,
      PaddedIntegralGeneratorSource.modulus, pairFst_pair, pairSnd_pair]
  exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m)) HI HM

noncomputable def value (B : Bank) (source refs : List Bool → List Bool) (q : List Bool) :=
  if Selected B source refs q then cofactor B refs q else []
theorem evaluator (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (source refs : List Bool → List Bool) (hs : source ∈ FP) (hr : refs ∈ FP) : SpaceFunction (value B source refs) := by
  have E := SpaceFunction.branch (fun q => decide (Selected B source refs q)) (selected_FP B h source refs hs hr).flag_mem_FP
    (cofactor_evaluator B h refs hr) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun q => by simp only [value, decide_eq_true_eq])

theorem encoded_numerator (B : Bank) (refs : List Bool → List Bool) (z : List Bool) (W i : ℕ) :
    FixedWidthKronecker.encode (atKey B.parameters B.plan B.data (key B z)).count W
      (numerator B refs z i) =
        if reference refs z i < (atKey B.parameters B.plan B.data (key B z)).count then
          Polynomial.monomial
            (UniformIntegralPowerSchedule.birth (B.parameters.cap (pairFst (key B z)) + 1)
              (2 ^ B.parameters.width (pairFst (key B z))) (reference refs z i) *
                2 ^ (IntegralMixedFramedBankTermBits.reverseIndex B.parameters B.plan B.data (key B z) (reference refs z i) * W))
            ((atKey B.parameters B.plan B.data (key B z)).cofactor
              (IntegralMixedFramedBankTermBits.reverseIndex B.parameters B.plan B.data (key B z) (reference refs z i)))
        else 0 := by
  unfold numerator IntegralMixedFramedBankTermBits.numeratorPolynomial
  split_ifs
  · rw [map_mul, map_pow]
    simp only [FixedWidthKronecker.encode, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
    rw [← pow_mul, Polynomial.C_mul_X_pow_eq_monomial, Nat.mul_comm (2 ^ _)]
  · exact map_zero _

theorem correct (B : Bank) (source refs : List Bool → List Bool) (q : List Bool) : value B source refs q =
    residueBits (((FixedWidthKronecker.encode (atKey B.parameters B.plan B.data (key B (context q))).count
      (width B source (context q)) (numerator B refs (context q) (Nat.fromBitsLE (indexWord q)))).coeff
        (Nat.fromBitsLE (target q)) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have HR : requested refs q = reference refs (context q) (Nat.fromBitsLE (indexWord q)) := by
    simp only [requested, refWord, WordList.reader, pairFst_pair, pairSnd_pair, reference]
  rw [encoded_numerator]
  by_cases h : requested refs q < count B q
  · have HC : reference refs (context q) (Nat.fromBitsLE (indexWord q)) <
        (atKey B.parameters B.plan B.data (key B (context q))).count := by rwa [← HR]
    have HM : min (requested refs q) (count B q) = requested refs q := min_eq_left h.le
    rw [ite_eq_left HC, Polynomial.coeff_monomial]
    have HE : UniformIntegralPowerSchedule.birth (B.parameters.cap (pairFst (key B (context q))) + 1)
        (2 ^ B.parameters.width (pairFst (key B (context q))))
          (reference refs (context q) (Nat.fromBitsLE (indexWord q))) *
            2 ^ (IntegralMixedFramedBankTermBits.reverseIndex B.parameters B.plan B.data (key B (context q))
              (reference refs (context q) (Nat.fromBitsLE (indexWord q))) * width B source (context q)) =
                encodedDegree B source refs q := by
      dsimp only [encodedDegree, power, newest, clipped]
      rw [HM, ← HR]
      rfl
    have HIndex : IntegralMixedFramedBankTermBits.reverseIndex B.parameters B.plan B.data (key B (context q))
        (reference refs (context q) (Nat.fromBitsLE (indexWord q))) = newest B refs q := by
      dsimp only [newest, clipped]
      rw [HM, ← HR]
      rfl
    rw [HE, HIndex]
    by_cases hd : Nat.fromBitsLE (target q) = encodedDegree B source refs q
    · rw [value, Selected, ite_eq_left (And.intro h hd), ite_eq_left hd.symm, cofactor_actual]
    · rw [value, Selected, ite_eq_right (fun H => hd H.2), ite_eq_right (Ne.symm hd)]
      rfl
  · have HC : ¬reference refs (context q) (Nat.fromBitsLE (indexWord q)) <
        (atKey B.parameters B.plan B.data (key B (context q))).count := by rwa [← HR]
    rw [ite_eq_right HC, Polynomial.coeff_zero, value, Selected, ite_eq_right (fun H => h H.1)]
    rfl

private noncomputable def entry (B : Bank) (source refs : List Bool → List Bool)
    (z index bits modulus : List Bool) := residueBits
  (((FixedWidthKronecker.encode (atKey B.parameters B.plan B.data (key B z)).count
    (width B source z) (numerator B refs z (Nat.fromBitsLE index))).coeff (Nat.fromBitsLE bits) : ℤ) :
      ZMod (Nat.fromBitsLE modulus + 1))

private theorem value_entry (B : Bank) (source refs : List Bool → List Bool) (q : List Bool) :
    value B source refs q = entry B source refs (context q) (indexWord q) (target q) (pairSnd q) :=
  correct B source refs q

attribute [local irreducible] entry

theorem packet (B : Bank) (source refs : List Bool → List Bool) (z : List Bool) (i k : ℕ) (modulus : List Bool) :
    value B source refs (pair (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) modulus) =
      residueBits (((FixedWidthKronecker.encode (atKey B.parameters B.plan B.data (key B z)).count
        (width B source z) (numerator B refs z i)).coeff k : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) := by
  rw [value_entry]
  simp only [context, indexWord, target, pairFst_pair, pairSnd_pair]
  unfold entry
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.Encoding.FormulaSignSlotRadialBankCenterNumerator
