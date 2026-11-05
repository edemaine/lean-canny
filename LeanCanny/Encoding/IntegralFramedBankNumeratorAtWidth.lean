/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialBankCenterNumerator
/-! # Original CurrentQ access to bank numerators in any charged output box

The actual chronological reference, cofactor and creating power are reused.
Only the Kronecker output width varies; modular division is never used.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankNumeratorAtWidth
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower FixedWidthPolynomial
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedBankSnapshotBits (atKey)
open FormulaSignSlotRadialBankCenterPolynomial (key reference numerator)
open FormulaSignSlotRadialBankCenterNumerator
  (context context_FP indexWord target target_FP count count_unary requested requested_binary refWord
    power power_binary newest newest_unary clipped cofactor cofactor_actual cofactor_evaluator encoded_numerator)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def encodedDegree (B : Bank) (refs : List Bool → List Bool) (V : List Bool → ℕ) (q : List Bool) :=
  power B refs q * 2 ^ (newest B refs q * V (context q))
theorem encodedDegree_binary (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (refs : List Bool → List Bool) (V : List Bool → ℕ) (hr : refs ∈ FP) (hV : UnaryFn V) :
    BinaryFn (encodedDegree B refs V) :=
  (power_binary B h refs hr).mul ((BinaryFn.const 2).powUnary ((newest_unary B h refs hr).mul (hV.comp context_FP)))

noncomputable def Selected (B : Bank) (refs : List Bool → List Bool) (V : List Bool → ℕ) (q : List Bool) : Prop :=
  requested refs q < count B q ∧ Nat.fromBitsLE (target q) = encodedDegree B refs V q
theorem selected_FP (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (refs : List Bool → List Bool) (V : List Bool → ℕ) (hr : refs ∈ FP) (hV : UnaryFn V) :
    FPPred (Selected B refs V) :=
  ((requested_binary refs hr).lt (BinaryFn.ofUnary (count_unary B h))).and
    ((BinaryFn.fromBits target_FP).eq (encodedDegree_binary B h refs V hr hV))

noncomputable def value (B : Bank) (refs : List Bool → List Bool) (V : List Bool → ℕ) (q : List Bool) :=
  if Selected B refs V q then cofactor B refs q else []
theorem evaluator (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (refs : List Bool → List Bool) (V : List Bool → ℕ) (hr : refs ∈ FP) (hV : UnaryFn V) :
    SpaceFunction (value B refs V) := by
  have E := SpaceFunction.branch (fun q => decide (Selected B refs V q)) (selected_FP B h refs V hr hV).flag_mem_FP
    (cofactor_evaluator B h refs hr) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun q => by simp only [value, decide_eq_true_eq])

theorem correct (B : Bank) (refs : List Bool → List Bool) (V : List Bool → ℕ) (q : List Bool) : value B refs V q =
    residueBits (((FixedWidthKronecker.encode (atKey B.parameters B.plan B.data (key B (context q))).count
      (V (context q)) (numerator B refs (context q) (Nat.fromBitsLE (indexWord q)))).coeff
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
              (reference refs (context q) (Nat.fromBitsLE (indexWord q))) * V (context q)) =
                encodedDegree B refs V q := by
      dsimp only [encodedDegree, power, newest, clipped]
      rw [HM, ← HR]
      rfl
    have HIndex : IntegralMixedFramedBankTermBits.reverseIndex B.parameters B.plan B.data (key B (context q))
        (reference refs (context q) (Nat.fromBitsLE (indexWord q))) = newest B refs q := by
      dsimp only [newest, clipped]
      rw [HM, ← HR]
      rfl
    rw [HE, HIndex]
    by_cases hd : Nat.fromBitsLE (target q) = encodedDegree B refs V q
    · rw [value, Selected, ite_eq_left (And.intro h hd), ite_eq_left hd.symm, cofactor_actual]
    · rw [value, Selected, ite_eq_right (fun H => hd H.2), ite_eq_right (Ne.symm hd)]
      rfl
  · have HC : ¬reference refs (context q) (Nat.fromBitsLE (indexWord q)) <
        (atKey B.parameters B.plan B.data (key B (context q))).count := by rwa [← HR]
    rw [ite_eq_right HC, Polynomial.coeff_zero, value, Selected, ite_eq_right (fun H => h H.1)]
    rfl

private noncomputable def entry (B : Bank) (refs : List Bool → List Bool) (V : List Bool → ℕ)
    (z index bits modulus : List Bool) := residueBits
  (((FixedWidthKronecker.encode (atKey B.parameters B.plan B.data (key B z)).count
    (V z) (numerator B refs z (Nat.fromBitsLE index))).coeff (Nat.fromBitsLE bits) : ℤ) :
      ZMod (Nat.fromBitsLE modulus + 1))

private theorem value_entry (B : Bank) (refs : List Bool → List Bool) (V : List Bool → ℕ) (q : List Bool) :
    value B refs V q = entry B refs V (context q) (indexWord q) (target q) (pairSnd q) :=
  correct B refs V q

attribute [local irreducible] entry

theorem packet (B : Bank) (refs : List Bool → List Bool) (V : List Bool → ℕ) (z : List Bool) (i k : ℕ) (modulus : List Bool) :
    value B refs V (pair (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) modulus) =
      residueBits (((FixedWidthKronecker.encode (atKey B.parameters B.plan B.data (key B z)).count
        (V z) (numerator B refs z i)).coeff k : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) := by
  rw [value_entry]
  simp only [context, indexWord, target, pairFst_pair, pairSnd_pair]
  unfold entry
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]


end LeanCanny.Encoding.IntegralFramedBankNumeratorAtWidth
