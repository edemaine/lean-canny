/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralRowQuery

/-! # Native lower rows of the actual monic scalar extension

The newest exponent selects one coefficient at the literal creating source.
Coordinate powers and the old basis box are checked by the existing native
reader. Only its actual companion evaluator is charged as a leaf.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralRowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open PaddedIntegralGeneratorSource UniformIntegralPowerSchedule MonicParameterRows
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def lowerPolynomial (S : Source) (cap : List Bool→ℕ) (c : List Bool) :
    MvPolynomial (Fin (S.arity c+1)) ℤ :=
  MvPolynomial.rename (headEquiv (S.arity c))
    (MonicParameterRows.lower (S.equation c) (scalarDegree S c)
      (weights (cap c) (scalarDegree S c) (S.arity c)) (birthPower S cap c))

private theorem monic (S : Source) (c : List Bool) :
    (S.equation c).Monic ∧ (S.equation c).natDegree=scalarDegree S c := by
  let := S.ring c
  let := S.nontrivial c
  exact PaddedIntegralParameterExtension.equation_monic (S.basis c) (S.polynomial c) (S.degree c) (Nat.two_pow_pos _)

private theorem active_value (S : Source) (cap V : List Bool→ℕ) (target modulus : List Bool→List Bool)
    (c : List Bool) (hc : Active S cap V target c) :
    FixedWidthRowBits.value (PaddedIntegralEquationMatrixBits.family S).arity (V ∘ pairFst)
      ((PaddedIntegralEquationMatrixBits.family S).poweredPolynomial (cap ∘ pairFst))
      (tailTarget V target ∘ pairFst) (modulus ∘ pairFst) (coefficientContext S cap V target c) =
    FixedWidthRowBits.value (fun q=>S.arity q+1) V (lowerPolynomial S cap) target modulus c := by
  generalize HZ : coefficientContext S cap V target c=z
  have HC : pairFst z=c := by rw [←HZ,coefficientContext,pairFst_pair]
  have HP : (PaddedIntegralEquationMatrixBits.power S z).val=
      selectedPower S cap V target c % scalarDegree S c := by
    rw [←HZ]
    simp only [PaddedIntegralEquationMatrixBits.power,coefficientContext,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits,scalarDegree]
  subst c
  have HN := monic S (pairFst z)
  have HG : entry (V (pairFst z)) (Nat.fromBitsLE (target (pairFst z))) 0 % birthPower S cap (pairFst z)=0 ∧
      entry (V (pairFst z)) (Nat.fromBitsLE (target (pairFst z))) 0 / birthPower S cap (pairFst z)<scalarDegree S (pairFst z) := by
    simpa only [Active,selectedPower,newExponent_eq] using hc
  have HK := Nat.mod_eq_of_lt hc.2
  dsimp only [FixedWidthRowBits.value,Function.comp_apply]
  rw [PaddedIntegralEquationMatrixBits.powered_polynomial_eq,HP,HK,lowerPolynomial]
  rw [native_lower_coefficient (S.equation (pairFst z)) (scalarDegree S (pairFst z)) HN.1 HN.2
    (weights (cap (pairFst z)) (scalarDegree S (pairFst z)) (S.arity (pairFst z)))
    (birthPower S cap (pairFst z)) (birth_pos _ _ _) (V (pairFst z)) (target (pairFst z)),ite_eq_left HG]
  simp only [selectedPower,newExponent_eq]
  rfl

theorem lower_evaluator (S : Source) (cap V : List Bool→ℕ) (target modulus : List Bool→List Bool)
    (hc : UnaryFn cap) (ha : UnaryFn S.arity) (hw : UnaryFn S.width) (hV : UnaryFn V)
    (ht : target∈FP) (hm : modulus∈FP) (E : SpaceFunction (PaddedIntegralGeneratorSource.value S)) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>S.arity q+1) V (lowerPolynomial S cap) target modulus) := by
  have HO := PaddedIntegralEquationMatrixBits.powered_evaluator S (cap ∘ pairFst) (V ∘ pairFst)
    (tailTarget V target ∘ pairFst) (modulus ∘ pairFst) (hc.comp pairFst_mem_FP) ha hw (hV.comp pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP (tailTarget_FP V target hV ht)) (mem_FP_comp pairFst_mem_FP hm) E
  have HR := HO.precompose (coefficientContext S cap V target) (coefficientContext_FP S cap V target hc ha hw hV ht)
  have H := SpaceFunction.branch (fun c=>decide (Active S cap V target c))
    (active_FP S cap V target hc ha hw hV ht).flag_mem_FP HR (SpaceFunction.ofFP _ (constFn_mem_FP []))
  apply H.congr
  funext c
  by_cases HA : Active S cap V target c
  · rw [ite_eq_left (decide_eq_true HA)]
    exact active_value S cap V target modulus c HA
  · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using HA)]
    have HN := monic S c
    have HG : ¬(entry (V c) (Nat.fromBitsLE (target c)) 0 % birthPower S cap c=0 ∧
        entry (V c) (Nat.fromBitsLE (target c)) 0 / birthPower S cap c<scalarDegree S c) := by
      simpa only [Active,selectedPower,newExponent_eq] using HA
    simp only [FixedWidthRowBits.value,lowerPolynomial]
    rw [native_lower_coefficient (S.equation c) (scalarDegree S c) HN.1 HN.2
      (weights (cap c) (scalarDegree S c) (S.arity c)) (birthPower S cap c)
      (birth_pos _ _ _) (V c) (target c),ite_eq_right HG]
    simp only [Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode]
    rfl

end LeanCanny.Algebra.PaddedIntegralRowBits
