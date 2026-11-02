/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankCoordinate
/-! # Native common-cleared coordinate polynomial coefficients

The source packet's row selects a retained coordinate; its column selects
the coefficient of the fixed-width Kronecker encoding. Scheduled powers are
computed from original metadata. Only actual producer-leading residues feed
the streamed integer cofactor, and invalid coordinate labels return zero.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankCoordinateBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankDenominatorBits (count count_unary index)
open IntegralMixedFramedCompanionQueryBits (callerModulus)
open scoped Classical

noncomputable def coefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (W : List Bool → ℕ) (q : List Bool) : List Bool :=
  residueBits (((FixedWidthKronecker.encode (count P D H q) (W q) (polynomial P D H q)).coeff
    (Nat.fromBitsLE (PaddedIntegralGeneratorSource.col q)) : ℤ) : ZMod (callerModulus q))

noncomputable def selected (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (W : List Bool → ℕ) (q : List Bool) : Prop :=
  index q<count P D H q ∧ Nat.fromBitsLE (PaddedIntegralGeneratorSource.col q)=encodedDegree P D H W q

theorem selected_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (W : List Bool → ℕ) (hW : UnaryFn W) : FPPred (selected P D H W) :=
  (IntegralMixedFramedBankDenominatorBits.index_binary.lt (BinaryFn.ofUnary (count_unary P a D H))).and
    ((BinaryFn.fromBits PaddedIntegralGeneratorSource.col_FP).eq (encodedDegree_binary P a D H W hW))

theorem coefficient_selected (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (W : List Bool → ℕ) (q : List Bool) (hq : selected P D H W q) :
    coefficient P D H W q=IntegralMixedFramedBankProductBits.value P D H index q := by
  unfold coefficient
  rw [encoded_polynomial,ite_eq_left hq.1,Polynomial.coeff_monomial,ite_eq_left hq.2.symm]
  rfl

theorem coefficient_outside (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (W : List Bool → ℕ) (q : List Bool) (hq : ¬selected P D H W q) : coefficient P D H W q=[] := by
  unfold coefficient
  rw [encoded_polynomial]
  by_cases hi : index q<count P D H q
  · have HD : encodedDegree P D H W q≠Nat.fromBitsLE (PaddedIntegralGeneratorSource.col q) := fun he => hq ⟨hi,he.symm⟩
    rw [ite_eq_left hi,Polynomial.coeff_monomial,ite_eq_right HD,Int.cast_zero]
    exact (ArithmeticBits.zero_residueBits _).symm
  · rw [ite_eq_right hi,Polynomial.coeff_zero,Int.cast_zero]
    exact (ArithmeticBits.zero_residueBits _).symm

noncomputable def finish (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (W : List Bool → ℕ) (z : List Bool) := if selected P D H W (pairFst z) then pairSnd z else []
theorem finish_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (W : List Bool → ℕ) (hW : UnaryFn W) : finish P D H W∈FP :=
  ((selected_FP P a D H W hW).comp pairFst_mem_FP).ite_mem_FP pairSnd_mem_FP (constFn_mem_FP [])

theorem coefficient_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    (W : List Bool → ℕ) (hW : UnaryFn W) : SpaceFunction (coefficient P D H W) := by
  have EC := IntegralMixedFramedBankProductBits.evaluator P a D H s hs hF hL index
    IntegralMixedFramedBankDenominatorBits.index_binary
  have EE := EC.withInput.postcompose (finish P D H W) (finish_FP P a D H W hW)
  exact EE.congr (funext fun q => by
    simp only [Function.comp_apply,finish,pairFst_pair,pairSnd_pair]
    split_ifs with hq
    · exact (coefficient_selected P D H W q hq).symm
    · exact (coefficient_outside P D H W q hq).symm)

end LeanCanny.Algebra.IntegralMixedFramedBankCoordinateBits
