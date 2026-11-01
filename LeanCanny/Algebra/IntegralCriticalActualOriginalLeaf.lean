/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCoefficientLeaves
public import LeanCanny.Algebra.IntegralCriticalFlatActualSources
/-! # Primitive integer command-coefficient reads for the total actual leaf -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualOriginalLeaf
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false

noncomputable def rawInteger (F : Scripts) (r : List Bool) (j k : ℕ) : ℤ :=
  (((F.rules r).reverse[j]?).map (fun command => command.low.coeff
    (RationalSubstitution.Indexed.exponentVector (F.ambient r + 1)
      (FixedWidthPolynomial.entry (F.sourceWidth r) k)))).getD 0

def rawModulus (p : List Bool) : ℕ :=
  let m := Nat.fromBitsLE (pairSnd (pairSnd (pairSnd p)))
  if m = 0 then 1 else m
noncomputable def rawReader (F : Scripts) (p : List Bool) : List Bool :=
  residueBits (rawInteger F (pairFst p) (Nat.fromBitsLE (pairFst (pairSnd p)))
    (Nat.fromBitsLE (pairFst (pairSnd (pairSnd p)))) : ZMod (rawModulus p))

/-- This additional primitive reads only an original integer command coefficient. -/
structure Access (F : Scripts) : Prop where
  coefficient : rawReader F ∈ FP

def packet (F : Scripts) (p : List Bool) : List Bool :=
  pair (root (pairFst p))
    (pair (BinaryNatCode.encode (IntegralCriticalHistoryTask.birth F.toParameters (pairFst p)))
      (pair (BinaryNat.normalize (pairSnd p))
        (BinaryNatCode.encode (IntegralCriticalHistoryTask.modulus F.toParameters (pairFst p)))))

theorem packet_FP (F : Scripts) (a : IntegralCriticalFlatHeightBits.Access F) : packet F ∈ FP := by
  have HB : UnaryFn (fun p => IntegralCriticalHistoryTask.birth F.toParameters (pairFst p)) :=
    (RankedHistoryTask.birth_unary _ (IntegralCriticalHistoryTask.birthCap_unary F.toParameters a.toAccess)).comp pairFst_mem_FP
  have HM : BinaryFn (fun p => IntegralCriticalHistoryTask.modulus F.toParameters (pairFst p)) :=
    (IntegralCriticalHistoryTask.modulus_binary F.toParameters a.toAccess).comp pairFst_mem_FP
  exact mem_FP_pair (mem_FP_comp pairFst_mem_FP RankedHistoryTask.root_FP)
    (mem_FP_pair (BinaryFn.ofUnary HB).bits_mem_FP
      (mem_FP_pair (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)
        HM.bits_mem_FP))

noncomputable def scalar (F : Scripts) : List Bool → List Bool := rawReader F ∘ packet F

theorem scalar_FP (F : Scripts) (a : IntegralCriticalFlatHeightBits.Access F) (n : Access F) : scalar F ∈ FP :=
  mem_FP_comp (packet_FP F a) n.coefficient

theorem scalar_space (F : Scripts) (a : IntegralCriticalFlatHeightBits.Access F) (n : SpaceFunction (rawReader F)) :
    SpaceFunction (scalar F) := n.precompose (packet F) (packet_FP F a)

theorem rawInteger_snapshot (F : Scripts) (q : List Bool) (k : ℕ) :
    rawInteger F (root q) (IntegralCriticalHistoryTask.birth F.toParameters q) k =
      IntegralCriticalOriginalCoefficientBits.coefficient (IntegralCriticalTotalCreatingBits.atFamily F) q k := by
  unfold IntegralCriticalOriginalCoefficientBits.coefficient
  by_cases h : valid F q
  · rw [IntegralCriticalTotalCreatingBits.atFamily_valid F q h]
    change (((IntegralCriticalScriptFP.commandAt (IntegralCriticalFlatClearedHeightBits.metadata F) q
      (IntegralCriticalHistoryTask.birth F.toParameters q)).map _).getD 0) = _
    rw [commandAt_creating F q h]
    rfl
  · have H : (F.rules (root q)).reverse[IntegralCriticalHistoryTask.birth F.toParameters q]? = none := by
      apply List.getElem?_eq_none
      rw [List.length_reverse]
      exact Nat.le_of_not_gt h
    unfold rawInteger
    rw [H]
    rw [IntegralCriticalTotalCreatingBits.atFamily_invalid F q h]
    change 0 = (0 : MvPolynomial (Fin 1) ℤ).coeff _
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily

theorem rawReader_packet (F : Scripts) (r : List Bool) (j k m : ℕ) (hm : m ≠ 0) :
    rawReader F (pair r (pair (BinaryNatCode.encode j) (pair (BinaryNatCode.encode k) (BinaryNatCode.encode m)))) =
      residueBits (rawInteger F r j k : ZMod m) := by
  have HM : rawModulus (pair r (pair (BinaryNatCode.encode j) (pair (BinaryNatCode.encode k) (BinaryNatCode.encode m)))) = m := by
    unfold rawModulus
    simp only [pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact ite_eq_right hm
  unfold rawReader
  rw [HM]
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem scalar_packet (F : Scripts) (q : List Bool) (k : ℕ) :
    scalar F (pair q (BinaryNatCode.encode k)) = residueBits
      (IntegralCriticalOriginalCoefficientBits.coefficient (IntegralCriticalTotalCreatingBits.atFamily F) q k :
        ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q)) := by
  have HN : BinaryNat.normalize (BinaryNatCode.encode k) = BinaryNatCode.encode k := by
    simp only [BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold scalar packet
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, HN]
  rw [rawReader_packet F (root q) (IntegralCriticalHistoryTask.birth F.toParameters q) k
    (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q), rawInteger_snapshot]

end LeanCanny.Algebra.IntegralCriticalActualOriginalLeaf
