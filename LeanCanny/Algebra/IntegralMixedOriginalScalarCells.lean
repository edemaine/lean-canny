/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOriginalRuleBody
/-! # Original leading and scale primitives are syntax reads -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOriginalRuleBodyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem get_ofFn {n : ℕ} (f : Fin n → List Bool) (i : ℕ) (hi : i < n) :
    WordList.get (WordList.encode (List.ofFn f)) i = f ⟨i, hi⟩ := by
  rw [WordList.get_encode, List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hi), Option.getD_some, List.getElem_ofFn]

def arity (P : Parameters) (q : List Bool) := P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1

theorem arity_unary (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) : UnaryFn (arity P) :=
  (a.ambient.comp (mem_FP_comp (IntegralMixedVirtualTaskBits.saved_FP P a) pairFst_mem_FP)).add (UnaryFn.const 1)

def leadingCode (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (q : List Bool) :=
  field h.writer 0 (IntegralMixedVirtualTaskBits.saved P q)

theorem leadingCode_FP (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) :
    leadingCode P D h ∈ FP := mem_FP_comp (IntegralMixedVirtualTaskBits.saved_FP P a) (field_FP _ h.writer_FP 0)

theorem leadingCode_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (q : List Bool) :
    leadingCode P D h q = SignStatisticBits.integerCode (D.spatial (RankedHistoryTask.root q)).leading := by
  rw [leadingCode, leading_field, IntegralMixedFullHistoryFamilyBits.saved_root]

def scaleCode (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (physical : Bool) (z : List Bool) :=
  if Nat.fromBitsLE (pairSnd z) < arity P (pairFst z) then
    WordList.get (field h.writer (if physical then 2 else 4) (IntegralMixedVirtualTaskBits.saved P (pairFst z))) (Nat.fromBitsLE (pairSnd z))
  else SignStatisticBits.integerCode 1

theorem scaleCode_FP (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (physical : Bool) :
    scaleCode P D h physical ∈ FP := by
  have HQ := mem_FP_comp pairFst_mem_FP (IntegralMixedVirtualTaskBits.saved_FP P a)
  have HI := BinaryFn.fromBits pairSnd_mem_FP
  have HF : (fun z => field h.writer (if physical then 2 else 4) (IntegralMixedVirtualTaskBits.saved P (pairFst z))) ∈ FP :=
    mem_FP_comp (f := fun z => IntegralMixedVirtualTaskBits.saved P (pairFst z)) (g := field h.writer (if physical then 2 else 4)) HQ (field_FP _ h.writer_FP _)
  exact (HI.lt ((BinaryFn.ofUnary (arity_unary P a)).comp pairFst_mem_FP)).ite_mem_FP
    (IntegralMixedCommandHeaderBits.fetched_FP _ _ HF HI) (constFn_mem_FP _)

theorem physical_scaleCode (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (z : List Bool) :
    scaleCode P D h true z = SignStatisticBits.integerCode
      (IntegralMixedPhysicalDenominatorPostBits.scale P (IntegralMixedHeightCellsBits.physicalFamily P D) (pairFst z) (Nat.fromBitsLE (pairSnd z))) := by
  change (if Nat.fromBitsLE (pairSnd z) < arity P (pairFst z) then _ else _) =
    SignStatisticBits.integerCode (if hi : Nat.fromBitsLE (pairSnd z) < arity P (pairFst z) then
      (physicalRule P D (IntegralMixedVirtualTaskBits.saved P (pairFst z))).scales ⟨_, hi⟩ else 1)
  by_cases hi : Nat.fromBitsLE (pairSnd z) < arity P (pairFst z)
  · rw [ite_eq_left hi, dite_eq_left hi]
    simp only [ite_true]
    rw [physical_scales]
    exact get_ofFn _ _ hi
  · rw [ite_eq_right hi, dite_eq_right hi]

theorem virtual_scaleCode (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (z : List Bool) :
    scaleCode P D h false z = SignStatisticBits.integerCode
      (IntegralMixedVirtualDenominatorPostBits.scale P (IntegralMixedFullHistoryFamilyBits.family P D) (pairFst z) (Nat.fromBitsLE (pairSnd z))) := by
  change (if Nat.fromBitsLE (pairSnd z) < arity P (pairFst z) then _ else _) =
    SignStatisticBits.integerCode (if hi : Nat.fromBitsLE (pairSnd z) < arity P (pairFst z) then
      (virtualRule P D (IntegralMixedVirtualTaskBits.saved P (pairFst z))).critical.scales ⟨_, hi⟩ else 1)
  by_cases hi : Nat.fromBitsLE (pairSnd z) < arity P (pairFst z)
  · rw [ite_eq_left hi, dite_eq_left hi]
    simp only [Bool.false_eq_true, ite_false]
    rw [virtual_scales]
    exact get_ofFn _ _ hi
  · rw [ite_eq_right hi, dite_eq_right hi]

theorem residue_space {f : List Bool → ℤ} (word : List Bool → List Bool) (hw : word ∈ FP) (he : ∀ q, word q = SignStatisticBits.integerCode (f q))
    (M : List Bool → ℕ) (hM : BinaryFn M) (hpos : ∀ q, 0 < M q) :
    SpaceFunction (fun q => residueBits (f q : ZMod (M q))) := by
  have E : SpaceFunction (fun q => SignStatisticBits.integerCode (f q)) := (SpaceFunction.ofFP word hw).congr (funext he)
  have H := SignedIntegerResidue.evaluator E ((hM.sub (BinaryFn.const 1)).bits_mem_FP)
  exact H.congr (funext fun q => congrArg (fun m => residueBits (f q : ZMod m)) (by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (hpos q)]))

theorem leading_primitive (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) :
    IntegralMixedFullScalarLeadingBits.Primitive P D :=
  residue_space (leadingCode P D h) (leadingCode_FP P a D h) (leadingCode_eq P D h)
    (modulus P) (modulus_binary P a) (fun q => Nat.pos_of_ne_zero (modulus_ne_zero P q))

theorem physical_scales_primitive (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) :
    IntegralMixedPhysicalNativeDenominatorBits.Primitive P (IntegralMixedHeightCellsBits.physicalFamily P D) :=
  residue_space (scaleCode P D h true) (scaleCode_FP P a D h true) (physical_scaleCode P D h)
    (fun z => modulus P (pairFst z)) ((modulus_binary P a).comp pairFst_mem_FP) (fun z => Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z)))

theorem virtual_scales_primitive (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) :
    IntegralMixedVirtualContextDenominatorBits.Primitive P (IntegralMixedFullHistoryFamilyBits.family P D) :=
  residue_space (scaleCode P D h false) (scaleCode_FP P a D h false) (virtual_scaleCode P D h)
    (fun z => modulus P (pairFst z)) ((modulus_binary P a).comp pairFst_mem_FP) (fun z => Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z)))
end LeanCanny.Algebra.IntegralMixedOriginalRuleBodyBits
