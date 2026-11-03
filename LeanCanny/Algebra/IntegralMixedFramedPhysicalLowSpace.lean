/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeSpace
public import LeanCanny.Algebra.IntegralMixedOriginalSpatialLeaves
public import LeanCanny.Algebra.FixedWidthBoxRepackSpace
/-! # Original physical LOW coefficients at arbitrary exponent-query widths

The source remains at the literal saved task. The existing charged original
integer coefficient leaf is repacked after a proved degree-box guard; neither
an expanded source term nor an interpreted matrix reader is supplied.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalLowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedPhysicalBits.family

noncomputable abbrev family (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedPhysicalTaskBits.family P (IntegralMixedFramedPhysicalBits.family P D J)
noncomputable abbrev indices (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedPhysicalTaskBits.indices P (IntegralMixedFramedPhysicalBits.family P D J)
noncomputable def arity (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  (family P D J).ambient q+1
noncomputable def width (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  ((family P D J).spatial q).degree.size
noncomputable def low (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : MvPolynomial (Fin (arity P D J q)) ℤ :=
  ((family P D J).spatial q).low

def modulusWord (P : Parameters) (q : List Bool) := BinaryNatCode.encode (modulus P q-1)
theorem modulusWord_FP (P : Parameters) (a : Access P) : modulusWord P∈FP :=
  ((modulus_binary P a).sub (BinaryFn.const 1)).bits_mem_FP

theorem modulusWord_value (P : Parameters) (q : List Bool) : Nat.fromBitsLE (modulusWord P q)+1=modulus P q := by
  simp only [modulusWord,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have H:=modulus_ne_zero P q
  omega

theorem metadata (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) :
    IntegralMixedPhysicalCriticalBits.Metadata (family P D J) (indices P D J) :=
  IntegralMixedPhysicalTaskBits.metadata P a _ (IntegralMixedFramedPhysicalBits.inputMetadata P a D J
    c.critical.tables c.critical.native c.critical.represents)

theorem fixed_evaluator_family (F : IntegralMixedPhysicalCriticalBits.Family)
    (I : IntegralMixedPhysicalCriticalBits.Indices F) (hI : ∀q,I.modulus q≠0)
    (original : SpaceFunction (IntegralMixedPhysicalOriginalBits.scalar F I))
    (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>F.ambient q+1) (fun q=>(F.spatial q).degree.size)
      (fun q=>(F.spatial q).low) target (fun q=>BinaryNatCode.encode (I.modulus q-1))) := by
  have E:=original.precompose (fun q=>pair q (target q)) (mem_FP_pair id_mem_FP ht)
  apply E.congr
  funext q
  simp only [Function.comp_apply]
  have HP : IntegralMixedPhysicalOriginalBits.scalar F I (pair q (target q))=
      residueBits (((F.spatial q).low.coeff (RationalSubstitution.Indexed.exponentVector (F.ambient q+1)
        (FixedWidthPolynomial.entry (F.spatial q).degree.size (Nat.fromBitsLE (target q))))) : ZMod (I.modulus q)) := by
    generalize HPAIR : pair q (target q)=p
    have HB : pairFst p=q := by rw [←HPAIR,pairFst_pair]
    have HT : pairSnd p=target q := by rw [←HPAIR,pairSnd_pair]
    subst q
    unfold IntegralMixedPhysicalOriginalBits.scalar
    rw [HT,IntegralMixedOriginalSpatialTermBits.physical_coefficient]
  have HC : RationalSubstitution.Indexed.exponentVector (F.ambient q+1)
      (FixedWidthPolynomial.entry (F.spatial q).degree.size (Nat.fromBitsLE (target q)))=
      nativeExponent (Equiv.refl (Fin (F.ambient q+1))) (F.spatial q).degree.size (Nat.fromBitsLE (target q)) := by
    rw [nativeExponent_refl]
  have HM : I.modulus q=Nat.fromBitsLE (BinaryNatCode.encode (I.modulus q-1))+1 := by
    simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have H:=hI q
    omega
  exact HP.trans (congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m))
    (congrArg (F.spatial q).low.coeff HC) HM)

theorem fixed_task_evaluator (P : Parameters) (F : IntegralMixedPhysicalCriticalBits.Family)
    (original : SpaceFunction (IntegralMixedPhysicalNativeLowerBits.originalScalar P F))
    (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>(IntegralMixedPhysicalTaskBits.family P F).ambient q+1)
      (fun q=>((IntegralMixedPhysicalTaskBits.family P F).spatial q).degree.size)
      (fun q=>((IntegralMixedPhysicalTaskBits.family P F).spatial q).low) target (modulusWord P)) := by
  unfold IntegralMixedPhysicalNativeLowerBits.originalScalar at original
  have E:=fixed_evaluator_family (IntegralMixedPhysicalTaskBits.family P F) (IntegralMixedPhysicalTaskBits.indices P F)
    (IntegralMixedPhysicalTaskBits.indices P F).modulus_ne_zero original target ht
  have HM : (fun q=>BinaryNatCode.encode ((IntegralMixedPhysicalTaskBits.indices P F).modulus q-1))=modulusWord P := rfl
  rw [HM] at E
  exact E

theorem fixed_evaluator (P : Parameters) (_a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (arity P D J) (width P D J) (low P D J) target (modulusWord P)) := by
  unfold arity width low modulusWord
  exact fixed_task_evaluator P (IntegralMixedFramedPhysicalBits.family P D J) c.critical.physicalOriginal target ht

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (arity P D J) V (low P D J) target (modulusWord P)) := by
  have HM:=metadata P a D J c
  have HA:UnaryFn (arity P D J):=HM.ambient.add (UnaryFn.const 1)
  have HW:UnaryFn (width P D J):=IntegralMixedPhysicalCriticalBits.sourceWidth_unary _ _ HM
  have HP : ∀q e,e∈(low P D J q).support→∀i,e i<2^width P D J q := by
    intro q e he i
    exact ((MvPolynomial.monomial_le_degreeOf i he).trans (MvPolynomial.degreeOf_le_totalDegree _ i)).trans_lt
      (((family P D J).spatial q).low_degree.trans (Nat.lt_size_self _))
  exact FixedWidthBoxRepackBits.evaluator (arity P D J) (width P D J) V (low P D J) HP target (modulusWord P)
    HA HW hV ht (fixed_evaluator P a D J c _ (FixedWidthQuery.repack_mem_FP HA hV HA HW ht))

end LeanCanny.Algebra.IntegralMixedFramedPhysicalLowBits
