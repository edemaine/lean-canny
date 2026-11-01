/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralScalarGeneratorView
public import LeanCanny.Computation.SpaceFunctionChain
/-! # Native processing of an explicitly supplied scalar degree

The selected degree is an input word to these local operations. No FP
certificate for computing an actual polynomial degree is required.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralScalarSpaceDegreeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralScalarGeneratorBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Native (F : Family) : Prop where
  scalarDegree : BinaryFn F.scalarDegree
  modulus : BinaryFn F.modulus
  row : BinaryFn (fun q => (F.row q).val)
  col : BinaryFn (fun q => (F.col q).val)
  oldRow : BinaryFn (fun q => (F.oldRow q).val)
  oldCol : BinaryFn (fun q => (F.oldCol q).val)

def coefficientQueryAt (F : Family) (q : List Bool) (D : ℕ) : List Bool :=
  pair q (pair (BinaryNatCode.encode ((F.row q).val - (F.scalarDegree q - D)))
    (pair (BinaryNatCode.encode (F.oldRow q).val) (BinaryNatCode.encode (F.oldCol q).val)))

def coefficientQuery (F : Family) (p : List Bool) : List Bool :=
  coefficientQueryAt F (pairFst p) (Nat.fromBitsLE (pairSnd p))

theorem coefficientQuery_FP (F : Family) (a : Native F) : coefficientQuery F ∈ FP := by
  have HR : BinaryFn (fun p => (F.row (pairFst p)).val) := a.row.comp pairFst_mem_FP
  have HN : BinaryFn (fun p => F.scalarDegree (pairFst p)) := a.scalarDegree.comp pairFst_mem_FP
  have HBR : BinaryFn (fun p => (F.oldRow (pairFst p)).val) := a.oldRow.comp pairFst_mem_FP
  have HBC : BinaryFn (fun p => (F.oldCol (pairFst p)).val) := a.oldCol.comp pairFst_mem_FP
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair
    (HR.sub (HN.sub (BinaryFn.fromBits pairSnd_mem_FP))).bits_mem_FP (mem_FP_pair HBR.bits_mem_FP HBC.bits_mem_FP))

def original (z : List Bool) := pairFst (pairFst (pairFst z))
def degreeWord (z : List Bool) := pairSnd (pairFst (pairFst z))
def coefficientWord (z : List Bool) := pairSnd (pairFst z)
def leadingWord (z : List Bool) := pairSnd z

theorem original_FP : original ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
theorem degreeWord_FP : degreeWord ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
theorem coefficientWord_FP : coefficientWord ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem leadingWord_FP : leadingWord ∈ FP := pairSnd_mem_FP

noncomputable def finishAt (F : Family) (q : List Bool) (D : ℕ) (coefficient leading : List Bool) : List Bool :=
  viewValue (F.modulus q) (F.scalarDegree q) D (F.row q).val (F.col q).val (F.oldRow q).val (F.oldCol q).val
    (Nat.fromBitsLE leading : ZMod (F.modulus q)) coefficient

noncomputable def finish (F : Family) (z : List Bool) : List Bool :=
  finishAt F (original z) (Nat.fromBitsLE (degreeWord z)) (coefficientWord z) (leadingWord z)

attribute [local irreducible] ArithmeticBits.negate

theorem finish_FP (F : Family) (a : Native F) : finish F ∈ FP := by
  have HM : BinaryFn (fun z => F.modulus (original z)) := a.modulus.comp original_FP
  have HN : BinaryFn (fun z => F.scalarDegree (original z)) := a.scalarDegree.comp original_FP
  have HR : BinaryFn (fun z => (F.row (original z)).val) := a.row.comp original_FP
  have HC : BinaryFn (fun z => (F.col (original z)).val) := a.col.comp original_FP
  have HBR : BinaryFn (fun z => (F.oldRow (original z)).val) := a.oldRow.comp original_FP
  have HBC : BinaryFn (fun z => (F.oldCol (original z)).val) := a.oldCol.comp original_FP
  have HD := BinaryFn.fromBits degreeWord_FP
  have HE := (HD.sub (BinaryFn.const 1)).sub (HR.sub (HN.sub HD))
  have HL := ModularScalarFP.natCast HM (fun z => Nat.fromBitsLE (leadingWord z)) (BinaryFn.fromBits leadingWord_FP)
  have HP := ModularScalarFP.pow HM (fun z => F.modulus_ne_zero (original z)) _ HE _ HL
  have HX := ModularScalarFP.natCast HM (fun z => Nat.fromBitsLE (coefficientWord z)) (BinaryFn.fromBits coefficientWord_FP)
  have HY := ModularScalarFP.mul HM _ _ HX HP
  have HNEG := mem_FP_comp (mem_FP_pair HM.bits_mem_FP HY) ArithmeticBits.negate_mem_FP
  have HF : (fun z => residueBits (-((Nat.fromBitsLE (coefficientWord z) : ZMod (F.modulus (original z))) *
      (Nat.fromBitsLE (leadingWord z) : ZMod (F.modulus (original z))) ^
        (Nat.fromBitsLE (degreeWord z) - 1 - ((F.row (original z)).val - (F.scalarDegree (original z) - Nat.fromBitsLE (degreeWord z))))))) ∈ FP :=
    mem_FP_of_eq HNEG (fun z => by
      let : NeZero (F.modulus (original z)) := ⟨F.modulus_ne_zero _⟩
      exact ArithmeticBits.negate_residueBits _ _)
  have HO := ModularScalarFP.natCast HM (fun _ => 1) (BinaryFn.const 1)
  have HZ : (fun z => residueBits (0 : ZMod (F.modulus (original z)))) ∈ FP :=
    mem_FP_of_eq (constFn_mem_FP []) (fun z => ArithmeticBits.zero_residueBits _)
  have HSHIFT := ((HC.add (BinaryFn.const 1)).lt HN).and ((HR.eq (HC.add (BinaryFn.const 1))).and (HBR.eq HBC))
  have HI := HSHIFT.ite_mem_FP HO HZ
  have HREQ := (((HC.add (BinaryFn.const 1)).lt HN).not).and ((HD.le HN).and ((HN.sub HD).le HR))
  refine mem_FP_of_eq (HREQ.ite_mem_FP HF HI) (fun z => ?_)
  unfold finish finishAt viewValue
  split_ifs <;> simp only [Nat.cast_one]
end LeanCanny.Algebra.IntegralScalarSpaceDegreeBits
