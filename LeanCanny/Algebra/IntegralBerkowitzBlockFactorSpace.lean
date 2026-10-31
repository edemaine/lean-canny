/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBerkowitzBlockMoment

/-! # Native relative Berkowitz factor programs

The ordinary factor selector applies to the outer indices. Its unit case
uses the old basis identity entry. Diagonal and trailing-moment requests
read original multiplication matrices and negate the resulting residue.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBerkowitzBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def dimensionWord (S : Source) (q : List Bool) : List Bool := BinaryNatCode.encode (S.dimension (pairFst q))
theorem dimensionWord_FP (S : Source) (a : Access S) : dimensionWord S ∈ FP := by
  have HD : BinaryFn (fun q => S.dimension (pairFst q)) := a.dimension.comp pairFst_mem_FP
  exact HD.bits_mem_FP

def selector (S : Source) : List Bool → List Bool := Berkowitz.QueryBits.selector (dimensionWord S)
theorem selector_FP (S : Source) (a : Access S) : selector S ∈ FP :=
  Berkowitz.QueryBits.selector_mem_FP (dimensionWord_FP S a)

theorem selector_eq (S : Source) (p : List Bool) : selector S p =
    Berkowitz.QueryBits.select (S.dimension (original p)) (stage S p) (targetStage S p)
      (sourceDegree S p) (targetDegree S p) := by
  rw [selector, Berkowitz.QueryBits.selector_eq_select]
  simp only [Berkowitz.QueryBits.inputDimension, dimensionWord, original, stage, targetStage,
    sourceDegree, targetDegree, MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
    Berkowitz.QueryBits.rowIndex, Berkowitz.QueryBits.colIndex, BinaryNatCode.encode, Nat.fromBitsLE_bits]

def oneWord (S : Source) (p : List Bool) : List Bool :=
  if (basisIndex S basisRowCode p).val = (basisIndex S basisColCode p).val then
    ArithmeticBits.one (BinaryNatCode.encode (S.modulus (original p))) else []

theorem oneWord_FP (S : Source) (a : Access S) : oneWord S ∈ FP := by
  have HM : BinaryFn (fun p => S.modulus (original p)) := a.modulus.comp original_FP
  have HO : (fun p => ArithmeticBits.one (BinaryNatCode.encode (S.modulus (original p)))) ∈ FP :=
    mem_FP_comp (f := fun p => BinaryNatCode.encode (S.modulus (original p))) (g := ArithmeticBits.one)
      HM.bits_mem_FP ArithmeticBits.one_mem_FP
  exact ((basisIndex_binary S a basisRowCode basisRowCode_FP).eq
    (basisIndex_binary S a basisColCode basisColCode_FP)).ite_mem_FP HO (constFn_mem_FP [])

def negative (S : Source) (z : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (BinaryNatCode.encode (S.modulus (original (pairFst z)))) (pairSnd z))

attribute [local irreducible] ArithmeticBits.negate

theorem negative_FP (S : Source) (a : Access S) : negative S ∈ FP := by
  have HQ : (fun z => original (pairFst z)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := original) pairFst_mem_FP original_FP
  have HM : BinaryFn (fun z => S.modulus (original (pairFst z))) := a.modulus.comp HQ
  have H := mem_FP_comp (f := fun z => pair (BinaryNatCode.encode (S.modulus (original (pairFst z)))) (pairSnd z))
    (g := ArithmeticBits.negate) (mem_FP_pair HM.bits_mem_FP pairSnd_mem_FP) ArithmeticBits.negate_mem_FP
  exact mem_FP_of_eq (g := negative S) H (fun _ => rfl)

def diagonalQuery (S : Source) (p : List Bool) : List Bool :=
  pair (IntegralBlockMomentBits.context (original p) (basisIndex S basisRowCode p).val (basisIndex S basisColCode p).val)
    (pair (BinaryNatCode.encode (stage S p)) (BinaryNatCode.encode (stage S p)))

theorem diagonalQuery_FP (S : Source) (a : Access S) : diagonalQuery S ∈ FP :=
  mem_FP_pair (mem_FP_pair original_FP (mem_FP_pair
    (basisIndex_binary S a basisRowCode basisRowCode_FP).bits_mem_FP
    (basisIndex_binary S a basisColCode basisColCode_FP).bits_mem_FP))
    (mem_FP_pair (stage_binary S a).bits_mem_FP (stage_binary S a).bits_mem_FP)

def mode (S : Source) (tag p : List Bool) : Bool := decide (selector S p = tag)
theorem mode_FP (S : Source) (a : Access S) (tag : List Bool) : (fun p => [mode S tag p]) ∈ FP :=
  (stringEq_fppred (selector_FP S a) (constFn_mem_FP tag)).flag_mem_FP

noncomputable def factorValue (S : Source) (a : Access S) (p : List Bool) : List Bool :=
  if selector S p = [true] then oneWord S p
  else if selector S p = [false, true] then negative S (pair p (a.entry (diagonalQuery S p)))
  else if selector S p = [true, true] then negative S (pair p ((momentFamily S).value p))
  else []

attribute [local irreducible] oneWord negative IntegralBlockMomentBits.Family.value

theorem factor_evaluator (S : Source) (a : Access S) (E : SpaceFunction a.entry) : SpaceFunction (factorValue S a) := by
  have ED := ((E.precompose (diagonalQuery S) (diagonalQuery_FP S a)).withInput).postcompose
    (negative S) (negative_FP S a)
  have EM := ((moment_evaluator S a E).withInput).postcompose (negative S) (negative_FP S a)
  have EZ := SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])
  have EO := SpaceFunction.ofFP (oneWord S) (oneWord_FP S a)
  have RM := SpaceFunction.branch (mode S [true, true]) (mode_FP S a _) EM EZ
  have RD := SpaceFunction.branch (mode S [false, true]) (mode_FP S a _) ED RM
  have R := SpaceFunction.branch (mode S [true]) (mode_FP S a _) EO RD
  refine R.congr (funext fun p => ?_)
  simp only [factorValue, mode, Function.comp_apply, decide_eq_true_eq]

end LeanCanny.Algebra.IntegralBerkowitzBlockBits
