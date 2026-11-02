/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalUnitRecord
public import LeanCanny.Algebra.IntegralMixedCanonicalUnitHeaderFP
public import LeanCanny.Algebra.IntegralMixedValueDeterminantMetadata
/-! # All four causal cut headers are original numeric metadata -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalUnitHeaderBits
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory
open IntegralMixedCausalUnitRecordBits IntegralMixedCausalRecordBits
open IntegralMixedUnitRecordCode (field virtualOffset)
open IntegralMixedCommandHeaderBits (Header Readers)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def free (n : ℕ) (code : List Bool) := n-virtualOffset n code+1
def coordinateDimension (n D : ℕ) (code : List Bool) := PurePowerReductionBounds.dimension (free n code) D
def valueLevel (n D : ℕ) (code : List Bool) := D-1+free n code*(coordinateDimension n D code-1)+1
def valueDimension (n D : ℕ) (code : List Bool) :=
  (free n code+3)*FixedWidthPolynomial.count (free n code+1) (valueLevel n D code).size

def choiceBound (n D : ℕ) (code : List Bool) :=
  if Nat.fromBitsLE (field code 11)%4=1 then coordinateDimension n D code
  else if Nat.fromBitsLE (field code 11)%4=2 then valueDimension n D code+2
  else coordinateDimension n D code+1

def selection (n D : ℕ) (code : List Bool) : Header :=
  ⟨if Nat.fromBitsLE (field code 11)%4=1 then 3 else if Nat.fromBitsLE (field code 11)%4=2 then 4 else 2,
    Nat.fromBitsLE (field code 4)%free n code,virtualOffset n code,
    Nat.fromBitsLE (field code 3)%free n code,
    Nat.fromBitsLE (field code 9)%(IntegralMixedExceptionalBounds.auxiliaryCap (n+1) D+1),
    Nat.fromBitsLE (field code 8)%choiceBound n D code,Nat.fromBitsLE (field code 11)%4+2⟩

def header (n D : ℕ) (code : List Bool) : Header :=
  if IntegralMixedUnitRecordCode.critical code then IntegralMixedCanonicalUnitHeaderBits.physical n code
  else selection n D code

private theorem value_dimension {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ)
    (code : List Bool) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B) :
    IntegralMixedGridValue.dimension S ((cut S hn birth code hcap).rule 1 one_ne_zero)=valueDimension n S.degree code := by
  unfold IntegralMixedGridValue.dimension IntegralMixedGridValue.width RelativeAffineGridValueGram.width
  rw [IntegralMixedValueDeterminantMetadata.level_eq]
  rfl

private noncomputable def cutHeader {n B : ℕ} {S : SpatialSource n} (c : Cut S B) : Header :=
  ⟨match c.tag with | .coordinate | .limitCoordinate => 2 | .squarefree => 3 | .value => 4,
    c.coordinate%(n-c.critical.offset.val+1),c.critical.offset.val,c.critical.objective,c.degree,
    c.choice%(match c.tag with
      | .coordinate | .limitCoordinate => PurePowerReductionBounds.dimension (n-c.critical.offset.val+1) S.degree+1
      | .squarefree => PurePowerReductionBounds.dimension (n-c.critical.offset.val+1) S.degree
      | .value => IntegralMixedGridValue.dimension S (c.rule 1 one_ne_zero)+2),
    match c.tag with | .coordinate => 2 | .squarefree => 3 | .value => 4 | .limitCoordinate => 5⟩

private theorem header_of_cut {n B : ℕ} {S : SpatialSource n} (c : Cut S B) :
    (Template.cut c).header=cutHeader c := by
  cases ht : c.tag <;> simp only [Template.header,Template.command,IntegralMixedCommandHeaderBits.command,
    Cut.kind,ht,cutHeader] <;> rfl

private theorem cut_header_numeric {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ)
    (code : List Bool) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B) :
    cutHeader (cut S hn birth code hcap)=selection n S.degree code := by
  have HT : (cut S hn birth code hcap).tag=tag code := rfl
  have HO : (cut S hn birth code hcap).critical.offset.val=virtualOffset n code := rfl
  have HJ : (cut S hn birth code hcap).coordinate=Nat.fromBitsLE (field code 4) := rfl
  have HI : (cut S hn birth code hcap).choice=Nat.fromBitsLE (field code 8) := rfl
  have HE : (cut S hn birth code hcap).critical.objective=Nat.fromBitsLE (field code 3)%free n code := rfl
  have HD : (cut S hn birth code hcap).degree=Nat.fromBitsLE (field code 9)%(IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree+1) := rfl
  have HV := value_dimension S hn birth code hcap
  simp only [cutHeader,HT,HO,HJ,HI,HE,HD,HV]
  have HB : Nat.fromBitsLE (field code 11)%4<4 := Nat.mod_lt _ (by decide)
  interval_cases htag : Nat.fromBitsLE (field code 11)%4 <;>
    simp only [tag,htag,selection,choiceBound,Nat.reduceEqDiff,ite_true,ite_false] <;> rfl

theorem record_header {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ)
    (code : List Bool) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B) :
    (record S hn birth code hcap).template.header=header n S.degree code := by
  cases hh : IntegralMixedUnitRecordCode.critical code
  · simp only [record,header,hh,Bool.false_eq_true,ite_false,header_of_cut]
    exact cut_header_numeric S hn birth code hcap
  · simp only [record,header,hh,ite_true,Template.header,Template.command,IntegralMixedCommandHeaderBits.command,
      physical,IntegralMixedCanonicalUnitRuleBits.physical,IntegralMixedCanonicalUnitHeaderBits.physical,
      IntegralMixedCanonicalUnitHeaderBits.physicalFree,Nat.mod_mod]

private theorem field_binary {code : List Bool→List Bool} (hc : code∈FP) (i : ℕ) :
    BinaryFn (fun q => Nat.fromBitsLE (field (code q) i)) :=
  BinaryFn.fromBits (mem_FP_comp (f:=code) (g:=fun w => WordList.get w i) hc (IntegralMixedCommandHeaderBits.get_FP i))

theorem choiceBound_binary {n D : List Bool→ℕ} (hn : UnaryFn n) (hD : BinaryFn D)
    {code : List Bool→List Bool} (hc : code∈FP) : BinaryFn (fun q => choiceBound (n q) (D q) (code q)) := by
  have HF := IntegralMixedCanonicalUnitHeaderBits.virtualFree_unary hn code hc
  have HD := PurePowerReductionBounds.dimension_binary HF hD
  have HL := ((hD.sub (BinaryFn.const 1)).add ((BinaryFn.ofUnary HF).mul (HD.sub (BinaryFn.const 1)))).add (BinaryFn.const 1)
  have HW : UnaryFn (fun q => (valueLevel (n q) (D q) (code q)).size) :=
    (UnaryFn.length HL.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  have HC := ((BinaryFn.const 2).powUnary HW).powUnary (HF.add (UnaryFn.const 1))
  have HV := ((BinaryFn.ofUnary HF).add (BinaryFn.const 3)).mul HC
  have HT := (field_binary hc 11).mod (BinaryFn.const 4)
  exact BinaryFn.ite (HT.eq (BinaryFn.const 1)) HD
    (BinaryFn.ite (HT.eq (BinaryFn.const 2)) (HV.add (BinaryFn.const 2)) (HD.add (BinaryFn.const 1)))

theorem selection_readers {n D : List Bool→ℕ} (hn : UnaryFn n) (hD : BinaryFn D)
    {code : List Bool→List Bool} (hc : code∈FP) : Readers (fun q => selection (n q) (D q) (code q)) := by
  have HO := IntegralMixedCanonicalUnitHeaderBits.virtualOffset_binary hn code hc
  have HF := BinaryFn.ofUnary (IntegralMixedCanonicalUnitHeaderBits.virtualFree_unary hn code hc)
  have HT := (field_binary hc 11).mod (BinaryFn.const 4)
  exact ⟨BinaryFn.ite (HT.eq (BinaryFn.const 1)) (BinaryFn.const 3)
      (BinaryFn.ite (HT.eq (BinaryFn.const 2)) (BinaryFn.const 4) (BinaryFn.const 2)),
    (field_binary hc 4).mod HF,HO,(field_binary hc 3).mod HF,
    (field_binary hc 9).mod ((IntegralMixedExceptionalBounds.auxiliaryCap_binary (hn.add (UnaryFn.const 1)) hD).add (BinaryFn.const 1)),
    (field_binary hc 8).mod (choiceBound_binary hn hD hc),HT.add (BinaryFn.const 2)⟩

theorem header_readers {n D : List Bool→ℕ} (hn : UnaryFn n) (hD : BinaryFn D)
    {code : List Bool→List Bool} (hc : code∈FP) : Readers (fun q => header (n q) (D q) (code q)) := by
  have HF := FPPred.getBit (mem_FP_comp hc (IntegralMixedCommandHeaderBits.get_FP 0)) (UnaryFn.const 0)
  exact Readers.choose _ HF (IntegralMixedCanonicalUnitHeaderBits.physical_readers hn code hc) (selection_readers hn hD hc)

theorem header_FP {n D : List Bool→ℕ} (hn : UnaryFn n) (hD : BinaryFn D)
    {code : List Bool→List Bool} (hc : code∈FP) :
    (fun q => IntegralMixedCommandHeaderBits.encode (header (n q) (D q) (code q)))∈FP :=
  (header_readers hn hD hc).writer_FP

end LeanCanny.Algebra.IntegralMixedCausalUnitHeaderBits
