/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalBankTermSource

/-! # Scalar suffix polynomials tested on one complete physical tuple

The original suffix offset is applied before the native scalar-column
injection. The old sampler supplies only the source type and its dimension;
no old sampler access, vertex, root or evaluation is required.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSuffixTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedPhysicalIndex (nativeScalarColumn)
open IntegralFramedPhysicalBankTerm (input)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralFramedPhysicalBankTerm.index
variable (B : Bank) (T : IntegralMixedHeaderTablesBits.Tables)
  (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
  (R : SquareSampleCompleteSuffixPolynomialTest.Source (IntegralFramedBankQuery.input B))

theorem scalar_count (c : List Bool) : (IntegralFramedBankQuery.input B).count c=
    (IntegralMixedFramedHistoryFamilyBits.commands B.parameters B.plan (B.key c)).length :=rfl

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

noncomputable def columns (c d : List Bool) : Fin (R.arity c d)→Fin ((input B).count c) :=
  fun i=>nativeScalarColumn B.parameters B.plan B.data T hr (B.key c)
    (Fin.cast ((R.dimension c d).trans (scalar_count B c)) (FixedWidthSuffixLiftBits.shift (R.newer c d) i))

theorem columns_injective (c d : List Bool) : Function.Injective (columns B T hr R c d) :=by
  apply (IntegralMixedFramedPhysicalIndex.nativeScalarColumn_injective B.parameters B.plan B.data T hr (B.key c)).comp
  exact (Fin.cast_injective _).comp (FixedWidthSuffixLiftBits.shift_injective _ _)

def shifted (q : List Bool) :=pair (pairFst q)
  (BinaryNatCode.encode (R.newer (pairFst (pairFst q)) (pairSnd (pairFst q))+Nat.fromBitsLE (pairSnd q)))
def index (q : List Bool) :=IntegralFramedPhysicalBankTerm.index B T (shifted B R q)

attribute [local irreducible] shifted index

theorem shifted_FP (hR : R.Access) : shifted B R∈FP :=by
  unfold shifted
  have HN : UnaryFn (fun q=>R.newer (pairFst (pairFst q)) (pairSnd (pairFst q))) :=
    hR.newer.comp pairFst_mem_FP
  exact mem_FP_pair pairFst_mem_FP ((BinaryFn.ofUnary HN).add (BinaryFn.fromBits pairSnd_mem_FP)).bits_mem_FP

theorem index_FP (h : IntegralFramedBankQuery.Access B) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hR : R.Access) : index B T R∈FP :=by
  unfold index
  exact mem_FP_comp (shifted_FP B R hR) (IntegralFramedPhysicalBankTerm.index_FP B T h ht)

theorem index_columns (z : List Bool) (i : Fin (R.arity (pairFst z) (pairSnd z))) :
    index B T R (pair z (BinaryNatCode.encode i.val))=
      BinaryNatCode.encode (columns B T hr R (pairFst z) (pairSnd z) i).val :=by
  simp only [index,shifted,IntegralFramedPhysicalBankTerm.index,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,columns,nativeScalarColumn,Fin.val_cast,FixedWidthSuffixLiftBits.shift]

theorem arity_unary (h : IntegralFramedBankQuery.Access B) (hR : R.Access) :
    UnaryFn (fun z=>R.arity (pairFst z) (pairSnd z)) :=by
  have HC : UnaryFn (fun z=>(IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data
      (B.key (pairFst z))).count) :=
    (IntegralMixedFramedBankSnapshotBits.count_unary B.parameters h.parameters B.plan B.data).comp
      (mem_FP_comp pairFst_mem_FP h.key)
  exact (HC.sub hR.newer).of_eq (fun z=>by
    have HE:=R.dimension (pairFst z) (pairSnd z)
    change R.newer (pairFst z) (pairSnd z)+R.arity (pairFst z) (pairSnd z)=
      (IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key (pairFst z))).count at HE
    omega)

noncomputable def test :=SquareSampleCompleteSuffixPolynomialTest.test
  (SquareSampleCompleteEmbeddedPolynomialTest.source (input B) R (columns B T hr R))
noncomputable def value :=SquareSampleCompleteIndexedPolynomialTest.value (input B) (test B T hr R)

theorem evaluator (h : IntegralFramedBankQuery.Access B) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hR : R.Access) (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input B))) :
    SpaceFunction (value B T hr R) :=by
  have HA:=IntegralFramedPhysicalSquare.access B.parameters h.parameters B.plan B.data T ht hr
    B.nodes B.factor B.seed B.bounds h.nodes h.factor h.seed B.key h.key B.positive ER
  exact SquareSampleCompleteEmbeddedPolynomialTest.evaluator (input B) R (columns B T hr R)
    (index B T R) (index_columns B T hr R) (columns_injective B T hr R) HA hR
    (arity_unary B R h hR) (index_FP B T R h ht hR)

theorem packet (c w d : List Bool) (hv : SquareSampleCompleteVertices.Valid (input B) c w) :
    value B T hr R (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign ((R.polynomial c d).eval₂ (Int.castRingHom ℝ)
        (fun i=>(SquareSampleCompleteVertices.candidate (input B) c w hv).val (columns B T hr R c d i)))) :=
  SquareSampleCompleteEmbeddedPolynomialTest.packet (input B) R (columns B T hr R) c w d hv

end LeanCanny.Encoding.IntegralFramedPhysicalSuffixTest
