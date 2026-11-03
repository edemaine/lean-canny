/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankTermCurrentQ
public import LeanCanny.Encoding.SquareSampleCompleteEmbeddedPolynomialTest
public import LeanCanny.Encoding.IntegralFramedPhysicalSquareAccess
public import LeanCanny.Algebra.IntegralMixedFramedScalarColumnRows
/-! # Original common-cleared bank terms for a full physical sample

The old square input is only the type index of the coefficient Source.
Neither its access nor a root or vertex is used. The polynomial already
contains the actual scalar powers and denominator clearing; its raw
variables are embedded through the actual injective scalar column map.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalBankTerm
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedPhysicalIndex (nativeScalarColumn)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (B : Bank)
noncomputable abbrev input :=IntegralFramedPhysicalSquare.input B.parameters B.plan B.data
  B.nodes B.factor B.seed B.bounds B.key B.positive

noncomputable def source (word : List Bool→List Bool) :
    SquareSampleCompleteSuffixPolynomialTest.Source (IntegralFramedBankQuery.input B) where
  arity c _:=(IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key c)).count
  newer _ _:=0
  polynomial c _:=IntegralMixedFramedBankTermBits.polynomial B.parameters B.plan B.data word (B.key c)
  degree c _:=IntegralMixedFramedBankTermBits.degree B.parameters B.plan B.data word (B.key c)
  mass c _:=IntegralMixedFramedBankTermBits.mass B.parameters B.plan B.data word B.nodes B.factor B.seed (B.key c)
  dimension _ _:=Nat.zero_add _
  polynomial_degree c _:=IntegralMixedFramedBankTermBits.polynomial_degree B.parameters B.plan B.data word (B.key c)
  polynomial_mass c _:=IntegralMixedFramedBankTermBits.polynomial_mass B.parameters B.plan B.data word B.nodes B.factor B.seed B.bounds (B.key c)

theorem source_access (h : IntegralFramedBankQuery.Access B) (word : List Bool→List Bool) (hw : word∈FP) :
    (source B word).Access where
  newer:=UnaryFn.const 0
  degree:=(IntegralFramedBankTermCurrentQ.test_access B h word hw).degree
  mass:=(IntegralFramedBankTermCurrentQ.test_access B h word hw).mass
  coefficient:=((IntegralMixedFramedCurrentQBankTermBits.coefficient_evaluator B.parameters h.parameters B.plan B.data
    h.liftedData h.controls h.bounds word hw).precompose
      (IntegralFramedBankTermCurrentQ.coefficientQuery B.key) (IntegralFramedBankTermCurrentQ.coefficientQuery_FP h.key)).congr (by
        funext q
        change IntegralMixedFramedBankTermBits.coefficient B.parameters B.plan B.data word
          (IntegralFramedBankTermCurrentQ.coefficientQuery B.key q)=_
        unfold IntegralFramedBankTermCurrentQ.coefficientQuery
        rw [IntegralMixedFramedBankTermBits.coefficient_std,FixedWidthPolynomial.nativeExponent_refl]
        rfl)

theorem source_arity (h : IntegralFramedBankQuery.Access B) (word : List Bool→List Bool) :
    UnaryFn (fun z=>(source B word).arity (pairFst z) (pairSnd z)) :=
  (IntegralMixedFramedBankSnapshotBits.count_unary B.parameters h.parameters B.plan B.data).comp
    (mem_FP_comp pairFst_mem_FP h.key)

variable (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
noncomputable def columns (word : List Bool→List Bool) (c d : List Bool) :
    Fin ((source B word).arity c d)→Fin ((input B).count c) :=
  nativeScalarColumn B.parameters B.plan B.data T hr (B.key c)

theorem columns_injective (word : List Bool→List Bool) (c d : List Bool) :
    Function.Injective (columns B T hr word c d) :=
  IntegralMixedFramedPhysicalIndex.nativeScalarColumn_injective B.parameters B.plan B.data T hr (B.key c)

def index (q : List Bool) :=BinaryNatCode.encode (IntegralMixedFramedPhysicalIndex.scalarColumn B.parameters T
  (pair (B.key (pairFst (pairFst q))) (pairSnd q)))

theorem index_FP (h : IntegralFramedBankQuery.Access B) (ht : IntegralMixedHeaderTablesBits.Access T) : index B T∈FP :=
  by
    have HP : (fun q=>pair (B.key (pairFst (pairFst q))) (pairSnd q))∈FP :=
      mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) h.key) pairSnd_mem_FP
    have HI : UnaryFn (fun q=>IntegralMixedFramedPhysicalIndex.scalarColumn B.parameters T
        (pair (B.key (pairFst (pairFst q))) (pairSnd q))) :=
      (IntegralMixedFramedPhysicalIndex.scalarColumn_unary B.parameters h.parameters T ht).comp HP
    exact (BinaryFn.ofUnary HI).bits_mem_FP

theorem index_columns (word : List Bool→List Bool) (z : List Bool) (i : Fin ((source B word).arity (pairFst z) (pairSnd z))) :
    index B T (pair z (BinaryNatCode.encode i.val))=BinaryNatCode.encode (columns B T hr word (pairFst z) (pairSnd z) i).val :=by
  simp only [index,pairFst_pair,pairSnd_pair,columns,nativeScalarColumn]

noncomputable def test (word : List Bool→List Bool) :=SquareSampleCompleteSuffixPolynomialTest.test
  (SquareSampleCompleteEmbeddedPolynomialTest.source (input B) (source B word) (columns B T hr word))
noncomputable def value (word : List Bool→List Bool) :=SquareSampleCompleteIndexedPolynomialTest.value (input B) (test B T hr word)

attribute [local irreducible] value

theorem evaluator (h : IntegralFramedBankQuery.Access B) (ht : IntegralMixedHeaderTablesBits.Access T)
    (word : List Bool→List Bool) (hw : word∈FP)
    (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input B))) : SpaceFunction (value B T hr word) :=by
  unfold value test
  have HA:=IntegralFramedPhysicalSquare.access B.parameters h.parameters B.plan B.data T ht hr
    B.nodes B.factor B.seed B.bounds h.nodes h.factor h.seed B.key h.key B.positive ER
  exact SquareSampleCompleteEmbeddedPolynomialTest.evaluator (input B) (source B word) (columns B T hr word)
    (index B T) (index_columns B T hr word) (columns_injective B T hr word) HA
    (source_access B h word hw) (source_arity B h word) (index_FP B T h ht)
end LeanCanny.Encoding.IntegralFramedPhysicalBankTerm
