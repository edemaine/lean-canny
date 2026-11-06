/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleIndexedSourceTest
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumSampler
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGridCatalogueNative
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # Actual radial grid features on the implicit stratum's own tuple

The reciprocal-square witness is an extra FINAL coordinate. Every original
joint coordinate retains its literal number, and the sample word is unchanged.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitGridTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity MvPolynomial
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
local notation "G" => FormulaSignSlotRadialJointGridSource.source

def header (c : List Bool) := FormulaSignSlotRadialJointStratum.header (ImplicitSourceGramGrid.header c)
def read (z : List Bool) :=pair (header (pairFst z)) (pairSnd z)
noncomputable def dimension (z : List Bool) := (F).count (pairFst z)
theorem header_FP : header∈FP := by polytime [header,FormulaSignSlotRadialJointStratum.header,ImplicitSourceGramGrid.header]
theorem read_FP : read∈FP := mem_FP_pair (mem_FP_comp (f:=pairFst) (g:=header) pairFst_mem_FP header_FP) pairSnd_mem_FP
theorem dimension_unary : UnaryFn dimension :=
  (ImplicitSourceGramGrid.access FormulaSignSlotRadialJointStratum.source
    FormulaSignSlotRadialJointStratumNative.access FormulaSignSlotRadialJointStratumSampler.positive).count.comp pairFst_mem_FP

theorem source_dimension (z : List Bool) : (G).arity (read z)+1=dimension z := by
  change FormulaSignSlotRadialJointLayout.dimension (FormulaSignSlotRadialJointGridLayout.header (read z))+1=
    FormulaSignSlotRadialJointLayout.dimension (header (pairFst z))+1
  simp only [FormulaSignSlotRadialJointGridLayout.header,read,pairFst_pair]
theorem degree_fit (z :List Bool) : (G).degree z<2^(G).width z :=
  FormulaSignSlotRadialJointGridSource.degree_fit z

attribute [local irreducible] FormulaSignSlotRadialJointGridSource.source
  ImplicitSourceGramGrid.input FormulaSignSlotRadialJointStratum.source

noncomputable def embedding (z : List Bool) : Fin ((G).arity (read z))→Fin (dimension z) :=
  fun i=>⟨i.val,by have H:=source_dimension z;have HI:=i.isLt;omega⟩
theorem injective (z : List Bool) : Function.Injective (embedding z) := by
  intro i j H
  have HE : (embedding z i).val=(embedding z j).val :=congrArg (fun x : Fin (dimension z)=>x.val) H
  exact Fin.ext HE
def columnCode (q : List Bool) := BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q))
theorem columnCode_FP : columnCode∈FP := (BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP
theorem columnCode_packet (z : List Bool) (i : Fin ((G).arity (read z))) :
    columnCode (pair z (BinaryNatCode.encode i.val))=BinaryNatCode.encode (embedding z i).val := by
  simp only [columnCode,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,embedding]

noncomputable def source : Source := IntegralFramedBankPolynomialEmbedding.source G read dimension embedding
  (fun z=>degree_fit (read z))
noncomputable def access : IntegralFramedBankPolynomialModel.Access source :=
  IntegralFramedBankPolynomialEmbedding.access G read dimension embedding
    (fun z=>degree_fit (read z))
    FormulaSignSlotRadialJointGridSource.access read_FP dimension_unary injective columnCode columnCode_FP columnCode_packet

theorem source_count (c d : List Bool) : source.arity (id (pair c d))=(F).count c := by
  simp only [source,IntegralFramedBankPolynomialEmbedding.source,dimension,id_eq,pairFst_pair]
noncomputable def test := SquareSampleIndexedSourceTest.test F source id source_count
noncomputable def value := SquareSampleIndexedSourceTest.value F source id source_count

theorem evaluator : SpaceFunction value := SquareSampleIndexedSourceTest.evaluator F source id id_mem_FP source_count
  (ImplicitSourceGramGrid.access FormulaSignSlotRadialJointStratum.source
    FormulaSignSlotRadialJointStratumNative.access FormulaSignSlotRadialJointStratumSampler.positive) access

noncomputable def env (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) : ℕ→ℝ :=
  IntegralMixedFramedBankObservation.extend (SquareSampleCompleteVertices.candidate F c w hw).val

private theorem embedding_evaluation {a b k :ℕ} (hb : b=k)
    (p : MvPolynomial (Fin a) ℤ) (f : Fin a→Fin b) (z : Fin k→ℝ)
    (hf : ∀i,(f i).val=i.val) :
    (rename f p).eval₂ (Int.castRingHom ℝ) (fun i=>z (Fin.cast hb i))=
      p.eval₂ (Int.castRingHom ℝ) (fun i=>IntegralMixedFramedBankObservation.extend z i.val) := by
  rw [MvPolynomial.eval₂_rename]
  apply congrArg (p.eval₂ (Int.castRingHom ℝ))
  funext i
  have HI : i.val<k := (hf i) ▸ (Fin.cast hb (f i)).isLt
  simp only [Function.comp_apply,IntegralMixedFramedBankObservation.extend,dite_eq_left HI]
  exact congrArg z (Fin.ext (hf i))

private theorem evaluation (c d : List Bool) (p : Fin ((F).count c)→ℝ) :
    (source.polynomial (pair c d)).eval₂ (Int.castRingHom ℝ) (fun i=>p (Fin.cast (source_count c d) i))=
      ((G).polynomial (read (pair c d))).eval₂ (Int.castRingHom ℝ)
        (fun i=>IntegralMixedFramedBankObservation.extend p i.val) := by
  unfold source
  exact embedding_evaluation (source_count c d) ((G).polynomial (read (pair c d)))
    (embedding (pair c d)) p (fun _=>rfl)

/-- This native sign reads an actual grid-feature polynomial at the SAME
implicit sampler word, including singular stratum roots. -/
theorem packet (c w d : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    value (pair (pair c w) d)=InfinitesimalSign.encode (SignType.sign
      (((G).polynomial (read (pair c d))).eval₂ (Int.castRingHom ℝ) (fun i=>env c w hw i.val))) := by
  rw [value,SquareSampleIndexedSourceTest.packet F source id source_count c w d hw]
  simpa only [id_eq,env] using
    congrArg (fun r :ℝ=>InfinitesimalSign.encode (SignType.sign r))
      (evaluation c d (SquareSampleCompleteVertices.candidate F c w hw).val)

noncomputable def language : Language := SquareSampleCompleteIndexedPolynomialTest.language F test 0

theorem decider : SpaceDecider language := SquareSampleCompleteIndexedPolynomialTest.decider
  (ImplicitSourceGramGrid.access FormulaSignSlotRadialJointStratum.source
    FormulaSignSlotRadialJointStratumNative.access FormulaSignSlotRadialJointStratumSampler.positive)
  (SquareSampleIndexedSourceTest.access F source id id_mem_FP source_count access) 0
theorem mem_PSPACE : language∈PSPACE := decider.mem_PSPACE

theorem language_packet_iff (c w d : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    pair (pair c w) d∈language ↔
      (((G).polynomial (read (pair c d))).eval₂ (Int.castRingHom ℝ) (fun i=>env c w hw i.val))=0 := by
  simp only [language,SquareSampleCompleteIndexedPolynomialTest.language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair]
  change (SquareSampleCompleteVertices.Valid F c w ∧value (pair (pair c w) d)=InfinitesimalSign.encode 0)↔_
  rw [packet c w d hw]
  simp only [hw,true_and]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitGridTest
