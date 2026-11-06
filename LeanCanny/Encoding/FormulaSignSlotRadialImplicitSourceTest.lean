/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleIndexedSourceTest
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumSampler
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # Charged integer source tests on the stratum sampler's unchanged tuple

The additional reciprocal witness is final, so every original column retains
its literal number. The native evaluator uses the Source's modular reader.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitSourceTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity MvPolynomial
open IntegralFramedBankPolynomialModel (Source Access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
variable (G : Source) (read : List Bool → List Bool)
  (hdim : ∀ z, G.arity (read z)+1=(F).count (pairFst z))
  (hfit : ∀ z, G.degree z<2^G.width z)
noncomputable def dimension (z : List Bool) := (F).count (pairFst z)
theorem dimension_unary : UnaryFn dimension :=
  (ImplicitSourceGramGrid.access FormulaSignSlotRadialJointStratum.source
    FormulaSignSlotRadialJointStratumNative.access FormulaSignSlotRadialJointStratumSampler.positive).count.comp pairFst_mem_FP

attribute [local irreducible] ImplicitSourceGramGrid.input FormulaSignSlotRadialJointStratum.source
noncomputable def embedding (z : List Bool) : Fin (G.arity (read z))→Fin (dimension z) :=
  fun i=>⟨i.val,by change i.val<(F).count (pairFst z);have H:=hdim z;have HI:=i.isLt;omega⟩
theorem injective (z : List Bool) : Function.Injective (embedding G read hdim z) := by
  intro i j H
  have HE : (embedding G read hdim z i).val=(embedding G read hdim z j).val :=congrArg (fun x : Fin (dimension z)=>x.val) H
  exact Fin.ext HE
def columnCode (q : List Bool) := BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q))
theorem columnCode_FP : columnCode∈FP := (BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP
theorem columnCode_packet (z : List Bool) (i : Fin (G.arity (read z))) :
    columnCode (pair z (BinaryNatCode.encode i.val))=BinaryNatCode.encode (embedding G read hdim z i).val := by
  simp only [columnCode,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,embedding]

noncomputable def source : Source := IntegralFramedBankPolynomialEmbedding.source G read dimension
  (embedding G read hdim) (fun z=>hfit (read z))
noncomputable def access (hr : read∈FP) (A : Access G) : Access (source G read hdim hfit) :=
  IntegralFramedBankPolynomialEmbedding.access G read dimension (embedding G read hdim)
    (fun z=>hfit (read z)) A hr dimension_unary (injective G read hdim)
    columnCode columnCode_FP (columnCode_packet G read hdim)
theorem source_count (c d : List Bool) : (source G read hdim hfit).arity (id (pair c d))=(F).count c := by
  simp only [source,IntegralFramedBankPolynomialEmbedding.source,dimension,id_eq,pairFst_pair]
noncomputable def test := SquareSampleIndexedSourceTest.test F (source G read hdim hfit) id (source_count G read hdim hfit)
noncomputable def value := SquareSampleIndexedSourceTest.value F (source G read hdim hfit) id (source_count G read hdim hfit)
theorem evaluator (hr : read∈FP) (A : Access G) : SpaceFunction (value G read hdim hfit) :=
  SquareSampleIndexedSourceTest.evaluator F (source G read hdim hfit) id id_mem_FP (source_count G read hdim hfit)
    (ImplicitSourceGramGrid.access FormulaSignSlotRadialJointStratum.source
      FormulaSignSlotRadialJointStratumNative.access FormulaSignSlotRadialJointStratumSampler.positive)
    (access G read hdim hfit hr A)
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
    ((source G read hdim hfit).polynomial (pair c d)).eval₂ (Int.castRingHom ℝ)
        (fun i=>p (Fin.cast (source_count G read hdim hfit c d) i))=
      (G.polynomial (read (pair c d))).eval₂ (Int.castRingHom ℝ)
        (fun i=>IntegralMixedFramedBankObservation.extend p i.val) := by
  unfold source
  exact embedding_evaluation (source_count G read hdim hfit c d) (G.polynomial (read (pair c d)))
    (embedding G read hdim (pair c d)) p (fun _=>rfl)

/-- Exact sign of the requested polynomial on the SAME own word. -/
theorem packet (c w d : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    value G read hdim hfit (pair (pair c w) d)=InfinitesimalSign.encode (SignType.sign
      ((G.polynomial (read (pair c d))).eval₂ (Int.castRingHom ℝ) (fun i=>env c w hw i.val))) := by
  rw [value,SquareSampleIndexedSourceTest.packet F (source G read hdim hfit) id (source_count G read hdim hfit) c w d hw]
  simpa only [id_eq,env] using congrArg (fun r :ℝ=>InfinitesimalSign.encode (SignType.sign r))
    (evaluation G read hdim hfit c d (SquareSampleCompleteVertices.candidate F c w hw).val)
noncomputable def language : Language :=
  SquareSampleCompleteIndexedPolynomialTest.language F (test G read hdim hfit) 0
theorem decider (hr : read∈FP) (A : Access G) : SpaceDecider (language G read hdim hfit) :=
  SquareSampleCompleteIndexedPolynomialTest.decider
    (ImplicitSourceGramGrid.access FormulaSignSlotRadialJointStratum.source
      FormulaSignSlotRadialJointStratumNative.access FormulaSignSlotRadialJointStratumSampler.positive)
    (SquareSampleIndexedSourceTest.access F (source G read hdim hfit) id id_mem_FP
      (source_count G read hdim hfit) (access G read hdim hfit hr A)) 0
theorem mem_PSPACE (hr : read∈FP) (A : Access G) : language G read hdim hfit∈PSPACE :=
  (decider G read hdim hfit hr A).mem_PSPACE
theorem language_packet_iff (c w d : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    pair (pair c w) d∈language G read hdim hfit ↔
      (G.polynomial (read (pair c d))).eval₂ (Int.castRingHom ℝ) (fun i=>env c w hw i.val)=0 := by
  simp only [language,SquareSampleCompleteIndexedPolynomialTest.language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair]
  change (SquareSampleCompleteVertices.Valid F c w ∧value G read hdim hfit (pair (pair c w) d)=InfinitesimalSign.encode 0)↔_
  rw [packet G read hdim hfit c w d hw]
  simp only [hw,true_and]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff
end LeanCanny.Encoding.FormulaSignSlotRadialImplicitSourceTest
