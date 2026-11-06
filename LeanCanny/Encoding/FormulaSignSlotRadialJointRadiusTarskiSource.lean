/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiKernelSource
public import LeanCanny.Encoding.FormulaSignSlotRadialJointLayout
public import LeanCanny.Encoding.FormulaSignSlotRadialCoordinatePacket
public import LeanCanny.Encoding.IntegralFramedBankPolynomialEmbedding
/-! # Radius-window principal polynomials on the actual joint columns

Context is pair joint-header [coordinate,tau,eta,degree-minus-one,seed,moment,order,role].
The radial source is rebuilt from the header. The endpoint is joint column 3;
center variables retain columns 4*j. No sampler or stratum is imported.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointRadiusTarskiSource
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialRadiusTarskiKernelSource.source

def header (z :List Bool) :=pairFst z
def slot (i :ℕ) (z :List Bool) :=WordList.reader (pair (pairSnd z) (BinaryNatCode.encode i))
noncomputable def radial (z :List Bool) :=FormulaSignSlotRadialCoordinatePacket.writer
  (pair (FormulaSignSlotRadialJointLayout.source true (header z)) (slot 0 z))
noncomputable def read (z :List Bool) :=pair (slot 7 z) (pair
  (pair (pair (radial z) (pair (slot 1 z) (slot 2 z))) (pair (slot 3 z) (pair (slot 4 z) (slot 5 z))))
  (slot 6 z))

theorem slot_FP (i :ℕ) :slot i∈FP :=mem_FP_comp
  (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP _)) WordList.reader_FP
theorem radial_FP :radial∈FP :=mem_FP_comp
  (mem_FP_pair (mem_FP_comp (f:=header) (g:=FormulaSignSlotRadialJointLayout.source true)
    pairFst_mem_FP (FormulaSignSlotRadialJointLayout.source_FP true)) (slot_FP 0))
  FormulaSignSlotRadialCoordinatePacket.writer_FP
theorem read_FP :read∈FP :=mem_FP_pair (slot_FP 7) (mem_FP_pair
  (mem_FP_pair (mem_FP_pair radial_FP (mem_FP_pair (slot_FP 1) (slot_FP 2)))
    (mem_FP_pair (slot_FP 3) (mem_FP_pair (slot_FP 4) (slot_FP 5)))) (slot_FP 6))
theorem radial_root (z :List Bool) :pairFst (radial z)=FormulaSignSlotRadialJointLayout.source true (header z) :=by
  simp only [radial,FormulaSignSlotRadialCoordinatePacket.writer,pairFst_pair]
theorem arity_eq (z :List Bool) :(S).arity (read z)=FormulaSignSlotRadialJointLayout.centerCount (header z)+1 :=by
  change FormulaSignSlotCenteredRadialGraph.d
    (pairFst (FormulaSignSlotRadialRadiusHeadReader.original
      (FormulaSignSlotRadialRadiusTarskiFamily.original (FormulaSignSlotRadialRadiusTarskiSource.original (FormulaSignSlotRadialRadiusTarskiKernelSource.payload (read z))))) )+1=_
  simp only [FormulaSignSlotRadialRadiusTarskiSource.original,FormulaSignSlotRadialRadiusTarskiFamily.original,
    FormulaSignSlotRadialRadiusHeadReader.original,FormulaSignSlotRadialRadiusTarskiKernelSource.payload,read,pairSnd_pair,pairFst_pair,radial_root]
  rfl
noncomputable def dimension (z :List Bool) :=FormulaSignSlotRadialJointLayout.dimension (header z)
theorem dimension_unary :UnaryFn dimension :=FormulaSignSlotRadialJointLayout.dimension_unary.comp pairFst_mem_FP
def column (i :ℕ) :=if i=0 then FormulaSignSlotRadialJointLayout.boundVariable else 4*(i-1)
theorem column_lt (z :List Bool) (i :Fin ((S).arity (read z))) :column i.val<dimension z :=by
  unfold column
  split_ifs with H
  · exact FormulaSignSlotRadialJointLayout.boundVariable_lt _
  · have HI :i.val<FormulaSignSlotRadialJointLayout.centerCount (header z)+1:=i.isLt.trans_eq (arity_eq z)
    have HF:=FormulaSignSlotRadialJointLayout.formal_le_slots (header z)
    change FormulaSignSlotRadialJointLayout.spatialCount (header z)+
      (FormulaSignSlotRadialJointLayout.centerCount (header z)+1)≤_ at HF
    unfold dimension FormulaSignSlotRadialJointLayout.dimension
    omega
noncomputable def embedding (z :List Bool) :Fin ((S).arity (read z))→Fin (dimension z) :=
  fun i=>⟨column i.val,column_lt z i⟩
theorem injective (z :List Bool) :Function.Injective (embedding z) :=by
  intro i j H
  apply Fin.ext
  have HE:=congrArg (fun x:Fin (dimension z)=>x.val) H
  change column i.val=column j.val at HE
  unfold column FormulaSignSlotRadialJointLayout.boundVariable at HE
  split_ifs at HE <;>omega
def columnCode (q :List Bool) :=BinaryNatCode.encode (column (Nat.fromBitsLE (pairSnd q)))
theorem columnCode_FP :columnCode∈FP :=by
  have HI:BinaryFn (fun q=>Nat.fromBitsLE (pairSnd q)):=BinaryFn.fromBits pairSnd_mem_FP
  exact (BinaryFn.ite (HI.eq (BinaryFn.const 0)) (BinaryFn.const 3)
    ((BinaryFn.const 4).mul (HI.sub (BinaryFn.const 1)))).bits_mem_FP
theorem columnCode_packet (z :List Bool) (i :Fin ((S).arity (read z))) :
    columnCode (pair z (BinaryNatCode.encode i.val))=BinaryNatCode.encode (embedding z i).val :=by
  simp only [columnCode,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,embedding]
attribute [local irreducible] read
theorem degree_fit (z :List Bool) :(S).degree (read z)<2^(S).width (read z) :=
  FormulaSignSlotRadialRadiusTarskiKernelSource.degree_fit _

noncomputable def source :IntegralFramedBankPolynomialModel.Source :=
  IntegralFramedBankPolynomialEmbedding.source S read dimension embedding degree_fit
noncomputable def access :IntegralFramedBankPolynomialModel.Access source :=
  IntegralFramedBankPolynomialEmbedding.access S read dimension embedding degree_fit
    FormulaSignSlotRadialRadiusTarskiKernelSource.access read_FP dimension_unary injective columnCode columnCode_FP columnCode_packet

theorem evaluation (z :List Bool) (v:ℕ→ℝ) :
    (source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      ((S).polynomial (read z)).eval₂ (Int.castRingHom ℝ)
        (fun i=>v (column i.val)) :=by
  rw [source,IntegralFramedBankPolynomialEmbedding.source,MvPolynomial.eval₂_rename]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialJointRadiusTarskiSource
