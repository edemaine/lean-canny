/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointRadiusTarskiSource
/-! # Actual radius/center sources on the unchanged joint columns

Radius is column 3 and center coordinate j is column 4*j. The modular reader
is constructed from the source reader and preserves the caller modulus.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialBoundCenterSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity MvPolynomial
open IntegralFramedBankPolynomialModel (Source Access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (G:Source) (read header:List Bool→List Bool)
  (hdim:∀z,G.arity (read z)=FormulaSignSlotRadialJointLayout.centerCount (header z)+1)
  (hfit:∀z,G.degree (read z)<2^G.width (read z))

noncomputable def dimension (z:List Bool):=FormulaSignSlotRadialJointLayout.dimension (header z)
theorem dimension_unary (hH:header∈FP):UnaryFn (dimension header):=
  FormulaSignSlotRadialJointLayout.dimension_unary.comp hH

include hdim
theorem column_lt (z:List Bool) (i:Fin (G.arity (read z))):
    FormulaSignSlotRadialJointRadiusTarskiSource.column i.val<dimension header z:=by
  unfold FormulaSignSlotRadialJointRadiusTarskiSource.column
  split_ifs with H
  · exact FormulaSignSlotRadialJointLayout.boundVariable_lt _
  · have HI:=i.isLt.trans_eq (hdim z)
    have HF:=FormulaSignSlotRadialJointLayout.formal_le_slots (header z)
    change FormulaSignSlotRadialJointLayout.spatialCount (header z)+
      (FormulaSignSlotRadialJointLayout.centerCount (header z)+1)≤_ at HF
    unfold dimension FormulaSignSlotRadialJointLayout.dimension
    omega
noncomputable def embedding (z:List Bool):Fin (G.arity (read z))→Fin (dimension header z):=
  fun i=>⟨FormulaSignSlotRadialJointRadiusTarskiSource.column i.val,column_lt G read header hdim z i⟩
theorem injective (z:List Bool):Function.Injective (embedding G read header hdim z):=by
  intro i j H
  apply Fin.ext
  have HE:=congrArg (fun x:Fin (dimension header z)=>x.val) H
  change FormulaSignSlotRadialJointRadiusTarskiSource.column i.val=
    FormulaSignSlotRadialJointRadiusTarskiSource.column j.val at HE
  unfold FormulaSignSlotRadialJointRadiusTarskiSource.column FormulaSignSlotRadialJointLayout.boundVariable at HE
  split_ifs at HE <;>omega
theorem columnCode_packet (z:List Bool) (i:Fin (G.arity (read z))):
    FormulaSignSlotRadialJointRadiusTarskiSource.columnCode (pair z (BinaryNatCode.encode i.val))=
      BinaryNatCode.encode (embedding G read header hdim z i).val:=by
  simp only [FormulaSignSlotRadialJointRadiusTarskiSource.columnCode,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,embedding]
noncomputable def source:Source:=IntegralFramedBankPolynomialEmbedding.source
  G read (dimension header) (embedding G read header hdim) hfit
noncomputable def access (A:Access G) (hr:read∈FP) (hH:header∈FP):Access (source G read header hdim hfit):=
  IntegralFramedBankPolynomialEmbedding.access G read (dimension header) (embedding G read header hdim) hfit
    A hr (dimension_unary header hH) (injective G read header hdim)
    FormulaSignSlotRadialJointRadiusTarskiSource.columnCode FormulaSignSlotRadialJointRadiusTarskiSource.columnCode_FP
    (columnCode_packet G read header hdim)
theorem degree_fit (z:List Bool):(source G read header hdim hfit).degree z<
    2^(source G read header hdim hfit).width z:=hfit z

theorem evaluation (z:List Bool) (v:ℕ→ℝ):
    ((source G read header hdim hfit).polynomial z).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      (G.polynomial (read z)).eval₂ (Int.castRingHom ℝ)
        (fun i=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val)):=by
  rw [source,IntegralFramedBankPolynomialEmbedding.source,MvPolynomial.eval₂_rename]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialBoundCenterSource
