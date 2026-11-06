/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialValueWindowCatalogue
public import LeanCanny.Encoding.FormulaSignSlotRadialJointLayout
public import LeanCanny.Encoding.IntegralFramedBankPolynomialEmbedding
/-! # Complete value-window features on the literal joint center and bound

The radius endpoint occupies column3 and center j occupies column4*j.
The complete value outer/inner ordinal is retained without a coordinate
factor. This source-only catalogue has no stratum or sampler dependency.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointValueWindowCatalogue
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S"=>FormulaSignSlotRadialValueWindowCatalogue.source
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial

def header (z:List Bool):=pairFst z
noncomputable def base (H:List Bool):=FormulaSignSlotRadialJointLayout.source true H
noncomputable def read (z:List Bool):=FormulaSignSlotRadialValueWindowCatalogue.row
  (pair (base (header z)) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd z))))
theorem base_FP:base∈FP:=FormulaSignSlotRadialJointLayout.source_FP true
theorem read_FP:read∈FP:=mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP base_FP)
  (BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP) FormulaSignSlotRadialValueWindowCatalogue.row_FP

theorem read_packet (H:List Bool) (i:ℕ):read (pair H (BinaryNatCode.encode i))=
    FormulaSignSlotRadialValueWindowCatalogue.row (pair (base H) (BinaryNatCode.encode i)):=by
  simp only [read,header,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
theorem arity_eq (z:List Bool):(S).arity (read z)=FormulaSignSlotRadialJointLayout.centerCount (header z)+1:=
  (FormulaSignSlotRadialValueWindowCatalogue.row_dimension (base (header z)) (Nat.fromBitsLE (pairSnd z)))

def column (i:ℕ):=if i=0 then FormulaSignSlotRadialJointLayout.boundVariable else 4*(i-1)
noncomputable def dimension (z:List Bool):=FormulaSignSlotRadialJointLayout.dimension (header z)
theorem dimension_unary:UnaryFn dimension:=FormulaSignSlotRadialJointLayout.dimension_unary.comp pairFst_mem_FP
theorem column_lt (z:List Bool) (i:Fin ((S).arity (read z))):column i.val<dimension z:=by
  unfold column
  split_ifs with H
  · exact FormulaSignSlotRadialJointLayout.boundVariable_lt _
  · have HI:=i.isLt.trans_eq (arity_eq z)
    have HF:=FormulaSignSlotRadialJointLayout.formal_le_slots (header z)
    change FormulaSignSlotRadialJointLayout.spatialCount (header z)+
      (FormulaSignSlotRadialJointLayout.centerCount (header z)+1)≤_ at HF
    unfold dimension FormulaSignSlotRadialJointLayout.dimension
    omega
noncomputable def embedding (z:List Bool):Fin ((S).arity (read z))→Fin (dimension z):=
  fun i=>⟨column i.val,column_lt z i⟩
theorem injective (z:List Bool):Function.Injective (embedding z):=by
  intro i j H
  apply Fin.ext
  have HE:=congrArg (fun x:Fin (dimension z)=>x.val) H
  change column i.val=column j.val at HE
  unfold column FormulaSignSlotRadialJointLayout.boundVariable at HE
  split_ifs at HE <;>omega

def columnCode (q:List Bool):=BinaryNatCode.encode (column (Nat.fromBitsLE (pairSnd q)))
theorem columnCode_FP:columnCode∈FP:=by
  have HI:BinaryFn (fun q=>Nat.fromBitsLE (pairSnd q)):=BinaryFn.fromBits pairSnd_mem_FP
  exact (BinaryFn.ite (HI.eq (BinaryFn.const 0)) (BinaryFn.const 3)
    ((BinaryFn.const 4).mul (HI.sub (BinaryFn.const 1)))).bits_mem_FP
theorem columnCode_packet (z:List Bool) (i:Fin ((S).arity (read z))):
    columnCode (pair z (BinaryNatCode.encode i.val))=BinaryNatCode.encode (embedding z i).val:=by
  simp only [columnCode,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,embedding]
theorem degree_fit (z:List Bool):(S).degree (read z)<2^(S).width (read z):=
  FormulaSignSlotRadialValueWindowCatalogue.input_access.fit _

attribute [local irreducible] read FormulaSignSlotRadialValueWindowCatalogue.source
noncomputable def source:IntegralFramedBankPolynomialModel.Source:=IntegralFramedBankPolynomialEmbedding.source
  S read dimension embedding degree_fit
noncomputable def source_access:IntegralFramedBankPolynomialModel.Access source:=IntegralFramedBankPolynomialEmbedding.access
  S read dimension embedding degree_fit FormulaSignSlotRadialValueWindowCatalogue.source_access read_FP dimension_unary
    injective columnCode columnCode_FP columnCode_packet

noncomputable def count (H:List Bool):=FormulaSignSlotRadialValueWindowCatalogue.count (base H)
noncomputable def degree (H:List Bool):=FormulaSignSlotRadialValueWindowCatalogue.degreeBound (base H)
noncomputable def mass (H:List Bool):=FormulaSignSlotRadialValueWindowCatalogue.massBound (base H)
theorem count_binary:BinaryFn count:=FormulaSignSlotRadialValueWindowCatalogue.count_binary.comp base_FP
theorem degree_binary:BinaryFn degree:=FormulaSignSlotRadialValueWindowCatalogue.degreeBound_binary.comp base_FP
theorem mass_binary:BinaryFn mass:=FormulaSignSlotRadialValueWindowCatalogue.massBound_binary.comp base_FP

theorem row_dimension (H:List Bool) (i:ℕ):source.arity (pair H (BinaryNatCode.encode i))=
    FormulaSignSlotRadialJointLayout.dimension H:=by
  change FormulaSignSlotRadialJointLayout.dimension (header (pair H (BinaryNatCode.encode i)))=_
  simp only [header,pairFst_pair]
theorem degree_bound (H:List Bool) (i:ℕ):source.degree (pair H (BinaryNatCode.encode i))≤degree H:=by
  change (S).degree (read (pair H (BinaryNatCode.encode i)))≤_
  rw [read_packet]
  exact FormulaSignSlotRadialValueWindowCatalogue.row_degree (base H) i
theorem mass_bound (H:List Bool) (i:ℕ):source.mass (pair H (BinaryNatCode.encode i))≤mass H:=by
  change (S).mass (read (pair H (BinaryNatCode.encode i)))≤_
  rw [read_packet]
  exact FormulaSignSlotRadialValueWindowCatalogue.row_mass (base H) i
noncomputable def input:ChargedPolynomialCatalogue.Input where
  source:=source
  row:=id
  arity:=FormulaSignSlotRadialJointLayout.dimension
  count:=count
  degree:=degree
  mass:=mass
  dimension:=row_dimension
  degree_bound:=degree_bound
  mass_bound:=mass_bound
noncomputable def family:=ChargedPolynomialCatalogue.family input
theorem source_fit (z:List Bool):source.degree z<2^source.width z:=by
  dsimp only [source,IntegralFramedBankPolynomialEmbedding.source]
  exact degree_fit z
noncomputable def input_access:ChargedPolynomialCatalogue.Access input where
  source:=source_access
  row:=id_mem_FP
  arity:=FormulaSignSlotRadialJointLayout.dimension_unary
  count:=count_binary
  degree:=degree_binary
  mass:=mass_binary
  fit:=source_fit
noncomputable def access:SquareFeatureProductFamily.Access family:=ChargedPolynomialCatalogue.access input input_access

private theorem eval_cast {a b:ℕ} (ha:a=b) (p:MvPolynomial (Fin a) ℤ) (v:ℕ→ℝ):
    (rename (Fin.cast ha) p).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      p.eval₂ (Int.castRingHom ℝ) (fun i=>v i.val):=by
  subst b
  simp only [Fin.cast_refl,MvPolynomial.rename_id,AlgHom.id_apply]
theorem source_evaluation (z:List Bool) (v:ℕ→ℝ):
    (source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      ((S).polynomial (read z)).eval₂ (Int.castRingHom ℝ) (fun i=>v (column i.val)):=by
  rw [source,IntegralFramedBankPolynomialEmbedding.source,MvPolynomial.eval₂_rename]
  rfl
theorem feature_value (H:List Bool) (i:ℕ) (v:ℕ→ℝ):
    (family.feature H i).eval₂ (Int.castRingHom ℝ) (fun j=>v j.val)=
      (FormulaSignSlotRadialValueWindowCatalogue.family.feature (base H) i).eval₂ (Int.castRingHom ℝ)
        (fun j=>v (column j.val)):=
  ((eval_cast (row_dimension H i) (source.polynomial _) v).trans (source_evaluation _ v)).trans
    (by rw [read_packet];exact (eval_cast (FormulaSignSlotRadialValueWindowCatalogue.row_dimension (base H) i)
      ((S).polynomial _) (fun j=>v (column j))).symm)

end LeanCanny.Encoding.FormulaSignSlotRadialJointValueWindowCatalogue
