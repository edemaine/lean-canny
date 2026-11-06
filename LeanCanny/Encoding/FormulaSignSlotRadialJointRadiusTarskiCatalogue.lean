/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiCatalogue
public import LeanCanny.Encoding.FormulaSignSlotRadialJointRadiusTarskiSource
/-! # Bounded radius-query controls on the actual joint tuple

Every spatial coordinate and every bounded principal/head/seed control is
included. The endpoint retains column 3 and centers retain columns 4*j.
This catalogue is source-only and introduces no new sampler.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointRadiusTarskiCatalogue
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialRadiusTarskiKernelSource.source

def header (z :List Bool):=pairFst z
def coordinateWord (z :List Bool):=pairFst (pairSnd z)
def controlWord (z :List Bool):=pairSnd (pairSnd z)
noncomputable def radial (z :List Bool):=FormulaSignSlotRadialCoordinatePacket.writer
  (pair (FormulaSignSlotRadialJointLayout.source true (header z)) (coordinateWord z))
noncomputable def control (z :List Bool):=Nat.fromBitsLE (controlWord z)
noncomputable def read (z :List Bool):=FormulaSignSlotRadialRadiusTarskiCatalogue.row
  (pair (radial z) (BinaryNatCode.encode (control z)))
theorem radial_FP :radial∈FP:=mem_FP_comp
  (mem_FP_pair (mem_FP_comp (f:=header) (g:=FormulaSignSlotRadialJointLayout.source true)
    pairFst_mem_FP (FormulaSignSlotRadialJointLayout.source_FP true))
    (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)) FormulaSignSlotRadialCoordinatePacket.writer_FP
theorem read_FP :read∈FP:=mem_FP_comp (mem_FP_pair radial_FP
  (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)).bits_mem_FP)
  FormulaSignSlotRadialRadiusTarskiCatalogue.row_FP
theorem radial_root (z :List Bool):pairFst (radial z)=FormulaSignSlotRadialJointLayout.source true (header z):=by
  simp only [radial,FormulaSignSlotRadialCoordinatePacket.writer,pairFst_pair]
theorem arity_eq (z :List Bool):(S).arity (read z)=FormulaSignSlotRadialJointLayout.centerCount (header z)+1:=by
  rw [read,FormulaSignSlotRadialRadiusTarskiCatalogue.dimension]
  unfold FormulaSignSlotRadialRadiusTarskiCatalogue.arity
  rw [radial_root]
  rfl
noncomputable def dimension (z :List Bool):=FormulaSignSlotRadialJointLayout.dimension (header z)
theorem dimension_unary :UnaryFn dimension:=FormulaSignSlotRadialJointLayout.dimension_unary.comp pairFst_mem_FP

theorem column_lt (z :List Bool) (i :Fin ((S).arity (read z))):
    FormulaSignSlotRadialJointRadiusTarskiSource.column i.val<dimension z:=by
  unfold FormulaSignSlotRadialJointRadiusTarskiSource.column
  split_ifs with H
  · exact FormulaSignSlotRadialJointLayout.boundVariable_lt _
  · have HI:=i.isLt.trans_eq (arity_eq z)
    have HF:=FormulaSignSlotRadialJointLayout.formal_le_slots (header z)
    change FormulaSignSlotRadialJointLayout.spatialCount (header z)+
      (FormulaSignSlotRadialJointLayout.centerCount (header z)+1)≤_ at HF
    unfold dimension FormulaSignSlotRadialJointLayout.dimension
    omega
noncomputable def embedding (z :List Bool):Fin ((S).arity (read z))→Fin (dimension z):=
  fun i=>⟨FormulaSignSlotRadialJointRadiusTarskiSource.column i.val,column_lt z i⟩
theorem injective (z :List Bool):Function.Injective (embedding z):=by
  intro i j H
  apply Fin.ext
  have HE:=congrArg (fun x:Fin (dimension z)=>x.val) H
  change FormulaSignSlotRadialJointRadiusTarskiSource.column i.val=
    FormulaSignSlotRadialJointRadiusTarskiSource.column j.val at HE
  unfold FormulaSignSlotRadialJointRadiusTarskiSource.column FormulaSignSlotRadialJointLayout.boundVariable at HE
  split_ifs at HE <;>omega
theorem columnCode_packet (z :List Bool) (i :Fin ((S).arity (read z))):
    FormulaSignSlotRadialJointRadiusTarskiSource.columnCode (pair z (BinaryNatCode.encode i.val))=
      BinaryNatCode.encode (embedding z i).val:=by
  simp only [FormulaSignSlotRadialJointRadiusTarskiSource.columnCode,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,embedding]
attribute [local irreducible] read
theorem degree_fit (z :List Bool):(S).degree (read z)<2^(S).width (read z):=
  FormulaSignSlotRadialRadiusTarskiKernelSource.degree_fit _
noncomputable def source:IntegralFramedBankPolynomialModel.Source:=IntegralFramedBankPolynomialEmbedding.source
  S read dimension embedding degree_fit
noncomputable def source_access:IntegralFramedBankPolynomialModel.Access source:=IntegralFramedBankPolynomialEmbedding.access
  S read dimension embedding degree_fit FormulaSignSlotRadialRadiusTarskiKernelSource.access read_FP dimension_unary injective
    FormulaSignSlotRadialJointRadiusTarskiSource.columnCode FormulaSignSlotRadialJointRadiusTarskiSource.columnCode_FP columnCode_packet

noncomputable def base (c :List Bool):=pair (FormulaSignSlotRadialJointLayout.source true c) []
noncomputable def limit (c :List Bool):=FormulaSignSlotRadialRadiusTarskiCatalogue.count (base c)
noncomputable def count (c :List Bool):=FormulaSignSlotRadialJointLayout.spatialCount c*limit c
noncomputable def degree (c :List Bool):=FormulaSignSlotRadialRadiusTarskiCatalogue.degree (base c)
noncomputable def mass (c :List Bool):=FormulaSignSlotRadialRadiusTarskiCatalogue.mass (base c)
noncomputable def row (q :List Bool):=pair (pairFst q) (pair
  (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q)/limit (pairFst q)))
  (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q)%limit (pairFst q))))
theorem root_eq (c :List Bool) (i :ℕ):pairFst (radial (row (pair c (BinaryNatCode.encode i))))=pairFst (base c):=by
  rw [radial_root]
  simp only [row,header,base,pairFst_pair]
theorem row_dimension (c :List Bool) (i :ℕ):source.arity (row (pair c (BinaryNatCode.encode i)))=
    FormulaSignSlotRadialJointLayout.dimension c:=by
  change FormulaSignSlotRadialJointLayout.dimension (header (row (pair c (BinaryNatCode.encode i))))=_
  simp only [header,row,pairFst_pair]
theorem degree_bound (c :List Bool) (i :ℕ):source.degree (row (pair c (BinaryNatCode.encode i)))≤degree c:=by
  change (S).degree (read (row (pair c (BinaryNatCode.encode i))))≤degree c
  unfold read
  exact (FormulaSignSlotRadialRadiusTarskiCatalogue.degree_bound _ _).trans_eq
    (FormulaSignSlotRadialRadiusTarskiCatalogue.degree_eq _ _ (root_eq c i))
theorem mass_bound (c :List Bool) (i :ℕ):source.mass (row (pair c (BinaryNatCode.encode i)))≤mass c:=by
  change (S).mass (read (row (pair c (BinaryNatCode.encode i))))≤mass c
  unfold read
  exact (FormulaSignSlotRadialRadiusTarskiCatalogue.mass_bound _ _).trans_eq
    (FormulaSignSlotRadialRadiusTarskiCatalogue.mass_eq _ _ (root_eq c i))

theorem base_FP :base∈FP:=mem_FP_pair (FormulaSignSlotRadialJointLayout.source_FP true) (constFn_mem_FP [])
theorem limit_binary :BinaryFn limit:=FormulaSignSlotRadialRadiusTarskiCatalogue.count_binary.comp base_FP
theorem count_binary :BinaryFn count:=(BinaryFn.ofUnary FormulaSignSlotRadialJointLayout.spatialCount_unary).mul limit_binary
theorem degree_binary :BinaryFn degree:=FormulaSignSlotRadialRadiusTarskiCatalogue.degree_binary.comp base_FP
theorem mass_binary :BinaryFn mass:=FormulaSignSlotRadialRadiusTarskiCatalogue.mass_binary.comp base_FP
theorem row_FP :row∈FP:=by
  have HI:=BinaryFn.fromBits pairSnd_mem_FP
  have HL:=limit_binary.comp pairFst_mem_FP
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair (HI.div HL).bits_mem_FP (HI.mod HL).bits_mem_FP)
noncomputable def input:ChargedPolynomialCatalogue.Input where
  source:=source
  row:=row
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
  row:=row_FP
  arity:=FormulaSignSlotRadialJointLayout.dimension_unary
  count:=count_binary
  degree:=degree_binary
  mass:=mass_binary
  fit:=source_fit
noncomputable def access:SquareFeatureProductFamily.Access family:=ChargedPolynomialCatalogue.access input input_access

noncomputable def encode (c :List Bool) (j k :ℕ):=k+limit c*j
theorem row_encode (c :List Bool) (j k :ℕ) (hk:k<limit c):
    row (pair c (BinaryNatCode.encode (encode c j k)))=
      pair c (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k)):=by
  have HB:0<limit c:=by omega
  have HD:encode c j k/limit c=j:=by
    rw [encode,Nat.add_mul_div_left _ _ HB,Nat.div_eq_of_lt hk,Nat.zero_add]
  have HM:encode c j k%limit c=k:=by
    rw [encode,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hk]
  simp only [row,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,HD,HM]
theorem encode_lt (c :List Bool) (j k :ℕ)
    (hj:j<FormulaSignSlotRadialJointLayout.spatialCount c) (hk:k<limit c):encode c j k<count c:=by
  calc
    _ < limit c+limit c*j:=Nat.add_lt_add_right hk _
    _ = limit c*(j+1):=by ring
    _ ≤ limit c*FormulaSignSlotRadialJointLayout.spatialCount c:=Nat.mul_le_mul_left _ (by omega)
    _ = count c:=by unfold count;ring

private theorem eval_cast {a b:ℕ} (ha:a=b) (p:MvPolynomial (Fin a) ℤ) (v:ℕ→ℝ):
    (rename (Fin.cast ha) p).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      p.eval₂ (Int.castRingHom ℝ) (fun i=>v i.val):=by
  subst b
  simp only [Fin.cast_refl,MvPolynomial.rename_id,AlgHom.id_apply]
theorem source_evaluation (z :List Bool) (v:ℕ→ℝ):
    (source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      ((S).polynomial (read z)).eval₂ (Int.castRingHom ℝ)
        (fun i=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val)):=by
  rw [source,IntegralFramedBankPolynomialEmbedding.source,MvPolynomial.eval₂_rename]
  rfl
theorem feature_value (c :List Bool) (i:ℕ) (v:ℕ→ℝ):
    (family.feature c i).eval₂ (Int.castRingHom ℝ) (fun j=>v j.val)=
      ((S).polynomial (read (row (pair c (BinaryNatCode.encode i))))).eval₂ (Int.castRingHom ℝ)
        (fun j=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column j.val)):=
  (eval_cast (row_dimension c i) (source.polynomial _) v).trans (source_evaluation _ v)
theorem feature_encode (c :List Bool) (j k:ℕ) (hk:k<limit c) (v:ℕ→ℝ):
    (family.feature c (encode c j k)).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      ((S).polynomial (read (pair c (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k))))).eval₂
        (Int.castRingHom ℝ) (fun i=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val)):=by
  rw [feature_value,row_encode c j k hk]

end LeanCanny.Encoding.FormulaSignSlotRadialJointRadiusTarskiCatalogue
