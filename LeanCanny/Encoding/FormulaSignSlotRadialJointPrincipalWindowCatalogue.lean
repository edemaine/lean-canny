/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialPrincipalWindowOrdinal
public import LeanCanny.Encoding.FormulaSignSlotRadialJointRadiusTarskiSource
/-! # Complete principal-window features on the literal joint tuple

The observable coordinate is clipped at every ordinal. Uniform original
bounds range over the resulting short radial packets; no equality of
profiles at different selector packets is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalWindowCatalogue
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S"=>FormulaSignSlotRadialCutWindowSources.principalSource
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial

noncomputable def radialBudget (H:List Bool):=2*(FormulaSignSlotRadialJointLayout.source true H).length+2+
  2*(FormulaSignSlotRadialJointLayout.spatialCount H).size+2
theorem radialBudget_unary:UnaryFn radialBudget:=
  ((((UnaryFn.const 2).mul (UnaryFn.length (FormulaSignSlotRadialJointLayout.source_FP true))).add (UnaryFn.const 2)).add
    ((UnaryFn.const 2).mul ((UnaryFn.length (BinaryFn.ofUnary FormulaSignSlotRadialJointLayout.spatialCount_unary).bits_mem_FP).of_eq
      (fun _=>BinaryNatCode.length_encode _)))).add (UnaryFn.const 2)

theorem count_exists:∃g:List Bool→ℕ,BinaryFn g ∧∀H u,u.length ≤ radialBudget H→
    FormulaSignSlotRadialPrincipalWindowCatalogue.count u ≤ g H:=
  FormulaSignSlotRadialPrincipalWindowCatalogue.count_binary.wordEnvelope radialBudget_unary
noncomputable def innerLimit:List Bool→ℕ:=Classical.choose count_exists
theorem innerLimit_binary:BinaryFn innerLimit:=(Classical.choose_spec count_exists).1
theorem inner_count_le (H u:List Bool) (hu:u.length ≤ radialBudget H):
    FormulaSignSlotRadialPrincipalWindowCatalogue.count u ≤ innerLimit H:=
  (Classical.choose_spec count_exists).2 H u hu

def header (z:List Bool):=pairFst z
def ordinal (z:List Bool):=Nat.fromBitsLE (pairSnd z)
noncomputable def selected (z:List Bool):=min (ordinal z/innerLimit (header z))
  (FormulaSignSlotRadialJointLayout.spatialCount (header z)-1)
noncomputable def inner (z:List Bool):=ordinal z%innerLimit (header z)
noncomputable def radial (z:List Bool):=FormulaSignSlotRadialCoordinatePacket.packet
  (FormulaSignSlotRadialJointLayout.source true (header z)) (selected z)
noncomputable def read (z:List Bool):=FormulaSignSlotRadialPrincipalWindowCatalogue.row
  (pair (radial z) (BinaryNatCode.encode (inner z)))
theorem spatial_pos (H:List Bool):0 < FormulaSignSlotRadialJointLayout.spatialCount H:=by
  unfold FormulaSignSlotRadialJointLayout.spatialCount FormulaSignSlotRadialFormalInput.spatial
  omega
theorem selected_lt (z:List Bool):selected z < FormulaSignSlotRadialJointLayout.spatialCount (header z):=by
  have H:=spatial_pos (header z)
  have HE:=Nat.min_le_right (ordinal z/innerLimit (header z))
    (FormulaSignSlotRadialJointLayout.spatialCount (header z)-1)
  unfold selected
  omega
theorem radial_length (z:List Bool):(radial z).length ≤ radialBudget (header z):=by
  have HI: (selected z).size ≤ (FormulaSignSlotRadialJointLayout.spatialCount (header z)).size:=
    Nat.size_le_size (selected_lt z).le
  simp only [radial,FormulaSignSlotRadialCoordinatePacket.packet,WordList.encode,pair_length,List.length_nil,BinaryNatCode.length_encode]
  unfold radialBudget
  omega

theorem read_FP:read∈FP:=by
  have HI:BinaryFn ordinal:=BinaryFn.fromBits pairSnd_mem_FP
  have HK:=innerLimit_binary.comp pairFst_mem_FP
  have HC:BinaryFn (fun z=>FormulaSignSlotRadialJointLayout.spatialCount (header z)-1):=
    (BinaryFn.ofUnary (FormulaSignSlotRadialJointLayout.spatialCount_unary.comp pairFst_mem_FP)).sub (BinaryFn.const 1)
  have HS:BinaryFn selected:=(BinaryFn.ite ((HI.div HK).le HC) (HI.div HK) HC).of_eq (fun _=>Nat.min_def.symm)
  have HP:radial∈FP:=mem_FP_pair
    (mem_FP_comp (f:=header) (g:=FormulaSignSlotRadialJointLayout.source true) pairFst_mem_FP
      (FormulaSignSlotRadialJointLayout.source_FP true)) (mem_FP_pair HS.bits_mem_FP (constFn_mem_FP []))
  exact mem_FP_comp (mem_FP_pair HP (HI.mod HK).bits_mem_FP) FormulaSignSlotRadialPrincipalWindowCatalogue.row_FP

theorem arity_eq (z:List Bool):(S).arity (read z)=FormulaSignSlotRadialJointLayout.centerCount (header z)+1:=by
  rw [read,FormulaSignSlotRadialPrincipalWindowCatalogue.dimension]
  unfold FormulaSignSlotRadialPrincipalWindowCatalogue.arity
  rw [radial,FormulaSignSlotRadialCoordinatePacket.root]
  rfl
noncomputable def dimension (z:List Bool):=FormulaSignSlotRadialJointLayout.dimension (header z)
theorem dimension_unary:UnaryFn dimension:=FormulaSignSlotRadialJointLayout.dimension_unary.comp pairFst_mem_FP
theorem column_lt (z:List Bool) (i:Fin ((S).arity (read z))):
    FormulaSignSlotRadialJointRadiusTarskiSource.column i.val < dimension z:=by
  unfold FormulaSignSlotRadialJointRadiusTarskiSource.column
  split_ifs with H
  · exact FormulaSignSlotRadialJointLayout.boundVariable_lt _
  · have HI:=i.isLt.trans_eq (arity_eq z)
    have HF:=FormulaSignSlotRadialJointLayout.formal_le_slots (header z)
    change FormulaSignSlotRadialJointLayout.spatialCount (header z)+
      (FormulaSignSlotRadialJointLayout.centerCount (header z)+1) ≤ _ at HF
    unfold dimension FormulaSignSlotRadialJointLayout.dimension
    omega
noncomputable def embedding (z:List Bool):Fin ((S).arity (read z))→Fin (dimension z):=
  fun i=>⟨FormulaSignSlotRadialJointRadiusTarskiSource.column i.val,column_lt z i⟩
theorem injective (z:List Bool):Function.Injective (embedding z):=by
  intro i j H
  apply Fin.ext
  have HE:=congrArg (fun x:Fin (dimension z)=>x.val) H
  change FormulaSignSlotRadialJointRadiusTarskiSource.column i.val=
    FormulaSignSlotRadialJointRadiusTarskiSource.column j.val at HE
  unfold FormulaSignSlotRadialJointRadiusTarskiSource.column FormulaSignSlotRadialJointLayout.boundVariable at HE
  split_ifs at HE  <;>omega
theorem columnCode_packet (z:List Bool) (i:Fin ((S).arity (read z))):
    FormulaSignSlotRadialJointRadiusTarskiSource.columnCode (pair z (BinaryNatCode.encode i.val))=
      BinaryNatCode.encode (embedding z i).val:=by
  simp only [FormulaSignSlotRadialJointRadiusTarskiSource.columnCode,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,embedding]
theorem degree_fit (z:List Bool):(S).degree (read z) < 2^(S).width (read z):=
  FormulaSignSlotRadialPrincipalWindowCatalogue.source_fit _
attribute [local irreducible] read
noncomputable def source:IntegralFramedBankPolynomialModel.Source:=IntegralFramedBankPolynomialEmbedding.source
  S read dimension embedding degree_fit
noncomputable def source_access:IntegralFramedBankPolynomialModel.Access source:=IntegralFramedBankPolynomialEmbedding.access
  S read dimension embedding degree_fit FormulaSignSlotRadialCutWindowSources.principalAccess read_FP dimension_unary injective
    FormulaSignSlotRadialJointRadiusTarskiSource.columnCode FormulaSignSlotRadialJointRadiusTarskiSource.columnCode_FP columnCode_packet

noncomputable def count (H:List Bool):=FormulaSignSlotRadialJointLayout.spatialCount H*innerLimit H
theorem count_binary:BinaryFn count:=(BinaryFn.ofUnary FormulaSignSlotRadialJointLayout.spatialCount_unary).mul innerLimit_binary

theorem degree_exists:∃g:List Bool→ℕ,BinaryFn g ∧∀H u,u.length ≤ radialBudget H→
    FormulaSignSlotRadialPrincipalWindowCatalogue.degree u ≤ g H:=
  FormulaSignSlotRadialPrincipalWindowCatalogue.degree_binary.wordEnvelope radialBudget_unary
noncomputable def degree:List Bool→ℕ:=Classical.choose degree_exists
theorem degree_binary:BinaryFn degree:=(Classical.choose_spec degree_exists).1
theorem mass_exists:∃g:List Bool→ℕ,BinaryFn g ∧∀H u,u.length ≤ radialBudget H→
    FormulaSignSlotRadialPrincipalWindowCatalogue.mass u ≤ g H:=
  FormulaSignSlotRadialPrincipalWindowCatalogue.mass_binary.wordEnvelope radialBudget_unary
noncomputable def mass:List Bool→ℕ:=Classical.choose mass_exists
theorem mass_binary:BinaryFn mass:=(Classical.choose_spec mass_exists).1

theorem row_dimension (H:List Bool) (i:ℕ):source.arity (pair H (BinaryNatCode.encode i))=
    FormulaSignSlotRadialJointLayout.dimension H:=by
  change FormulaSignSlotRadialJointLayout.dimension (header (pair H (BinaryNatCode.encode i)))=_
  simp only [header,pairFst_pair]
theorem degree_bound (H:List Bool) (i:ℕ):source.degree (pair H (BinaryNatCode.encode i)) ≤ degree H:=by
  let z:=pair H (BinaryNatCode.encode i)
  change (S).degree (read z) ≤ degree H
  unfold read
  exact (FormulaSignSlotRadialPrincipalWindowCatalogue.degree_bound (radial z) (inner z)).trans
    ((Classical.choose_spec degree_exists).2 H (radial z) (by simpa only [z,header,pairFst_pair] using radial_length z))
theorem mass_bound (H:List Bool) (i:ℕ):source.mass (pair H (BinaryNatCode.encode i)) ≤ mass H:=by
  let z:=pair H (BinaryNatCode.encode i)
  change (S).mass (read z) ≤ mass H
  unfold read
  exact (FormulaSignSlotRadialPrincipalWindowCatalogue.mass_bound (radial z) (inner z)).trans
    ((Classical.choose_spec mass_exists).2 H (radial z) (by simpa only [z,header,pairFst_pair] using radial_length z))
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
theorem source_fit (z:List Bool):source.degree z < 2^source.width z:=by
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

noncomputable def encode (H:List Bool) (j k:ℕ):=k+innerLimit H*j
private theorem digit_div (B a d:ℕ) (hd:d < B):(d+B*a)/B=a:=by
  rw [Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt hd,Nat.zero_add]
theorem encoded_radial (H:List Bool) (j k:ℕ) (hj:j < FormulaSignSlotRadialJointLayout.spatialCount H) (hk:k < innerLimit H):
    radial (pair H (BinaryNatCode.encode (encode H j k)))=
      FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j:=by
  have HD:encode H j k/innerLimit H=j:=digit_div _ _ _ hk
  have HM:min j (FormulaSignSlotRadialJointLayout.spatialCount H-1)=j:=Nat.min_eq_left (by omega)
  simp only [radial,selected,ordinal,header,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,HD,HM]
theorem encoded_inner (H:List Bool) (j k:ℕ) (hk:k < innerLimit H):
    inner (pair H (BinaryNatCode.encode (encode H j k)))=k:=by
  simp only [inner,ordinal,header,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [encode,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hk]
theorem encode_lt (H:List Bool) (j k:ℕ) (hj:j < FormulaSignSlotRadialJointLayout.spatialCount H) (hk:k < innerLimit H):
    encode H j k < count H:=by
  calc
    _  <  innerLimit H+innerLimit H*j:=Nat.add_lt_add_right hk _
    _ = innerLimit H*(j+1):=by ring
    _ ≤ innerLimit H*FormulaSignSlotRadialJointLayout.spatialCount H:=Nat.mul_le_mul_left _ (by omega)
    _ = count H:=by unfold count;ring

theorem packet_length (H:List Bool) (j:ℕ) (hj:j < FormulaSignSlotRadialJointLayout.spatialCount H):
    (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j).length ≤ radialBudget H:=by
  have HI:j.size ≤ (FormulaSignSlotRadialJointLayout.spatialCount H).size:=Nat.size_le_size hj.le
  simp only [FormulaSignSlotRadialCoordinatePacket.packet,WordList.encode,pair_length,List.length_nil,BinaryNatCode.length_encode]
  unfold radialBudget
  omega

theorem covers (H:List Bool) (j k:ℕ) (hj:j < FormulaSignSlotRadialJointLayout.spatialCount H)
    (hk:k < FormulaSignSlotRadialPrincipalWindowCatalogue.count
      (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j)):
    ∃i < count H,read (pair H (BinaryNatCode.encode i))=
      FormulaSignSlotRadialPrincipalWindowCatalogue.row
        (pair (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j)
          (BinaryNatCode.encode k)):=by
  have HK:k < innerLimit H:=hk.trans_le (inner_count_le H _ (packet_length H j hj))
  refine ⟨encode H j k,encode_lt H j k hj HK,?_⟩
  unfold read
  rw [encoded_radial H j k hj HK,encoded_inner H j k HK]

noncomputable def value (u:List Bool) (k:ℕ) (v:ℕ→ℝ):=
  (FormulaSignSlotRadialPrincipalWindowCatalogue.family.feature u k).eval₂ (Int.castRingHom ℝ)
    (fun i=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val))
private theorem eval_cast {a b:ℕ} (ha:a=b) (p:MvPolynomial (Fin a) ℤ) (v:ℕ→ℝ):
    (rename (Fin.cast ha) p).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      p.eval₂ (Int.castRingHom ℝ) (fun i=>v i.val):=by
  subst b
  simp only [Fin.cast_refl,MvPolynomial.rename_id,AlgHom.id_apply]
theorem source_evaluation (z:List Bool) (v:ℕ→ℝ):
    (source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      ((S).polynomial (read z)).eval₂ (Int.castRingHom ℝ)
        (fun i=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val)):=by
  rw [source,IntegralFramedBankPolynomialEmbedding.source,MvPolynomial.eval₂_rename]
  rfl
theorem feature_value (H:List Bool) (i:ℕ) (v:ℕ→ℝ):
    (family.feature H i).eval₂ (Int.castRingHom ℝ) (fun j=>v j.val)=
      value (radial (pair H (BinaryNatCode.encode i))) (inner (pair H (BinaryNatCode.encode i))) v:=
  ((eval_cast (row_dimension H i) (source.polynomial _) v).trans (source_evaluation _ v)).trans
    (by unfold read value
        exact (eval_cast (FormulaSignSlotRadialPrincipalWindowCatalogue.dimension _ _)
          ((S).polynomial _) (fun j=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column j))).symm)
attribute [local irreducible] value

theorem feature_encode (H:List Bool) (j k:ℕ) (hj:j < FormulaSignSlotRadialJointLayout.spatialCount H)
    (hk:k < FormulaSignSlotRadialPrincipalWindowCatalogue.count
      (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j)) (v:ℕ→ℝ):
    (family.feature H (encode H j k)).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      value (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j) k v:=by
  have HK:k < innerLimit H:=hk.trans_le (inner_count_le H _ (packet_length H j hj))
  rw [feature_value,encoded_radial H j k hj HK,encoded_inner H j k HK]

theorem encoded_feature_eval (H:List Bool) (j k:ℕ) (hj:j < FormulaSignSlotRadialJointLayout.spatialCount H)
    (hk:k < FormulaSignSlotRadialPrincipalWindowCatalogue.count
      (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j)) (v:ℕ→ℝ):
    (family.feature H (encode H j k)).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      (FormulaSignSlotRadialPrincipalWindowCatalogue.family.feature
        (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j) k).eval₂
          (Int.castRingHom ℝ) (fun i=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val)):=by
  have HE:=feature_encode H j k hj hk v
  unfold value at HE
  exact HE

end LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalWindowCatalogue
