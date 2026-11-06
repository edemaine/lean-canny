/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialValueCatalogueLayout
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiOrdinal
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiRowLength
/-! # Original-only value-window controls with one exact native catalogue

The actual radius-first value coefficient source is retained. An outer row
selects its bounded coordinate tables and coefficient; an inner row selects
head, seed or principal controls. Surplus inner ordinals repeat actual rows.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialValueWindowCatalogue
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "Raw"=>FormulaSignSlotRadialValueRadiusSource.source
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialCenterValuePacking.source

noncomputable def centers (c:List Bool):=FormulaSignSlotCenteredRadialGraph.d
  (FormulaSignSlotRadialCenterValueLayout.original (pairFst c))
theorem dimension_eq (c:List Bool):(Raw).arity c=centers c+1:=rfl
theorem centers_unary:UnaryFn centers:=FormulaSignSlotSource.dimension_unary.comp
  (mem_FP_comp pairFst_mem_FP FormulaSignSlotRadialCenterValueLayout.original_FP)
noncomputable def source:=IntegralPolynomialWindowTarski.source Raw centers dimension_eq
noncomputable def source_access:IntegralFramedBankPolynomialModel.Access source:=
  IntegralPolynomialWindowTarski.sourceAccess Raw centers dimension_eq FormulaSignSlotRadialValueRadiusSource.access
    centers_unary FormulaSignSlotRadialValueRadiusSource.degree_fit

noncomputable def innerCount (u:List Bool):=6*(FormulaSignSlotRadialValueCatalogueBounds.degreeCap u+2)^3
noncomputable def count (u:List Bool):=FormulaSignSlotRadialValueCatalogueLayout.outerCount u*innerCount u
noncomputable def outerIndex (u:List Bool) (i:ℕ):=i/innerCount u
noncomputable def innerIndex (u:List Bool) (i:ℕ):=i%innerCount u
noncomputable def rawContext (u:List Bool) (i:ℕ):=FormulaSignSlotRadialValueCatalogueLayout.context
  (pair u (BinaryNatCode.encode (outerIndex u i)))
noncomputable def row (q:List Bool):=IntegralPolynomialWindowTarskiCatalogue.row Raw
  (pair (rawContext (pairFst q) (Nat.fromBitsLE (pairSnd q)))
    (BinaryNatCode.encode (innerIndex (pairFst q) (Nat.fromBitsLE (pairSnd q)))))

theorem innerCount_binary:BinaryFn innerCount:=
  (BinaryFn.const 6).mul ((FormulaSignSlotRadialValueCatalogueBounds.degreeCap_binary.add (BinaryFn.const 2)).powUnary (UnaryFn.const 3))
theorem count_binary:BinaryFn count:=FormulaSignSlotRadialValueCatalogueLayout.outerCount_binary.mul innerCount_binary
theorem innerCount_pos (u:List Bool):0< innerCount u:=Nat.mul_pos (by decide) (pow_pos (by omega) _)
theorem row_FP:row∈FP:=by
  have HI:BinaryFn (fun q=>Nat.fromBitsLE (pairSnd q)):=BinaryFn.fromBits pairSnd_mem_FP
  have HC:BinaryFn (fun q=>innerCount (pairFst q)):=innerCount_binary.comp pairFst_mem_FP
  have HO:(fun q=>pair (pairFst q) (BinaryNatCode.encode (outerIndex (pairFst q) (Nat.fromBitsLE (pairSnd q)))))∈FP:=
    mem_FP_pair pairFst_mem_FP (HI.div HC).bits_mem_FP
  have HR:(fun q=>rawContext (pairFst q) (Nat.fromBitsLE (pairSnd q)))∈FP:=
    mem_FP_comp HO FormulaSignSlotRadialValueCatalogueLayout.context_FP
  exact mem_FP_comp (mem_FP_pair HR (HI.mod HC).bits_mem_FP)
    (IntegralPolynomialWindowTarskiCatalogue.row_FP Raw FormulaSignSlotRadialValueRadiusSource.access)

theorem row_packet (u:List Bool) (i:ℕ):row (pair u (BinaryNatCode.encode i))=
    IntegralPolynomialWindowTarskiCatalogue.row Raw
      (pair (rawContext u i) (BinaryNatCode.encode (innerIndex u i))):=by
  simp only [row,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

noncomputable def rawBudget (u:List Bool):=2*FormulaSignSlotRadialValueCatalogueBounds.familyBudget u+
  (FormulaSignSlotRadialValueCatalogueBounds.degreeCap u).size+2
noncomputable def rowBudget (u:List Bool):=4*rawBudget u+9*(FormulaSignSlotRadialValueCatalogueBounds.degreeCap u+2).size+22
private theorem capSize_unary:UnaryFn (fun u=>(FormulaSignSlotRadialValueCatalogueBounds.degreeCap u).size):=
  (UnaryFn.length FormulaSignSlotRadialValueCatalogueBounds.degreeCap_binary.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
theorem rawBudget_unary:UnaryFn rawBudget:=
  (((UnaryFn.const 2).mul FormulaSignSlotRadialValueCatalogueBounds.familyBudget_unary).add capSize_unary).add (UnaryFn.const 2)
theorem rowBudget_unary:UnaryFn rowBudget:=by
  have HW:UnaryFn (fun u=>(FormulaSignSlotRadialValueCatalogueBounds.degreeCap u+2).size):=
    (UnaryFn.length (FormulaSignSlotRadialValueCatalogueBounds.degreeCap_binary.add (BinaryFn.const 2)).bits_mem_FP).of_eq
      (fun _=>BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 4).mul rawBudget_unary).add ((UnaryFn.const 9).mul HW)).add (UnaryFn.const 22)

theorem raw_length (u:List Bool) (i:ℕ):(rawContext u i).length≤rawBudget u:=by
  have HF:=FormulaSignSlotRadialValueCatalogueLayout.family_length u (outerIndex u i)
  have HD:FormulaSignSlotRadialCenterValuePacking.degree
      (FormulaSignSlotRadialValueCatalogueLayout.family u (outerIndex u i))≤FormulaSignSlotRadialValueCatalogueBounds.degreeCap u:=
    FormulaSignSlotRadialValueCatalogueBounds.degree_le u _ HF
  have HO:=Nat.size_le_size ((FormulaSignSlotRadialValueCatalogueLayout.order_le u (outerIndex u i)).trans HD)
  simp only [rawContext,FormulaSignSlotRadialValueCatalogueLayout.context_packet,pair_length,BinaryNatCode.length_encode]
  unfold rawBudget
  omega

theorem raw_degree (u:List Bool) (i:ℕ):(Raw).degree (rawContext u i)≤FormulaSignSlotRadialValueCatalogueBounds.degreeCap u:=
  FormulaSignSlotRadialValueCatalogueLayout.source_degree u (outerIndex u i)
theorem row_length (u:List Bool) (i:ℕ):(row (pair u (BinaryNatCode.encode i))).length≤rowBudget u:=by
  rw [row_packet]
  have H:=IntegralPolynomialWindowTarskiCatalogue.row_length Raw (rawContext u i)
    (FormulaSignSlotRadialValueCatalogueBounds.degreeCap u) (innerIndex u i) (raw_degree u i)
  have HR:=raw_length u i
  unfold rowBudget
  omega

theorem degree_exists:∃g:List Bool→ℕ,BinaryFn g ∧∀u z,z.length≤rowBudget u→source.degree z≤g u:=
  source_access.degree.wordEnvelope rowBudget_unary
noncomputable def degreeBound:List Bool→ℕ:=Classical.choose degree_exists
theorem degreeBound_binary:BinaryFn degreeBound:=(Classical.choose_spec degree_exists).1
theorem mass_exists:∃g:List Bool→ℕ,BinaryFn g ∧∀u z,z.length≤rowBudget u→source.mass z≤g u:=
  source_access.mass.wordEnvelope rowBudget_unary
noncomputable def massBound:List Bool→ℕ:=Classical.choose mass_exists
theorem massBound_binary:BinaryFn massBound:=(Classical.choose_spec mass_exists).1

theorem row_dimension (u:List Bool) (i:ℕ):source.arity (row (pair u (BinaryNatCode.encode i)))=
    FormulaSignSlotCenteredRadialGraph.d u+1:=by
  rw [row_packet]
  exact (IntegralPolynomialWindowTarskiCatalogue.dimension Raw centers dimension_eq (rawContext u i) (innerIndex u i)).trans
    (FormulaSignSlotRadialValueCatalogueLayout.source_arity u (outerIndex u i))
theorem row_degree (u:List Bool) (i:ℕ):source.degree (row (pair u (BinaryNatCode.encode i)))≤degreeBound u:=
  (Classical.choose_spec degree_exists).2 u _ (row_length u i)
theorem row_mass (u:List Bool) (i:ℕ):source.mass (row (pair u (BinaryNatCode.encode i)))≤massBound u:=
  (Classical.choose_spec mass_exists).2 u _ (row_length u i)

private theorem inner_count_le (u c:List Bool) (h:(Raw).degree c≤FormulaSignSlotRadialValueCatalogueBounds.degreeCap u):
    IntegralPolynomialWindowTarskiCatalogue.count Raw c≤ innerCount u:=by
  have HL:=Nat.add_le_add_right h 2
  unfold IntegralPolynomialWindowTarskiCatalogue.count IntegralPolynomialWindowTarskiCatalogue.limit innerCount
  calc
    6*(((Raw).degree c+2)*(((Raw).degree c+2)*((Raw).degree c+2)))≤
        6*((FormulaSignSlotRadialValueCatalogueBounds.degreeCap u+2)*
          ((FormulaSignSlotRadialValueCatalogueBounds.degreeCap u+2)*(FormulaSignSlotRadialValueCatalogueBounds.degreeCap u+2))):=
      Nat.mul_le_mul_left 6 (Nat.mul_le_mul HL (Nat.mul_le_mul HL HL))
    _=6*(FormulaSignSlotRadialValueCatalogueBounds.degreeCap u+2)^3:=by ring

/-- Every bounded value-family choice and every actual inner control has one
ordinal in the original-only combined catalogue, with exact byte readback. -/
theorem covers (u:List Bool) (tau deg:ℕ→ℕ)
    (ht:∀j,j<FormulaSignSlotRadialValueCatalogueBounds.coordinates u→tau j≤FormulaSignSlotRadialValueCatalogueBounds.bound u)
    (hd:∀j,j<FormulaSignSlotRadialValueCatalogueBounds.coordinates u→deg j≤FormulaSignSlotRadialValueCatalogueBounds.bound u)
    (ell:ℕ) (hell:ell≤FormulaSignSlotRadialCenterValuePacking.degree
      (FormulaSignSlotRadialValueCatalogueBounds.familyContext u tau deg))
    (r m j s d:ℕ) (hr:r<3) (hm:m<2)
    (hj:j<IntegralPolynomialWindowTarskiCatalogue.limit Raw
      (pair (FormulaSignSlotRadialValueCatalogueBounds.familyContext u tau deg) (BinaryNatCode.encode ell)))
    (hs:s<IntegralPolynomialWindowTarskiCatalogue.limit Raw
      (pair (FormulaSignSlotRadialValueCatalogueBounds.familyContext u tau deg) (BinaryNatCode.encode ell)))
    (hdeg:d<IntegralPolynomialWindowTarskiCatalogue.limit Raw
      (pair (FormulaSignSlotRadialValueCatalogueBounds.familyContext u tau deg) (BinaryNatCode.encode ell))):
    ∃i:ℕ,i<count u ∧row (pair u (BinaryNatCode.encode i))=
      pair (BinaryNatCode.encode r) (pair (IntegralPolynomialWindowTarskiCatalogue.control
        (pair (FormulaSignSlotRadialValueCatalogueBounds.familyContext u tau deg) (BinaryNatCode.encode ell))
        d s (decide (m=1))) (BinaryNatCode.encode j)):=by
  let c:=pair (FormulaSignSlotRadialValueCatalogueBounds.familyContext u tau deg) (BinaryNatCode.encode ell)
  obtain ⟨o,ho,HC⟩:=FormulaSignSlotRadialValueCatalogueLayout.covers u tau deg ht hd ell hell
  let k:=IntegralPolynomialWindowTarskiCatalogue.encode Raw c r m j s d
  have HK:k<IntegralPolynomialWindowTarskiCatalogue.count Raw c:=
    IntegralPolynomialWindowTarskiCatalogue.encode_lt Raw c r m j s d hr hm hj hs hdeg
  have HD:(Raw).degree c≤FormulaSignSlotRadialValueCatalogueBounds.degreeCap u:=by
    dsimp only [c]
    rw [←HC]
    exact FormulaSignSlotRadialValueCatalogueLayout.source_degree u o
  have HInner:k< innerCount u:=HK.trans_le (inner_count_le u c HD)
  let i:=o*innerCount u+k
  have HI:i<count u:=by
    unfold i count
    calc
      o*innerCount u+k<o*innerCount u+innerCount u:=Nat.add_lt_add_left HInner _
      _=(o+1)*innerCount u:=(Nat.succ_mul _ _).symm
      _≤FormulaSignSlotRadialValueCatalogueLayout.outerCount u*innerCount u:=Nat.mul_le_mul_right _ ho
  have HO:outerIndex u i=o:=by
    unfold outerIndex i
    rw [Nat.mul_comm o (innerCount u),Nat.add_comm,Nat.add_mul_div_left _ _ (innerCount_pos u),
      Nat.div_eq_of_lt HInner,Nat.zero_add]
  have HJ:innerIndex u i=k:=by
    unfold innerIndex i
    rw [Nat.mul_comm o (innerCount u),Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt HInner]
  refine ⟨i,HI,?_⟩
  rw [row_packet,rawContext,HO,HC,HJ]
  exact IntegralPolynomialWindowTarskiCatalogue.row_encode Raw c r m j s d hr hm hj hs hdeg

noncomputable def input:ChargedPolynomialCatalogue.Input where
  source:=source
  row:=row
  arity u:=FormulaSignSlotCenteredRadialGraph.d u+1
  count:=count
  degree:=degreeBound
  mass:=massBound
  dimension:=row_dimension
  degree_bound:=row_degree
  mass_bound:=row_mass
noncomputable def input_access:ChargedPolynomialCatalogue.Access input where
  source:=source_access
  row:=row_FP
  arity:=FormulaSignSlotSource.dimension_unary.add (UnaryFn.const 1)
  count:=count_binary
  degree:=degreeBound_binary
  mass:=massBound_binary
  fit:=IntegralPolynomialWindowTarski.degree_fit Raw centers dimension_eq
noncomputable def family:=ChargedPolynomialCatalogue.family input
noncomputable def access:SquareFeatureProductFamily.Access family:=ChargedPolynomialCatalogue.access input input_access

end LeanCanny.Encoding.FormulaSignSlotRadialValueWindowCatalogue
