/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialValueCatalogueBounds
public import LeanCanny.Algebra.FixedWidthCoordinateBinary
public import LeanCanny.Encoding.FrozenCoordinatePermutationFP
public import LeanCanny.Encoding.ChargedPolynomialCatalogue
/-! # Finite native outer contexts for the actual value radius source

Two original-dimension tables are represented by one binary rank. Entries
are clipped to the genuine coordinate bound. Every bounded numerical table
has a canonical row, without enumerating or writing the full catalogue.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialValueCatalogueLayout
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation FixedWidthPolynomial
open FormulaSignSlotRadialValueCatalogueBounds
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialCenterValuePacking.source

private theorem binary_min {f g:List Bool→ℕ} (hf:BinaryFn f) (hg:BinaryFn g):
    BinaryFn (fun q=>min (f q) (g q)):=by
  have H:BinaryFn (fun q=>if f q≤g q then f q else g q):=BinaryFn.ite (hf.le hg) hf hg
  exact H.of_eq (fun q=>by split_ifs <;> omega)

noncomputable def orderLimit (u:List Bool):=degreeCap u+1
noncomputable def tableCount (u:List Bool):=count (2*coordinates u) (blockWidth u)
noncomputable def outerCount (u:List Bool):=tableCount u*orderLimit u
noncomputable def tableRank (u:List Bool) (i:ℕ):=i/orderLimit u
noncomputable def values (tag:Bool) (u:List Bool) (i j:ℕ):=
  min (entry (blockWidth u) (tableRank u i) (j+if tag then coordinates u else 0)) (bound u)
noncomputable def family (u:List Bool) (i:ℕ):=familyContext u (values false u i) (values true u i)
noncomputable def orderIndex (u:List Bool) (i:ℕ):=
  min (i%orderLimit u) (FormulaSignSlotRadialCenterValuePacking.degree (family u i))
noncomputable def context (q:List Bool):=pair (family (pairFst q) (Nat.fromBitsLE (pairSnd q)))
  (BinaryNatCode.encode (orderIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))))

theorem orderLimit_binary:BinaryFn orderLimit:=degreeCap_binary.add (BinaryFn.const 1)
theorem tableCount_binary:BinaryFn tableCount:=
  ((BinaryFn.const 2).powUnary (((UnaryFn.const 2).mul coordinates_unary).mul blockWidth_unary)).of_eq
    (fun u=>by simp only [tableCount,count,←pow_mul,Nat.mul_comm])
theorem outerCount_binary:BinaryFn outerCount:=tableCount_binary.mul orderLimit_binary

theorem values_le (tag:Bool) (u:List Bool) (i j:ℕ):values tag u i j≤bound u:=Nat.min_le_right _ _
theorem family_length (u:List Bool) (i:ℕ):(family u i).length≤familyBudget u:=
  FormulaSignSlotRadialValueCatalogueBounds.family_length u _ _ (fun j _=>values_le false u i j) (fun j _=>values_le true u i j)
theorem family_original (u:List Bool) (i:ℕ):FormulaSignSlotRadialCenterValueLayout.original (family u i)=u:=
  FormulaSignSlotRadialValueCatalogueBounds.family_original u _ _
theorem order_le (u:List Bool) (i:ℕ):orderIndex u i≤FormulaSignSlotRadialCenterValuePacking.degree (family u i):=Nat.min_le_right _ _

private theorem table_FP (N:List Bool→ℕ) (hN:UnaryFn N) (v:List Bool→ℕ→ℕ)
    (hV:BinaryFn (fun z=>v (pairFst z) (pairSnd z).length)):
    (fun q=>table (N q) (v q))∈FP:=by
  have HE:=mem_FP_pair hV.bits_mem_FP (constFn_mem_FP [])
  apply mem_FP_of_eq (flatMap_range_mem_FP HE (hN.replicate_mem_FP true))
  intro q
  simp only [table,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    pairFst_pair,pairSnd_pair,List.length_replicate]

private theorem values_binary (tag:Bool):BinaryFn (fun z=>values tag (pairFst (pairFst z))
    (Nat.fromBitsLE (pairSnd (pairFst z))) (pairSnd z).length):=by
  have HH:BinaryFn (fun q=>Nat.fromBitsLE (pairSnd q)):=BinaryFn.fromBits pairSnd_mem_FP
  have HR:BinaryFn (fun z=>tableRank (pairFst (pairFst z)) (Nat.fromBitsLE (pairSnd (pairFst z)))):=
    (HH.div (orderLimit_binary.comp pairFst_mem_FP)).comp pairFst_mem_FP
  have HW:UnaryFn (fun z=>blockWidth (pairFst (pairFst z))):=
    blockWidth_unary.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have HB:BinaryFn (fun z=>bound (pairFst (pairFst z))):=
    bound_binary.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have HO:UnaryFn (fun z=>if tag then coordinates (pairFst (pairFst z)) else 0):=by
    cases tag
    · exact UnaryFn.const 0
    · exact coordinates_unary.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have HD:BinaryFn (fun z=>entry (blockWidth (pairFst (pairFst z)))
      (tableRank (pairFst (pairFst z)) (Nat.fromBitsLE (pairSnd (pairFst z))))
      ((pairSnd z).length+if tag then coordinates (pairFst (pairFst z)) else 0)):=
    ((HR.div ((BinaryFn.const 2).powUnary ((UnaryFn.index.add HO).mul HW))).mod
      ((BinaryFn.const 2).powUnary HW)).of_eq (fun z=>by rw [entry_eq_digit])
  exact binary_min HD HB

theorem family_FP:(fun q=>family (pairFst q) (Nat.fromBitsLE (pairSnd q)))∈FP:=by
  have HT (tag:Bool):
      (fun q=>table (coordinates (pairFst q)) (values tag (pairFst q) (Nat.fromBitsLE (pairSnd q))))∈FP:=
    table_FP (fun q=>coordinates (pairFst q)) (coordinates_unary.comp pairFst_mem_FP) _ (values_binary tag)
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair (HT false) (HT true))

theorem context_FP:context∈FP:=by
  have HI:BinaryFn (fun q=>Nat.fromBitsLE (pairSnd q)):=BinaryFn.fromBits pairSnd_mem_FP
  have HO:BinaryFn (fun q=>orderIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))):=
    binary_min (HI.mod (orderLimit_binary.comp pairFst_mem_FP))
      (FormulaSignSlotRadialCenterValuePacking.degree_binary.comp family_FP)
  exact mem_FP_pair family_FP HO.bits_mem_FP

theorem context_packet (u:List Bool) (i:ℕ):context (pair u (BinaryNatCode.encode i))=
    pair (family u i) (BinaryNatCode.encode (orderIndex u i)):=by
  simp only [context,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
theorem original_context (u:List Bool) (i:ℕ):
    FormulaSignSlotRadialCenterValueLayout.original (pairFst (context (pair u (BinaryNatCode.encode i))))=u:=by
  rw [context_packet,pairFst_pair,family_original]
theorem source_arity (u:List Bool) (i:ℕ):
    FormulaSignSlotRadialValueRadiusSource.source.arity (context (pair u (BinaryNatCode.encode i)))=
      FormulaSignSlotCenteredRadialGraph.d u+1:=by
  change FormulaSignSlotCenteredRadialGraph.d
    (FormulaSignSlotRadialCenterValueLayout.original (pairFst (context (pair u (BinaryNatCode.encode i)))))+1=_
  rw [original_context]
theorem source_degree (u:List Bool) (i:ℕ):
    FormulaSignSlotRadialValueRadiusSource.source.degree (context (pair u (BinaryNatCode.encode i)))≤degreeCap u:=by
  change FormulaSignSlotRadialCenterValuePacking.degree (pairFst (context (pair u (BinaryNatCode.encode i))))≤_
  rw [context_packet,pairFst_pair]
  exact FormulaSignSlotRadialValueCatalogueBounds.degree_le u _ (family_length u i)
theorem source_mass (u:List Bool) (i:ℕ):
    FormulaSignSlotRadialValueRadiusSource.source.mass (context (pair u (BinaryNatCode.encode i)))≤massCap u:=by
  change FormulaSignSlotRadialCenterValueMass.budget (pairFst (context (pair u (BinaryNatCode.encode i))))≤_
  rw [context_packet,pairFst_pair]
  exact FormulaSignSlotRadialValueCatalogueBounds.mass_le u _ (family_length u i)

private theorem bounded_rank (A W:ℕ) (e:ℕ→ℕ) (he:∀j,j<A→e j<2^W):
    ∃r:ℕ,r<count A W ∧∀j,j<A→entry W r j=e j:=by
  let m:=RationalSubstitution.Indexed.exponentVector A e
  have hm:∀j:Fin A,m j<2^W:=fun j=>he j.val j.isLt
  let r:=index A W m hm
  refine ⟨r.val,r.isLt,?_⟩
  intro j hj
  have H:=congrArg (fun v:Fin A→₀ℕ=>v ⟨j,hj⟩) (vector_index A W m hm)
  rw [←entry_vector A W r] at H
  exact H

private theorem table_congr (n:ℕ) (f g:ℕ→ℕ) (H:∀i,i<n→f i=g i):table n f=table n g:=by
  unfold table
  apply congrArg WordList.encode
  apply List.map_congr_left
  intro i hi
  rw [H i (List.mem_range.mp hi)]

/-- Every bounded numerical selection table and target coefficient occurs in
the finite native catalogue with its canonical WordList serialization. -/
theorem covers (u:List Bool) (tau deg:ℕ→ℕ)
    (ht:∀j,j<coordinates u→tau j≤bound u) (hd:∀j,j<coordinates u→deg j≤bound u)
    (ell:ℕ) (hell:ell≤FormulaSignSlotRadialCenterValuePacking.degree (familyContext u tau deg)):
    ∃i:ℕ,i<outerCount u ∧context (pair u (BinaryNatCode.encode i))=
      pair (familyContext u tau deg) (BinaryNatCode.encode ell):=by
  let f:ℕ→ℕ:=fun j=>if j<coordinates u then tau j else deg (j-coordinates u)
  have HF:∀j,j<2*coordinates u→f j<2^blockWidth u:=by
    intro j hj
    apply lt_of_le_of_lt _ (bound_fit u)
    dsimp only [f]
    split_ifs with HJ
    · exact ht j HJ
    · exact hd _ (by omega)
  obtain ⟨r,hr,HE⟩:=bounded_rank (2*coordinates u) (blockWidth u) f HF
  have hL:0<orderLimit u:=Nat.zero_lt_succ _
  have hEll:ell<orderLimit u:=by
    have HG:=FormulaSignSlotRadialValueCatalogueBounds.degree_le u _
      (FormulaSignSlotRadialValueCatalogueBounds.family_length u tau deg ht hd)
    unfold orderLimit
    omega
  let i:=r*orderLimit u+ell
  have HI:i<outerCount u:=by
    unfold i outerCount
    calc
      r*orderLimit u+ell<r*orderLimit u+orderLimit u:=Nat.add_lt_add_left hEll _
      _=(r+1)*orderLimit u:=(Nat.succ_mul _ _).symm
      _≤tableCount u*orderLimit u:=Nat.mul_le_mul_right _ hr
  have HDiv:i/orderLimit u=r:=by
    dsimp only [i]
    rw [Nat.mul_comm r (orderLimit u),Nat.add_comm,Nat.add_mul_div_left _ _ hL,
      Nat.div_eq_of_lt hEll,Nat.zero_add]
  have HMod:i%orderLimit u=ell:=by
    dsimp only [i]
    rw [Nat.mul_comm r (orderLimit u),Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hEll]
  have HT:∀j,j<coordinates u→values false u i j=tau j:=by
    intro j hj
    change min (entry (blockWidth u) (i/orderLimit u) j) (bound u)=_
    rw [HDiv,HE j (by omega)]
    simpa only [f,ite_eq_left hj] using Nat.min_eq_left (ht j hj)
  have HD:∀j,j<coordinates u→values true u i j=deg j:=by
    intro j hj
    change min (entry (blockWidth u) (i/orderLimit u) (j+coordinates u)) (bound u)=_
    rw [HDiv,HE (j+coordinates u) (by omega)]
    have HJ:¬j+coordinates u<coordinates u:=by omega
    simpa only [f,ite_eq_right HJ,Nat.add_sub_cancel_right] using Nat.min_eq_left (hd j hj)
  have HFamily:family u i=familyContext u tau deg:=by
    unfold family familyContext
    exact congrArg (fun ts=>pair u ts) (congrArg₂ pair
      (table_congr (coordinates u) _ tau HT) (table_congr (coordinates u) _ deg HD))
  have HOrder:orderIndex u i=ell:=by
    unfold orderIndex
    rw [HMod,HFamily,Nat.min_eq_left hell]
  exact ⟨i,HI,by rw [context_packet,HFamily,HOrder]⟩

noncomputable def input:ChargedPolynomialCatalogue.Input where
  source:=FormulaSignSlotRadialValueRadiusSource.source
  row:=context
  arity u:=FormulaSignSlotCenteredRadialGraph.d u+1
  count:=outerCount
  degree:=degreeCap
  mass:=massCap
  dimension:=source_arity
  degree_bound:=source_degree
  mass_bound:=source_mass
noncomputable def input_access:ChargedPolynomialCatalogue.Access input where
  source:=FormulaSignSlotRadialValueRadiusSource.access
  row:=context_FP
  arity:=FormulaSignSlotSource.dimension_unary.add (UnaryFn.const 1)
  count:=outerCount_binary
  degree:=degreeCap_binary
  mass:=massCap_binary
  fit:=FormulaSignSlotRadialValueRadiusSource.degree_fit
noncomputable def catalogue:=ChargedPolynomialCatalogue.family input
noncomputable def catalogue_access:SquareFeatureProductFamily.Access catalogue:=
  ChargedPolynomialCatalogue.access input input_access

end LeanCanny.Encoding.FormulaSignSlotRadialValueCatalogueLayout
