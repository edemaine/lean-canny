/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialPrincipalWindowBounds
public import LeanCanny.Encoding.FormulaSignSlotRadialCutWindowSources
/-! # Every bounded original PSC and its actual interval-query controls

Original perturbation/degree/order controls are finite. Inner rows retain
the actual raw-source degree box; excess outer-budget ordinals repeat rows.
All original resource caps follow from the constructed native readers.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialPrincipalWindowCatalogue
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S"=>FormulaSignSlotRadialPrincipalRadiusSource.source
local notation "W"=>FormulaSignSlotRadialCutWindowSources.principalSource

attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial
noncomputable def outerLimit (u:List Bool):=FormulaSignSlotRadialPrincipalWindowBounds.bound u+1
noncomputable def orderLimit (u:List Bool):=2*FormulaSignSlotRadialPrincipalWindowBounds.bound u+2
noncomputable def innerLimit (u:List Bool):=FormulaSignSlotRadialPrincipalWindowBounds.innerCount u
noncomputable def count (u:List Bool):=outerLimit u*(outerLimit u*(orderLimit u*innerLimit u))
noncomputable def innerIndex (u:List Bool) (i:ℕ):=i%innerLimit u
noncomputable def orderIndex (u:List Bool) (i:ℕ):=i/innerLimit u%orderLimit u
noncomputable def declaredIndex (u:List Bool) (i:ℕ):=i/innerLimit u/orderLimit u%outerLimit u
noncomputable def tauIndex (u:List Bool) (i:ℕ):=i/innerLimit u/orderLimit u/outerLimit u%outerLimit u
noncomputable def raw (u:List Bool) (i:ℕ):=FormulaSignSlotRadialPrincipalWindowBounds.rawContext u
  (tauIndex u i) (declaredIndex u i) (orderIndex u i)
noncomputable def row (q:List Bool):=IntegralPolynomialWindowTarskiCatalogue.row S
  (pair (raw (pairFst q) (Nat.fromBitsLE (pairSnd q)))
    (BinaryNatCode.encode (innerIndex (pairFst q) (Nat.fromBitsLE (pairSnd q)))))
noncomputable def arity (u:List Bool):=FormulaSignSlotSource.dimension (pairFst u)+1

theorem outerLimit_binary:BinaryFn outerLimit:=FormulaSignSlotRadialPrincipalWindowBounds.bound_binary.add (BinaryFn.const 1)
theorem orderLimit_binary:BinaryFn orderLimit:=((BinaryFn.const 2).mul
  FormulaSignSlotRadialPrincipalWindowBounds.bound_binary).add (BinaryFn.const 2)
theorem innerLimit_binary:BinaryFn innerLimit:=FormulaSignSlotRadialPrincipalWindowBounds.innerCount_binary
theorem count_binary:BinaryFn count:=outerLimit_binary.mul
  (outerLimit_binary.mul (orderLimit_binary.mul innerLimit_binary))
theorem arity_unary:UnaryFn arity:=(FormulaSignSlotSource.dimension_unary.comp pairFst_mem_FP).add (UnaryFn.const 1)

theorem row_packet (u:List Bool) (i:ℕ):row (pair u (BinaryNatCode.encode i))=
    IntegralPolynomialWindowTarskiCatalogue.row S (pair (raw u i) (BinaryNatCode.encode (innerIndex u i))):=by
  simp only [row,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
theorem tau_le (u:List Bool) (i:ℕ):tauIndex u i ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound u:=
  Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.zero_lt_succ _))
theorem declared_le (u:List Bool) (i:ℕ):declaredIndex u i ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound u:=
  Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.zero_lt_succ _))
theorem order_le (u:List Bool) (i:ℕ):orderIndex u i ≤ 2*FormulaSignSlotRadialPrincipalWindowBounds.bound u+1:=
  Nat.le_of_lt_succ (Nat.mod_lt _ (by unfold orderLimit;omega))
theorem row_length (u:List Bool) (i:ℕ):
    (row (pair u (BinaryNatCode.encode i))).length ≤ FormulaSignSlotRadialPrincipalWindowBounds.queryBudget u:=by
  rw [row_packet]
  exact FormulaSignSlotRadialPrincipalWindowBounds.row_length u _ _ _ _ (tau_le u i) (declared_le u i) (order_le u i)

theorem raw_dimension (u:List Bool) (i:ℕ):(S).arity (raw u i)=arity u:=by
  simp only [FormulaSignSlotRadialPrincipalRadiusSource.source,FormulaSignSlotRadialPrincipalRadiusSource.arity,
    FormulaSignSlotRadialPrincipalRadiusSource.family,FormulaSignSlotRadialCenterPrincipalFamily.arity,
    FormulaSignSlotRadialCenterPrincipalFamily.original,raw,FormulaSignSlotRadialPrincipalWindowBounds.rawContext,pairFst_pair]
  rfl
theorem dimension (u:List Bool) (i:ℕ):(W).arity (row (pair u (BinaryNatCode.encode i)))=arity u:=by
  rw [row_packet]
  exact (IntegralPolynomialWindowTarskiCatalogue.dimension S FormulaSignSlotRadialCutWindowSources.principalCenters
    FormulaSignSlotRadialCutWindowSources.principal_dimension (raw u i) (innerIndex u i)).trans (raw_dimension u i)

theorem degree_exists:∃g:List Bool→ℕ,BinaryFn g ∧∀u z,z.length ≤ FormulaSignSlotRadialPrincipalWindowBounds.queryBudget u→
    (W).degree z ≤ g u:=FormulaSignSlotRadialCutWindowSources.principalAccess.degree.wordEnvelope
      FormulaSignSlotRadialPrincipalWindowBounds.queryBudget_unary
noncomputable def degree:List Bool→ℕ:=Classical.choose degree_exists
theorem degree_binary:BinaryFn degree:=(Classical.choose_spec degree_exists).1
theorem degree_bound (u:List Bool) (i:ℕ):(W).degree (row (pair u (BinaryNatCode.encode i))) ≤ degree u:=
  (Classical.choose_spec degree_exists).2 u _ (row_length u i)
theorem mass_exists:∃g:List Bool→ℕ,BinaryFn g ∧∀u z,z.length ≤ FormulaSignSlotRadialPrincipalWindowBounds.queryBudget u→
    (W).mass z ≤ g u:=FormulaSignSlotRadialCutWindowSources.principalAccess.mass.wordEnvelope
      FormulaSignSlotRadialPrincipalWindowBounds.queryBudget_unary
noncomputable def mass:List Bool→ℕ:=Classical.choose mass_exists
theorem mass_binary:BinaryFn mass:=(Classical.choose_spec mass_exists).1
theorem mass_bound (u:List Bool) (i:ℕ):(W).mass (row (pair u (BinaryNatCode.encode i))) ≤ mass u:=
  (Classical.choose_spec mass_exists).2 u _ (row_length u i)

theorem row_FP:row∈FP:=by
  have HI:BinaryFn (fun q=>Nat.fromBitsLE (pairSnd q)):=BinaryFn.fromBits pairSnd_mem_FP
  have HK:=innerLimit_binary.comp pairFst_mem_FP
  have HJ:=orderLimit_binary.comp pairFst_mem_FP
  have HD:=outerLimit_binary.comp pairFst_mem_FP
  have HInner:BinaryFn (fun q=>innerIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))):=HI.mod HK
  have HOrder:BinaryFn (fun q=>orderIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))):=(HI.div HK).mod HJ
  have HDeclared:BinaryFn (fun q=>declaredIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))):=((HI.div HK).div HJ).mod HD
  have HTau:BinaryFn (fun q=>tauIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))):=(((HI.div HK).div HJ).div HD).mod HD
  have HR:(fun q=>raw (pairFst q) (Nat.fromBitsLE (pairSnd q)))∈FP:=
    mem_FP_pair (mem_FP_pair pairFst_mem_FP (mem_FP_pair HTau.bits_mem_FP HDeclared.bits_mem_FP)) HOrder.bits_mem_FP
  exact mem_FP_comp (mem_FP_pair HR HInner.bits_mem_FP)
    (IntegralPolynomialWindowTarskiCatalogue.row_FP S FormulaSignSlotRadialPrincipalRadiusSource.access)

theorem source_fit (z:List Bool):(W).degree z<2^(W).width z:=
  IntegralPolynomialWindowTarski.degree_fit S FormulaSignSlotRadialCutWindowSources.principalCenters
    FormulaSignSlotRadialCutWindowSources.principal_dimension z
noncomputable def input:ChargedPolynomialCatalogue.Input where
  source:=W
  row:=row
  arity:=arity
  count:=count
  degree:=degree
  mass:=mass
  dimension:=dimension
  degree_bound:=degree_bound
  mass_bound:=mass_bound
noncomputable def family:=ChargedPolynomialCatalogue.family input
noncomputable def input_access:ChargedPolynomialCatalogue.Access input where
  source:=FormulaSignSlotRadialCutWindowSources.principalAccess
  row:=row_FP
  arity:=arity_unary
  count:=count_binary
  degree:=degree_binary
  mass:=mass_binary
  fit:=source_fit
noncomputable def access:SquareFeatureProductFamily.Access family:=ChargedPolynomialCatalogue.access input input_access

end LeanCanny.Encoding.FormulaSignSlotRadialPrincipalWindowCatalogue
