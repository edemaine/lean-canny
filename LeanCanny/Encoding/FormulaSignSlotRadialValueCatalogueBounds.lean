/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialValueRadiusSource
public import LeanCanny.Computation.WordResourceEnvelope
/-! # Original-input profiles for all bounded value-system tables -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialValueCatalogueBounds
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialFormalEliminant.eliminant

noncomputable def coordinates (u:List Bool):=FormulaSignSlotRadialFormalInput.spatial u
noncomputable def bound (u:List Bool):=FormulaSignSlotRadialCenterValueSelection.bound u
noncomputable def blockWidth (u:List Bool):=(bound u).size

theorem coordinates_unary:UnaryFn coordinates:=FormulaSignSlotRadialFormalInput.spatial_unary
theorem bound_binary:BinaryFn bound:=by
  have H:BinaryFn (fun u=>FormulaSignSlotRadialCenterValuePacking.inputBound (pair u [])):=
    FormulaSignSlotRadialCenterValuePacking.inputBound_binary.comp
    (mem_FP_pair id_mem_FP (constFn_mem_FP []))
  exact H.of_eq (fun u=>by simp only [FormulaSignSlotRadialCenterValuePacking.inputBound,
    FormulaSignSlotRadialCenterValueLayout.original,pairFst_pair];rfl)
theorem blockWidth_unary:UnaryFn blockWidth:=
  (UnaryFn.length bound_binary.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
theorem bound_fit (u:List Bool):bound u<2^blockWidth u:=Nat.lt_size_self _

noncomputable def table (n:ℕ) (v:ℕ→ℕ):=WordList.encode ((List.range n).map (fun i=>BinaryNatCode.encode (v i)))
noncomputable def familyContext (u:List Bool) (tau deg:ℕ→ℕ):=
  pair u (pair (table (coordinates u) tau) (table (coordinates u) deg))

theorem table_lookup (n:ℕ) (v:ℕ→ℕ) (i:ℕ) (hi:i<n):
    Nat.fromBitsLE (WordList.get (table n v) i)=v i:=by
  simp only [table,WordList.get_encode,List.getElem?_map,List.getElem?_range hi,
    Option.map_some,Option.getD_some,BinaryNatCode.encode,Nat.fromBitsLE_bits]
theorem family_original (u:List Bool) (tau deg:ℕ→ℕ):
    FormulaSignSlotRadialCenterValueLayout.original (familyContext u tau deg)=u:=by
  simp only [familyContext,FormulaSignSlotRadialCenterValueLayout.original,pairFst_pair]
theorem family_tau (u:List Bool) (tau deg:ℕ→ℕ) (i:ℕ) (hi:i<coordinates u):
    FormulaSignSlotRadialCenterValueLayout.tau (familyContext u tau deg) i=tau i:=by
  simp only [FormulaSignSlotRadialCenterValueLayout.tau,FormulaSignSlotRadialCenterValueLayout.tauTable,
    familyContext,pairFst_pair,pairSnd_pair,table_lookup _ _ _ hi]
theorem family_degree (u:List Bool) (tau deg:ℕ→ℕ) (i:ℕ) (hi:i<coordinates u):
    FormulaSignSlotRadialCenterValueLayout.degree (familyContext u tau deg) i=deg i:=by
  simp only [FormulaSignSlotRadialCenterValueLayout.degree,FormulaSignSlotRadialCenterValueLayout.degreeTable,
    familyContext,pairSnd_pair,table_lookup _ _ _ hi]

noncomputable def familyBudget (u:List Bool):=2*u.length+3*((2*blockWidth u+2)*coordinates u)+4
theorem familyBudget_unary:UnaryFn familyBudget:=
  (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add
    ((UnaryFn.const 3).mul ((((UnaryFn.const 2).mul blockWidth_unary).add (UnaryFn.const 2)).mul coordinates_unary))).add (UnaryFn.const 4)

private theorem table_length (n B:ℕ) (v:ℕ→ℕ) (hv:∀i,i<n→v i≤B):
    (table n v).length≤(2*B.size+2)*n:=by
  apply (WordList.length_le _ B.size ?_).trans_eq
    (congrArg (fun a=> (2*B.size+2)*a) (by simp only [List.length_map,List.length_range]))
  intro w hw
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw
  rw [BinaryNatCode.length_encode]
  exact Nat.size_le_size (hv i (List.mem_range.mp hi))

theorem family_length (u:List Bool) (tau deg:ℕ→ℕ)
    (ht:∀i,i<coordinates u→tau i≤bound u) (hd:∀i,i<coordinates u→deg i≤bound u):
    (familyContext u tau deg).length≤familyBudget u:=by
  have HT:=table_length (coordinates u) (bound u) tau ht
  have HD:=table_length (coordinates u) (bound u) deg hd
  simp only [familyContext,pair_length]
  unfold familyBudget blockWidth
  omega

theorem degree_exists:∃g:List Bool→ℕ,BinaryFn g ∧∀u c,c.length≤familyBudget u→
    FormulaSignSlotRadialCenterValuePacking.degree c≤g u:=
  FormulaSignSlotRadialCenterValuePacking.degree_binary.wordEnvelope familyBudget_unary
noncomputable def degreeCap:List Bool→ℕ:=Classical.choose degree_exists
theorem degreeCap_binary:BinaryFn degreeCap:=(Classical.choose_spec degree_exists).1
theorem degree_le (u c:List Bool) (hc:c.length≤familyBudget u):
    FormulaSignSlotRadialCenterValuePacking.degree c≤degreeCap u:=
  (Classical.choose_spec degree_exists).2 u c hc

theorem mass_exists:∃g:List Bool→ℕ,BinaryFn g ∧∀u c,c.length≤familyBudget u→
    FormulaSignSlotRadialCenterValueMass.budget c≤g u:=
  FormulaSignSlotRadialCenterValueMass.budget_binary.wordEnvelope familyBudget_unary
noncomputable def massCap:List Bool→ℕ:=Classical.choose mass_exists
theorem massCap_binary:BinaryFn massCap:=(Classical.choose_spec mass_exists).1
theorem mass_le (u c:List Bool) (hc:c.length≤familyBudget u):
    FormulaSignSlotRadialCenterValueMass.budget c≤massCap u:=
  (Classical.choose_spec mass_exists).2 u c hc

/-- The parameter-degree allowance also dominates the actual target degree.
No exact-degree, nonvanishing or selected-center premise is needed. -/
theorem target_degree (c:List Bool):(FormulaSignSlotRadialCenterValuePacking.source c).natDegree≤
    FormulaSignSlotRadialCenterValuePacking.degree c:=by
  have HT:=RelativeAffineGridValueGram.degree_le
    (FormulaSignSlotRadialCenterValueFamily.input (FormulaSignSlotRadialCenterValueLayout.original c)
      (fun i=>FormulaSignSlotRadialCenterValueLayout.tau c i.val)
      (fun i=>FormulaSignSlotRadialCenterValueLayout.degree c i.val))
    (FormulaSignSlotRadialFormalCenter.polynomial (FormulaSignSlotRadialCenterValueLayout.original c))
    (fun i=>FormulaSignSlotRadialCenterValueLayout.degree c i.val)
    (FormulaSignSlotCenteredRadialLimits.degreeBudget (FormulaSignSlotRadialCenterValueLayout.original c)+1)
  have H: (FormulaSignSlotRadialCenterValuePacking.source c).natDegree≤
      FormulaSignSlotRadialCenterValuePacking.dimension c+1:=by
    simpa only [FormulaSignSlotRadialCenterValuePacking.source,FormulaSignSlotRadialCenterValueFamily.polynomial,
      FormulaSignSlotRadialCenterValuePacking.dimension,FormulaSignSlotRadialCenterValuePacking.spatial_width,
      FormulaSignSlotRadialCenterValueLayout.arity,FormulaSignSlotRadialCenterValueLayout.testDegree,
      FormulaSignSlotRadialFormalInput.spatial] using HT
  have HP:0<FormulaSignSlotRadialCenterValuePacking.dimension c:=by
    unfold FormulaSignSlotRadialCenterValuePacking.dimension RelativeProjectiveValueGram.dimension FixedWidthPolynomial.count
    exact Nat.mul_pos (by omega) (pow_pos (Nat.two_pow_pos _) _)
  apply H.trans
  unfold FormulaSignSlotRadialCenterValuePacking.degree
  calc
    FormulaSignSlotRadialCenterValuePacking.dimension c+1≤
        FormulaSignSlotRadialCenterValuePacking.dimension c+FormulaSignSlotRadialCenterValuePacking.dimension c:=
      Nat.add_le_add_left HP _
    _=FormulaSignSlotRadialCenterValuePacking.dimension c*2:=(Nat.mul_two _).symm
    _≤_:=Nat.mul_le_mul_left _ (by omega)

theorem coefficient_zero (c:List Bool) (ell:ℕ) (h:FormulaSignSlotRadialCenterValuePacking.degree c<ell):
    (FormulaSignSlotRadialCenterValuePacking.source c).coeff ell=0:=
  Polynomial.coeff_eq_zero_of_natDegree_lt ((target_degree c).trans_lt h)

end LeanCanny.Encoding.FormulaSignSlotRadialValueCatalogueBounds
