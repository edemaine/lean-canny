/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankPolynomialSpace
public import LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest
/-! # One actual bank sampler with integer polynomial selected only by datum -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankPolynomialSource
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedBankSnapshotBits (atKey)
open IntegralFramedBankPolynomialModel (Source Access polynomial degree mass allowance coordinateMass)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def canonical (z : List Bool) := pair (pairFst z) (pairSnd z)
theorem canonical_FP : canonical ∈ FP := mem_FP_pair pairFst_mem_FP pairSnd_mem_FP

noncomputable def source (S : Source) (B : Bank) (read refs : List Bool → List Bool) :
    SquareSampleCompleteSuffixPolynomialTest.Source (IntegralFramedBankQuery.input B) where
  arity c _ := (atKey B.parameters B.plan B.data (B.key c)).count
  newer _ _ := 0
  polynomial := polynomial S B read refs
  degree := degree S B read
  mass := mass S B read
  dimension _ _ := Nat.zero_add _
  polynomial_degree := IntegralFramedBankPolynomialModel.degree_bound S B read refs
  polynomial_mass := IntegralFramedBankPolynomialModel.mass_bound S B read refs

private def queryBase (u : List Bool) := pairFst (pairFst u)
private theorem queryBase_FP : queryBase ∈ FP := by polytime [queryBase]
private noncomputable def queryBank (B : Bank) : Bank where
  parameters := B.parameters
  plan := B.plan
  data := B.data
  nodes := B.nodes
  factor := B.factor
  seed := B.seed
  bounds := B.bounds
  key u := B.key (queryBase u)
  positive u := B.positive (queryBase u)
  coordinate u := B.coordinate (queryBase u)
private noncomputable def queryBank_access (B : Bank) (h : IntegralFramedBankQuery.Access B) :
    IntegralFramedBankQuery.Access (queryBank B) where
  parameters := h.parameters
  liftedData := h.liftedData
  controls := h.controls
  bounds := h.bounds
  nodes := h.nodes
  factor := h.factor
  seed := h.seed
  key := mem_FP_comp (f := queryBase) (g := B.key) queryBase_FP h.key
  coordinate := h.coordinate.comp queryBase_FP

theorem coefficient_evaluator (S : Source) (A : Access S) (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (read refs : List Bool → List Bool) (hr : read ∈ FP) (hf : refs ∈ FP) :
    SpaceFunction (SquareSampleCompleteSuffixPolynomialTest.coefficient (source S B read refs)) := by
  let ctx := RationalSubstitution.IntegerBits.context
  let origin := fun q => canonical (ctx q)
  have HO : origin ∈ FP := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP canonical_FP
  have HS : (read ∘ origin) ∈ FP := mem_FP_comp HO hr
  have HF : (refs ∘ queryBase) ∈ FP := mem_FP_comp queryBase_FP hf
  have E := IntegralFramedBankPolynomialSpace.row_evaluator S A (queryBank B) (queryBank_access B h)
    (read ∘ origin) (refs ∘ queryBase) RationalSubstitution.IntegerBits.selectedDegree pairSnd
    HS HF RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  apply E.congr
  funext q
  rfl

theorem access (S : Source) (A : Access S) (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (read refs : List Bool → List Bool) (hr : read ∈ FP) (hf : refs ∈ FP) : (source S B read refs).Access := by
  have HS : (read ∘ canonical) ∈ FP := mem_FP_comp canonical_FP hr
  have HD : BinaryFn (fun z => degree S B read (pairFst z) (pairSnd z)) :=
    BinaryFn.mul (A.degree.comp HS) ((IntegralMixedFramedBankTermBits.maxPower_binary B.parameters h.parameters
      B.plan B.data).comp (mem_FP_comp pairFst_mem_FP h.key))
  have HG : BinaryFn (fun z => coordinateMass B (pairFst z)) :=
    (IntegralMixedFramedBankTermBits.coordinateMass_binary B.parameters h.parameters B.plan B.data
      h.nodes h.factor h.seed).comp (mem_FP_comp pairFst_mem_FP h.key)
  have HA := A.arity.comp HS
  have HW := A.width.comp HS
  have HB : BinaryFn (fun z => allowance S read (pairFst z) (pairSnd z)) :=
    (BinaryFn.ofUnary HA).mul ((BinaryFn.const 2).mul ((BinaryFn.const 2).powUnary HW))
  exact ⟨UnaryFn.const 0, HD, BinaryFn.add (A.mass.comp HS) (HG.mul HB), coefficient_evaluator S A B h read refs hr hf⟩

end LeanCanny.Encoding.IntegralFramedBankPolynomialSource
