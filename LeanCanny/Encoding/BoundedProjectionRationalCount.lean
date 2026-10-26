/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionRootCount
public import LeanCanny.Algebra.RationalCutSpace

/-! # Native counts of projection roots below a rational threshold

The source context is the first field; the second carries a signed rational
cut as two natural numerators and a denominator minus one. The only root
coefficient reader is the already constructed reader for the selected source.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionRationalCount
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets MatrixPower
open scoped Classical
attribute [local irreducible] BoundedCriticalProjection.polynomial

noncomputable def family (P : Readers) : SignPatternBits.Family where
  root := BoundedCriticalProjection.polynomial (P.comp pairFst)
  polynomial c _ := RationalCutBits.polynomial c
  pattern _ _ := .neg
  count _ := BinaryNatCode.encode 1
  rootDegree c := BinaryNatCode.encode (BoundedProjectionRootCount.degree (P.comp pairFst) c)
  degree _ := BinaryNatCode.encode 1
  rootMass c := BinaryNatCode.encode (BoundedProjectionRootCount.massExponent (P.comp pairFst) c)
  mass c := BinaryNatCode.encode (RationalCutBits.massExponent c)
  rootDegree_pos c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact pow_pos (by decide) _
  root_degree c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact BoundedCriticalProjection.polynomial_degree (P.comp pairFst) c
  root_mass c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact BoundedProjectionRootCount.mass_bound (P.comp pairFst) c
  polynomial_degree c _ _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact RationalCutBits.polynomial_degree c
  polynomial_mass c _ _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact RationalCutBits.polynomial_mass c

theorem family_polyTime {P : Readers} (h : P.PolyTime) : SignPatternBits.ControlsPolyTime (family P) := by
  refine ⟨constFn_mem_FP _, ?_,
    (BoundedProjectionRootCount.degree_binary (h.comp pairFst_mem_FP)).bits_mem_FP,
    constFn_mem_FP _,
    (BoundedProjectionRootCount.massExponent_binary (h.comp pairFst_mem_FP)).bits_mem_FP,
    bits_mem_FP RationalCutBits.massExponent_unary⟩
  exact UnaryFn.const 1

def cutQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pairSnd (pairSnd (pairFst q)))) (pairSnd q)

theorem cutQuery_FP : cutQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def access (P : Readers) : SignPatternBits.Access (family P) where
  rootCoefficient := BoundedProjectionRootCount.coefficient (P.comp pairFst)
  polynomialCoefficient := RationalCutBits.coefficient ∘ cutQuery
  pattern _ := [true]
  root_eq := BoundedProjectionRootCount.coefficient_packet (P.comp pairFst)
  polynomial_eq c _ _ k m hm := by
    simp only [Function.comp_apply, cutQuery, pairFst_pair, pairSnd_pair]
    exact RationalCutBits.coefficient_packet c k m hm
  pattern_eq _ _ := rfl

noncomputable def count (P : Readers) (c : List Bool) : ℕ :=
  ((BoundedCriticalLabels.rootSet P (pairFst c)).filter (fun t => t < RationalCutBits.threshold c)).card

theorem family_count (P : Readers) (c : List Bool) : SignPatternBits.rootCount (family P) c = count P c := by
  simp only [SignPatternBits.rootCount, family, RootSignQueries.signCount,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, RationalCutBits.sign_neg_iff, forall_const,
    BoundedProjectionRootCount.polynomial_comp, count, BoundedCriticalLabels.rootSet]
  rw [algebraMap_int_eq]

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => BinaryNatCode.encode (count P c)) := by
  have H := BoundedProjectionRootCount.coefficient_evaluator (h.comp pairFst_mem_FP) (fun q => ha (pairFst q))
  have Q := SpaceFunction.ofFP _ (mem_FP_comp cutQuery_FP RationalCutBits.coefficient_FP)
  have E := SignPatternBits.rootCountEvaluator (access P) (family_polyTime h) (constFn_mem_FP [true]) H Q
  exact E.congr (funext fun c => congrArg BinaryNatCode.encode (family_count P c))

theorem count_le (P : Readers) (c : List Bool) :
    count P c ≤ BoundedProjectionRootCount.count P (pairFst c) := Finset.card_filter_le _ _

/-- A sample lies below a cut exactly when its ordered label is below the
native count at that cut. This remains true when the polynomial has extraneous roots. -/
theorem rank_lt_count_iff (P : Readers) (c : List Bool)
    (x : BoundedFullCriticalSamples.Samples P (pairFst c)) :
    BoundedCriticalLabels.rank P (pairFst c) x < count P c ↔
      BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) (pairFst c) x.val <
        RationalCutBits.threshold c := by
  rw [BoundedProjectionRootCount.rank_eq_card_below]
  let s := BoundedCriticalLabels.rootSet P (pairFst c)
  let v := BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) (pairFst c) x.val
  have hv : v ∈ s := (BoundedCriticalLabels.projectedRoot P (pairFst c) x).property
  change (s.filter (fun t => t < v)).card < (s.filter (fun t => t < RationalCutBits.threshold c)).card ↔
    v < RationalCutBits.threshold c
  constructor
  · intro hr
    by_contra hx
    have hsub : s.filter (fun t => t < RationalCutBits.threshold c) ⊆ s.filter (fun t => t < v) := by
      intro t ht
      obtain ⟨hs, ht⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨hs, ht.trans_le (le_of_not_gt hx)⟩
    exact (not_lt_of_ge (Finset.card_le_card hsub)) hr
  · intro hx
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro t ht
      obtain ⟨hs, ht⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨hs, ht.trans hx⟩
    · intro he
      have hmem : v ∈ s.filter (fun t => t < RationalCutBits.threshold c) := Finset.mem_filter.mpr ⟨hv, hx⟩
      rw [← he] at hmem
      exact lt_irrefl v (Finset.mem_filter.mp hmem).2

/-- Fixed-width root labels below the rational cut. Extraneous projection
roots are retained, consistently with the ordered sample-label convention. -/
def belowLanguage (P : Readers) : Language :=
  {q | (pairSnd q).length = BoundedCriticalProjection.labelWidth P (pairFst (pairFst q)) ∧
    Nat.fromBitsLE (pairSnd q) < count P (pairFst q)}

noncomputable def compare (P : Readers) (z : List Bool) : Bool :=
  decide ((pairSnd (pairFst z)).length = BoundedCriticalProjection.labelWidth P (pairFst (pairFst (pairFst z))) ∧
    Nat.fromBitsLE (pairSnd (pairFst z)) < Nat.fromBitsLE (pairSnd z))

theorem compare_FP {P : Readers} (h : P.PolyTime) : (fun z => [compare P z]) ∈ FP := by
  have hl := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hs := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
  have hw := (BoundedCriticalProjection.labelWidth_unary h).comp hs
  have hi := BinaryFn.fromBits hl
  have hn := BinaryFn.fromBits pairSnd_mem_FP
  exact ((FPPred.eq (UnaryFn.length hl) hw).and (hi.lt hn)).flag_mem_FP

theorem belowDecider {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (belowLanguage P) := by
  have E := ((evaluator h ha).precompose pairFst pairFst_mem_FP).withInput
  apply E.decider (compare P) (compare_FP h)
  intro q
  simp only [compare, belowLanguage, Set.mem_ofPred_eq, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem below_mem_PSPACE {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : belowLanguage P ∈ PSPACE :=
  (belowDecider h ha).mem_PSPACE

theorem label_below_iff (P : Readers) (c : List Bool)
    (x : BoundedFullCriticalSamples.Samples P (pairFst c)) :
    pair c (BoundedCriticalLabels.label P (pairFst c) x) ∈ belowLanguage P ↔
      BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) (pairFst c) x.val <
        RationalCutBits.threshold c := by
  simp only [belowLanguage, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair,
    BoundedCriticalLabels.label_length, BoundedCriticalLabels.label_value, true_and]
  exact rank_lt_count_iff P c x

end LeanCanny.Encoding.BoundedProjectionRationalCount
