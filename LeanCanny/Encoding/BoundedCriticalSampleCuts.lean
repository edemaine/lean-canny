/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleLabels
public import LeanCanny.Algebra.SignPatternComposition
public import LeanCanny.Algebra.RationalCutSpace

/-! # Native rational-cut comparisons for exact critical-sample labels

The cut is appended to all original critical-equation filters. Native counts
therefore compare short ordered sample labels with rational thresholds while
retaining exact sample validity, including empty sources and threshold roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleCuts
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open SignPatternBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter
  BoundedCriticalSampleCount.family SignPatternBits.rootCount BoundedCriticalFilters.polynomial PrimitivePairBits.coefficient
  RationalCutBits.coefficient

noncomputable def cutFamily (P : Readers) : Family where
  root := ((BoundedCriticalSampleCount.family P).comp pairFst).root
  rootDegree := ((BoundedCriticalSampleCount.family P).comp pairFst).rootDegree
  rootMass := ((BoundedCriticalSampleCount.family P).comp pairFst).rootMass
  rootDegree_pos := ((BoundedCriticalSampleCount.family P).comp pairFst).rootDegree_pos
  root_degree := ((BoundedCriticalSampleCount.family P).comp pairFst).root_degree
  root_mass := ((BoundedCriticalSampleCount.family P).comp pairFst).root_mass
  polynomial c _ := RationalCutBits.polynomial c
  pattern _ _ := .neg
  count _ := BinaryNatCode.encode 1
  degree _ := BinaryNatCode.encode 1
  mass c := BinaryNatCode.encode (RationalCutBits.massExponent c)
  polynomial_degree c _ _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact RationalCutBits.polynomial_degree c
  polynomial_mass c _ _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact RationalCutBits.polynomial_mass c

theorem cut_controls {P : Readers} (h : P.PolyTime) : ControlsPolyTime (cutFamily P) := by
  have H := comp_controls (BoundedCriticalSampleCount.controls h) pairFst_mem_FP
  refine ⟨constFn_mem_FP _, ?_, H.rootDegree, constFn_mem_FP _, H.rootMass, bits_mem_FP RationalCutBits.massExponent_unary⟩
  exact UnaryFn.const 1

def cutQuery (q : List Bool) : List Bool := pair (pair (SignPatternBits.original q)
  (pairSnd (SignPatternBits.queryIndex q))) (pairSnd q)
theorem cutQuery_FP : cutQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair original_mem_FP (mem_FP_comp queryIndex_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def cutAccess (P : Readers) : Access (cutFamily P) where
  rootCoefficient := ((BoundedCriticalSampleCount.access P).comp pairFst).rootCoefficient
  polynomialCoefficient := RationalCutBits.coefficient ∘ cutQuery
  pattern _ := InfinitesimalSign.encode .neg
  root_eq := ((BoundedCriticalSampleCount.access P).comp pairFst).root_eq
  polynomial_eq c _ _ k m hm := by
    simp only [Function.comp_apply, cutQuery, SignPatternBits.original, queryIndex, pairFst_pair, pairSnd_pair]
    exact RationalCutBits.coefficient_packet c k m hm
  pattern_eq _ _ := rfl

noncomputable def family (P : Readers) : Family :=
  ((BoundedCriticalSampleCount.family P).comp pairFst).append (cutFamily P)

noncomputable def count (P : Readers) (c : List Bool) : ℕ :=
  ((BoundedCriticalSampleLabels.rootSet P (pairFst c)).filter (fun theta => theta < RationalCutBits.threshold c)).card

theorem family_count (P : Readers) (c : List Bool) : rootCount (family P) c = count P c := by
  have hr (F G : Family) : (F.append G).root = F.root := rfl
  unfold family rootCount RootSignQueries.signCount count
  apply congrArg Finset.card
  ext theta
  simp only [hr, Finset.mem_filter, BoundedCriticalSampleLabels.mem_rootSet, Fin.forall_iff]
  rw [append_signs, BoundedCriticalFilters.valid_iff_filters]
  simp only [Family.comp, BoundedCriticalSampleCount.family, cutFamily, Function.comp_apply]
  simp only [show Nat.fromBitsLE (BinaryNatCode.encode (P.dim (pairFst c) + 4)) = P.dim (pairFst c) + 4 from Nat.fromBitsLE_bits _,
    show Nat.fromBitsLE (BinaryNatCode.encode 1) = 1 from Nat.fromBitsLE_bits _,
    RationalCutBits.sign_neg_iff, Nat.lt_one_iff, forall_eq]
  have hm : algebraMap ℤ ℝ = Int.castRingHom ℝ := RingHom.ext_int _ _
  simp only [hm]
  simp only [Multiset.mem_toFinset, Polynomial.mem_roots (BoundedCriticalSampleLabels.mapped_ne_zero P (pairFst c)),
    Polynomial.IsRoot.def, Polynomial.eval_map, sign_eq_zero_iff, Fin.forall_iff, and_assoc]

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => BinaryNatCode.encode (count P c)) := by
  let A := (BoundedCriticalSampleCount.access P).comp pairFst
  have H : SpaceFunction A.rootCoefficient := (BoundedCriticalRationalCoordinates.parameter_coefficient_evaluator h ha).precompose
    (compQuery pairFst) (compQuery_FP pairFst_mem_FP)
  have Q : SpaceFunction A.polynomialCoefficient := ((BoundedCriticalFilterCoefficients.evaluator h ha).precompose
    BoundedCriticalSampleCount.filterQuery BoundedCriticalSampleCount.filterQuery_FP).precompose
      (compQuery pairFst) (compQuery_FP pairFst_mem_FP)
  have R : SpaceFunction (cutAccess P).polynomialCoefficient :=
    SpaceFunction.ofFP (RationalCutBits.coefficient ∘ cutQuery) (mem_FP_comp cutQuery_FP RationalCutBits.coefficient_FP)
  have hA : A.pattern ∈ FP := by
    change ((BoundedCriticalSampleCount.access P).pattern ∘ compPattern pairFst) ∈ FP
    exact mem_FP_comp (compPattern_FP pairFst_mem_FP) (constFn_mem_FP (InfinitesimalSign.encode 0))
  have E : SpaceFunction (fun c => BinaryNatCode.encode (rootCount (family P) c)) :=
    appendCountEvaluator A (cutAccess P) (comp_controls (BoundedCriticalSampleCount.controls h) pairFst_mem_FP)
    (cut_controls h) hA
    (constFn_mem_FP (InfinitesimalSign.encode .neg)) H Q R
  exact E.congr (funext fun c => congrArg BinaryNatCode.encode (family_count P c))

theorem count_le (P : Readers) (c : List Bool) : count P c ≤ BoundedCriticalSampleCount.count P (pairFst c) := by
  rw [← BoundedCriticalSampleLabels.rootSet_card]
  exact Finset.card_filter_le _ _

theorem rank_lt_count_iff (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P (pairFst c)) :
    BoundedCriticalSampleLabels.rank P (pairFst c) x < count P c ↔
      (BoundedCriticalSampleLabels.parameter P (pairFst c) x).val < RationalCutBits.threshold c := by
  rw [BoundedCriticalSampleLabels.rank_eq_card_below]
  let s := BoundedCriticalSampleLabels.rootSet P (pairFst c)
  let v := (BoundedCriticalSampleLabels.parameter P (pairFst c) x).val
  have hv : v ∈ s := (BoundedCriticalSampleLabels.parameter P (pairFst c) x).property
  change (s.filter (fun theta => theta < v)).card < (s.filter (fun theta => theta < RationalCutBits.threshold c)).card ↔ _
  constructor
  · intro h
    by_contra hh
    have hs : s.filter (fun theta => theta < RationalCutBits.threshold c) ⊆ s.filter (fun theta => theta < v) := by
      intro theta ht
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2.trans_le (le_of_not_gt hh)⟩
    exact not_lt_of_ge (Finset.card_le_card hs) h
  · intro h
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro theta ht
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2.trans h⟩
    · intro he
      have hv' : v ∈ s.filter (fun theta => theta < RationalCutBits.threshold c) := Finset.mem_filter.mpr ⟨hv, h⟩
      rw [← he] at hv'
      exact lt_irrefl v (Finset.mem_filter.mp hv').2

def belowLanguage (P : Readers) : Language := {q |
  (pairSnd q).length = BoundedFullCriticalSamples.labelWidth P (pairFst (pairFst q)) ∧
    Nat.fromBitsLE (pairSnd q) < count P (pairFst q)}
noncomputable def compare (P : Readers) (z : List Bool) : Bool := decide
  ((pairSnd (pairFst z)).length = BoundedFullCriticalSamples.labelWidth P (pairFst (pairFst (pairFst z))) ∧
    Nat.fromBitsLE (pairSnd (pairFst z)) < Nat.fromBitsLE (pairSnd z))

theorem compare_FP {P : Readers} (h : P.PolyTime) : (fun z => [compare P z]) ∈ FP := by
  have hw := (BoundedFullCriticalSamples.labelWidth_unary h).comp
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP)
  have hr := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact ((FPPred.eq (UnaryFn.length hr) hw).and ((BinaryFn.fromBits hr).lt (BinaryFn.fromBits pairSnd_mem_FP))).flag_mem_FP

theorem below_decider {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (belowLanguage P) := by
  have E := ((evaluator h ha).precompose pairFst pairFst_mem_FP).withInput
  apply E.decider (compare P) (compare_FP h)
  intro q
  simp only [belowLanguage, Set.mem_ofPred_eq, compare, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem label_below_iff (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P (pairFst c)) :
    pair c (BoundedCriticalSampleLabels.label P (pairFst c) x) ∈ belowLanguage P ↔
      (BoundedCriticalSampleLabels.parameter P (pairFst c) x).val < RationalCutBits.threshold c := by
  simp only [belowLanguage, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair,
    BoundedCriticalSampleLabels.label_length, BoundedCriticalSampleLabels.label_value, true_and]
  exact rank_lt_count_iff P c x

theorem below_mem_PSPACE {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : belowLanguage P ∈ PSPACE :=
  (below_decider h ha).mem_PSPACE

end LeanCanny.Encoding.BoundedCriticalSampleCuts
