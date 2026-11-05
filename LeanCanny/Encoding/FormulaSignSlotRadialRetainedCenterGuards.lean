/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRetainedCenterTest
public import LeanCanny.Computation.FiniteCoefficientSignScan
/-! # Native finite selection guards on one actual retained center

The marker records zero versus nonzero of an entire radius polynomial; it
does not assert its sign. The fourth scan head is the constant nonzero marker,
because these are coefficient guards rather than a fresh-root test.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRetainedCenterGuards
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open LeanCanny.Encoding.Brackets
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialRetainedCenterTest.value

def context (q : List Bool) := pairFst (pairFst q)
def choice (q : List Bool) := Nat.fromBitsLE (pairFst (pairSnd q))
def degree (q : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd q))
noncomputable def bound (radial : List Bool → List Bool) (q : List Bool) :=
  FormulaSignSlotRadialEliminantPacked.resultDegree (radial (context q))
theorem context_FP : context ∈ FP := by polytime [context]
theorem choice_binary : BinaryFn choice := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem degree_binary : BinaryFn degree := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
theorem bound_binary (radial : List Bool → List Bool) (hs : radial ∈ FP) : BinaryFn (bound radial) :=
  FormulaSignSlotRadialEliminantFormalMass.degree_binary.comp (mem_FP_comp context_FP hs)

def radiusQuery (z : List Bool) := pair (pairFst (pairFst (pairFst z)))
  (WordList.encode [BinaryNat.normalize (pairSnd (pairSnd (pairFst z))),
    BinaryNat.normalize (pairFst (pairSnd (pairFst z))), BinaryNat.normalize (pairSnd z)])
theorem radiusQuery_FP : radiusQuery ∈ FP := by
  unfold radiusQuery WordList.encode
  apply mem_FP_pair
  · polytime
  · apply mem_FP_pair
    · exact mem_FP_comp (by polytime) BinaryNat.normalize_mem_FP
    · apply mem_FP_pair
      · exact mem_FP_comp (by polytime) BinaryNat.normalize_mem_FP
      · exact mem_FP_pair (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP) (constFn_mem_FP [])

theorem radius_query_packet (q : List Bool) (e k r : ℕ) :
    radiusQuery (pair (FiniteCoefficientSignScan.query q e k) (BinaryNatCode.encode r)) =
      pair (pairFst q) (FormulaSignSlotRadialRetainedCenterTest.indices k e r) := by
  simp only [radiusQuery, FiniteCoefficientSignScan.query, pairFst_pair, pairSnd_pair,
    BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    FormulaSignSlotRadialRetainedCenterTest.indices]

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R) (outer : Bool) (radial refs : List Bool → List Bool)

noncomputable def RadiusZero (q : List Bool) : Prop := ∀ r < bound radial (pairFst q) + 1,
  FormulaSignSlotRadialRetainedCenterTest.value hn ht ha hR outer radial refs
    (radiusQuery (pair q (BinaryNatCode.encode r))) = InfinitesimalSign.encode 0
noncomputable def marker (q : List Bool) := if RadiusZero hn ht ha hR outer radial refs q then
  InfinitesimalSign.encode 0 else InfinitesimalSign.encode 1

theorem marker_evaluator (hs : radial ∈ FP) (hf : refs ∈ FP) :
    SpaceFunction (marker hn ht ha hR outer radial refs) := by
  have ES := (FormulaSignSlotRadialRetainedCenterTest.evaluator hn ht ha hR outer radial refs hs hf).precompose
    radiusQuery radiusQuery_FP
  have EZ := ES.postcompose (fun z => [decide (z = InfinitesimalSign.encode 0)])
    (stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  have EA := EZ.forall_binary (BinaryFn.add ((bound_binary radial hs).comp pairFst_mem_FP) (BinaryFn.const 1))
  have EF := EA.postcompose (fun z => if z = [true] then InfinitesimalSign.encode 0 else InfinitesimalSign.encode 1)
    ((stringEq_fppred id_mem_FP (constFn_mem_FP [true])).ite_mem_FP (constFn_mem_FP _) (constFn_mem_FP _))
  exact EF.congr (funext fun q => by
    simp only [Function.comp_apply, marker, RadiusZero, List.cons.injEq, and_true, decide_eq_true_eq]
    split_ifs <;> rfl)

theorem marker_zero (q : List Bool) : marker hn ht ha hR outer radial refs q = InfinitesimalSign.encode 0 ↔
    RadiusZero hn ht ha hR outer radial refs q := by
  by_cases H : RadiusZero hn ht ha hR outer radial refs q
  · simp only [marker, H, ite_true]
  · simp only [marker, H, ite_false, iff_false]
    decide

noncomputable def Guards (q : List Bool) : Prop := (choice q ≤ bound radial q ∧ degree q ≤ bound radial q) ∧
  FiniteCoefficientSignScan.Guards (marker hn ht ha hR outer radial refs) (fun _ => InfinitesimalSign.encode 1)
    choice degree (bound radial) q

private theorem constant_head (sign : List Bool → List Bool) (K D N : List Bool → ℕ) (q : List Bool) :
    FiniteCoefficientSignScan.Guards sign (fun _ => InfinitesimalSign.encode 1) K D N q ↔
      (∀ k < K q, ∀ e < N q + 1, FiniteCoefficientSignScan.Zero sign q e k) ∧
      ¬FiniteCoefficientSignScan.Zero sign q (D q) (K q) ∧
      (∀ e < N q + 1, D q < e → FiniteCoefficientSignScan.Zero sign q e (K q)) := by
  change (_ ∧ _ ∧ _ ∧ (InfinitesimalSign.encode (1 : SignType) ≠ InfinitesimalSign.encode 0 ∨ _)) ↔ _
  have H : InfinitesimalSign.encode (1 : SignType) ≠ InfinitesimalSign.encode 0 := by decide
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · rintro ⟨hL, hC, hH⟩
    exact ⟨hL, hC, hH, Or.inl H⟩

theorem evaluator (hs : radial ∈ FP) (hf : refs ∈ FP) :
    SpaceFunction (fun q => [decide (Guards hn ht ha hR outer radial refs q)]) := by
  have EC := FiniteCoefficientSignScan.evaluator (marker hn ht ha hR outer radial refs)
    (fun _ => InfinitesimalSign.encode 1) choice degree (bound radial)
    (marker_evaluator hn ht ha hR outer radial refs hs hf) (SpaceFunction.ofFP _ (constFn_mem_FP _))
    choice_binary degree_binary (bound_binary radial hs)
  have EB := SpaceFunction.ofFP _
    (((choice_binary.le (bound_binary radial hs)).and (degree_binary.le (bound_binary radial hs))).flag_mem_FP)
  exact (EB.andFlags EC).congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Guards, List.cons.injEq, and_true, decide_eq_true_eq])

theorem guards_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (tau d : ℕ) :
    Guards hn ht ha hR outer radial refs (pair (pair c w) (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode d))) ↔
      FormulaSignSlotRadialCenterSelection.Guards (radial c)
        (FormulaSignSlotRadialRetainedCenterTest.center hn ht ha hR outer radial refs c w hv) tau d := by
  let q := pair (pair c w) (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode d))
  have HZ (e k : ℕ) : FiniteCoefficientSignScan.Zero (marker hn ht ha hR outer radial refs) q e k ↔
      ∀ r < FormulaSignSlotRadialCenterSelection.bound (radial c) + 1,
        FormulaSignSlotRadialCenterSelection.Zero (radial c)
          (FormulaSignSlotRadialRetainedCenterTest.center hn ht ha hR outer radial refs c w hv) k e r := by
    rw [FiniteCoefficientSignScan.Zero, marker_zero]
    simp only [RadiusZero, FiniteCoefficientSignScan.query, pairFst_pair]
    change (∀ r < bound radial q + 1,
      FormulaSignSlotRadialRetainedCenterTest.value hn ht ha hR outer radial refs
        (radiusQuery (pair (FiniteCoefficientSignScan.query q e k) (BinaryNatCode.encode r))) = _) ↔ _
    simp_rw [radius_query_packet]
    simp only [q, pairFst_pair, bound, context]
    simp_rw [FormulaSignSlotRadialRetainedCenterTest.zero_packet hn ht ha hR outer radial refs c w hv]
  change Guards hn ht ha hR outer radial refs q ↔ _
  rw [Guards, constant_head]
  simp_rw [HZ]
  simp only [choice, degree, bound, context, q, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, FormulaSignSlotRadialCenterSelection.Guards,
    FormulaSignSlotRadialCenterSelection.bound, and_assoc, not_forall, exists_prop]

theorem exists_guards (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w) :
    ∃ tau ≤ FormulaSignSlotRadialCenterSelection.bound (radial c),
      ∃ d ≤ FormulaSignSlotRadialCenterSelection.bound (radial c),
        Guards hn ht ha hR outer radial refs
          (pair (pair c w) (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode d))) := by
  obtain ⟨tau, htau, d, hd, H⟩ := FormulaSignSlotRadialCenterSelection.exists_guards (radial c)
    (FormulaSignSlotRadialRetainedCenterTest.center hn ht ha hR outer radial refs c w hv)
  exact ⟨tau, htau, d, hd, (guards_packet hn ht ha hR outer radial refs c w hv tau d).mpr H⟩

end LeanCanny.Encoding.FormulaSignSlotRadialRetainedCenterGuards
