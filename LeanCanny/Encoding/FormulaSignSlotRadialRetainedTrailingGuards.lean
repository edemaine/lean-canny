/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRetainedCenterGuards
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterTrailingSelection
/-! # Native same-bank selection of the margin's actual trailing coefficient -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRetainedTrailingGuards
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def slot (i : ℕ) (q : List Bool) := WordList.reader (pair (pairSnd q) (BinaryNatCode.encode i))
theorem slot_FP (i : ℕ) : slot i ∈ FP :=
  mem_FP_comp (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP _)) WordList.reader_FP
def degree (q : List Bool) := Nat.fromBitsLE (slot 1 q)
def trailing (q : List Bool) := Nat.fromBitsLE (slot 2 q)
def centerQuery (q : List Bool) := pair (pairFst q) (pair (slot 0 q) (slot 1 q))
def coefficientQuery (q : List Bool) := pair (centerQuery (pairFst q))
  (pair (BinaryNat.normalize (pairSnd q)) (BinaryNat.normalize (slot 0 (pairFst q))))
def chosenQuery (q : List Bool) := pair q (BinaryNat.normalize (slot 2 q))
theorem degree_binary : BinaryFn degree := BinaryFn.fromBits (slot_FP 1)
theorem trailing_binary : BinaryFn trailing := BinaryFn.fromBits (slot_FP 2)
theorem centerQuery_FP : centerQuery ∈ FP := mem_FP_pair pairFst_mem_FP (mem_FP_pair (slot_FP 0) (slot_FP 1))
attribute [local irreducible] slot centerQuery
theorem coefficientQuery_FP : coefficientQuery ∈ FP := by
  have HS : (fun q => slot 0 (pairFst q)) ∈ FP := mem_FP_comp pairFst_mem_FP (slot_FP 0)
  have HC : (fun q => centerQuery (pairFst q)) ∈ FP := mem_FP_comp pairFst_mem_FP centerQuery_FP
  exact mem_FP_pair HC (mem_FP_pair (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)
    (mem_FP_comp HS BinaryNat.normalize_mem_FP))
theorem chosenQuery_FP : chosenQuery ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_comp (slot_FP 2) BinaryNat.normalize_mem_FP)
def query (c w : List Bool) (tau D ell : ℕ) := pair (pair c w)
  (WordList.encode [BinaryNatCode.encode tau, BinaryNatCode.encode D, BinaryNatCode.encode ell])

private theorem slots_query (c w : List Bool) (tau D ell : ℕ) :
    slot 0 (query c w tau D ell) = BinaryNatCode.encode tau ∧
    slot 1 (query c w tau D ell) = BinaryNatCode.encode D ∧
    slot 2 (query c w tau D ell) = BinaryNatCode.encode ell := by
  simp only [slot, query, pairSnd_pair, WordList.reader_packet, WordList.get_encode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, and_self]
private theorem center_query (c w : List Bool) (tau D ell : ℕ) : centerQuery (query c w tau D ell) =
    pair (pair c w) (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode D)) := by
  rw [centerQuery, (slots_query c w tau D ell).1, (slots_query c w tau D ell).2.1]
  rw [query, pairFst_pair]
private theorem coefficient_query (c w : List Bool) (tau D ell j : ℕ) :
    coefficientQuery (pair (query c w tau D ell) (BinaryNatCode.encode j)) =
      FiniteCoefficientSignScan.query
        (pair (pair c w) (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode D))) j tau := by
  simp only [coefficientQuery, pairFst_pair, pairSnd_pair, center_query, (slots_query c w tau D ell).1,
    BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, FiniteCoefficientSignScan.query]

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R) (outer : Bool) (radial refs : List Bool → List Bool)

noncomputable def Zero (q : List Bool) (j : ℕ) : Prop :=
  FormulaSignSlotRadialRetainedCenterGuards.marker hn ht ha hR outer radial refs
    (coefficientQuery (pair q (BinaryNatCode.encode j))) = InfinitesimalSign.encode 0
noncomputable def Guards (q : List Bool) : Prop :=
  FormulaSignSlotRadialRetainedCenterGuards.Guards hn ht ha hR outer radial refs (centerQuery q) ∧
  trailing q ≤ degree q ∧ (∀ j < trailing q, Zero hn ht ha hR outer radial refs q j) ∧
    ¬Zero hn ht ha hR outer radial refs q (trailing q)

theorem evaluator (hs : radial ∈ FP) (hf : refs ∈ FP) :
    SpaceFunction (fun q => [decide (Guards hn ht ha hR outer radial refs q)]) := by
  have EM := (FormulaSignSlotRadialRetainedCenterGuards.marker_evaluator hn ht ha hR outer radial refs hs hf).precompose
    coefficientQuery coefficientQuery_FP
  have EZ := EM.postcompose (fun z => [decide (z = InfinitesimalSign.encode 0)])
    (stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  have EL := EZ.forall_binary trailing_binary
  have EC := (EZ.precompose chosenQuery chosenQuery_FP).postcompose _
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  have EG := (FormulaSignSlotRadialRetainedCenterGuards.evaluator hn ht ha hR outer radial refs hs hf).precompose
    centerQuery centerQuery_FP
  have EB := SpaceFunction.ofFP _ (trailing_binary.le degree_binary).flag_mem_FP
  refine (EG.andFlags (EB.andFlags (EL.andFlags EC))).congr (funext fun q => ?_)
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, Guards, Zero, chosenQuery, trailing, BinaryNat.normalize_eq_bits,
    List.cons.injEq, and_true, decide_eq_true_eq, id_eq, BinaryNatCode.encode]

private theorem zero_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (tau D ell j : ℕ) : Zero hn ht ha hR outer radial refs (query c w tau D ell) j ↔
      ∀ r < FormulaSignSlotRadialCenterSelection.bound (radial c) + 1,
        FormulaSignSlotRadialCenterSelection.Zero (radial c)
          (FormulaSignSlotRadialRetainedCenterTest.center hn ht ha hR outer radial refs c w hv) tau j r := by
  rw [Zero, coefficient_query, FormulaSignSlotRadialRetainedCenterGuards.marker_zero]
  unfold FormulaSignSlotRadialRetainedCenterGuards.RadiusZero
  have HF : pairFst (FiniteCoefficientSignScan.query
      (pair (pair c w) (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode D))) j tau) =
        pair (pair c w) (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode D)) := by
    simp only [FiniteCoefficientSignScan.query, pairFst_pair]
  rw [HF]
  simp_rw [FormulaSignSlotRadialRetainedCenterGuards.radius_query_packet]
  simp only [FormulaSignSlotRadialRetainedCenterGuards.bound, FormulaSignSlotRadialRetainedCenterGuards.context,
    pairFst_pair]
  simp_rw [FormulaSignSlotRadialRetainedCenterTest.zero_packet hn ht ha hR outer radial refs c w hv]

theorem guards_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (tau D ell : ℕ) : Guards hn ht ha hR outer radial refs (query c w tau D ell) ↔
      FormulaSignSlotRadialCenterTrailingSelection.Guards (radial c)
        (FormulaSignSlotRadialRetainedCenterTest.center hn ht ha hR outer radial refs c w hv) tau D ell := by
  rw [Guards, center_query, FormulaSignSlotRadialRetainedCenterGuards.guards_packet hn ht ha hR outer radial refs c w hv]
  simp_rw [zero_packet hn ht ha hR outer radial refs c w hv]
  simp only [trailing, degree, (slots_query c w tau D ell).2.1, (slots_query c w tau D ell).2.2,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, FormulaSignSlotRadialCenterTrailingSelection.Guards]

theorem exists_guards (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w) :
    ∃ tau ≤ FormulaSignSlotRadialCenterSelection.bound (radial c),
      ∃ D ≤ FormulaSignSlotRadialCenterSelection.bound (radial c),
        ∃ ell ≤ D, Guards hn ht ha hR outer radial refs (query c w tau D ell) := by
  obtain ⟨tau, htau, D, hD, ell, hell, H⟩ := FormulaSignSlotRadialCenterTrailingSelection.exists_guards
    (radial c) (FormulaSignSlotRadialRetainedCenterTest.center hn ht ha hR outer radial refs c w hv)
  exact ⟨tau, htau, D, hD, ell, hell, (guards_packet hn ht ha hR outer radial refs c w hv tau D ell).mpr H⟩

theorem trailing_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (tau D ell r : ℕ) (h : Guards hn ht ha hR outer radial refs (query c w tau D ell)) :
    FormulaSignSlotRadialRetainedCenterTest.value hn ht ha hR outer radial refs
      (pair (pair c w) (FormulaSignSlotRadialRetainedCenterTest.indices tau ell r)) =
        InfinitesimalSign.encode (SignType.sign
          ((FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c)
            (FormulaSignSlotRadialRetainedCenterTest.center hn ht ha hR outer radial refs c w hv)).trailingCoeff.coeff r)) := by
  have H := (guards_packet hn ht ha hR outer radial refs c w hv tau D ell).mp h
  rw [FormulaSignSlotRadialRetainedCenterTest.packet hn ht ha hR outer radial refs c w _ hv]
  simp only [FormulaSignSlotRadialRetainedCenterTest.indices, WordList.get_encode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact congrArg (fun a : ℝ => InfinitesimalSign.encode (SignType.sign a))
    (FormulaSignSlotRadialCenterTrailingSelection.coefficient (radial c)
      (FormulaSignSlotRadialRetainedCenterTest.center hn ht ha hR outer radial refs c w hv) tau D ell r H).symm

end LeanCanny.Encoding.FormulaSignSlotRadialRetainedTrailingGuards
