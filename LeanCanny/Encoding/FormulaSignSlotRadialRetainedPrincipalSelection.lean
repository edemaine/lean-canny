/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRetainedPrincipalGuards
/-! # Exact same-word semantics of the actual principal-selection scan -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRetainedPrincipalSelection
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialRetainedPrincipalTest.value

def query (c w : List Bool) (tau D k : ℕ) := pair (pair c w)
  (WordList.encode [BinaryNatCode.encode tau, BinaryNatCode.encode D, BinaryNatCode.encode k])
def familyContext (c : List Bool) (tau D : ℕ) := pair c (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode D))

private theorem slot_query (c w : List Bool) (tau D k : ℕ) (i : ℕ) :
    FormulaSignSlotRadialRetainedPrincipalGuards.slot i (query c w tau D k) =
      WordList.get (WordList.encode [BinaryNatCode.encode tau, BinaryNatCode.encode D, BinaryNatCode.encode k]) i := by
  simp only [FormulaSignSlotRadialRetainedPrincipalGuards.slot, FormulaSignSlotRadialRetainedPrincipalTest.slot,
    query, pairSnd_pair, WordList.reader_packet]

theorem radius_query (c w : List Bool) (tau D k j r : ℕ) :
    FormulaSignSlotRadialRetainedPrincipalGuards.radiusQuery
      (pair (pair (query c w tau D k) (BinaryNatCode.encode j)) (BinaryNatCode.encode r)) =
        pair (pair c w) (FormulaSignSlotRadialRetainedPrincipalTest.indices tau D j r) := by
  simp only [FormulaSignSlotRadialRetainedPrincipalGuards.radiusQuery, FormulaSignSlotRadialRetainedPrincipalGuards.base,
    pairFst_pair, pairSnd_pair, slot_query, WordList.get_encode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, BinaryNatCode.encode, BinaryNat.normalize_bits,
    FormulaSignSlotRadialRetainedPrincipalTest.indices]
  simp only [query, pairFst_pair]

theorem bound_query (radial : List Bool → List Bool) (c w : List Bool) (tau D k : ℕ) :
    FormulaSignSlotRadialRetainedPrincipalGuards.bound radial (query c w tau D k) =
      FormulaSignSlotRadialCenterPrincipalFamily.degreeBound (familyContext (radial c) tau D) := by
  simp only [FormulaSignSlotRadialRetainedPrincipalGuards.bound, FormulaSignSlotRadialRetainedPrincipalGuards.familyContext,
    FormulaSignSlotRadialRetainedPrincipalGuards.context, slot_query,
    WordList.get_encode, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, familyContext]
  simp only [query, pairFst_pair]

theorem degree_query (c w : List Bool) (tau D k : ℕ) :
    FormulaSignSlotRadialRetainedPrincipalGuards.degree (query c w tau D k) = D := by
  simp only [FormulaSignSlotRadialRetainedPrincipalGuards.degree, slot_query, WordList.get_encode,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, BinaryNatCode.encode, Nat.fromBitsLE_bits]
theorem order_query (c w : List Bool) (tau D k : ℕ) :
    FormulaSignSlotRadialRetainedPrincipalGuards.order (query c w tau D k) = k := by
  simp only [FormulaSignSlotRadialRetainedPrincipalGuards.order, slot_query, WordList.get_encode,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, BinaryNatCode.encode, Nat.fromBitsLE_bits]
theorem center_query (c w : List Bool) (tau D k : ℕ) :
    FormulaSignSlotRadialRetainedPrincipalGuards.centerQuery (query c w tau D k) =
      pair (pair c w) (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode D)) := by
  simp only [FormulaSignSlotRadialRetainedPrincipalGuards.centerQuery, slot_query,
    WordList.get_encode, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  simp only [query, pairFst_pair]

private noncomputable def centerSelection (c : List Bool) (tau D : ℕ) (x : ℕ → ℝ) : Prop :=
  FormulaSignSlotRadialCenterSelection.Guards c (fun i => x i.val) tau D
private noncomputable def squarefreeSelection (c : List Bool) (tau D k : ℕ) (x : ℕ → ℝ) : Prop :=
  FormulaSignSlotRadialCenterSquarefreeSelection.Guards c (fun i => x i.val) tau D k
private theorem math_guards (c : List Bool) (k : ℕ) (x : ℕ → ℝ) :
    FormulaSignSlotRadialCenterPrincipalGuards.Guards c (fun i => x i.val) k ↔
      squarefreeSelection (FormulaSignSlotRadialCenterPrincipalFamily.original c)
        (FormulaSignSlotRadialCenterPrincipalFamily.tau c) (FormulaSignSlotRadialCenterPrincipalFamily.degree c) k x :=
  FormulaSignSlotRadialCenterPrincipalGuards.guards_iff c _ k
private theorem principal_definition (c : List Bool) (k : ℕ) (x : ℕ → ℝ) :
    FormulaSignSlotRadialCenterPrincipalGuards.Guards c (fun i => x i.val) k ↔
      centerSelection (FormulaSignSlotRadialCenterPrincipalFamily.original c)
        (FormulaSignSlotRadialCenterPrincipalFamily.tau c) (FormulaSignSlotRadialCenterPrincipalFamily.degree c) x ∧
      if FormulaSignSlotRadialCenterPrincipalFamily.degree c = 0 then k = 0 else
        k < FormulaSignSlotRadialCenterPrincipalFamily.degree c ∧
        (∀ j < k, ∀ r < FormulaSignSlotRadialCenterPrincipalFamily.degreeBound c + 1,
          FormulaSignSlotRadialCenterPrincipalGuards.Zero c (fun i => x i.val) j r) ∧
        ¬∀ r < FormulaSignSlotRadialCenterPrincipalFamily.degreeBound c + 1,
          FormulaSignSlotRadialCenterPrincipalGuards.Zero c (fun i => x i.val) k r := Iff.rfl
attribute [local irreducible] centerSelection squarefreeSelection
private theorem center_context (c : List Bool) (tau D : ℕ) (x : ℕ → ℝ) :
    centerSelection (FormulaSignSlotRadialCenterPrincipalFamily.original (familyContext c tau D))
      (FormulaSignSlotRadialCenterPrincipalFamily.tau (familyContext c tau D))
      (FormulaSignSlotRadialCenterPrincipalFamily.degree (familyContext c tau D)) x ↔ centerSelection c tau D x := by
  simp only [familyContext, FormulaSignSlotRadialCenterPrincipalFamily.original,
    FormulaSignSlotRadialCenterPrincipalFamily.tau, FormulaSignSlotRadialCenterPrincipalFamily.degree,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
private theorem squarefree_context (c : List Bool) (tau D k : ℕ) (x : ℕ → ℝ) :
    FormulaSignSlotRadialCenterPrincipalGuards.Guards (familyContext c tau D) (fun i => x i.val) k ↔
      squarefreeSelection c tau D k x := by
  rw [math_guards]
  simp only [familyContext, FormulaSignSlotRadialCenterPrincipalFamily.original,
    FormulaSignSlotRadialCenterPrincipalFamily.tau, FormulaSignSlotRadialCenterPrincipalFamily.degree,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R) (outer : Bool) (radial refs : List Bool → List Bool)

theorem radius_zero_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (tau D k j : ℕ) :
    FormulaSignSlotRadialRetainedPrincipalGuards.RadiusZero hn ht ha hR outer radial refs
      (pair (query c w tau D k) (BinaryNatCode.encode j)) ↔
        ∀ r < FormulaSignSlotRadialCenterPrincipalFamily.degreeBound (familyContext (radial c) tau D) + 1,
          FormulaSignSlotRadialCenterPrincipalGuards.Zero (familyContext (radial c) tau D)
            (fun i => FormulaSignSlotRadialRetainedPrincipalTest.center hn ht ha hR outer refs c w hv i.val) j r := by
  rw [FormulaSignSlotRadialRetainedPrincipalGuards.RadiusZero, pairFst_pair, bound_query]
  apply forall_congr'
  intro r
  apply forall_congr'
  intro _
  rw [radius_query]
  exact FormulaSignSlotRadialRetainedPrincipalTest.zero_packet hn ht ha hR outer radial refs c w hv tau D j r

theorem guards_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (tau D k : ℕ) :
    FormulaSignSlotRadialRetainedPrincipalGuards.Guards hn ht ha hR outer radial refs (query c w tau D k) ↔
      FormulaSignSlotRadialCenterSquarefreeSelection.Guards (radial c)
        (fun i => FormulaSignSlotRadialRetainedPrincipalTest.center hn ht ha hR outer refs c w hv i.val) tau D k := by
  let x := FormulaSignSlotRadialRetainedPrincipalTest.center hn ht ha hR outer refs c w hv
  let ctx := familyContext (radial c) tau D
  have HD : FormulaSignSlotRadialCenterPrincipalFamily.degree ctx = D := by
    simp only [ctx, familyContext, FormulaSignSlotRadialCenterPrincipalFamily.degree, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HO : FormulaSignSlotRadialRetainedCenterGuards.Guards hn ht ha hR outer radial refs
      (FormulaSignSlotRadialRetainedPrincipalGuards.centerQuery (query c w tau D k)) ↔ centerSelection (radial c) tau D x := by
    rw [center_query, FormulaSignSlotRadialRetainedCenterGuards.guards_packet hn ht ha hR outer radial refs c w hv tau D]
    unfold centerSelection
    rfl
  have HL : FormulaSignSlotRadialRetainedPrincipalGuards.Lower hn ht ha hR outer radial refs (query c w tau D k) ↔
      ∀ j < k, ∀ r < FormulaSignSlotRadialCenterPrincipalFamily.degreeBound ctx + 1,
        FormulaSignSlotRadialCenterPrincipalGuards.Zero ctx (fun i => x i.val) j r := by
    rw [FormulaSignSlotRadialRetainedPrincipalGuards.Lower, order_query]
    exact forall_congr' (fun j => forall_congr' (fun _ => radius_zero_packet hn ht ha hR outer radial refs c w hv tau D k j))
  have HS : FormulaSignSlotRadialRetainedPrincipalGuards.RadiusZero hn ht ha hR outer radial refs
      (FormulaSignSlotRadialRetainedPrincipalGuards.chosen (query c w tau D k)) ↔
        ∀ r < FormulaSignSlotRadialCenterPrincipalFamily.degreeBound ctx + 1,
          FormulaSignSlotRadialCenterPrincipalGuards.Zero ctx (fun i => x i.val) k r := by
    rw [FormulaSignSlotRadialRetainedPrincipalGuards.chosen, order_query]
    exact radius_zero_packet hn ht ha hR outer radial refs c w hv tau D k k
  have HM : FormulaSignSlotRadialCenterPrincipalGuards.Guards ctx (fun i => x i.val) k ↔
      centerSelection (radial c) tau D x ∧ if D = 0 then k = 0 else k < D ∧
        (∀ j < k, ∀ r < FormulaSignSlotRadialCenterPrincipalFamily.degreeBound ctx + 1,
          FormulaSignSlotRadialCenterPrincipalGuards.Zero ctx (fun i => x i.val) j r) ∧
        ¬∀ r < FormulaSignSlotRadialCenterPrincipalFamily.degreeBound ctx + 1,
          FormulaSignSlotRadialCenterPrincipalGuards.Zero ctx (fun i => x i.val) k r := by
    rw [principal_definition, center_context, HD]
  have HN : FormulaSignSlotRadialRetainedPrincipalGuards.Guards hn ht ha hR outer radial refs (query c w tau D k) ↔
      FormulaSignSlotRadialCenterPrincipalGuards.Guards ctx (fun i => x i.val) k := by
    rw [HM, FormulaSignSlotRadialRetainedPrincipalGuards.Guards, HO, degree_query, order_query]
    by_cases hD : D = 0
    · simp only [hD, ite_true]
    · simp only [ite_eq_right hD, HL, HS]
  have H := HN.trans (squarefree_context (radial c) tau D k x)
  unfold squarefreeSelection at H
  exact H

theorem exists_guards (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w) :
    ∃ tau ≤ FormulaSignSlotRadialCenterSelection.bound (radial c),
      ∃ D ≤ FormulaSignSlotRadialCenterSelection.bound (radial c), ∃ k ≤ D,
        FormulaSignSlotRadialRetainedPrincipalGuards.Guards hn ht ha hR outer radial refs (query c w tau D k) := by
  obtain ⟨tau, htau, D, hD, k, hk, H⟩ := FormulaSignSlotRadialCenterSquarefreeSelection.exists_guards (radial c)
    (fun i => FormulaSignSlotRadialRetainedPrincipalTest.center hn ht ha hR outer refs c w hv i.val)
  exact ⟨tau, htau, D, hD, k, hk, (guards_packet hn ht ha hR outer radial refs c w hv tau D k).mpr H⟩

end LeanCanny.Encoding.FormulaSignSlotRadialRetainedPrincipalSelection
