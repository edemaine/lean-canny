/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTablePreparation

/-! # Root semantics for any valid symbolic direction table

An admissible direction table whose symbolic nodes are separable encodes the
entire Cartesian product of real leaf roots at every sufficiently small
positive evaluation. The actual integer-prepared table supplies that property.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open scoped Classical

abbrev Values := BalancedPrimitiveTree.Values

noncomputable def pairCoordinates {L : Type*} [Field L] (φ : Coefficient →+* L)
    (p q : Polynomial Coefficient) (c : ℕ) (theta : L) : L × L :=
  ((PrimitivePair.leftNumerator p q c).eval₂ φ theta / (PrimitivePair.denominator p q c).eval₂ φ theta,
    (PrimitivePair.rightNumerator p q c).eval₂ φ theta / (PrimitivePair.denominator p q c).eval₂ φ theta)

theorem pairCoordinates_eq {L : Type*} [Field L] (φ : Coefficient →+* L)
    (p q : Polynomial Coefficient) (c : ℕ) (theta : L)
    (hp : (p.map φ).natDegree = p.natDegree) (hq : (q.map φ).natDegree = q.natDegree) :
    pairCoordinates φ p q c theta = fieldDecode (p.map φ) (q.map φ) c theta := by
  simp only [pairCoordinates, fieldDecode, ← leftNumerator_map_of_degrees φ p q c hp hq,
    ← rightNumerator_map_of_degrees φ p q c hp hq, ← denominator_map_of_degrees φ p q c hp hq,
    Polynomial.eval_map]

noncomputable def valid (a : ℕ → Polynomial Coefficient) (beta : ℝ) : (h : ℕ) → ℕ → Values ℝ h → Prop
  | 0, i, x => (a i).eval₂ (scalarEvaluation beta) x = 0
  | h + 1, i, x => valid a beta h (2 * i) x.1 ∧ valid a beta h (2 * i + 1) x.2

noncomputable def decode (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ) (beta : ℝ) :
    (h : ℕ) → ℕ → ℝ → Values ℝ h
  | 0, _, theta => theta
  | h + 1, i, theta =>
    let z := pairCoordinates (scalarEvaluation beta) (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i) theta
    (decode a c beta h (2 * i) z.1, decode a c beta h (2 * i + 1) z.2)

noncomputable def encode (c : ℕ → ℕ → ℕ) : (h : ℕ) → ℕ → Values ℝ h → ℝ
  | 0, _, x => x
  | h + 1, i, x => shear (c h i) (encode c h (2 * i) x.1, encode c h (2 * i + 1) x.2)

def SeparableTable (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ) (height : ℕ) : Prop :=
  ∀ h i, h ≤ height → ((node a c h i).map embedding).Separable

theorem specialized_node_separable (B : Budget) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c) (height : ℕ) (hs : SeparableTable a c height)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (referenceExponent B height))
    (h i : ℕ) (hh : h ≤ height) : ((node a c h i).map (scalarEvaluation beta)).Separable := by
  have hn : node a c h i ≠ 0 := (Polynomial.map_ne_zero_iff embedding_injective).mp (hs h i hh).ne_zero
  exact (node_separable_iff B a c ha hc height h i hh hn beta hb he).mpr (hs h i hh)

theorem decode_root (B : Budget) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c) (height : ℕ) (hs : SeparableTable a c height)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (referenceExponent B height))
    (h i : ℕ) (hh : h ≤ height) (theta : ℝ) (ht : (node a c h i).eval₂ (scalarEvaluation beta) theta = 0) :
    valid a beta h i (decode a c beta h i theta) ∧ encode c h i (decode a c beta h i theta) = theta := by
  induction h generalizing i theta with
  | zero => exact ⟨ht, rfl⟩
  | succ h ih =>
    have hdl := node_degree_map B a c ha hc height h (2 * i) (by omega) beta hb he
    have hdr := node_degree_map B a c ha hc height h (2 * i + 1) (by omega) beta hb he
    have hml := specialized_node_separable B a c ha hc height hs beta hb he h (2 * i) (by omega)
    have hmr := specialized_node_separable B a c ha hc height hs beta hb he h (2 * i + 1) (by omega)
    have hms := specialized_node_separable B a c ha hc height hs beta hb he (h + 1) i hh
    have hm := resultant_map_of_degrees (scalarEvaluation beta) (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i) hdl hdr
    have ht' : (cannyResultant ((node a c h (2 * i)).map (scalarEvaluation beta))
        ((node a c h (2 * i + 1)).map (scalarEvaluation beta)) (c h i)).eval theta = 0 := by
      rw [← hm, Polynomial.eval_map]
      exact ht
    have hr := field_decode_root _ _ (c h i) theta hml hmr (by rw [← hm]; exact hms) ht'
    rw [← pairCoordinates_eq _ _ _ _ _ hdl hdr] at hr
    have hl := ih (2 * i) (by omega) _ (by simpa only [Polynomial.eval_map] using hr.1)
    have hh' := ih (2 * i + 1) (by omega) _ (by simpa only [Polynomial.eval_map] using hr.2.1)
    refine ⟨⟨hl.1, hh'.1⟩, ?_⟩
    simp only [decode, encode]
    rw [hl.2, hh'.2]
    exact hr.2.2.1

theorem encode_valid (B : Budget) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c) (height : ℕ) (hs : SeparableTable a c height)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (referenceExponent B height))
    (h i : ℕ) (hh : h ≤ height) (x : Values ℝ h) (hx : valid a beta h i x) :
    (node a c h i).eval₂ (scalarEvaluation beta) (encode c h i x) = 0 ∧ decode a c beta h i (encode c h i x) = x := by
  induction h generalizing i with
  | zero => exact ⟨hx, rfl⟩
  | succ h ih =>
    have hl := ih (2 * i) (by omega) x.1 hx.1
    have hr := ih (2 * i + 1) (by omega) x.2 hx.2
    have hdl := node_degree_map B a c ha hc height h (2 * i) (by omega) beta hb he
    have hdr := node_degree_map B a c ha hc height h (2 * i + 1) (by omega) beta hb he
    have hm := resultant_map_of_degrees (scalarEvaluation beta) (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i) hdl hdr
    have ht := field_encode_roots _ _ (c h i) _ _
      (specialized_node_separable B a c ha hc height hs beta hb he h (2 * i) (by omega))
      (specialized_node_separable B a c ha hc height hs beta hb he h (2 * i + 1) (by omega))
      (by rw [← hm]; exact specialized_node_separable B a c ha hc height hs beta hb he (h + 1) i hh)
      (by simpa only [Polynomial.eval_map] using hl.1) (by simpa only [Polynomial.eval_map] using hr.1)
    rw [← hm, Polynomial.eval_map, ← pairCoordinates_eq _ _ _ _ _ hdl hdr] at ht
    refine ⟨ht.1, ?_⟩
    simp only [decode, encode]
    rw [ht.2]
    exact Prod.ext hl.2 hr.2

noncomputable def rootEquiv (B : Budget) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c) (height : ℕ) (hs : SeparableTable a c height)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (referenceExponent B height))
    (h i : ℕ) (hh : h ≤ height) :
    {theta : ℝ // (node a c h i).eval₂ (scalarEvaluation beta) theta = 0} ≃ {x : Values ℝ h // valid a beta h i x} where
  toFun theta := ⟨decode a c beta h i theta.val, (decode_root B a c ha hc height hs beta hb he h i hh theta.val theta.property).1⟩
  invFun x := ⟨encode c h i x.val, (encode_valid B a c ha hc height hs beta hb he h i hh x.val x.property).1⟩
  left_inv theta := Subtype.ext (decode_root B a c ha hc height hs beta hb he h i hh theta.val theta.property).2
  right_inv x := Subtype.ext (encode_valid B a c ha hc height hs beta hb he h i hh x.val x.property).2

theorem prepared_separableTable (B : Budget) (a : ℕ → Polynomial Coefficient)
    (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) (height : ℕ) :
    SeparableTable (fun i => SymbolicScaledSquarefree.polynomial (a i)) (preparedDirections B a ha hn height) height :=
  fun h i hh => prepared_node_generic_separable B a ha hn height h i hh

theorem valid_squarefree_iff (B : Budget) (a : ℕ → Polynomial Coefficient)
    (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic B.testExponent)
    (h i : ℕ) (x : Values ℝ h) :
    valid (fun i => SymbolicScaledSquarefree.polynomial (a i)) beta h i x ↔ valid a beta h i x := by
  induction h generalizing i with
  | zero =>
    exact small_roots_iff _ (hn i) B.massExponent (ha i).2.2 beta hb
      (he.trans (dyadic_antitone (by
        unfold SymbolicScaledSquarefree.smallExponent Budget.testExponent
        exact Nat.add_le_add_right (Nat.add_le_add_left (gcdMassExponent_mono (ha i).1 le_rfl) _) _))) x
  | succ h ih => exact and_congr (ih (2 * i) x.1) (ih (2 * i + 1) x.2)

noncomputable def preparedRootEquiv (B : Budget) (a : ℕ → Polynomial Coefficient)
    (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) (height : ℕ)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic (preparationExponent B height))
    (h i : ℕ) (hh : h ≤ height) :
    {theta : ℝ // (node (fun i => SymbolicScaledSquarefree.polynomial (a i))
      (preparedDirections B a ha hn height) h i).eval₂ (scalarEvaluation beta) theta = 0} ≃
      {x : Values ℝ h // valid a beta h i x} :=
  (rootEquiv B.squarefree _ _ (fun i => B.squarefree_controls _ (ha i))
    (preparedDirections_admissible B a ha hn height) height (prepared_separableTable B a ha hn height)
    beta hb (he.trans (dyadic_antitone (Nat.le_add_left _ _))) h i hh).trans
    (Equiv.subtypeEquivProp (funext fun x => propext (valid_squarefree_iff B a ha hn beta hb
      (he.trans (dyadic_antitone (Nat.le_add_right _ _))) h i x)))

end LeanCanny.Algebra.SymbolicFixedTable
