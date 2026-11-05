/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordRowBounds
public import LeanCanny.Encoding.CoefficientMarkedRecordRootBranches
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowTransport
public import LeanCanny.Encoding.CoefficientMarkedRecordCutCoefficientBounds
/-! # Actual historical rows keep their physical column numbers -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordRowPersistence
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedFramedPhysicalRowTransport
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def naturalRow {R : Type*} [CommRing R] (D : CoefficientMarkedRecordRows.Data R) (j : ℕ) :
    MvPolynomial ℕ R := if h : j < D.count then MvPolynomial.rename Fin.val (D.rows ⟨j, h⟩) else 0

private theorem naturalRow_map {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (D : CoefficientMarkedRecordRows.Data R) (j : ℕ) :
    naturalRow (CoefficientMarkedRecordRows.map φ D) j = MvPolynomial.map φ (naturalRow D j) := by
  unfold naturalRow
  simp only [CoefficientMarkedRecordRows.map]
  split_ifs
  · exact (MvPolynomial.map_rename _ _ _).symm
  · exact (map_zero (MvPolynomial.map φ)).symm

private theorem naturalRow_indexed (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (j : ℕ) (hj : j < IntegralFramedPhysicalSquare.count P D key) :
    naturalRow (CoefficientMarkedRecordRowBounds.samplerData P D H key) j = keyRow P D key j := by
  unfold naturalRow
  have hi : j < (CoefficientMarkedRecordRowBounds.samplerData P D H key).count := hj
  rw [dite_eq_left hi]
  exact (keyRow_family P D H key j hj).symm

noncomputable def natural {N : ℕ} (z : Fin N → ℝ) (i : ℕ) : ℝ :=
  if h : i < N then z ⟨i, h⟩ else 0

private theorem naturalRow_eval (D : CoefficientMarkedRecordRows.Data ℤ[X]) (j : ℕ)
    (hj : j < D.count) (φ : ℤ[X] →+* ℝ) (z : Fin D.count → ℝ) :
    (naturalRow D j).eval₂ φ (natural z) = (D.rows ⟨j, hj⟩).eval₂ φ z := by
  unfold naturalRow
  rw [dite_eq_left hj, MvPolynomial.eval₂_rename]
  have he : natural z ∘ Fin.val = z := by
    funext i
    exact dite_eq_left i.isLt
  rw [he]

private theorem zero_of_dyadic_tail (p : ℤ[X]) (C : ℕ)
    (hp : ∀ r, C ≤ r → p.eval ((2 : ℤ)^r) = 0) : p = 0 := by
  have hd : p.natDegree ≤ 0 := (IntegerPolynomialDyadic.degree_mass_of_growth p C 0 0 (by
    intro r hr; rw [hp r hr]; exact Nat.zero_le _)).1
  have he := Polynomial.eq_C_of_natDegree_le_zero hd
  have hv := hp C le_rfl
  rw [he, Polynomial.eval_C] at hv
  rw [he, hv, Polynomial.C_0]

private theorem dyadic_maps_injective (p q : MvPolynomial ℕ ℤ[X]) (C : ℕ)
    (h : ∀ r, C ≤ r → MvPolynomial.map (evalRingHom ((2 : ℤ)^r)) p =
      MvPolynomial.map (evalRingHom ((2 : ℤ)^r)) q) : p = q := by
  apply MvPolynomial.ext
  intro v
  apply sub_eq_zero.mp
  apply zero_of_dyadic_tail _ C
  intro r hr
  have he := congrArg (fun x : MvPolynomial ℕ ℤ => x.coeff v) (h r hr)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map] at he
  change (p.coeff v).eval ((2 : ℤ)^r) = (q.coeff v).eval ((2 : ℤ)^r) at he
  rw [Polynomial.eval_sub, he, sub_self]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem fixed_count (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) :
    (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count =
      (CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx k hk).count := rfl

private theorem prefix_key (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (aux : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.prefixLength (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux) =
      (CoefficientMarkedPreludeActual.indices n ctx).length + k :=
  IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ _ _ _
    (CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedFramedHistoryFamilyBits.family

/-- The computed physical variable count is monotone along one original trace. -/
theorem count_mono (ctx : List Bool) (k l : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (hl : l ≤ IntegralMixedCausalRecordPlanBits.count ctx) (hkl : k ≤ l) :
    (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count ≤
      (CoefficientMarkedRecordRows.symbolic hn ht ha ctx l hl).count := by
  rw [fixed_count, fixed_count,
    ← CoefficientMarkedRecordRowLayout.count_eq hn ht ha ctx (fun _ => 0) k hk [],
    ← CoefficientMarkedRecordRowLayout.count_eq hn ht ha ctx (fun _ => 0) l hl []]
  apply key_count_le
  · exact (CoefficientMarkedRecordRowLayout.key_root (n := n) ctx k []).trans
      (CoefficientMarkedRecordRowLayout.key_root (n := n) ctx l []).symm
  · rw [prefix_key hn ht ha ctx k hk [], prefix_key hn ht ha ctx l hl []]
    exact Nat.add_le_add_left hkl _

private theorem mapped_row (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (j : ℕ)
    (hj : j < (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))
      (naturalRow (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk) j) =
    keyRow (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R)
      (CoefficientMarkedRecordRowLayout.key (n := n) ctx k []) j := by
  have he := congrArg (fun D : CoefficientMarkedRecordRows.Data ℤ => naturalRow D j)
    (CoefficientMarkedRecordRows.map_indexed hn ht ha ctx R k hk [] hR)
  rw [naturalRow_map] at he
  have hc : j < IntegralFramedPhysicalSquare.count (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R)
      (CoefficientMarkedRecordRowLayout.key (n := n) ctx k []) := by
    rw [CoefficientMarkedRecordRowLayout.count_eq hn ht ha ctx R k hk [], ← fixed_count]
    exact hj
  exact he.trans (naturalRow_indexed _ _ _ _ j hc)

/-- A later prefix has EXACTLY the old parameter-polynomial rows in the same
natural physical columns, hence at every real parameter, not only dyadic ones. -/
theorem rows_persist (ctx : List Bool) (k l : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (hl : l ≤ IntegralMixedCausalRecordPlanBits.count ctx) (hkl : k ≤ l) (j : ℕ)
    (hj : j < (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count) :
    naturalRow (CoefficientMarkedRecordRows.symbolic hn ht ha ctx l hl) j =
      naturalRow (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk) j := by
  apply dyadic_maps_injective _ _ (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx)
  intro r hr
  have hjl := hj.trans_le (count_mono hn ht ha ctx k l hk hl hkl)
  rw [mapped_row hn ht ha ctx (fun _ => r) l hl j hjl hr,
    mapped_row hn ht ha ctx (fun _ => r) k hk j hj hr]
  apply key_rows
  · exact (CoefficientMarkedRecordRowLayout.key_root (n := n) ctx k []).trans
      (CoefficientMarkedRecordRowLayout.key_root (n := n) ctx l []).symm
  · rw [prefix_key hn ht ha ctx k hk [], prefix_key hn ht ha ctx l hl []]
    exact Nat.add_le_add_left hkl _
  · rw [fixed_count, ← CoefficientMarkedRecordRowLayout.count_eq hn ht ha ctx (fun _ => r) k hk []] at hj
    exact hj

/-- ONE later full tuple restricts to a genuine root at EVERY older raw
prefix, with the same original parameter and exact physical column values. -/
theorem rowsAt_restrict (ctx : List Bool) (k l : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (hl : l ≤ IntegralMixedCausalRecordPlanBits.count ctx) (hkl : k ≤ l) (β : ℝ)
    (z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx l hl).count → ℝ)
    (hz : CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx l hl β z) :
    CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx k hk β
      (fun i => z (Fin.castLE (count_mono hn ht ha ctx k l hk hl hkl) i)) := by
  let h := count_mono hn ht ha ctx k l hk hl hkl
  intro i
  have hi := i.isLt.trans_le h
  have he : (naturalRow (CoefficientMarkedRecordRows.symbolic hn ht ha ctx l hl) i.val).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation β) (natural z) = 0 := by
    rw [naturalRow_eval _ _ hi]
    exact hz ⟨i.val, hi⟩
  rw [rows_persist hn ht ha ctx k l hk hl hkl i.val i.isLt] at he
  unfold naturalRow at he
  rw [dite_eq_left i.isLt, MvPolynomial.eval₂_rename] at he
  have hs : natural z ∘ Fin.val = (fun j => z (Fin.castLE h j)) := by
    funext j
    exact dite_eq_left (j.isLt.trans_le h)
  rw [hs] at he
  exact he

end LeanCanny.Encoding.CoefficientMarkedRecordRowPersistence
