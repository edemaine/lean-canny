/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueCoefficientSnapshot
/-! # A native first-digit writer for squarefree coefficients at disjoint raw phase24 -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeCoefficientTasks
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralCoordinateBasis
open scoped Classical

noncomputable def scalar (P : Parameters) (F : Family) (q : List Bool) := 2 ^ F.width (IntegralMixedVirtualTaskBits.saved P q)
noncomputable def oldRank (P : Parameters) (F : Family) (q : List Bool) :=
  count (F.birth (IntegralMixedVirtualTaskBits.saved P q)) (F.width (IntegralMixedVirtualTaskBits.saved P q))
theorem scalar_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (scalar P F) :=
  ((BinaryFn.const 2).powUnary h.width).comp (IntegralMixedVirtualTaskBits.saved_FP P a)
theorem oldRank_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (oldRank P F) :=
  (((BinaryFn.const 2).powUnary h.width).powUnary h.birth).comp (IntegralMixedVirtualTaskBits.saved_FP P a)

def Labels (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  get P .row q < oldRank P F q ∧ get P .col q < oldRank P F q ∧ get P .coefficient q < scalar P F q
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (Labels P F q) := inferInstanceAs (Decidable (_ ∧ _))
theorem labels_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (Labels P F) :=
  ((get_binary P a .row).lt (oldRank_binary P a F h)).and
    (((get_binary P a .col).lt (oldRank_binary P a F h)).and
      ((get_binary P a .coefficient).lt (scalar_binary P a F h)))

noncomputable def packedRow (P : Parameters) (F : Family) (q : List Bool) := get P .coefficient q + scalar P F q * get P .row q
noncomputable def packedCol (P : Parameters) (F : Family) (q : List Bool) := scalar P F q * get P .col q

theorem packedRow_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (packedRow P F) :=
  (get_binary P a .coefficient).add ((scalar_binary P a F h).mul (get_binary P a .row))
theorem packedCol_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (packedCol P F) :=
  (scalar_binary P a F h).mul (get_binary P a .col)

theorem pack_lt (m B r k : ℕ) (hr : r < count m B) (hk : k < 2 ^ B) :
    k + 2 ^ B * r < count (m + 1) B := (pairIndex m B (⟨r, hr⟩, ⟨k, hk⟩)).isLt

theorem firstRank_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    count (F.birth (IntegralMixedVirtualTaskBits.saved P q) + 1) (F.width (IntegralMixedVirtualTaskBits.saved P q)) ≤
      numericCap P (RankedHistoryTask.root q) :=
  (IntegralMixedVirtualCaps.auxiliary_rank_le P F g q hv 1 (by decide)).trans
    (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.1

theorem row_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hl : Labels P F q) :
    packedRow P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  (pack_lt _ _ _ _ hl.1 hl.2.2).le.trans (firstRank_cap P F g q hv)
theorem col_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hl : Labels P F q) :
    packedCol P F q ≤ numericCap P (RankedHistoryTask.root q) := by
  simpa only [Nat.zero_add, packedCol, scalar] using
    (pack_lt _ _ _ 0 hl.2.1 (Nat.two_pow_pos _)).le.trans (firstRank_cap P F g q hv)

noncomputable def first (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P id .rawFactor .relativePower .row (packedRow P F)
noncomputable def query (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P (first P F) .rawFactor .relativePower .col (packedCol P F)
theorem first_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : first P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _ (packedRow_binary P a F h)
theorem query_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : query P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (first_FP P a F h) _ _ _ _ (packedCol_binary P a F h)

theorem query_root (P : Parameters) (F : Family) (q : List Bool) :
    RankedHistoryTask.root (query P F q) = RankedHistoryTask.root q := by
  simp only [query, first, IntegralMixedValueFieldQuery.query_root, id_eq]
theorem query_birth (P : Parameters) (F : Family) (q : List Bool) : birth P (query P F q) = birth P q := by
  simp only [query, first, IntegralMixedValueFieldQuery.query_birth, id_eq]
theorem query_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P F q) = IntegralMixedVirtualTaskBits.saved P q :=
  (IntegralMixedValueFieldQuery.query_saved P (first P F) .rawFactor .relativePower .col _ q (by decide)).trans
    (IntegralMixedValueFieldQuery.query_saved P id .rawFactor .relativePower .row _ q (by decide))
theorem query_modulus (P : Parameters) (F : Family) (q : List Bool) : modulus P (query P F q) = modulus P q :=
  (IntegralMixedValueFieldQuery.query_modulus P (first P F) .rawFactor .relativePower .col _ q (by decide)).trans
    (IntegralMixedValueFieldQuery.query_modulus P id .rawFactor .relativePower .row _ q (by decide))
theorem query_get (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hl : Labels P F q) (f : Field) :
    get P f (query P F q) = if f = .slot14 then 4 else if f = .col then packedCol P F q else
      if f = .row then packedRow P F q else get P f q := by
  simp only [query, first, IntegralMixedValueFieldQuery.query_get, IntegralMixedValueFieldQuery.query_root, id_eq]
  rw [min_eq_left (row_cap P F g q hv hl), min_eq_left (col_cap P F g q hv hl)]
  cases f <;> rfl

theorem query_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 4) (hp : phase q = 26) :
    IntegralMixedRoutineTaskBits.Frame P q (query P F q) := by
  refine ⟨query_root P F q, ?_, ?_⟩
  · have H := IntegralMixedValueFieldQuery.query_length P (first P F) .rawFactor .relativePower .col (packedCol P F) q
    have HW : wordBudget P (first P F q) = wordBudget P q := by
      unfold wordBudget RankedHistoryTask.wordBudget
      rw [first, IntegralMixedValueFieldQuery.query_root]
      rfl
    exact H.trans_eq HW
  · apply IntegralMixedRoutineTaskBits.lower_phase P q _ (query_birth P F q)
    · exact (IntegralMixedValueFieldQuery.query_routine P (first P F) .rawFactor .relativePower .col _ q).trans hr.symm
    · rw [query, IntegralMixedValueFieldQuery.query_phase, hp]
      decide

end LeanCanny.Algebra.IntegralMixedSquarefreeCoefficientTasks
