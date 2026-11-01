/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHistoryPrefix
public import LeanCanny.Algebra.IntegralMixedPhysicalCaps
/-! # Actual full-history physical critical backend

Each saved key interprets its literal scalar prefix, including normalized
cut births. A creating physical critical command supplies its exact rule;
other words use a fixed offset-zero rule. The constructor works in ambient
zero and needs no frozen sweep coordinate or nilpotent coefficient digit.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullPhysicalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Data (P : Parameters) where
  spatial : ∀ root, SpatialSource (P.ambient root)
  degree_eq : ∀ root, (spatial root).degree = P.degree root
  sourceWidth : ∀ root, (spatial root).degree.size ≤ P.sourceWidth root
  scalar_cap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root + 1) (spatial root).degree ≤ 2 ^ P.width root
  rules : ∀ root, List (Command (spatial root) (P.width root))
  room : ∀ root, (rules root).length + 2 ≤ P.cap root + 1

def prefixLength (P : Parameters) (key : List Bool) := min (Nat.fromBitsLE (pairFst (pairSnd key))) (P.cap (pairFst key) + 1)

theorem prefix_unary (P : Parameters) (a : Access P) : UnaryFn (prefixLength P) :=
  UnaryFn.fromBitsLE_min (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) ((a.cap.add (UnaryFn.const 1)).comp pairFst_mem_FP)

noncomputable def initial (P : Parameters) (D : Data P) (root : List Bool) :
    State (D.spatial root) (P.cap root + 1) (P.width root) 0 (Fin 0) :=
  IntegralMixedHistory.base (D.spatial root) (IntegralHistorySampler.base (P.cap root + 1) (2 ^ P.width root))
    ((by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
      PurePowerReductionBounds.dimension (P.ambient root + 1) (D.spatial root).degree ≤
        IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root + 1) (D.spatial root).degree).trans (D.scalar_cap root))

noncomputable def commands (P : Parameters) (D : Data P) (key : List Bool) := paddedPast (D.rules (pairFst key)) (prefixLength P key)
noncomputable def creating (P : Parameters) (D : Data P) (key : List Bool) := chronological (D.rules (pairFst key)) (prefixLength P key)

def defaultRule (n : ℕ) : CriticalRule n where
  offset := ⟨0, Nat.succ_pos _⟩
  objective := 0
  coordinate := 0
  scales _ := 1
  scales_ne_zero _ := one_ne_zero
  heights _ := .constant 0

noncomputable def rule (P : Parameters) (D : Data P) (key : List Bool) : CriticalRule (P.ambient (pairFst key)) :=
  match creating P D key with
  | some (.critical r) => r
  | _ => defaultRule _

noncomputable def family (P : Parameters) (D : Data P) : IntegralMixedPhysicalCriticalBits.Family where
  ambient key := P.ambient (pairFst key)
  cap key := P.cap (pairFst key) + 1
  width key := P.width (pairFst key)
  birth key := (commands P D key).length
  physical key := Index (Fin 0) (commands P D key)
  spatial key := D.spatial (pairFst key)
  state key := run (initial P D (pairFst key)) (commands P D key) (by
    change (paddedPast (D.rules (pairFst key)) (prefixLength P key)).length ≤ P.cap (pairFst key) + 1 + 1
    rw [paddedPast_length]
    exact (min_le_right _ _).trans (Nat.le_succ _))
  birth_bound key := by
    change (paddedPast _ _).length ≤ _
    rw [paddedPast_length]
    exact min_le_right _ _
  rule := rule P D

theorem family_birth (P : Parameters) (D : Data P) (key : List Bool) :
    (family P D).birth key = prefixLength P key := paddedPast_length _ _

structure Metadata (P : Parameters) (D : Data P) : Prop where
  offset : UnaryFn (fun key => (rule P D key).offset.val)
  objective : BinaryFn (fun key => (rule P D key).objective)

theorem inputMetadata (P : Parameters) (a : Access P) (D : Data P) (h : Metadata P D) :
    IntegralMixedPhysicalQueryBits.InputMetadata (family P D) where
  ambient := a.ambient.comp pairFst_mem_FP
  birth := (prefix_unary P a).of_eq (fun key => (family_birth P D key).symm)
  width := a.width.comp pairFst_mem_FP
  offset := h.offset
  degree := by
    have HD : BinaryFn (fun key => P.degree (pairFst key)) := a.degree.comp pairFst_mem_FP
    exact HD.of_eq (fun key => (D.degree_eq (pairFst key)).symm)
  objective := h.objective

theorem rule_critical (P : Parameters) (D : Data P) (key : List Bool)
    (r : CriticalRule (P.ambient (pairFst key)))
    (hc : creating P D key = some (.critical r)) : rule P D key = r := by
  unfold rule
  rw [hc]

theorem saved_birth (P : Parameters) (D : Data P) (q : List Bool) :
    (family P D).birth (IntegralMixedPhysicalTaskBits.saved P q) = birth P q := by
  rw [family_birth]
  simp only [prefixLength, IntegralMixedPhysicalTaskBits.saved, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact min_eq_left (min_le_right _ _)

theorem geometry (P : Parameters) (D : Data P) : IntegralMixedPhysicalCaps.RootGeometry P (family P D) where
  ambient q := by change P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q)) ≤ _; rw [IntegralMixedPhysicalTaskBits.saved, pairFst_pair]
  degree q := by change (D.spatial (pairFst (IntegralMixedPhysicalTaskBits.saved P q))).degree ≤ _; rw [IntegralMixedPhysicalTaskBits.saved, pairFst_pair, D.degree_eq]
  sourceWidth q := by change (D.spatial (pairFst (IntegralMixedPhysicalTaskBits.saved P q))).degree.size ≤ _; rw [IntegralMixedPhysicalTaskBits.saved, pairFst_pair]; exact D.sourceWidth _
  width q := by change P.width (pairFst (IntegralMixedPhysicalTaskBits.saved P q)) = _; rw [IntegralMixedPhysicalTaskBits.saved, pairFst_pair]
  birth q := saved_birth P D q

noncomputable abbrev source (P : Parameters) (D : Data P) := IntegralMixedPhysicalTaskBits.source P (family P D)
noncomputable def access (P : Parameters) (a : Access P) (D : Data P) (h : Metadata P D) :
    IntegralClearedCriticalBits.Access (source P D) :=
  IntegralMixedPhysicalTaskBits.access P a (family P D) (inputMetadata P a D h)

theorem canonical (P : Parameters) (D : Data P) (key : List Bool) : Canonical ((family P D).state key) := by
  apply run_canonical
  intro i
  exact Fin.elim0 i

theorem origin_denominator (P : Parameters) (D : Data P) (key : List Bool) (i : Fin ((family P D).birth key)) :
    ((family P D).state key).bank.denominator i =
      leading (birthState (initial P D (pairFst key)) (commands P D key)
        (((family P D).birth_bound key).trans (Nat.le_succ _)) i)
        (older_bound (commands P D key) (((family P D).birth_bound key).trans (Nat.le_succ _)) i)
        (chosen (commands P D key) i) :=
  (IntegralMixedFullHistoryScript.origin (initial P D (pairFst key)) (commands P D key)
    (((family P D).birth_bound key).trans (Nat.le_succ _)) i).denominator_eq

theorem source_polynomial (P : Parameters) (D : Data P) (q : List Bool)
    (hc : get P .slot13 q = (rule P D (IntegralMixedPhysicalTaskBits.saved P q)).coordinate) :
    (source P D).annihilator q = criticalPolynomial
      ((family P D).state (IntegralMixedPhysicalTaskBits.saved P q))
      ((family P D).birth_bound (IntegralMixedPhysicalTaskBits.saved P q))
      (rule P D (IntegralMixedPhysicalTaskBits.saved P q)) := by
  apply IntegralMixedPhysicalCriticalBits.critical_polynomial
  exact congrArg (fun j => j % (P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q)) -
    (rule P D (IntegralMixedPhysicalTaskBits.saved P q)).offset.val + 1)) hc
end LeanCanny.Algebra.IntegralMixedFullPhysicalBits
