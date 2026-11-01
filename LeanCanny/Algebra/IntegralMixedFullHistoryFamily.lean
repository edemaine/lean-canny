/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOldBankProvenance
/-! # Actual full-history banks behind uniform saved task keys

The planned sampler cap is task cap plus one. Every key decodes one
bounded scalar-prefix length and interprets its literal padded command
prefix. Raw-cut selection reads the actual creating cut payload; other
command kinds use an explicit immutable-metadata fallback. Native metadata
access never assumes that the interpreted state can be evaluated.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHistoryFamilyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Selection {n : ℕ} (S : SpatialSource n) where
  rule : IntegralMixedCriticalSweep.Rule n
  kind : IntegralMixedRelativeCuts.Kind S rule
  degree : ℕ
  degree_bound : degree ≤ IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) S.degree

structure Data (P : Parameters) where
  spatial : ∀ root, SpatialSource (P.ambient root)
  degree_eq : ∀ root, (spatial root).degree = P.degree root
  sourceWidth : ∀ root, (spatial root).degree.size ≤ P.sourceWidth root
  scalar_cap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root + 1) (spatial root).degree ≤ 2 ^ P.width root
  rules : ∀ root, List (Command (spatial root) (P.width root))
  room : ∀ root, (rules root).length + 2 ≤ P.cap root + 1
  fallback : ∀ key, Selection (spatial (pairFst key))

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

noncomputable def creating (P : Parameters) (D : Data P) (key : List Bool) : Option (Command (D.spatial (pairFst key)) (P.width (pairFst key))) :=
  chronological (D.rules (pairFst key)) (prefixLength P key)

noncomputable def selection (P : Parameters) (D : Data P) (key : List Bool) : Selection (D.spatial (pairFst key)) :=
  match creating P D key with
  | some (.cut r k d ha _) => ⟨r, k, d, ha⟩
  | _ => D.fallback key

noncomputable def family (P : Parameters) (D : Data P) : IntegralMixedCutSource.Family where
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
  rule key := (selection P D key).rule
  kind key := (selection P D key).kind
  degree key := (selection P D key).degree
  degree_bound key := (selection P D key).degree_bound
  scalar_cap key := D.scalar_cap (pairFst key)

theorem family_birth (P : Parameters) (D : Data P) (key : List Bool) : (family P D).birth key = prefixLength P key := paddedPast_length _ _

theorem family_birth_unary (P : Parameters) (a : Access P) (D : Data P) : UnaryFn (family P D).birth :=
  (prefix_unary P a).of_eq (fun key => (family_birth P D key).symm)

theorem saved_root (P : Parameters) (q : List Bool) : pairFst (IntegralMixedVirtualTaskBits.saved P q) = RankedHistoryTask.root q := pairFst_pair _ _

theorem saved_prefix (P : Parameters) (q : List Bool) : prefixLength P (IntegralMixedVirtualTaskBits.saved P q) = birth P q := by
  simp only [prefixLength, IntegralMixedVirtualTaskBits.saved, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact min_eq_left (min_le_right _ _)

theorem geometry (P : Parameters) (D : Data P) : IntegralMixedVirtualCaps.RootGeometry P (family P D) where
  ambient q := by change P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) ≤ _; rw [saved_root]
  degree q := by change (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))).degree ≤ _; rw [saved_root, D.degree_eq]
  sourceWidth q := by change (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))).degree.size ≤ _; rw [saved_root]; exact D.sourceWidth _
  width q := by change P.width (pairFst (IntegralMixedVirtualTaskBits.saved P q)) = _; rw [saved_root]
  birth q := by rw [family_birth, saved_prefix]

noncomputable def creatingCommand (P : Parameters) (D : Data P) (key : List Bool) := (creating P D key).getD defaultCommand

structure Metadata (P : Parameters) (D : Data P) : Prop where
  offset : UnaryFn (fun key => (selection P D key).rule.critical.offset.val)
  objective : BinaryFn (fun key => (selection P D key).rule.critical.objective)
  degree : BinaryFn (fun key => (selection P D key).degree)
  context : BinaryFn (fun key => (creatingCommand P D key).context)
  coordinate : BinaryFn (fun key => (creatingCommand P D key).coordinate)

theorem inputMetadata (P : Parameters) (a : Access P) (D : Data P) (h : Metadata P D) :
    IntegralMixedVirtualQueryBits.InputMetadata (family P D) where
  ambient := a.ambient.comp pairFst_mem_FP
  birth := family_birth_unary P a D
  width := a.width.comp pairFst_mem_FP
  offset := h.offset
  degree := by
    have HD : BinaryFn (fun key => P.degree (pairFst key)) := a.degree.comp pairFst_mem_FP
    exact HD.of_eq (fun key => (D.degree_eq (pairFst key)).symm)
  objective := h.objective

theorem controls (P : Parameters) (a : Access P) (D : Data P) (h : Metadata P D) : IntegralMixedCutSource.Controls (family P D) where
  birth := family_birth_unary P a D
  width := a.width.comp pairFst_mem_FP
  degree := h.degree

theorem selection_cut (P : Parameters) (D : Data P) (key : List Bool)
    (r : IntegralMixedCriticalSweep.Rule (P.ambient (pairFst key)))
    (k : IntegralMixedRelativeCuts.Kind (D.spatial (pairFst key)) r) (d : ℕ)
    (ha : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst key) + 1) (D.spatial (pairFst key)).degree)
    (hd : d ≤ 2 ^ P.width (pairFst key))
    (hc : creating P D key = some (.cut r k d ha hd)) : selection P D key = ⟨r, k, d, ha⟩ := by
  unfold selection
  rw [hc]

theorem canonical (P : Parameters) (D : Data P) (key : List Bool) : Canonical ((family P D).state key) := by
  apply run_canonical
  intro i
  exact Fin.elim0 i

noncomputable def origin (P : Parameters) (D : Data P) (key : List Bool) (i : Fin ((family P D).birth key)) :=
  IntegralMixedFullHistoryScript.origin (initial P D (pairFst key)) (commands P D key)
    (((family P D).birth_bound key).trans (Nat.le_succ _)) i

theorem origin_denominator (P : Parameters) (D : Data P) (key : List Bool) (i : Fin ((family P D).birth key)) :
    ((family P D).state key).bank.denominator i =
      leading (birthState (initial P D (pairFst key)) (commands P D key)
        (((family P D).birth_bound key).trans (Nat.le_succ _)) i)
        (older_bound (commands P D key) (((family P D).birth_bound key).trans (Nat.le_succ _)) i)
        (chosen (commands P D key) i) :=
  (origin P D key i).denominator_eq

theorem origin_birth (P : Parameters) (D : Data P) (key : List Bool) (i : Fin ((family P D).birth key)) :
    (older (commands P D key) i).length = prefixLength P key - 1 - i.val :=
  padded_producer_birth (D.rules (pairFst key)) (prefixLength P key) i

def producerKey (z : List Bool) : List Bool := pair (RankedHistoryTask.root (pairFst z))
  (pair (BinaryNatCode.encode (IntegralMixedOldBankCofactorBits.producerBirth z)) [])

theorem producerKey_FP : producerKey ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP RankedHistoryTask.root_FP)
    (mem_FP_pair IntegralMixedOldBankCofactorBits.producerBirth_binary.bits_mem_FP (constFn_mem_FP []))

noncomputable def routing (P : Parameters) (D : Data P) : IntegralMixedOldBankCofactorBits.Routing where
  coordinate z := (creatingCommand P D (producerKey z)).coordinate
  context z := (creatingCommand P D (producerKey z)).context

theorem routingAccess (P : Parameters) (D : Data P) (h : Metadata P D) : IntegralMixedOldBankCofactorBits.RoutingAccess (routing P D) where
  coordinate := h.coordinate.comp producerKey_FP
  context := h.context.comp producerKey_FP

theorem routing_context_bound (P : Parameters) (D : Data P) (z : List Bool) :
    (routing P D).context z ≤ numericCap P (RankedHistoryTask.root (pairFst z)) :=
  (Command.context_le _).trans ((by decide : 4 ≤ 6).trans (IntegralMixedRoutineTaskBits.routine_cap P _))

theorem routing_coordinate_bound (P : Parameters) (D : Data P) (z : List Bool) :
    (routing P D).coordinate z ≤ numericCap P (RankedHistoryTask.root (pairFst z)) := by
  have H := Command.coordinate_le (creatingCommand P D (producerKey z))
  have HR : pairFst (producerKey z) = RankedHistoryTask.root (pairFst z) := pairFst_pair _ _
  have HB := H.trans_eq (congrArg P.ambient HR)
  exact (HB.trans (Nat.le_succ _)).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.1

theorem origin_command (P : Parameters) (D : Data P) (key : List Bool) (i : Fin ((family P D).birth key)) :
    chosen (commands P D key) i =
      (chronological (D.rules (pairFst key)) (prefixLength P key - 1 - i.val)).getD defaultCommand := by
  have HI : i.val < prefixLength P key := lt_of_lt_of_eq i.isLt (family_birth P D key)
  have HB : prefixLength P key - 1 - i.val < prefixLength P key := by omega
  have HA := padded_producer_command (D.rules (pairFst key)) (prefixLength P key) i
  have HC := paddedPast_chronological (D.rules (pairFst key)) (prefixLength P key) _ HB
  exact Option.some.inj (HA.symm.trans HC)
end LeanCanny.Algebra.IntegralMixedFullHistoryFamilyBits
