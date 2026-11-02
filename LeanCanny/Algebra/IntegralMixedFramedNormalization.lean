/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNormalizationPlanning
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalFamily
public import LeanCanny.Algebra.IntegralMixedNormalizationScopedCurrent
public import LeanCanny.Algebra.IntegralMixedRawDispatcherCurrent
public import LeanCanny.Algebra.IntegralMixedGramScopedCurrent
public import LeanCanny.Algebra.IntegralMixedPscContextBranch
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionScoped
/-! # Actual framed raw and normalization factories with current closure

Header controls come from represented framed instructions. The normalization
matrix height is derived from the actual bank/source syntax ceiling; no top
matrix evaluator or height oracle is supplied. Current raw, Gram and PSC replies
remain the lower routine contracts used when assembling the whole controller.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNormalizationBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedRawHeight IntegralMixedFramedOriginalBounds IntegralMixedFramedStepHeight
open scoped Classical

structure Controls (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  tables : IntegralMixedHeaderTablesBits.Tables
  native : IntegralMixedHeaderTablesBits.Access tables
  represents : IntegralMixedFramedHeaderBits.Represents P D H tables
  nodes : List Bool → ℕ
  factor : List Bool → ℕ
  seed : List Bool → ℕ
  nodes_native : BinaryFn nodes
  factor_native : BinaryFn factor
  seed_native : BinaryFn seed

theorem input (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : IntegralMixedVirtualQueryBits.InputMetadata (family P D H) :=
  IntegralMixedFramedPhysicalBits.virtualInputMetadata P a D H h.tables h.native h.represents

theorem degree (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : BinaryFn (family P D H).degree :=
  IntegralMixedFramedHeaderBits.degree_binary P a D H h.tables h.native h.represents

theorem kind (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : IntegralMixedRawKindBits.Metadata (family P D H) :=
  IntegralMixedFramedHeaderBits.rawMetadata P a D H h.tables h.native h.represents

theorem routingAccess (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : IntegralMixedOldBankCofactorBits.RoutingAccess (IntegralMixedFramedHeaderBits.routing P D) :=
  IntegralMixedFramedHeaderBits.routingAccess P a D H h.tables h.native h.represents

theorem heightNative (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : BinaryFn (rootCeiling P h.nodes h.factor h.seed) :=
  rootCeiling_binary P a h.nodes_native h.factor_native h.seed_native

noncomputable def machine (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : Machine :=
  IntegralMixedNormalizationScopedBits.machine P a (family P D H) (input P a D H h) (degree P a D H h)
    (rootCeiling P h.nodes h.factor h.seed) (heightNative P a D H h)

noncomputable def rawMachine (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : Machine :=
  IntegralMixedRawDispatcherBits.machine P a (family P D H) (input P a D H h) (kind P a D H h) (degree P a D H h)
    (IntegralMixedFramedHeaderBits.routing P D) (routingAccess P a D H h)

abbrev Matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q=5 → answer q=(machine P a D H h).model q

abbrev RawMatches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) (answer : List Bool → List Bool) : Prop :=
  IntegralMixedRawDispatcherBits.Matches P a (family P D H) (input P a D H h) (kind P a D H h) (degree P a D H h)
    (IntegralMixedFramedHeaderBits.routing P D) (routingAccess P a D H h) answer

theorem top_height (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) (hs : FamilyInputs P D h.nodes h.factor h.seed) (hF : ∀ root, 1≤h.factor root)
    (hf : ∀ key, FallbackBounds P D H h.nodes h.seed key) (q : List Bool)
    (i j : Fin (IntegralMixedNormalizationTopBits.dimension (family P D H) (IntegralMixedVirtualTaskBits.saved P q))) :
    (IntegralMixedNormalizationTopBits.top (family P D H) (IntegralMixedVirtualTaskBits.saved P q) i j).natAbs≤
      2^rootCeiling P h.nodes h.factor h.seed (RankedHistoryTask.root q) := by
  have HB := top_root_height P D H h.nodes h.factor h.seed hs hF hf (IntegralMixedVirtualTaskBits.saved P q) i j
  simpa only [IntegralMixedVirtualTaskBits.saved,pairFst_pair] using HB

theorem raw_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) (answer : List Bool → List Bool) (hr : RawMatches P a D H h answer) :
    IntegralMixedNormalizationScopedBits.RawMatches P (family P D H) answer :=
  IntegralMixedRawDispatcherBits.raw_matches P a (family P D H) (input P a D H h) (kind P a D H h) (degree P a D H h)
    (IntegralMixedFramedHeaderBits.routing P D) (routingAccess P a D H h) answer hr

theorem correct (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) (hs : FamilyInputs P D h.nodes h.factor h.seed) (hF : ∀ root, 1≤h.factor root)
    (hf : ∀ key, FallbackBounds P D H h.nodes h.seed key)
    (hc : ∀ root, requiredModulus P h.nodes h.factor h.seed root≤P.modulusBound root)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hn : Matches P a D H h (fun q => residueBits (x q))) (hr : RawMatches P a D H h (fun q => residueBits (x q))) :
    Correct (machine P a D H h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply IntegralMixedNormalizationScopedBits.correct_of_current P a (family P D H) (input P a D H h) (degree P a D H h)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H) (rootCeiling P h.nodes h.factor h.seed) (heightNative P a D H h)
    (fun q _ => top_height P D H h hs hF hf q) hc x _ (raw_matches P a D H h _ hr)
  intro q hq
  exact hn q hq.1 hq.2.1

theorem producer_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) (answer : List Bool → List Bool) (hn : Matches P a D H h answer) :
    IntegralMixedNormalizedCompanionBits.ScopedNormalizationMatches P (family P D H) answer := by
  intro q hv hr hp hx
  exact (hn q hv hr).trans (IntegralMixedNormalizationScopedBits.model_phase14 P a (family P D H)
    (input P a D H h) (degree P a D H h) (rootCeiling P h.nodes h.factor h.seed) (heightNative P a D H h) q ⟨hv,hr,hx⟩ hp)

theorem raw_correct (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : RawMatches P a D H h (fun q => residueBits (x q)))
    (critical : IntegralMixedVirtualContextComponentBits.Matches P (family P D H) (fun q => residueBits (x q)))
    (bank : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedOldBankCofactorBits.RepliesAt P (family P D H)
      (IntegralMixedFramedHeaderBits.routing P D) (fun q => residueBits (x q)) q)
    (gram : IntegralMixedGramScopedBits.CurrentMatches P a (family P D H) (input P a D H h) (fun q => residueBits (x q)))
    (psc : IntegralMixedPscContextBranchBits.CurrentMatches P a (family P D H) (input P a D H h) (fun q => residueBits (x q))) :
    Correct (rawMachine P a D H h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedRawDispatcherBits.correct P a (family P D H) (input P a D H h) (kind P a D H h) (degree P a D H h)
    (IntegralMixedFramedHeaderBits.routing P D) (routingAccess P a D H h) (IntegralMixedFramedHistoryFamilyBits.geometry P D H)
    x hm critical bank (IntegralMixedGramScopedBits.matches_of_current P a (family P D H) (input P a D H h) _ gram)
    (IntegralMixedPscContextBranchBits.matches_of_current P a (family P D H) (input P a D H h) _ psc)

theorem selected (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) (q : List Bool) : (machine P a D H h).selected q=true :=
  IntegralMixedNormalizationScopedBits.machine_selected P a (family P D H) (input P a D H h) (degree P a D H h)
    (rootCeiling P h.nodes h.factor h.seed) (heightNative P a D H h) q

theorem raw_selected (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) (q : List Bool) : (rawMachine P a D H h).selected q=true :=
  IntegralMixedRawDispatcherBits.selected P a (family P D H) (input P a D H h) (kind P a D H h) (degree P a D H h)
    (IntegralMixedFramedHeaderBits.routing P D) (routingAccess P a D H h) q

theorem canonical (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z=(machine P a D H h).model q :=
  IntegralMixedNormalizationScopedBits.canonical P a (family P D H) (input P a D H h) (degree P a D H h)
    (rootCeiling P h.nodes h.factor h.seed) (heightNative P a D H h) q

theorem raw_canonical (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z=(rawMachine P a D H h).model q :=
  IntegralMixedRawDispatcherBits.canonical P a (family P D H) (input P a D H h) (kind P a D H h) (degree P a D H h)
    (IntegralMixedFramedHeaderBits.routing P D) (routingAccess P a D H h) q

end LeanCanny.Algebra.IntegralMixedFramedNormalizationBits
