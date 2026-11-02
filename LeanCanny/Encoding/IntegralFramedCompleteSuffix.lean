/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutParentRoots
public import LeanCanny.Encoding.SquareSampleCompleteVertices
public import LeanCanny.Algebra.IntegralMixedFramedSuffixRoots
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # One actual complete terminal vertex interprets every earlier framed prefix

Only the literal terminal tuple is decoded. All earlier row systems follow
from chronological padded-history persistence, including source changes and
out-of-range default instructions. The old interpretation is constructed.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCompleteSuffix
open LeanCanny.Algebra IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralMixedFramedHistoryFamilyBits (Plan family keyAt)
open IntegralMixedFramedFamilyRunView (runAt)
open IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

private theorem rows_roots_heq {a b : ℕ} (f : Fin a→MvPolynomial (Fin a) ℤ)
    (g : Fin b→MvPolynomial (Fin b) ℤ) (hm : a=b) (hf : HEq f g) (z : ℕ→ℝ) :
    (∀ i,(f i).eval₂ (Int.castRingHom ℝ) (fun j=>z j.val)=0) ↔
      (∀ i,(g i).eval₂ (Int.castRingHom ℝ) (fun j=>z j.val)=0) := by
  cases hm
  have he:=eq_of_heq hf
  cases he
  rfl

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀ q,0<(family P D H).birth (key q))
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w)

noncomputable def joint : ℕ→ℝ := IntegralMixedFramedBankObservation.extend
  (SquareSampleCompleteVertices.candidate (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w hv).val

theorem terminal_roots : RootsAt ((family P D H).state (key c)).sampler.scalarPrefix
    (joint P D H L F C hs key hpos c w hv) := by
  have HM : (IntegralFramedCompleteSquare.input P D H L F C hs key hpos).count c=(family P D H).birth (key c) := rfl
  have HR : ∀ i,((IntegralFramedCompleteSquare.input P D H L F C hs key hpos).system c i).eval₂ (Int.castRingHom ℝ)
      (fun j=>joint P D H L F C hs key hpos c w hv j.val)=0 := by
    intro i
    have HE : (fun j : Fin ((IntegralFramedCompleteSquare.input P D H L F C hs key hpos).count c)=>
        joint P D H L F C hs key hpos c w hv j.val)=
        (SquareSampleCompleteVertices.candidate (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w hv).val := by
      funext j
      unfold joint IntegralMixedFramedBankObservation.extend
      rw [dite_eq_left j.isLt]
    rw [HE]
    exact (SquareSampleCompleteVertices.candidate (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w hv).property i
  exact (rows_roots_heq _ _ HM (IntegralFramedCompleteSquare.rows_heq P D H L F C hs key hpos c) _).mp HR

omit L F C hs key hpos c w hv in
theorem roots_at_keys (root oldContext terminalContext : List Bool) (birth newer : ℕ)
    (hb : birth+newer≤P.cap root+1) (z : ℕ→ℝ)
    (hz : RootsAt ((family P D H).state (keyAt root (birth+newer) terminalContext)).sampler.scalarPrefix z) :
    RootsAt ((family P D H).state (keyAt root birth oldContext)).sampler.scalarPrefix (fun i=>z (i+newer)) := by
  have HNew:=(IntegralFramedCutParentRoots.roots_at_key P D H root terminalContext (birth+newer) hb z).mp hz
  have HOld:=padded_roots_suffix (IntegralMixedFramedHistoryFamilyBits.initial P D root)
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) birth newer (by omega) z HNew
  exact (IntegralFramedCutParentRoots.roots_at_key P D H root oldContext birth (by omega) (fun i=>z (i+newer))).mpr HOld

theorem suffix_roots (root oldContext terminalContext : List Bool) (birth newer : ℕ)
    (hb : birth+newer≤P.cap root+1) (hk : key c=keyAt root (birth+newer) terminalContext) :
    RootsAt ((family P D H).state (keyAt root birth oldContext)).sampler.scalarPrefix
      (fun i=>joint P D H L F C hs key hpos c w hv (i+newer)) := by
  have HR:=terminal_roots P D H L F C hs key hpos c w hv
  rw [hk] at HR
  exact roots_at_keys P D H root oldContext terminalContext birth newer hb _ HR

theorem exists_interpretation (root oldContext terminalContext : List Bool) (birth newer : ℕ)
    (hb : birth+newer≤P.cap root+1) (hk : key c=keyAt root (birth+newer) terminalContext) :
    ∃ φ : ((family P D H).state (keyAt root birth oldContext)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀ i,φ (((family P D H).state (keyAt root birth oldContext)).sampler.scalarPrefix.basis.generator i)=
        joint P D H L F C hs key hpos c w hv (i.val+newer)^
          UniformIntegralPowerSchedule.weights ((family P D H).cap (keyAt root birth oldContext))
            (2^(family P D H).width (keyAt root birth oldContext)) ((family P D H).birth (keyAt root birth oldContext)) i :=
  ((family P D H).state (keyAt root birth oldContext)).sampler.scalarPrefix.interpret ℝ
    (fun i=>joint P D H L F C hs key hpos c w hv (i.val+newer))
    (suffix_roots P D H L F C hs key hpos c w hv root oldContext terminalContext birth newer hb hk)

end LeanCanny.Encoding.IntegralFramedCompleteSuffix
