/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarRoots
public import LeanCanny.Encoding.IntegralFramedCompleteSuffixSaved
/-! # One full terminal tuple interprets every literal older saved prefix

Only same-root chronology is required. The old generator values use the
raw scalar suffix of the same full vertex with the OLD weights. No old
vertex, label reindexing, power ratio, or selected-hom oracle is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalOlderParent
open LeanCanny.Algebra IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralMixedFramedHistoryFamilyBits (Plan family prefixLength initial)
open IntegralMixedFramedFamilyRunView (runAt)
open IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

private theorem run_roots_congr (P : Parameters) (D : Plan P) (r s : List Bool) (a b : ℕ)
    (ha : a≤P.cap r+1) (hb : b≤P.cap s+1) (hr : r=s) (he : a=b) (z : ℕ→ℝ) :
    RootsAt (runAt P D r a ha).sampler.scalarPrefix z ↔ RootsAt (runAt P D s b hb).sampler.scalarPrefix z :=by
  cases hr
  cases he
  rfl

theorem older_roots (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (old terminal : List Bool) (hroot : pairFst terminal=pairFst old)
    (hfit : (family P D H).birth old≤(family P D H).birth terminal) (z : ℕ→ℝ)
    (hz : RootsAt ((family P D H).state terminal).sampler.scalarPrefix z) :
    RootsAt ((family P D H).state old).sampler.scalarPrefix
      (fun i=>z (i+((family P D H).birth terminal-(family P D H).birth old))) :=by
  let root:=pairFst old
  let b:=prefixLength P old
  let newer:=(family P D H).birth terminal-b
  have HB : b≤P.cap root+1:=min_le_right _ _
  have HM : (family P D H).birth terminal≤P.cap root+1 :=by
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    exact (min_le_right _ _).trans_eq (congrArg (fun r=>P.cap r+1) hroot)
  have HF : b≤(family P D H).birth terminal :=by
    exact (IntegralMixedFramedHistoryFamilyBits.family_birth P D H old).symm.trans_le hfit
  have HE : prefixLength P terminal=b+newer :=by
    rw [←IntegralMixedFramedHistoryFamilyBits.family_birth P D H terminal]
    dsimp only [newer]
    omega
  have HNew:=(IntegralFramedCompleteSuffixSaved.roots_at_word P D H terminal z).mp hz
  have HN:=(run_roots_congr P D (pairFst terminal) root (prefixLength P terminal) (b+newer)
    (min_le_right _ _) (by omega) hroot HE z).mp HNew
  have HO:=padded_roots_suffix (initial P D root)
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) b newer (by omega) z HN
  apply (IntegralFramedCompleteSuffixSaved.roots_at_word P D H old _).mpr
  have HD : (family P D H).birth terminal-(family P D H).birth old=newer :=by
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth P D H old]
  simpa only [HD,root,b,runAt] using HO

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
  (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hpos) c w)
  (old : List Bool) (hroot : pairFst (key c)=pairFst old)
  (hfit : (family P D H).birth old≤(family P D H).birth (key c))

include hroot in
theorem exists_interpretation :
    ∃φ : ((family P D H).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀i,φ (((family P D H).state old).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hpos c w hv
          (UniformIntegralPowerSchedule.embed hfit i)^
          UniformIntegralPowerSchedule.weights ((family P D H).cap old) (2^(family P D H).width old)
            ((family P D H).birth old) i :=by
  let z:=IntegralMixedFramedBankObservation.extend (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hpos c w hv)
  have HR:=older_roots P D H old (key c) hroot hfit z (IntegralFramedPhysicalSquare.scalar_roots_at P D H L F C hs key hpos c w hv)
  obtain ⟨φ,hφ⟩:=((family P D H).state old).sampler.scalarPrefix.interpret ℝ
    (fun i=>z (i.val+((family P D H).birth (key c)-(family P D H).birth old))) HR
  refine ⟨φ,fun i=>(hφ i).trans ?_⟩
  apply congrArg (fun a : ℝ=>a^UniformIntegralPowerSchedule.weights ((family P D H).cap old)
    (2^(family P D H).width old) ((family P D H).birth old) i)
  have HI : i.val+((family P D H).birth (key c)-(family P D H).birth old)<(family P D H).birth (key c) :=by
    have HH:=i.isLt
    omega
  dsimp only [z,IntegralMixedFramedBankObservation.extend]
  rw [dite_eq_left HI]
  apply congrArg
  apply Fin.ext
  exact Nat.add_comm _ _
end LeanCanny.Encoding.IntegralFramedPhysicalOlderParent
