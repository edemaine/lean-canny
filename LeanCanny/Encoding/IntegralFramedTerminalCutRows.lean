/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutRootRows
public import LeanCanny.Encoding.IntegralFramedCompleteSuffixSaved
/-! # A terminal root satisfies every earlier actual normalized cut row -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutRows
open LeanCanny.Algebra IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralMixedFramedHistoryFamilyBits (Plan family keyAt prefixLength)
open IntegralMixedFramedFamilyRunView (runAt)
open IntegralMixedFramedHistoryScript
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedHistory.normalizedScalarPolynomial IntegralMixedCutMatrix.raw

private theorem run_roots_congr (P : Parameters) (D : Plan P) (r s : List Bool) (a b : ℕ)
    (ha : a≤P.cap r+1) (hb : b≤P.cap s+1) (hr : r=s) (he : a=b) (z : ℕ→ℝ) :
    RootsAt (runAt P D r a ha).sampler.scalarPrefix z ↔ RootsAt (runAt P D s b hb).sampler.scalarPrefix z := by
  cases hr
  cases he
  rfl

theorem prefix_roots (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (terminal root context : List Bool) (b : ℕ) (hroot : pairFst terminal=root)
    (hfit : b≤(family P D H).birth terminal) (z : ℕ→ℝ)
    (hz : RootsAt ((family P D H).state terminal).sampler.scalarPrefix z) :
    RootsAt ((family P D H).state (keyAt root b context)).sampler.scalarPrefix
      (fun i=>z (i+((family P D H).birth terminal-b))) := by
  let newer:=(family P D H).birth terminal-b
  have HM : (family P D H).birth terminal≤P.cap root+1 := by
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    exact (min_le_right _ _).trans_eq (congrArg (fun r=>P.cap r+1) hroot)
  have HE : prefixLength P terminal=b+newer := by
    rw [←IntegralMixedFramedHistoryFamilyBits.family_birth P D H terminal]
    dsimp only [newer]
    omega
  have HNew:=(IntegralFramedCompleteSuffixSaved.roots_at_word P D H terminal z).mp hz
  have HN:=(run_roots_congr P D (pairFst terminal) root (prefixLength P terminal) (b+newer)
    (min_le_right _ _) (by omega) hroot HE z).mp HNew
  have HOld:=padded_roots_suffix (IntegralMixedFramedHistoryFamilyBits.initial P D root)
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) b newer (by omega) z HN
  exact (IntegralFramedCutParentRoots.roots_at_key P D H root context b (by omega) _).mpr HOld

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀ q,0<(family P D H).birth (key q))
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w)
  (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
local notation "G" => family P D H
local notation "parent" => IntegralMixedVirtualTaskBits.saved P c
local notation "old" => IntegralMixedCutSource.Family.state G parent
local notation "degree" => IntegralMixedCutSource.Family.degree G parent
local notation "p" => IntegralMixedHistory.normalizedScalarPolynomial old
  (IntegralMixedCutMatrix.raw old (IntegralMixedCutSource.Family.birth_bound G parent)
    (IntegralMixedCutSource.Family.rule G parent) (IntegralMixedCutSource.Family.kind G parent) degree) degree
local notation "z" => IntegralFramedCompleteSuffix.joint P D H L F C hs key hpos c w hv

include ha in
theorem rows (hcut : IntegralFramedCreatingCut.ParentCut P D c)
    (hroot : pairFst (key c)=RankedHistoryTask.root c) (hfit : birth P c<(G).birth (key c)) :
    ∀ i,(UniformIntegralPrefixRows.rows ((G).cap parent) (old).sampler.scalarPrefix.rows (old).sampler.scalarPrefix.basis p degree i).eval₂
      (Int.castRingHom ℝ) (fun j=>z (j.val+((G).birth (key c)-(birth P c+1))))=0 := by
  let sigma : ℕ→ℝ:=fun j=>z (j+((G).birth (key c)-(birth P c+1)))
  have HR : RootsAt ((G).state (IntegralFramedCutSuccessor.key P c)).sampler.scalarPrefix sigma :=
    prefix_roots P D H (key c) (RankedHistoryTask.root c) (BinaryNatCode.encode (get P .slot15 c))
      (birth P c+1) hroot (by omega) z (IntegralFramedCompleteSuffix.terminal_roots P D H L F C hs key hpos c w hv)
  have HRows:=IntegralFramedCutRootRows.normalized_rows P D H c ha sigma HR hcut
  exact HRows

end LeanCanny.Encoding.IntegralFramedTerminalCutRows
