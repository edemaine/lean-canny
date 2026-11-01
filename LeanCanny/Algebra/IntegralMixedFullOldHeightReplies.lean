/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullOldHeight
public import LeanCanny.Algebra.IntegralMixedOldBankLeadingSnapshot
/-! # Current actual producer replies suffice for literal mixed old-height evaluation -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedOldHeightBits
open IntegralMixedOldBankCofactorBits (Routing)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure ProducerRepliesAt (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (R : Routing) (reply : List Bool → List Bool) (q : List Bool) : Prop where
  leading : request P q → ∀ i : Fin (IntegralMixedOldBankCofactorBits.count P (bankFamily P D) q),
    let c := IntegralMixedOldBankCofactorBits.writer P R (IntegralMixedOldBankCofactorBits.packet P (bankFamily P D) q i.val)
    reply c = residueBits (IntegralMixedFullHistoryCompanionBits.leading P D
      (IntegralMixedVirtualTaskBits.saved P c) : ZMod (modulus P c))
  companion : request P q → reply (writer P R q) = IntegralMixedFullHistoryCompanionBits.value P D (writer P R q)

attribute [local irreducible] IntegralMixedFullHistoryCompanionBits.leading IntegralMixedOldBankLeadingBits.rootLeading

theorem producer_replies (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (he : ProducerRepliesAt P D R reply q) : PassRepliesAt P D R reply q := by
  refine ⟨?_, he.companion⟩
  intro hq i
  let c := IntegralMixedOldBankCofactorBits.writer P R (IntegralMixedOldBankCofactorBits.packet P (bankFamily P D) q i.val)
  have HL : IntegralMixedFullHistoryCompanionBits.leading P D (IntegralMixedVirtualTaskBits.saved P c) =
      ((bankFamily P D).state (IntegralMixedVirtualTaskBits.saved P q)).bank.denominator i :=
    IntegralMixedOldBankLeadingBits.child_leading P D R q i
  have HM : modulus P c = modulus P q := by
    simpa only [c, IntegralMixedOldBankCofactorBits.packet, pairFst_pair] using
      IntegralMixedOldBankCofactorBits.writer_modulus P R (IntegralMixedOldBankCofactorBits.packet P (bankFamily P D) q i.val)
  have HC := congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m)) HL HM
  exact (he.leading hq i).trans HC

theorem correct_of_producers (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullHistoryFamilyBits.Metadata P D) (reply : List Bool → List Bool)
    (he : ∀ q, IntegralMixedNativeOldHeightBits.selected P q = true →
      ProducerRepliesAt P D (IntegralMixedFullHistoryFamilyBits.routing P D) reply q) :
    NativeControllerBranch.Correct (machine P a D h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a D h reply (fun q hq => producer_replies P D _ reply q (he q hq))

end LeanCanny.Algebra.IntegralMixedFullOldHeightBits
