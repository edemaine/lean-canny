/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightPass
/-! # Exact product and earlier-birth frames for the mixed old-height pass -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open IntegralMixedOldHeightBits (request index writer_frame)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem pass_cofactor (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing)
    (q : List Bool) (hq : request P q) :
    (passScalars P D F R).cofactor q = cofactor P D F q * companionInteger P D F R q := by
  change (∏ j ∈ Finset.range (passCount P q), if j = index P q then 1 else passScale P D F R q j) = _
  rw [passCount, ite_eq_left hq, Finset.prod_range_succ]
  have HI : index P q < birth P q := by unfold index; rw [min_eq_left hq.1.1.le]; exact hq.1.1
  rw [ite_eq_right (Ne.symm (Nat.ne_of_lt HI)), passScale,
    dite_eq_right (by rw [bank_birth]; exact Nat.lt_irrefl _)]
  congr 1
  unfold cofactor CommonHeightBits.Scalars.cofactor
  change _ = ∏ j ∈ Finset.range ((bankFamily P D F).birth (IntegralMixedVirtualTaskBits.saved P q)),
    if j = index P q then 1 else IntegralMixedBankCofactor.scale (IntegralMixedVirtualTaskBits.family P (bankFamily P D F)) q j
  rw [bank_birth]
  apply Finset.prod_congr rfl
  intro j hj
  have HJ : j < (bankFamily P D F).birth (IntegralMixedVirtualTaskBits.saved P q) :=
    (Finset.mem_range.mp hj).trans_eq (bank_birth P D F q).symm
  by_cases HE : j = index P q
  · simp only [HE, ite_true]
  · simp only [ite_eq_right HE]
    rw [passScale, dite_eq_left HJ, IntegralMixedBankCofactor.scale]
    change _ = if hi : j < (bankFamily P D F).birth (IntegralMixedVirtualTaskBits.saved P q) then
      (state P D F q).bank.denominator ⟨j, hi⟩ else 1
    rw [dite_eq_left HJ]

theorem pass_requests_frame (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing)
    (reply : List Bool → List Bool) (q c : List Bool) (budget : List Bool → ℕ)
    (hc : (passProgram P D F R).controller.Requests reply budget q c) : IntegralMixedRoutineTaskBits.Frame P q c := by
  have HC := IntegralMixedVirtualNativeLowerBits.fold_requests_bound (passProgram P D F R) reply budget q c hc
  obtain ⟨j, hj, rfl⟩ := (CommonHeightRecursivePass.requests_iff (passScalars P D F R) (passTask P R) reply q c).mp HC
  change j < passCount P q at hj
  have HQ : request P q := by
    by_contra hn
    have H : j < 0 := by simpa only [passCount, ite_eq_right hn] using hj
    exact Nat.not_lt_zero j H
  have HJ : j < birth P q + 1 := by simpa only [passCount, ite_eq_left HQ] using hj
  by_cases HB : j < birth P q
  · rw [passTask_leading P D F R q _ j HB]
    exact IntegralMixedOldBankCofactorBits.writer_packet_frame P (bankFamily P D F)
      (IntegralMixedFramedHistoryFamilyBits.geometry P D F) R q j
      (HB.trans_eq (bank_birth P D F q).symm)
  · have HM : j = birth P q := by omega
    subst j
    rw [passTask_companion]
    exact writer_frame P R q HQ

noncomputable def passStateBound (P : Parameters) (q : List Bool) :=
  2 * q.length + 2 * (passCount P q).size + (modulus P q).size + 2

theorem passStateBound_unary (P : Parameters) (a : Access P) : UnaryFn (passStateBound P) := by
  have HC : UnaryFn (fun q => (passCount P q).size) :=
    (UnaryFn.length (BinaryFn.ofUnary (passCount_unary P a)).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  have HM : UnaryFn (fun q => (modulus P q).size) :=
    (UnaryFn.length (modulus_binary P a).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HC)).add HM).add (UnaryFn.const 2)

theorem pass_state_length (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (he : PassRepliesAt P D F R reply q) (t : ℕ) :
    (RecursiveFold.encState (((passProgram P D F R).controller.reference reply)^[t]
      ((passProgram P D F R).initial q))).length ≤ passStateBound P q := by
  have H := CommonHeightRecursivePass.orbit_length (passScalars P D F R) (passTask P R) reply q
    (passReplies_scale P D F R reply q he) t
  change _ ≤ 2 * q.length + 2 * (Turing.MultiTapeTM.encNat (passCount P q)).length +
    (BinaryNatCode.encode (modulus P q)).length + 2 at H
  simpa only [passProgram, passStateBound, Turing.MultiTapeTM.encNat_apply, Nat.size_eq_bits_len, BinaryNatCode.length_encode] using H

end LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
