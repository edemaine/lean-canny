/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualNativeAccess
public import LeanCanny.Algebra.IntegralCriticalLeadingSpace
public import LeanCanny.Computation.TwoCallController
/-! # Resumable common-leading arithmetic for virtual critical sources

The original integer leading and common denominator are recursive replies.
The local native postprocessor computes a * Q^D * D modulo the caller's
modulus. Its certificates assume no evaluator for either scalar leaf.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualLeadingRequestBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralFrozenPowerBits
set_option backward.isDefEq.respectTransparency false

def post (S : Source) (z : List Bool) : List Bool :=
  IntegralCriticalLeadingBits.degreePost S (pair (pairFst z)
    (multiplyPost S (pair (pairFst z) (pair (pairFst (pairSnd z))
      (IntegralCriticalLeadingBits.powerPost S (pair (pairFst z) (pairSnd (pairSnd z))))))))

theorem post_FP (S : Source) (a : Access S) : post S ∈ FP := by
  have HP := mem_FP_comp (mem_FP_pair pairFst_mem_FP
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)) (IntegralCriticalLeadingBits.powerPost_FP S a)
  have HM := mem_FP_comp (mem_FP_pair pairFst_mem_FP
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) HP)) (multiplyPost_FP S a)
  exact mem_FP_comp (mem_FP_pair pairFst_mem_FP HM) (IntegralCriticalLeadingBits.degreePost_FP S a)

theorem post_packet (S : Source) (q : List Bool) (a b : ZMod (S.modulus q)) :
    post S (pair q (pair (residueBits a) (residueBits b))) =
      residueBits (a * b ^ S.allowance q * (S.allowance q : ZMod (S.modulus q))) := by
  simp only [post, pairFst_pair, pairSnd_pair]
  rw [IntegralCriticalLeadingBits.powerPost_packet, multiplyPost_packet,
    IntegralCriticalLeadingBits.degreePost_packet]

def program (S : Source) (originalLeading commonDenominator : List Bool → List Bool) : RecursiveFold.Program :=
  TwoCall.program originalLeading commonDenominator (post S)

theorem certificates (S : Source) (a : Access S) (originalLeading commonDenominator : List Bool → List Bool)
    (hl : originalLeading ∈ FP) (hq : commonDenominator ∈ FP) :
    (program S originalLeading commonDenominator).controller.Certificates
      (encQ := encBits) (encS := RecursiveFold.encState) :=
  TwoCall.certificates originalLeading commonDenominator (post S) hl hq (post_FP S a)

theorem value_at (S : Source) (a : Access S) (originalLeading commonDenominator reply : List Bool → List Bool)
    (q : List Bool) (hl : reply (originalLeading q) = a.leading q)
    (hq : reply (commonDenominator q) = a.denominator q) :
    (program S originalLeading commonDenominator).value reply q = IntegralCriticalLeadingBits.value S q := by
  rw [program, TwoCall.value_eq, hl, hq, a.leading_eq, a.denominator_eq, post_packet]
  unfold IntegralCriticalLeadingBits.value
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]

theorem requests_iff (S : Source) (originalLeading commonDenominator reply : List Bool → List Bool)
    (q c : List Bool) :
    (program S originalLeading commonDenominator).controller.Requests reply (fun _ => 2) q c ↔
      c = originalLeading q ∨ c = commonDenominator q :=
  TwoCall.requests_iff originalLeading commonDenominator (post S) reply q c

theorem halted_after (S : Source) (originalLeading commonDenominator reply : List Bool → List Bool)
    (q : List Bool) :
    (program S originalLeading commonDenominator).controller.halted
      (((program S originalLeading commonDenominator).controller.reference reply)^[2]
        ((program S originalLeading commonDenominator).initial q)) = true :=
  (program S originalLeading commonDenominator).halted_after reply q

noncomputable def stateBound (S : Source) (q : List Bool) : ℕ :=
  2 * q.length + 2 * (encNat 2).length + (S.modulus q).size + 2

theorem stateBound_unary (S : Source) (a : Access S) : UnaryFn (stateBound S) := by
  have HM : UnaryFn (fun q => (S.modulus q).size) :=
    (UnaryFn.length a.modulus.bits_mem_FP).of_eq (fun _ => Nat.size_eq_bits_len _)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const (2 * (encNat 2).length))).add HM).add (UnaryFn.const 2)

theorem state_length_at (S : Source) (a : Access S) (originalLeading commonDenominator reply : List Bool → List Bool)
    (q : List Bool) (hl : reply (originalLeading q) = a.leading q)
    (hq : reply (commonDenominator q) = a.denominator q) (t : ℕ) :
    (RecursiveFold.encState (((program S originalLeading commonDenominator).controller.reference reply)^[t]
      ((program S originalLeading commonDenominator).initial q))).length ≤ stateBound S q := by
  let : NeZero (S.modulus q) := ⟨S.modulus_ne_zero q⟩
  have HL : (a.leading q).length ≤ (S.modulus q).size := by rw [a.leading_eq]; exact residueBits_length_le _ _
  have HV : (IntegralCriticalLeadingBits.value S q).length ≤ (S.modulus q).size := residueBits_length_le _ _
  have H := TwoCall.state_length originalLeading commonDenominator (post S) reply q t
  have HP : post S (pair q (pair (reply (originalLeading q)) (reply (commonDenominator q)))) =
      IntegralCriticalLeadingBits.value S q := by
    exact (TwoCall.value_eq originalLeading commonDenominator (post S) reply q).symm.trans
      (value_at S a originalLeading commonDenominator reply q hl hq)
  rw [HP, hl] at H
  exact H.trans (by dsimp only [stateBound]; omega)

-- The concrete virtual source has this exact native program without changing
-- its coefficient algebra to a physical history prefix.
noncomputable abbrev virtualProgram (F : IntegralMixedCutSource.Family)
    (I : IntegralMixedVirtualSweepSource.Indices F) (originalLeading commonDenominator : List Bool → List Bool) :=
  program (IntegralMixedVirtualNativeBits.arithmetic F I).toGradient.toFrozen originalLeading commonDenominator
end LeanCanny.Algebra.IntegralMixedVirtualLeadingRequestBits
