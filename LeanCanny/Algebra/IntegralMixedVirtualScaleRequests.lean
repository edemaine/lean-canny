/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualLeadingRequests
public import LeanCanny.Algebra.IntegralMixedScalarQueries
/-! # Charged original scale a * Q^D without modular division

The local postprocessor asks the same original-leading/common-denominator
children as the common-leading stage, and omits the final multiplication by
D. Thus the result is valid when D is not a unit modulo the caller modulus.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualScaleRequestBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralFrozenPowerBits
set_option backward.isDefEq.respectTransparency false

noncomputable def value (S : Source) (q : List Bool) : List Bool :=
  residueBits ((S.leading q * S.denominator q ^ S.allowance q : ℤ) : ZMod (S.modulus q))

def post (S : Source) (z : List Bool) : List Bool :=
  multiplyPost S (pair (pairFst z) (pair (pairFst (pairSnd z))
    (IntegralCriticalLeadingBits.powerPost S (pair (pairFst z) (pairSnd (pairSnd z))))))

theorem post_FP (S : Source) (a : Access S) : post S ∈ FP := by
  have HP := mem_FP_comp (mem_FP_pair pairFst_mem_FP
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)) (IntegralCriticalLeadingBits.powerPost_FP S a)
  exact mem_FP_comp (mem_FP_pair pairFst_mem_FP (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) HP)) (multiplyPost_FP S a)

theorem post_packet (S : Source) (q : List Bool) (a b : ZMod (S.modulus q)) :
    post S (pair q (pair (residueBits a) (residueBits b))) = residueBits (a * b ^ S.allowance q) := by
  simp only [post, pairFst_pair, pairSnd_pair]
  rw [IntegralCriticalLeadingBits.powerPost_packet, multiplyPost_packet]

def program (S : Source) (originalLeading commonDenominator : List Bool → List Bool) : RecursiveFold.Program :=
  TwoCall.program originalLeading commonDenominator (post S)

theorem certificates (S : Source) (a : Access S) (originalLeading commonDenominator : List Bool → List Bool)
    (hl : originalLeading ∈ FP) (hq : commonDenominator ∈ FP) :
    (program S originalLeading commonDenominator).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  TwoCall.certificates originalLeading commonDenominator (post S) hl hq (post_FP S a)

theorem value_at (S : Source) (a : Access S) (originalLeading commonDenominator reply : List Bool → List Bool)
    (q : List Bool) (hl : reply (originalLeading q) = a.leading q) (hq : reply (commonDenominator q) = a.denominator q) :
    (program S originalLeading commonDenominator).value reply q = value S q := by
  rw [program, TwoCall.value_eq, hl, hq, a.leading_eq, a.denominator_eq, post_packet]
  unfold value
  simp only [Int.cast_mul, Int.cast_pow]

theorem requests_iff (S : Source) (originalLeading commonDenominator reply : List Bool → List Bool) (q c : List Bool) :
    (program S originalLeading commonDenominator).controller.Requests reply (fun _ => 2) q c ↔
      c = originalLeading q ∨ c = commonDenominator q :=
  TwoCall.requests_iff originalLeading commonDenominator (post S) reply q c

theorem halted_after (S : Source) (originalLeading commonDenominator reply : List Bool → List Bool) (q : List Bool) :
    (program S originalLeading commonDenominator).controller.halted
      (((program S originalLeading commonDenominator).controller.reference reply)^[2]
        ((program S originalLeading commonDenominator).initial q)) = true :=
  (program S originalLeading commonDenominator).halted_after reply q

noncomputable abbrev stateBound := IntegralMixedVirtualLeadingRequestBits.stateBound
 theorem stateBound_unary (S : Source) (a : Access S) : UnaryFn (stateBound S) := IntegralMixedVirtualLeadingRequestBits.stateBound_unary S a

theorem state_length_at (S : Source) (a : Access S) (originalLeading commonDenominator reply : List Bool → List Bool)
    (q : List Bool) (hl : reply (originalLeading q) = a.leading q) (hq : reply (commonDenominator q) = a.denominator q) (t : ℕ) :
    (RecursiveFold.encState (((program S originalLeading commonDenominator).controller.reference reply)^[t]
      ((program S originalLeading commonDenominator).initial q))).length ≤ stateBound S q := by
  let : NeZero (S.modulus q) := ⟨S.modulus_ne_zero q⟩
  have HL : (a.leading q).length ≤ (S.modulus q).size := by rw [a.leading_eq]; exact residueBits_length_le _ _
  have HV : (value S q).length ≤ (S.modulus q).size := residueBits_length_le _ _
  have H := TwoCall.state_length originalLeading commonDenominator (post S) reply q t
  have HP : post S (pair q (pair (reply (originalLeading q)) (reply (commonDenominator q)))) = value S q :=
    (TwoCall.value_eq originalLeading commonDenominator (post S) reply q).symm.trans
      (value_at S a originalLeading commonDenominator reply q hl hq)
  rw [HP, hl] at H
  exact H.trans (by dsimp only [stateBound, IntegralMixedVirtualLeadingRequestBits.stateBound]; omega)
end LeanCanny.Algebra.IntegralMixedVirtualScaleRequestBits
