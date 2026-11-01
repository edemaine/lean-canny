/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRoutineTask
public import LeanCanny.Algebra.IntegralMixedVirtualLeadingRequests
public import LeanCanny.Algebra.IntegralMixedVirtualFrozenRequests
public import LeanCanny.Algebra.IntegralMixedVirtualMonomialRequests
/-! # Concrete scalar-child tags for virtual arithmetic

The scalar routine uses phase digits 0,1,2,3,4 for original leading,
common denominator, old cleared height, common leading, and virtual height.
These names are local to routine zero; the shared phase codes are unchanged.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedScalarQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedRoutineTaskBits
set_option backward.isDefEq.respectTransparency false

def originalLeading (P : Parameters) := query P (birth P) .scalar .originalCoefficient
 def commonDenominator (P : Parameters) := query P (birth P) .scalar .derivativeCoefficient
 def oldHeight (P : Parameters) := query P (birth P) .scalar .clearedHeight
 def commonLeading (P : Parameters) := query P (birth P) .scalar .monomialFactor
 def virtualHeight (P : Parameters) := query P (birth P) .scalar .factorPower

theorem scalarQuery_FP (P : Parameters) (a : Access P) (p : Phase) : query P (birth P) .scalar p ∈ FP :=
  query_FP P a (birth P) (BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (birthCap_unary P a))) .scalar p

theorem scalar_frame (P : Parameters) (p : Phase) (q : List Bool) (hr : 0 < routine P q) :
    Frame P q (query P (birth P) .scalar p q) := query_frame_routine P .scalar p q hr

theorem scalar_frame_phase (P : Parameters) (p : Phase) (q : List Bool)
    (hr : routine P q = 0) (hp : p.code < phase q) : Frame P q (query P (birth P) .scalar p q) := by
  have HC : birth P q ≤ birthCap P (RankedHistoryTask.root q) := min_le_right _ _
  refine ⟨query_root P (birth P) .scalar p q, query_length P (birth P) .scalar p q HC, ?_⟩
  apply lower_phase P q _ (query_birth P (birth P) .scalar p q HC)
  · rw [query_routine, hr]; rfl
  · rw [query_phase]; exact hp

theorem scalar_value (P : Parameters) (F : IntegralMixedCutSource.Family) (p : Phase) (q : List Bool) :
    (IntegralMixedVirtualTaskBits.source P F).value (query P (birth P) .scalar p q) =
      (IntegralMixedVirtualTaskBits.source P F).value q := by
  apply IntegralMixedVirtualTaskBits.value_invariance
  · exact query_root P (birth P) .scalar p q
  · exact query_birth P (birth P) .scalar p q (min_le_right _ _)
  · rw [query_get]; rfl
  · exact query_coordinate P (birth P) .scalar p q
  · rw [query_get]; rfl
  · rw [query_get]; rfl
  · rw [query_get]; rfl
  · unfold IntegralCriticalHistoryTask.modulus
    rw [query_get]
    rfl

noncomputable def commonLeadingProgram (P : Parameters) (F : IntegralMixedCutSource.Family) :=
  IntegralMixedVirtualLeadingRequestBits.program
    (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen (originalLeading P) (commonDenominator P)

theorem commonLeading_certificates (P : Parameters) (a : Access P)
    (F : IntegralMixedCutSource.Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (commonLeadingProgram P F).controller.Certificates
      (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  IntegralMixedVirtualLeadingRequestBits.certificates _ (IntegralMixedVirtualTaskBits.access P a F h).toEuler.toGradient.toFrozen
    _ _ (scalarQuery_FP P a .originalCoefficient) (scalarQuery_FP P a .derivativeCoefficient)

theorem commonLeading_value (P : Parameters) (a : Access P)
    (F : IntegralMixedCutSource.Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (reply : List Bool → List Bool) (q : List Bool)
    (hl : reply (originalLeading P q) = (IntegralMixedVirtualTaskBits.access P a F h).leading q)
    (hq : reply (commonDenominator P q) = (IntegralMixedVirtualTaskBits.access P a F h).denominator q) :
    (commonLeadingProgram P F).value reply q =
      IntegralCriticalLeadingBits.value (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen q :=
  IntegralMixedVirtualLeadingRequestBits.value_at _ (IntegralMixedVirtualTaskBits.access P a F h).toEuler.toGradient.toFrozen
    _ _ reply q hl hq

theorem commonLeading_requests_frame (P : Parameters) (F : IntegralMixedCutSource.Family)
    (reply : List Bool → List Bool) (q c : List Bool) (hr : routine P q = 0) (hp : phase q = 3)
    (hc : (commonLeadingProgram P F).controller.Requests reply (fun _ => 2) q c) : Frame P q c := by
  rcases (IntegralMixedVirtualLeadingRequestBits.requests_iff _ _ _ reply q c).mp hc with rfl | rfl
  · exact scalar_frame_phase P .originalCoefficient q hr (by rw [hp]; decide)
  · exact scalar_frame_phase P .derivativeCoefficient q hr (by rw [hp]; decide)
end LeanCanny.Algebra.IntegralMixedScalarQueryBits
