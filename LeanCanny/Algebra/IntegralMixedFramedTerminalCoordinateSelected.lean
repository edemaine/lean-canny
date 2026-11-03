/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedSelected
public import LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateHead
public import LeanCanny.Algebra.SelectedParameterHeadEvaluation
/-! # Full terminal coordinate heads specialize the same older algebra

The old raw tuple is the literal scalar suffix of the terminal tuple.
Its generator interpretation is explicit here and can be discharged from
full-system roots; no independent old vertex or coefficient evaluator is used.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateSelected
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (parent terminal : List Bool→List Bool) (q : List Bool)
local notation "G" => family P D H
local notation "oldKey" => IntegralMixedVirtualTaskBits.saved P (parent q)
local notation "x" => IntegralMixedCutSource.Family.state (family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "r" => IntegralMixedCutSource.Family.rule (family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "j" => IntegralMixedCoordinateCoefficientSnapshot.coordinate (family P D H)
  (IntegralMixedVirtualTaskBits.saved P (parent q)) (get P Field.slot13 (parent q))
local notation "d" => IntegralMixedSelectedCoordinateHead.fullDegree P (family P D H) parent
local notation "e" => IntegralMixedSelectedCoordinateHead.fullParameter P parent

theorem full_selected (hcore : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q)
    (φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P (parent q))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (z : Fin (IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count→ℝ)
    (hφ : ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      z (UniformIntegralPowerSchedule.embed hcount i)^
        UniformIntegralPowerSchedule.weights ((G).cap oldKey) (2^(G).width oldKey) ((G).birth oldKey) i) (η : ℝ) :
    (IntegralMixedFramedTerminalCoordinateHeadBits.polynomial P D H parent terminal d e q).map
      (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons η z))=
        (IntegralMixedCriticalSweep.selected x ((G).birth_bound oldKey) r j φ).map (Polynomial.evalRingHom η) :=by
  unfold IntegralMixedFramedTerminalCoordinateHeadBits.polynomial
  rw [dite_eq_left hcount]
  change (SelectedParameterHeadEvaluation.enlarged hcount
    (IntegralMixedFramedCoordinatePackedBits.guardedHead P D H parent d e q)).map _=_
  rw [SelectedParameterHeadEvaluation.suffix,←SelectedParameterHeadEvaluation.map_point]
  exact congrArg (fun p : (ℝ[X])[X]=>p.map (Polynomial.evalRingHom η))
    (IntegralMixedFramedCoordinatePackedSelected.guarded_full_selected P D H parent q hcore φ
      (fun i=>z (UniformIntegralPowerSchedule.embed hcount i)) hφ)

theorem specialized_degree (hcore : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q)
    (φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P (parent q))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (z : Fin (IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count→ℝ)
    (hφ : ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      z (UniformIntegralPowerSchedule.embed hcount i)^
        UniformIntegralPowerSchedule.weights ((G).cap oldKey) (2^(G).width oldKey) ((G).birth oldKey) i) (η : ℝ) :
    ((IntegralMixedFramedTerminalCoordinateHeadBits.polynomial P D H parent terminal d e q).map
      (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons η z))).natDegree=
        PurePowerReductionBounds.dimension ((G).ambient oldKey-(r).critical.offset.val+1) ((G).spatial oldKey).degree :=by
  rw [full_selected P D H parent terminal q hcore hcount φ z hφ η]
  exact IntegralMixedCriticalSweep.specialized_degree x ((G).birth_bound oldKey) r j φ η

end LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateSelected
