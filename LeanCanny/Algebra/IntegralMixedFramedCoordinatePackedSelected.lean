/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedBounds
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateHeadWidth
/-! # The actual full packed coordinate head uses one selected old hom -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedSelected
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (parent : List Bool→List Bool) (q : List Bool)
local notation "G" => family P D H
local notation "key" => IntegralMixedVirtualTaskBits.saved P (parent q)
local notation "x" => IntegralMixedCutSource.Family.state (family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "r" => IntegralMixedCutSource.Family.rule (family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "j" => IntegralMixedCoordinateCoefficientSnapshot.coordinate (family P D H)
  (IntegralMixedVirtualTaskBits.saved P (parent q)) (get P Field.slot13 (parent q))

theorem horizon_eq : IntegralMixedFramedAllCoordinateSourceBits.horizon P (parent q)=(G).cap key :=by
  unfold IntegralMixedFramedHistoryFamilyBits.family
  change P.cap (RankedHistoryTask.root (parent q))+1=P.cap (pairFst key)+1
  rw [IntegralMixedVirtualTaskBits.saved,pairFst_pair]

theorem head_eq (d e : List Bool→ℕ) :
    IntegralMixedFramedCoordinatePackedBits.head P D H parent d e q=
      IntegralMixedSelectedCoordinateHead.head x ((G).birth_bound key) r j (d q) (e q) :=by
  unfold IntegralMixedFramedCoordinatePackedBits.head IntegralMixedSelectedCoordinateHead.head
  rw [horizon_eq P D H parent q]

theorem fullDegree_eq : IntegralMixedSelectedCoordinateHead.fullDegree P G parent q=
    PurePowerReductionBounds.dimension ((G).ambient key-(r).critical.offset.val+1) ((G).spatial key).degree :=rfl

theorem fullParameter_eq : IntegralMixedSelectedCoordinateHead.fullParameter P parent q=2^(G).width key-1 :=by
  unfold IntegralMixedFramedHistoryFamilyBits.family
  change 2^P.width (RankedHistoryTask.root (parent q))-1=2^P.width (pairFst key)-1
  rw [IntegralMixedVirtualTaskBits.saved,pairFst_pair]

theorem full_selected
    (φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P (parent q))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (z : Fin ((G).birth key)→ℝ)
    (hφ : ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      z i^UniformIntegralPowerSchedule.weights ((G).cap key) (2^(G).width key) ((G).birth key) i) :
    (IntegralMixedFramedCoordinatePackedBits.head P D H parent
      (IntegralMixedSelectedCoordinateHead.fullDegree P G parent)
      (IntegralMixedSelectedCoordinateHead.fullParameter P parent) q).map
        (SelectedMultivariatePolynomialLift.evaluate (MvPolynomial.aeval z).toRingHom)=
      IntegralMixedCriticalSweep.selected x ((G).birth_bound key) r j φ :=by
  rw [head_eq,fullDegree_eq,fullParameter_eq]
  exact IntegralMixedSelectedCoordinateHead.selected_at_width x ((G).birth_bound key) r j φ z hφ ((G).scalar_cap key)

theorem guarded_full_selected
    (hc : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P (parent q))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (z : Fin ((G).birth key)→ℝ)
    (hφ : ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      z i^UniformIntegralPowerSchedule.weights ((G).cap key) (2^(G).width key) ((G).birth key) i) :
    (IntegralMixedFramedCoordinatePackedBits.guardedHead P D H parent
      (IntegralMixedSelectedCoordinateHead.fullDegree P G parent)
      (IntegralMixedSelectedCoordinateHead.fullParameter P parent) q).map
        (SelectedMultivariatePolynomialLift.evaluate (MvPolynomial.aeval z).toRingHom)=
      IntegralMixedCriticalSweep.selected x ((G).birth_bound key) r j φ :=by
  rw [IntegralMixedFramedCoordinatePackedBits.guardedHead,ite_eq_left hc]
  exact full_selected P D H parent q φ z hφ

end LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedSelected
