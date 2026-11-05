/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalInterpretation
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalPoint
/-! # Both external slack sources vanish at one marked lift of the own tuple -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialExternalSlackRoots
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.ETR
open FormulaSignSlotRadialExternalContext FormulaSignSlotRadialExternalPreludeNative
open FormulaSignSlotRadialExternalInterpretation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
def CorrelatedRoots {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (E r : ℕ)
    (sphere regular : Polynomial ℤ) (p : ℕ→ℝ) : Prop :=
  ∃ a : BoundedZeroSource.Bounded q r,
    (∀i : Fin n,a.val i=p i.val) ∧
    sphere.eval₂ (Int.castRingHom ℝ) (BoundedRegularSource.sphereSlack q r a)=0 ∧
    regular.eval₂ (Int.castRingHom ℝ) (BoundedRegularSource.regularSlack q E E r a).re=0

private theorem from_interpretation (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (N R d L K : List Bool→ℕ) (M n E r : ℕ)
    (hM : M=n) (hN : N key=n) (hR : R key=r)
    (hd : d key=BoundedZeroSource.powerDegree E)
    (hL : L key=BoundedRegularSource.regularizationExponent n E E r)
    (hK : K key=BoundedZeroSource.penaltyExponent n E r)
    (q : MvPolynomial (Fin n) ℤ) (a : BoundedZeroSource.Bounded q r) (p : ℕ→ℝ)
    (ha : ∀i : Fin n,a.val i=p i.val) (HI : CoordinateInterpretation P D H key M p) :
    CorrelatedRoots q E r
      (Polynomial.expand ℤ 2 (ScaledGradedReductionAnnihilator.polynomial
        (IntegralMixedFramedSlackMatrixBits.sphere P D H N R key)
        (IntegralMixedFramedSlackMatrixBits.commonAt P D H key^2) 1))
      (Polynomial.expand ℤ (d key) (ScaledGradedReductionAnnihilator.polynomial
        (IntegralMixedFramedSlackMatrixBits.regular P D H N d R L K key)
        ((2:ℤ)^L key*IntegralMixedFramedSlackMatrixBits.commonAt P D H key^d key) 1)) p := by
  cases hM
  obtain ⟨φ,hφ⟩ := HI
  have HC : ∀i : Fin M,φ (IntegralMixedFramedSlackMatrixBits.elementAt P D H key (M-i.val))=
      (IntegralMixedFramedSlackMatrixBits.commonAt P D H key:ℝ)*a.val i := by
    intro i
    rw [ha]
    exact hφ i
  refine ⟨a,ha,?_,?_⟩
  · exact IntegralMixedFramedSlackPolynomialRootsAt.sphere_root P D H key N R M r hN hR φ q a HC
  · exact IntegralMixedFramedSlackPolynomialRootsAt.regular_root P D H key N R M r hN hR φ q a HC E E d L K hd hL hK

attribute [local irreducible] Term.finitePolynomial CanonicalAuxiliaryCandidateCover.equation
  AuxiliaryCandidateRegularLift.original FormulaSignSlotRadialExternalSlackSource.sphereSource
  FormulaSignSlotRadialExternalSlackSource.regularSource

variable (H : List Bool) (k : ℕ) (Gamma label : List Bool) (side : Bool) (w : List Bool)
local notation "ctx" => packet H k Gamma label side w
local notation "m" => CanonicalAuxiliaryCandidateCover.dimension (FormulaSignSlotRadialJointLayout.source side H)
local notation "q" => AuxiliaryCandidateRegularLift.original CanonicalAuxiliaryCandidateCover.dimension
  CanonicalAuxiliaryCandidateCover.equation (FormulaSignSlotRadialJointLayout.source side H)
local notation "r" => FormulaSignSlotRadialExternalPrelude.radius ctx
local notation "E" => AuxiliaryCandidateRegularLift.allowance CanonicalAuxiliaryCandidateCover.equation
  (FormulaSignSlotRadialJointLayout.source side H)
local notation "key" => FormulaSignSlotRadialExternalSlackSource.key ctx

private theorem n_at : FormulaSignSlotRadialExternalSlackSource.N key=m := by
  have HN := number_packet H k Gamma label side w
  dsimp only [FormulaSignSlotRadialJointLayout.circleCount] at HN
  exact (FormulaSignSlotRadialExternalSlackSource.N_at ctx).trans HN
private theorem charge_at : FormulaSignSlotRadialExternalSlackSource.charge key=E := by
  simp only [FormulaSignSlotRadialExternalSlackSource.charge,FormulaSignSlotRadialExternalSlackSource.key_root,
    FormulaSignSlotRadialExternalPrelude.original,original_packet,AuxiliaryCandidateRegularLift.allowance]

theorem exists_roots
    (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid ctx)
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈
      FormulaSignSlotRadialJointStratumSampler.language) :
    CorrelatedRoots (n := m) q E r
      (FormulaSignSlotRadialExternalSlackSource.sphereSource.polynomial key)
      (FormulaSignSlotRadialExternalSlackSource.regularSource.polynomial key)
      (FormulaSignSlotRadialExternalCoordinates.point ctx hw) := by
  let a := FormulaSignSlotRadialExternalPoint.boundedPoint H k Gamma label side w hw hq
  have HA := FormulaSignSlotRadialExternalPoint.boundedPoint_coordinate H k Gamma label side w hw hq
  dsimp only [FormulaSignSlotRadialJointLayout.circleCount] at HA
  have HM := number_packet H k Gamma label side w
  dsimp only [FormulaSignSlotRadialJointLayout.circleCount] at HM
  have HD : FormulaSignSlotRadialExternalSlackSource.d key=BoundedZeroSource.powerDegree E :=
    congrArg BoundedZeroSource.powerDegree (charge_at H k Gamma label side w)
  have HL : FormulaSignSlotRadialExternalSlackSource.Lam key=BoundedRegularSource.regularizationExponent m E E r := by
    simp only [FormulaSignSlotRadialExternalSlackSource.Lam,n_at H k Gamma label side w,
      charge_at H k Gamma label side w,FormulaSignSlotRadialExternalSlackSource.R_at]
  have HK : FormulaSignSlotRadialExternalSlackSource.K key=BoundedZeroSource.penaltyExponent m E r := by
    simp only [FormulaSignSlotRadialExternalSlackSource.K,n_at H k Gamma label side w,
      charge_at H k Gamma label side w,FormulaSignSlotRadialExternalSlackSource.R_at]
  have HC := from_interpretation certifiedParameters certifiedPlan certifiedData key
    FormulaSignSlotRadialExternalSlackSource.N FormulaSignSlotRadialExternalSlackSource.R
    FormulaSignSlotRadialExternalSlackSource.d FormulaSignSlotRadialExternalSlackSource.Lam FormulaSignSlotRadialExternalSlackSource.K
    _ m E r HM (n_at H k Gamma label side w) (FormulaSignSlotRadialExternalSlackSource.R_at ctx) HD HL HK q a
    (FormulaSignSlotRadialExternalCoordinates.point ctx hw) HA (exists_interpretation ctx hw)
  have HS := IntegralMixedFramedChargedSlackSource.sphere_polynomial certifiedParameters certifiedPlan certifiedData
    (fun _=>1) (fun _=>1) seed certifiedInputs FormulaSignSlotRadialExternalSlackSource.N FormulaSignSlotRadialExternalSlackSource.R key
  have HR := IntegralMixedFramedChargedSlackSource.regular_polynomial certifiedParameters certifiedPlan certifiedData
    (fun _=>1) (fun _=>1) seed certifiedInputs FormulaSignSlotRadialExternalSlackSource.N FormulaSignSlotRadialExternalSlackSource.d
    FormulaSignSlotRadialExternalSlackSource.R FormulaSignSlotRadialExternalSlackSource.Lam FormulaSignSlotRadialExternalSlackSource.K key
  unfold FormulaSignSlotRadialExternalSlackSource.sphereSource FormulaSignSlotRadialExternalSlackSource.regularSource
  exact Eq.mp (congrArg₂ (fun sp rp => CorrelatedRoots q E r sp rp
    (FormulaSignSlotRadialExternalCoordinates.point ctx hw)) HS.symm HR.symm) HC

end LeanCanny.Encoding.FormulaSignSlotRadialExternalSlackRoots
