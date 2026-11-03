/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedZeroTarskiFamily
public import LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateSelected
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateOrderedQueries
public import LeanCanny.Algebra.MvTwoParameterEvaluation
public import LeanCanny.Geometry.IntegralMixedFramedWindowQuery
/-! # Exact same-terminal-tuple constant-head epsilon-window models -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedZeroTarskiBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family RealIteratedTarski.evaluate

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (d e selected : List Bool→ℕ)

theorem head_evaluated (c : List Bool) (z : Fin (arity P D H terminal c)→ℝ) (ε δ : ℝ) :
    ((head P D H parent terminal d e c).map (MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z)).map
      (RealIteratedTarski.evaluate ε δ)=
        (IntegralMixedFramedTerminalCoordinateHeadBits.polynomial P D H parent terminal d e c).map
          (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons 0 z)) :=by
  apply Polynomial.ext
  intro y
  simp only [Polynomial.coeff_map]
  rw [MvTwoParameterCoefficient.point_evaluate]
  have HT:=congrArg (fun p : ℝ[X]=>p.coeff y) (FixedWidthBivariateZeroLiftBits.selected
    (arity P D H terminal) (IntegralMixedFramedTerminalCoordinateHeadBits.polynomial P D H parent terminal d e) c z δ ε)
  simpa only [head,Polynomial.coeff_map,MvPolynomial.coe_eval₂Hom] using HT

theorem query_evaluated (power : List Bool→Fin 3) (negative : Bool) (c : List Bool)
    (hi : selected c<(atKey P D H (terminal c)).count) (z : Fin (arity P D H terminal c)→ℝ) (ε δ : ℝ) :
    ((query P D H L F C hs terminal selected power negative c).map
      (MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z)).map (RealIteratedTarski.evaluate ε δ)=
      (Polynomial.C (((atKey P D H (terminal c)).common:ℝ)^2)*
        (Polynomial.X-Polynomial.C (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal c)) z ⟨selected c,hi⟩)+
          Polynomial.C (if negative then -ε else ε)))^(power c).val :=by
  have Hbase :((baseQuery P D H L F C hs terminal selected negative c).map
      (MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z)).map (RealIteratedTarski.evaluate ε δ)=
        (IntegralMixedFramedWindowQuery.polynomial P D H L F C hs terminal selected negative c).map
          (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons ε z)) :=by
    apply Polynomial.ext
    intro y
    simp only [Polynomial.coeff_map]
    rw [MvTwoParameterCoefficient.point_evaluate]
    have HT:=congrArg (fun p : ℝ[X]=>p.coeff y) (FixedWidthBivariateZeroLiftBits.epsilon_selected
      (arity P D H terminal) (IntegralMixedFramedWindowQuery.polynomial P D H L F C hs terminal selected negative) c z δ ε)
    simpa only [baseQuery,Polynomial.coeff_map,MvPolynomial.coe_eval₂Hom] using HT
  unfold query
  rw [Polynomial.map_pow,Polynomial.map_pow,Hbase]
  apply congrArg (fun p : ℝ[X]=>p^(power c).val)
  apply Polynomial.funext
  intro u
  rw [Polynomial.eval_map]
  let Fw:=IntegralMixedFramedWindowQuery.family P D H L F C hs terminal selected
  have HE:=RationalMonomialWindowQuery.eval_cleared Fw negative c z hi
    (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.common_ne_zero P D H (terminal c)) ε u
  have HA : (Fw.scalars.numerator c:ℝ)*z ⟨Fw.index c,hi⟩^Fw.weight c/(Fw.scalars.denominator c:ℝ)=
      LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
        (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal c)) z ⟨selected c,hi⟩ :=
    LeanCanny.Geometry.IntegralMixedFramedWindowQuery.coordinate P D H L F C hs terminal selected c hi z
  have HF:=HE.trans (congrArg (fun a : ℝ=>(Fw.scalars.denominator c:ℝ)^2*(u-a+if negative then -ε else ε)) HA)
  simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_X,
    Fw,IntegralMixedFramedWindowQuery.polynomial,IntegralMixedFramedWindowQuery.family,
    IntegralMixedFramedBankScalars.scalars] using HF

theorem query_model (power : List Bool→Fin 3) (negative : Bool) (c : List Bool)
    (hi : selected c<(atKey P D H (terminal c)).count) (z : Fin (arity P D H terminal c)→ℝ) :
    (query P D H L F C hs terminal selected power negative c).map (MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z)=
      IntegralMixedSelectedCoordinateWindowDegree.query
        (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal c)) z ⟨selected c,hi⟩)
        (((atKey P D H (terminal c)).common:ℝ)^2) negative (power c) :=by
  apply MvTwoParameterCoefficient.polynomial_ext
  intro ε δ
  rw [query_evaluated P D H L F C hs terminal selected power negative c hi z ε δ,
    IntegralMixedSelectedCoordinateOrderedQueries.evaluated_query]

variable (q : List Bool)
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "oldKey" => IntegralMixedVirtualTaskBits.saved P (parent q)
local notation "x" => IntegralMixedCutSource.Family.state (IntegralMixedFramedHistoryFamilyBits.family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "r" => IntegralMixedCutSource.Family.rule (IntegralMixedFramedHistoryFamilyBits.family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "j" => IntegralMixedCoordinateCoefficientSnapshot.coordinate (IntegralMixedFramedHistoryFamilyBits.family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q)) (get P Field.slot13 (parent q))
local notation "fd" => IntegralMixedSelectedCoordinateHead.fullDegree P (IntegralMixedFramedHistoryFamilyBits.family P D H) parent
local notation "fe" => IntegralMixedSelectedCoordinateHead.fullParameter P parent

theorem head_model (hcore : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q)
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : Fin (arity P D H terminal q)→ℝ)
    (hφ :∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=z (UniformIntegralPowerSchedule.embed hcount i)^
      UniformIntegralPowerSchedule.weights ((G).cap oldKey) (2^(G).width oldKey) ((G).birth oldKey) i) :
    (head P D H parent terminal fd fe q).map (MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z)=
      IntegralMixedSelectedCoordinateWindowDegree.head
        (((IntegralMixedCriticalSweep.selected x ((G).birth_bound oldKey) r j φ).map (Polynomial.evalRingHom 0)).map Polynomial.C) :=by
  apply MvTwoParameterCoefficient.polynomial_ext
  intro ε δ
  rw [head_evaluated P D H parent terminal fd fe q z ε δ,
    IntegralMixedFramedTerminalCoordinateSelected.full_selected P D H parent terminal q hcore hcount φ z hφ 0,
    IntegralMixedSelectedCoordinateOrderedQueries.evaluated_head]
  apply Polynomial.ext
  intro y
  simp only [Polynomial.coeff_map,Polynomial.coe_evalRingHom,Polynomial.eval_C]

end LeanCanny.Algebra.IntegralMixedFramedZeroTarskiBits
