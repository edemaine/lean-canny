/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientHistoryPrefix

/-! # An index-independent statement of the proved prefix invariant

The property records specialization of already constructed prefix data.
Heterogeneous row and slot equality permits explicit index casts in the
actual dependent interpreter; no maps are stored in the prefix constructor.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoefficientHistoryPrefix
open Polynomial IntegralMixedHistory
variable {n S width m : ℕ} {P : SpatialSource n} {I J K : Type}

def Specializes (radius : ℕ) (F : Prefix ℤ[X] S width m I) (x : State P S width m J) : Prop :=
  ∃ ψ : F.carrier →+* x.sampler.scalarPrefix.carrier,
    CoefficientCoordinateBasis.Specializes (evalRingHom ((2 : ℤ) ^ radius)) ψ F.basis
      (CoefficientCoordinateBasis.ofIntegral x.sampler.scalarPrefix.basis) ∧
    CoefficientHeightBank.Specializes (evalRingHom ((2 : ℤ) ^ radius)) ψ F.bank
      (CoefficientHeightBank.ofState x) ∧
    HEq (fun j => MvPolynomial.map (evalRingHom ((2 : ℤ) ^ radius)) (F.rows j)) x.sampler.rows ∧
    HEq F.scalar x.sampler.scalar

theorem specializes_of_pointwise (radius : ℕ) (F : Prefix ℤ[X] S width m I)
    (x : State P S width m I) (ψ : F.carrier →+* x.sampler.scalarPrefix.carrier)
    (HB : CoefficientCoordinateBasis.Specializes (evalRingHom ((2 : ℤ) ^ radius)) ψ F.basis
      (CoefficientCoordinateBasis.ofIntegral x.sampler.scalarPrefix.basis))
    (HG : CoefficientHeightBank.Specializes (evalRingHom ((2 : ℤ) ^ radius)) ψ F.bank
      (CoefficientHeightBank.ofState x))
    (HR : ∀ j, MvPolynomial.map (evalRingHom ((2 : ℤ) ^ radius)) (F.rows j) = x.sampler.rows j)
    (HS : F.scalar = x.sampler.scalar) : Specializes radius F x :=
  ⟨ψ, HB, HG, heq_of_eq (funext HR), heq_of_eq HS⟩

theorem Specializes.pointwise {radius : ℕ} {F : Prefix ℤ[X] S width m I} {x : State P S width m I}
    (h : Specializes radius F x) :
    ∃ ψ : F.carrier →+* x.sampler.scalarPrefix.carrier,
      CoefficientCoordinateBasis.Specializes (evalRingHom ((2 : ℤ) ^ radius)) ψ F.basis
        (CoefficientCoordinateBasis.ofIntegral x.sampler.scalarPrefix.basis) ∧
      CoefficientHeightBank.Specializes (evalRingHom ((2 : ℤ) ^ radius)) ψ F.bank
        (CoefficientHeightBank.ofState x) ∧
      (∀ j, MvPolynomial.map (evalRingHom ((2 : ℤ) ^ radius)) (F.rows j) = x.sampler.rows j) ∧
      F.scalar = x.sampler.scalar := by
  obtain ⟨ψ, hb, hg, hr, hs⟩ := h
  exact ⟨ψ, hb, hg, congrFun (eq_of_heq hr), eq_of_heq hs⟩

theorem Specializes.state_transport {radius : ℕ} {F : Prefix ℤ[X] S width m K}
    {x : State P S width m I} {y : State P S width m J}
    (h : Specializes radius F x) (hI : I = J) (hx : HEq x y) : Specializes radius F y := by
  cases hI
  have he := eq_of_heq hx
  subst y
  exact h

theorem Specializes.prefix_transport {radius : ℕ} {F : Prefix ℤ[X] S width m I}
    {G : Prefix ℤ[X] S width m J} {x : State P S width m K}
    (h : Specializes radius F x) (hI : I = J) (hF : HEq F G) : Specializes radius G x := by
  cases hI
  have he := eq_of_heq hF
  subst G
  exact h

end LeanCanny.Algebra.CoefficientHistoryPrefix
