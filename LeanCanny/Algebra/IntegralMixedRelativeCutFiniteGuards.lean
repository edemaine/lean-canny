/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRelativeCuts
/-! # Finite actual coefficient guards validate every relative cut tag

Lower choices use the same coordinate and old selected embedding. Even the
squarefree tag can be tested through its actual exceptional factor: its
fixed top-coordinate factor is nonzero after every real specialization.
Only the one original auxiliary scalar-degree cap is quantified over.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRelativeCuts
open IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def choiceIndex (r : Rule n) : Kind P r→ℕ
  | .coordinate _ c | .squarefree _ c | .value _ c | .limitCoordinate _ c => c.val

def lowerChoice (r : Rule n) (c : Kind P r) (k : ℕ) (hk : k<choiceIndex r c) : Kind P r :=
  match c with
  | .coordinate j c => .coordinate j ⟨k,hk.trans c.isLt⟩
  | .squarefree j c => .squarefree j ⟨k,hk.trans c.isLt⟩
  | .value j c => .value j ⟨k,hk.trans c.isLt⟩
  | .limitCoordinate j c => .limitCoordinate j ⟨k,hk.trans c.isLt⟩

theorem valid_iff_lower_factors (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) :
    Valid x hm r φ c ↔
      (∀ k (hk : k<choiceIndex r c),(factor x hm r (lowerChoice r c k hk)).map φ.toRingHom=0) ∧
      (factor x hm r c).map φ.toRingHom≠0 := by
  cases c with
  | coordinate j c => rfl
  | value j c => rfl
  | limitCoordinate j c => rfl
  | squarefree j c =>
    have HT:=IntegralMixedCoordinateSquarefree.selected_leading_nonzero x hm r j φ
    simp only [Valid,IntegralMixedCoordinateSquarefree.Valid,factor,IntegralMixedCoordinateSquarefree.exceptional,
      choiceIndex,lowerChoice,Polynomial.map_mul,mul_eq_zero,or_iff_right HT]
    exact and_congr_right (fun _=>(mul_ne_zero_iff.trans (and_iff_right HT)).symm)

theorem factor_map_zero_iff (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) :
    (factor x hm r c).map φ.toRingHom=0 ↔
      ∀ k,k≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree→φ.toRingHom ((factor x hm r c).coeff k)=0 := by
  constructor
  · intro H k _
    have HE:=congrArg (fun p : Polynomial ℝ=>p.coeff k) H
    simpa only [Polynomial.coeff_map,Polynomial.coeff_zero] using HE
  · intro H
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_map,Polynomial.coeff_zero]
    by_cases hk : k≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree
    · exact H k hk
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((factor_degree x hm r c).trans_lt (by omega)),map_zero]

def CoefficientGuards (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) (d : ℕ) : Prop :=
  (∀ k (hk : k<choiceIndex r c),∀ j,j≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree→
    φ.toRingHom ((factor x hm r (lowerChoice r c k hk)).coeff j)=0) ∧
  φ.toRingHom ((factor x hm r c).coeff d)≠0 ∧
  ∀ j,d<j→j≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree→φ.toRingHom ((factor x hm r c).coeff j)=0

theorem coefficientGuards_valid (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) (d : ℕ)
    (h : CoefficientGuards x hm r φ c d) : Valid x hm r φ c := by
  apply (valid_iff_lower_factors x hm r φ c).mpr
  refine ⟨fun k hk=>(factor_map_zero_iff x hm r φ _).mpr (h.1 k hk),?_⟩
  intro H
  have HC:=congrArg (fun p : Polynomial ℝ=>p.coeff d) H
  exact h.2.1 (by simpa only [Polynomial.coeff_map,Polynomial.coeff_zero] using HC)

theorem coefficientGuards_degree (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) (d : ℕ)
    (h : CoefficientGuards x hm r φ c d) : ((factor x hm r c).map φ.toRingHom).natDegree=d := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [Polynomial.coeff_map]
    by_cases hc : k≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree
    · exact h.2.2 k hk hc
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((factor_degree x hm r c).trans_lt (by omega)),map_zero]
  · rw [Polynomial.coeff_map]
    exact h.2.1

end LeanCanny.Algebra.IntegralMixedRelativeCuts
