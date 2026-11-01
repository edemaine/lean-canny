/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoerciveCriticalHomogenization
/-! # Finite tilted coercive critical fibers with the same pure spatial powers -/
@[expose] public section
namespace LeanCanny.Algebra.TiltedCoerciveCriticalFibers
open MvPolynomial
open CoerciveCriticalHomogenization
open scoped Classical BigOperators
variable {σ R : Type*} [Fintype σ] [CommRing R] [DecidableEq σ]

noncomputable def polynomial (q : MvPolynomial σ R) (D : ℕ) (u : σ) (s : R) : MvPolynomial σ R :=
  q^2+C (s^2)*(∑ i : σ, X i^(2*D+2))-C s*X u

def tilt (u : σ) (s : R) (j : σ) : R := if j=u then s else 0
noncomputable def lower (q : MvPolynomial σ R) (u : σ) (s : R) (j : σ) : MvPolynomial σ R :=
  pderiv j (q^2)-C (tilt u s j)

omit [Fintype σ] in
theorem lower_degree (q : MvPolynomial σ R) (D : ℕ) (hD : q.totalDegree≤D) (u : σ) (s : R) (j : σ) :
    (lower q u s j).totalDegree<2*D+1 := by
  have H := (PartialDerivativeDegree.degree_le (q^2) j).trans
    (Nat.sub_le_sub_right ((totalDegree_pow q 2).trans (Nat.mul_le_mul_left 2 hD)) 1)
  exact (totalDegree_sub _ _).trans_lt (max_lt (by omega) (by simp))

noncomputable def nativeSystem (q : MvPolynomial σ R) (D : ℕ) (u : σ) (s t : R) (i : σ) :
    Option σ → MvPolynomial (Option σ) R
  | none => C t*X none-X (some i)
  | some j => WeightedHomogenization.homogenize (fun _ => 1) (2*D+1) (lower q u s j)+
      monomial (Finsupp.single (some j) (2*D+1)) (((2*D+2 : ℕ) : R)*(s^2))

theorem homogeneous (q : MvPolynomial σ R) (D : ℕ) (u : σ) (s t : R) (i : σ) (j : Option σ) :
    (nativeSystem q D u s t i j).IsHomogeneous (nativeDegree D j) := by
  cases j with
  | none => exact ((isHomogeneous_X R none).C_mul t).sub (isHomogeneous_X R (some i))
  | some j =>
    apply IsHomogeneous.add
    · have H := WeightedHomogenization.homogeneous (fun _ : σ => 1) (2*D+1) (lower q u s j)
      have HW : WeightedHomogenization.weights (fun _ : σ => 1)=1 := by funext i; cases i <;> rfl
      simpa only [IsHomogeneous,HW,nativeDegree] using H
    · exact isHomogeneous_monomial _ (Finsupp.degree_single _ _)

theorem map_nativeSystem {S : Type*} [CommRing S] (φ : R →+* S)
    (q : MvPolynomial σ R) (D : ℕ) (u : σ) (s t : R) (i : σ) (j : Option σ) :
    (nativeSystem q D u s t i j).map φ=nativeSystem (q.map φ) D u (φ s) (φ t) i j := by
  have HT (k : σ) : φ (tilt u s k)=tilt u (φ s) k := by
    unfold tilt
    split_ifs <;> simp
  cases j <;> simp [nativeSystem,lower,HT,WeightedHomogenization.map_homogenize,pderiv_map,map_ofNat]

section Field
variable {K : Type*} [Field K]

theorem gradient_eq (q : MvPolynomial σ K) (D : ℕ) (u : σ) (s : K) (j : σ) :
    pderiv j (polynomial q D u s)=pderiv j (CoerciveCriticalFibers.polynomial q D (s^2))-C (tilt u s j) := by
  change pderiv j (CoerciveCriticalFibers.polynomial q D (s^2)-C s*X u)=_
  simp only [map_sub,pderiv_C_mul,pderiv_X,tilt]
  by_cases H : j=u <;> simp [H]

theorem finite_critical [CharZero K] (q : MvPolynomial σ K) (D : ℕ) (hD : q.totalDegree≤D)
    (u : σ) (s : K) (hs : s≠0) : {x | ∀ j, eval x (pderiv j (polynomial q D u s))=0}.Finite := by
  have H := CoerciveCriticalFibers.finite_gradient_fiber q D hD (s^2) (pow_ne_zero 2 hs) (tilt u s)
  simpa only [gradient_eq,eval_sub,eval_C,sub_eq_zero] using H

theorem eval_chart (q : MvPolynomial σ K) (D : ℕ) (hD : q.totalDegree≤D)
    (u : σ) (s t : K) (i : σ) (x : σ → K) (j : σ) :
    eval (fun k => k.elim 1 x) (nativeSystem q D u s t i (some j))=eval x (pderiv j (polynomial q D u s)) := by
  have HP (e) (he : e∈(lower q u s j).support) : Finsupp.weight (fun _ : σ => 1) e≤2*D+1 :=
    (WeightedHomogenization.weight_le_degree _ (by simp) e).trans
      ((MvPolynomial.le_totalDegree he).trans (Nat.le_of_lt (lower_degree q D hD u s j)))
  simp only [nativeSystem,map_add,gradient_eq,CoerciveCriticalFibers.gradient_eq,eval_sub,eval_C,
    eval_monomial,Finsupp.prod_single_index,pow_zero,CoerciveCriticalFibers.leadingScalar]
  have HC := WeightedHomogenization.eval_chart _ _ _ HP (RingHom.id K) x
  simp only [eval₂_id] at HC
  rw [HC]
  simp only [lower,eval_sub,eval_C,Option.elim_some]
  ring

theorem no_zero_at_infinity [CharZero K] (q : MvPolynomial σ K) (D : ℕ) (hD : q.totalDegree≤D)
    (u : σ) (s t : K) (hs : s≠0) (i : σ) (x : Option σ → K) (hx : x none=0)
    (hr : ∀ j, eval x (nativeSystem q D u s t i j)=0) : x=0 := by
  funext j
  cases j with
  | none => exact hx
  | some j =>
    have H := hr (some j)
    simp only [nativeSystem,map_add,homogenize_eval_infinity _ _ (lower_degree q D hD u s j) x hx,
      zero_add,eval_monomial,Finsupp.prod_single_index,pow_zero] at H
    exact (pow_eq_zero_iff (by omega)).mp ((mul_eq_zero.mp H).resolve_left
      (CoerciveCriticalFibers.leadingScalar_ne_zero D (s^2) (pow_ne_zero 2 hs)))

theorem exists_root_free [CharZero K] [Infinite K] (q : MvPolynomial σ K) (D : ℕ) (hD : q.totalDegree≤D) (u i : σ) :
    ∃ t : K, ∀ x : Option σ → K, (∀ j, eval x (nativeSystem q D u 1 t i j)=0) → x=0 := by
  let S : Set (σ → K) := {x | ∀ j, eval x (pderiv j (polynomial q D u 1))=0}
  have HS : S.Finite := finite_critical q D hD u 1 one_ne_zero
  obtain ⟨t,HT⟩ := (HS.image (fun x => x i)).exists_notMem
  refine ⟨t,?_⟩
  intro y hy
  by_cases H0 : y none=0
  · exact no_zero_at_infinity q D hD u 1 t one_ne_zero i y H0 hy
  · exfalso
    let x : σ → K := fun j => (y none)⁻¹*y (some j)
    have HC : (fun j : Option σ => (y none)⁻¹*y j)=fun j => j.elim 1 x := by
      funext j
      cases j with
      | none => exact inv_mul_cancel₀ H0
      | some j => rfl
    have HR (j : Option σ) : eval (fun j => j.elim 1 x) (nativeSystem q D u 1 t i j)=0 := by
      rw [← HC,CoerciveCriticalHomogenization.eval_scale _ _ (homogeneous q D u 1 t i j),hy j,mul_zero]
    have HX : x∈S := fun j => (eval_chart q D hD u 1 t i x j).symm.trans (HR (some j))
    have HI : x i=t := by
      have H := HR none
      simp only [nativeSystem,map_sub,map_mul,eval_C,eval_X,Option.elim_none,Option.elim_some,mul_one,sub_eq_zero] at H
      exact H.symm
    exact HT ⟨x,HX,HI⟩

end Field
end LeanCanny.Algebra.TiltedCoerciveCriticalFibers
