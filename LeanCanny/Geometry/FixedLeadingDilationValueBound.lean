/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedLeadingTiltedGradient
public import LeanCanny.Geometry.FermatLevelCritical
public import Mathlib.Topology.Algebra.MvPolynomial

/-! # An original-height level bound along the actual dilation

The physical E coordinate is eta/Q, with Q the fixed nonzero bank denominator.
Its limiting source value is exactly the retained frozen Fermat sum. A single
integer coefficient A from that old-coordinate height dominates the value;
the source degree stays fixed throughout the limit.
-/
@[expose] public section
namespace LeanCanny.Geometry.FixedLeadingDilationValueBound
open LeanCanny.Algebra LeanCanny.ETR MvPolynomial Filter
open scoped Topology BigOperators
variable {n : ℕ}

noncomputable def frozenValue (k D : ℕ) (a : Fin n → ℝ) : ℝ :=
  FixedLeadingTiltedSource.frozenPenalty k n D (Formula.extend a)

theorem point_extend (k : ℕ) (s : ℝ) (a : Fin n → ℝ) :
    FixedLeadingTiltedGradient.point k s a =
      fun i : Fin (n+1) => PartialHomogenization.lifted k s (Formula.extend a) i.val := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp [FixedLeadingTiltedGradient.point,PartialHomogenization.lifted,Formula.extend,j.isLt]

theorem value_zero (k D : ℕ) (u : Fin n) (t : Term) (ht : t.degreeBound ≤ D)
    (ha : t.arity ≤ n) (hu : k ≤ u.val) (hD : 0 < D) (a : Fin n → ℝ) :
    (FixedLeadingTiltedSource.polynomial k D u t ht).eval₂ (Int.castRingHom ℝ)
      (FixedLeadingTiltedGradient.point k 0 a) = frozenValue k D a := by
  have H := FixedLeadingTiltedSource.eval_polynomial k D u t ht ha hu 0 (Formula.extend a)
  rw [← point_extend] at H
  have HM : FixedLeadingTiltedSource.degree D≠0 := by unfold FixedLeadingTiltedSource.degree; omega
  simpa only [zero_pow (by omega : 2*D≠0),zero_mul,zero_add,zero_pow HM,add_zero,frozenValue] using H

theorem point_tendsto {I : Type*} (l : Filter I) (k : ℕ) (s : I → ℝ)
    (x : I → Fin n → ℝ) (a : Fin n → ℝ)
    (hs : Tendsto s l (𝓝 0)) (hx : Tendsto x l (𝓝 a)) :
    Tendsto (fun i => FixedLeadingTiltedGradient.point k (s i) (x i)) l
      (𝓝 (FixedLeadingTiltedGradient.point k 0 a)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [FixedLeadingTiltedGradient.point,Fin.cases_zero] using hs
  · by_cases H : j.val<k
    · simpa only [FixedLeadingTiltedGradient.point,Fin.cases_succ,H,ite_true] using tendsto_pi_nhds.mp hx j
    · simpa only [FixedLeadingTiltedGradient.point,Fin.cases_succ,H,ite_false,zero_mul] using
        hs.mul (tendsto_pi_nhds.mp hx j)

theorem value_tendsto {I : Type*} (l : Filter I) (k D : ℕ) (u : Fin n) (t : Term)
    (ht : t.degreeBound ≤ D) (ha : t.arity ≤ n) (hu : k ≤ u.val) (hD : 0 < D)
    (eta : I → ℝ) (Q : ℝ) (x : I → Fin n → ℝ) (a : Fin n → ℝ)
    (heta : Tendsto eta l (𝓝 0)) (hx : Tendsto x l (𝓝 a)) :
    Tendsto (fun i => (FixedLeadingTiltedSource.polynomial k D u t ht).eval₂ (Int.castRingHom ℝ)
      (FixedLeadingTiltedGradient.point k (eta i/Q) (x i))) l (𝓝 (frozenValue k D a)) := by
  have HS : Tendsto (fun i => eta i/Q) l (𝓝 0) := by
    simpa only [zero_div] using heta.div_const Q
  have H := ((FixedLeadingTiltedSource.polynomial k D u t ht).map (Int.castRingHom ℝ)).continuous_eval.continuousAt.tendsto.comp
    (point_tendsto l k _ x a HS hx)
  simpa only [Function.comp_def,eval_map,value_zero k D u t ht ha hu hD a] using H

theorem frozen_height (k D G : ℕ) (a : Fin n → ℝ)
    (ha : ∀ i, i.val<k → |a i| ≤ (2:ℝ)^G) :
    |frozenValue k D a| ≤ (n:ℝ)*((2:ℝ)^G)^FixedLeadingTiltedSource.degree D := by
  unfold frozenValue FixedLeadingTiltedSource.frozenPenalty
  calc
    _ ≤ ∑ i : Fin n, |if i.val<k then (Formula.extend a i.val)^FixedLeadingTiltedSource.degree D else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ((2:ℝ)^G)^FixedLeadingTiltedSource.degree D := by
      apply Finset.sum_le_sum
      intro i _
      by_cases H : i.val<k
      · simp only [H,ite_true,Formula.extend,i.isLt,↓reduceDIte,abs_pow]
        gcongr
        exact ha i H
      · simp only [H,ite_false,abs_zero]
        positivity
    _ = _ := by simp

def levelCoefficient (n D G : ℕ) : ℤ := 2^(n.size+G*FixedLeadingTiltedSource.degree D+2)

theorem frozen_margin (k D G : ℕ) (a : Fin n → ℝ)
    (ha : ∀ i, i.val<k → |a i| ≤ (2:ℝ)^G) :
    |frozenValue k D a| < (levelCoefficient n D G:ℝ)-1 := by
  have HN : (n:ℝ) ≤ (2:ℝ)^n.size := by exact_mod_cast (Nat.lt_size_self n).le
  have HP : 1 ≤ (2:ℝ)^(n.size+G*FixedLeadingTiltedSource.degree D) := one_le_pow₀ (by norm_num)
  have HF := frozen_height k D G a ha
  have HU : (n:ℝ)*((2:ℝ)^G)^FixedLeadingTiltedSource.degree D ≤
      (2:ℝ)^(n.size+G*FixedLeadingTiltedSource.degree D) := by
    rw [pow_add,pow_mul]
    gcongr
  have HA : (levelCoefficient n D G:ℝ) = 4*(2:ℝ)^(n.size+G*FixedLeadingTiltedSource.degree D) := by
    unfold levelCoefficient
    push_cast
    rw [pow_add]
    norm_num
    ring
  rw [HA]
  linarith

theorem eventually_value_bound {I : Type*} (l : Filter I) (k D G : ℕ) (u : Fin n) (t : Term)
    (ht : t.degreeBound ≤ D) (ha : t.arity ≤ n) (hu : k ≤ u.val) (hD : 0 < D)
    (eta : I → ℝ) (Q : ℝ) (x : I → Fin n → ℝ) (a : Fin n → ℝ)
    (heta : Tendsto eta l (𝓝 0)) (hx : Tendsto x l (𝓝 a))
    (hbound : ∀ i, i.val<k → |a i| ≤ (2:ℝ)^G) :
    ∀ᶠ i in l, |(FixedLeadingTiltedSource.polynomial k D u t ht).eval₂ (Int.castRingHom ℝ)
      (FixedLeadingTiltedGradient.point k (eta i/Q) (x i))| ≤ (levelCoefficient n D G:ℝ)-1 := by
  have H := (value_tendsto l k D u t ht ha hu hD eta Q x a heta hx).abs
  exact ((tendsto_order.mp H).2 _ (frozen_margin k D G a hbound)).mono (fun _ h => h.le)

theorem eventually_level_critical {I : Type*} (l : Filter I) (k D G : ℕ) (u : Fin n) (t : Term)
    (ht : t.degreeBound ≤ D) (ha : t.arity ≤ n) (hu : k ≤ u.val) (hD : 0 < D)
    (eta : I → ℝ) (Q : ℝ) (hQ : Q≠0) (x : I → Fin n → ℝ) (a : Fin n → ℝ)
    (heta : Tendsto eta l (𝓝 0)) (hx : Tendsto x l (𝓝 a))
    (hne : ∀ᶠ i in l, eta i≠0) (hbound : ∀ i, i.val<k → |a i| ≤ (2:ℝ)^G)
    (hcritical : ∀ᶠ i in l, ∀ j : Fin n, k ≤ j.val →
      (pderiv j (FixedLeadingTiltedGradient.tilted k D u t (eta i/Q))).eval (x i)=0) :
    ∀ᶠ i in l, ∃ v ∈ Set.Icc (-1:ℝ) 1,
      (FermatLevelLift.polynomial (FermatLevelLift.source
        (FixedLeadingTiltedSource.source k D u t ht) (levelCoefficient n D G))).eval₂ (Int.castRingHom ℝ)
        (Fin.snoc (FixedLeadingTiltedGradient.point k (eta i/Q) (x i)) v)=0 ∧
      ∀ j : Fin (n+1), k+1 ≤ j.val →
        (pderiv j.castSucc (FermatLevelLift.polynomial (FermatLevelLift.source
          (FixedLeadingTiltedSource.source k D u t ht) (levelCoefficient n D G)))).eval₂ (Int.castRingHom ℝ)
          (Fin.snoc (FixedLeadingTiltedGradient.point k (eta i/Q) (x i)) v)=0 := by
  have HW : FermatLevelLift.polynomial (FixedLeadingTiltedSource.source k D u t ht)=
      FixedLeadingTiltedSource.polynomial k D u t ht := by
    simp only [FermatLevelLift.polynomial,FermatCriticalHomogenization.polynomial,
      FixedLeadingTiltedSource.polynomial,FixedLeadingTiltedSource.source,C_1,one_mul]
  have HE : Even (FixedLeadingTiltedSource.degree D) := ⟨2*D+1,by unfold FixedLeadingTiltedSource.degree; omega⟩
  filter_upwards [eventually_value_bound l k D G u t ht ha hu hD eta Q x a heta hx hbound,hne,hcritical] with i hi hni hci
  apply FermatLevelCritical.lift_critical _ _ rfl HE _ (by rw [HW]; exact hi) (k+1)
  intro j
  refine Fin.cases ?_ (fun b => ?_) j
  · intro hj
    simp at hj
  · intro hj
    simp only [Fin.val_succ] at hj
    rw [HW]
    exact (FixedLeadingTiltedGradient.critical_iff k D u t ht ha hu (eta i/Q) (div_ne_zero hni hQ) (x i)).mpr hci b (by omega)

end LeanCanny.Geometry.FixedLeadingDilationValueBound
