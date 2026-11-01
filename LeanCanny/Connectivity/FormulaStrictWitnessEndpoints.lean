/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaStrictWitnessWriter
/-! # Exact algebraic singleton endpoints for the strict-inequality lift -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaStrictWitness
open ETR Set LeanCanny.Geometry CircularWitness
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def endpoint (n : ℕ) (s : Formula) (t : Term) : Formula :=
  .and s (.and (.eqZero (term n t))
    (.and (.eqZero (.var (n+1))) (.ltZero (.mul (.const (-1)) (.var n)))))

theorem endpoint_arity (n : ℕ) (s : Formula) (t : Term) (hs : s.arity ≤ n) (ht : t.arity ≤ n) :
    (endpoint n s t).arity ≤ n+2 := by
  have H := term_arity n t ht
  simp only [endpoint,Formula.arity,Term.arity]
  omega

theorem endpoint_tuple (n : ℕ) (s : Formula) (t : Term) (hs : s.arity ≤ n) (ht : t.arity ≤ n)
    (x : Fin n → ℝ) (w : Plane) :
    (endpoint n s t).Holds (Formula.extend (tuple n (x,w))) ↔
      s.Holds (Formula.extend x) ∧ (-t.eval (Formula.extend x))*‖w‖^2=1 ∧ w 1=0 ∧ 0<w 0 := by
  simp only [endpoint,Formula.Holds,holds_old n s hs x w,term_eval n t ht x w,sub_eq_zero,Term.eval]
  have H0 := extend_tuple_fresh n x w 0
  have H1 := extend_tuple_fresh n x w 1
  simp only [Fin.val_zero,Nat.add_zero,Fin.val_one] at H0 H1
  rw [H0,H1]
  simp only [Int.cast_neg,Int.cast_one,neg_one_mul,neg_lt_zero]

noncomputable def witness (n : ℕ) (t : Term) (x : Fin n → ℝ) : Plane :=
  (Real.sqrt (-t.eval (Formula.extend x)))⁻¹ • unit

theorem witness_zero (n : ℕ) (t : Term) (x : Fin n → ℝ) :
    witness n t x 0 = (Real.sqrt (-t.eval (Formula.extend x)))⁻¹ := by simp [witness,unit]
theorem witness_one (n : ℕ) (t : Term) (x : Fin n → ℝ) : witness n t x 1 = 0 := by simp [witness,unit]

theorem witness_norm (n : ℕ) (t : Term) (x : Fin n → ℝ) :
    ‖witness n t x‖ = (Real.sqrt (-t.eval (Formula.extend x)))⁻¹ := by
  simp [witness,norm_smul,unit_norm,Real.norm_eq_abs]

noncomputable def point (n : ℕ) (p : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n)
    (x : (original n p t).realization) : (lifted n p t).realization :=
  ⟨tuple n (x.val,witness n t x.val),(lifted_tuple n p t hp ht _ _).mpr ⟨x.property.1,
    (StrictInequalityWitness.norm_iff _ _).mpr ⟨by
      have H := x.property.2
      change t.eval (Formula.extend x.val)<0 at H
      linarith,witness_norm n t x.val⟩⟩⟩

theorem projection_point (n : ℕ) (p : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n)
    (x : (original n p t).realization) : projection n p t hp ht (point n p t hp ht x) = x := by
  apply Subtype.ext
  funext i
  rw [projection_val]
  exact Fin.append_left _ _ _

theorem endpoint_denotes (n : ℕ) (p s : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n)
    (x : (original n p t).realization) (hs : Denotes n s x.val) :
    Denotes (n+2) (endpoint n s t) (point n p t hp ht x).val := by
  refine ⟨endpoint_arity n s t hs.1 ht,?_⟩
  have Hpos : 0 < -t.eval (Formula.extend x.val) := by
    have H := x.property.2
    change t.eval (Formula.extend x.val)<0 at H
    linarith
  have Hsqrt : 0 < (Real.sqrt (-t.eval (Formula.extend x.val)))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr Hpos)
  have HP : (endpoint n s t).Holds (Formula.extend (point n p t hp ht x).val) := by
    apply (endpoint_tuple n s t hs.1 ht _ _).mpr
    exact ⟨(hs.2 _).mpr rfl,(StrictInequalityWitness.norm_iff _ _).mpr ⟨Hpos,witness_norm n t x.val⟩,
      witness_one n t x.val,by rw [witness_zero]; exact Hsqrt⟩
  intro y
  constructor
  · intro HY
    let q := (tuple n).symm y
    have Htuple : tuple n (q.1,q.2) = y := (tuple n).apply_symm_apply y
    have HQ := (endpoint_tuple n s t hs.1 ht q.1 q.2).mp (Htuple.symm ▸ HY)
    have HX : q.1 = x.val := (hs.2 _).mp HQ.1
    have Hnorm := ((StrictInequalityWitness.norm_iff _ _).mp HQ.2.1).2
    rw [HX] at Hnorm
    have Hw0 : q.2 0 = (Real.sqrt (-t.eval (Formula.extend x.val)))⁻¹ := by
      have Hsq := EuclideanSpace.real_norm_sq_eq q.2
      rw [Fin.sum_univ_two,HQ.2.2.1,Hnorm] at Hsq
      nlinarith [HQ.2.2.2]
    have HW : q.2 = witness n t x.val := by
      ext j
      fin_cases j
      · exact Hw0.trans (witness_zero n t x.val).symm
      · exact HQ.2.2.1.trans (witness_one n t x.val).symm
    calc
      y = tuple n (q.1,q.2) := Htuple.symm
      _ = (point n p t hp ht x).val := by rw [HX,HW]; rfl
  · rintro rfl
    exact HP

theorem connected_iff (n : ℕ) (p : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n) :
    (lifted n p t).Connected ↔ (original n p t).Connected := by
  have HL := lifted_wellFormed n p t hp ht
  have HO : (original n p t).WellFormed := max_le hp ht
  simpa only [Description.Connected,HL,HO,true_and] using preconnected_iff n p t hp ht

theorem ambient_joined_iff (n : ℕ) (p : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n)
    (y z : (lifted n p t).realization) :
    JoinedIn (lifted n p t).realization y.val z.val ↔
      JoinedIn (original n p t).realization (projection n p t hp ht y).val (projection n p t hp ht z).val := by
  rw [joinedIn_iff_joined y.property z.property,← joinedIn_univ,
    joined_iff n p t hp ht y z,joinedIn_univ,
    ← joinedIn_iff_joined (projection n p t hp ht y).property (projection n p t hp ht z).property]

theorem reachable_iff (n : ℕ) (p s d : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n)
    (x y : (original n p t).realization) (hs : Denotes n s x.val) (hd : Denotes n d y.val) :
    (PointQuery.mk (lifted n p t) (endpoint n s t) (endpoint n d t)).Reachable ↔
      (PointQuery.mk (original n p t) s d).Reachable := by
  rw [PointQuery.reachable_iff (endpoint_denotes n p s t hp ht x hs) (endpoint_denotes n p d t hp ht y hd),
    PointQuery.reachable_iff hs hd]
  have HL := lifted_wellFormed n p t hp ht
  have HO : (original n p t).WellFormed := max_le hp ht
  simp only [HL,HO,true_and]
  simpa only [projection_point] using ambient_joined_iff n p t hp ht (point n p t hp ht x) (point n p t hp ht y)

end LeanCanny.Connectivity.FormulaStrictWitness
