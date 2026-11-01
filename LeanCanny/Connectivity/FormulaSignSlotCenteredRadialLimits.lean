/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotCenteredRadialSource
public import LeanCanny.Geometry.CoerciveComponentSampling
public import LeanCanny.Algebra.CoerciveCriticalFibers
/-! # Actual constrained critical limits in the fixed-center radial source

The freezing polynomial has exactly the literal coordinate-frozen graph as
its zero set. Compactness is discharged by the bounded-source projection.
Every clopen zero-set piece admits bounded critical approximants converging
into that same piece, even though the exact graph is singular.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotCenteredRadialLimits
open Set Filter ETR LeanCanny.Encoding LeanCanny.Geometry MvPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical BigOperators Topology
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) :
    MvPolynomial (Fin (N c+d c+1)) ℝ :=
  ((FormulaSignSlotCenteredRadialSource.equation c).finitePolynomial
    (N c+d c+1)).map (Int.castRingHom ℝ)+
    (∑ i, (X (centerIndex c i)-C (a i))^2)+(X (radiusIndex c)-C r)^2

private theorem original_nonneg (c : List Bool)
    (x : Fin (N c+d c+1) → ℝ) :
    0≤((FormulaSignSlotCenteredRadialSource.equation c).finitePolynomial
      (N c+d c+1)).eval₂ (Int.castRingHom ℝ) x := by
  rw [Term.eval_finitePolynomial]
  simp only [FormulaSignSlotCenteredRadialSource.equation,Term.square,Term.eval,Int.cast_zero,add_zero]
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem zero_iff (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ)
    (x : Fin (N c+d c+1) → ℝ) :
    (polynomial c a r).eval x=0 ↔
      (CenteredRadialGraph.description (N c) (d c) (p c)).formula.Holds (Formula.extend x) ∧
        (∀ i, x (centerIndex c i)=a i) ∧ x (radiusIndex c)=r := by
  have HS : 0≤∑ i, (x (centerIndex c i)-a i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp only [polynomial,eval_add,eval_map,eval_sum,eval_pow,eval_sub,eval_X,eval_C]
  rw [add_eq_zero_iff_of_nonneg (add_nonneg (original_nonneg c x) HS) (sq_nonneg _),
    add_eq_zero_iff_of_nonneg (original_nonneg c x) HS]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [Finset.mem_univ,forall_const,sq_eq_zero_iff,sub_eq_zero,Term.eval_finitePolynomial,
    FormulaSignSlotCenteredRadialSource.zero_iff,and_assoc]

theorem zero_image (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) :
    {x | (polynomial c a r).eval x=0}=Subtype.val '' slice c a r := by
  ext x
  rw [mem_ofPred_eq,zero_iff]
  constructor
  · rintro ⟨hx,hc,hr⟩
    exact ⟨⟨x,hx⟩,⟨hc,hr⟩,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,hy.1,hy.2⟩

theorem compact_zeros (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (hr : 0≤r) :
    IsCompact (CoerciveComponentSampling.Zeros (polynomial c a r)) := by
  change IsCompact {x | (polynomial c a r).eval x=0}
  rw [zero_image]
  exact (compact_slice c a r hr).image continuous_subtype_val

theorem exists_critical_limits (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (hr : 0≤r)
    (D : ℕ) (S : Set (CoerciveComponentSampling.Zeros (polynomial c a r))) (hS : IsClopen S)
    (x0 : CoerciveComponentSampling.Zeros (polynomial c a r)) (hx0 : x0∈S)
    (s : ℕ → ℝ) (hs : ∀ k, 0 < s k) (hs0 : Tendsto s atTop (𝓝 0)) :
    ∃ (y : ℕ → (Fin (N c+d c+1) → ℝ))
      (z : CoerciveComponentSampling.Zeros (polynomial c a r)) (φ : ℕ → ℕ), z∈S ∧ StrictMono φ ∧
      Tendsto (y ∘ φ) atTop (𝓝 z.val) ∧
      (∀ k, CoercivePolynomialSampling.penalty D (y k)≤CoercivePolynomialSampling.penalty D x0.val) ∧
      ∀ᶠ k in atTop, ∀ j, eval (y (φ k))
        (pderiv j (CoercivePolynomialSampling.regularization (polynomial c a r) D (s (φ k))))=0 :=
  CoerciveComponentSampling.exists_critical_limits _ D (compact_zeros c a r hr) S hS x0 hx0 s hs hs0

noncomputable def degreeBudget (c : List Bool) := (FormulaSignSlotCenteredRadialSource.equation c).toData.size+2

theorem degreeBudget_unary : UnaryFn degreeBudget := by
  have H : UnaryFn (fun c => (FormulaSignSlotCenteredRadialSource.equation c).toData.size) :=
    (UnaryFn.length FormulaSignSlotCenteredRadialSource.equation_FP).of_eq
      (fun c => Data.length_toBits (FormulaSignSlotCenteredRadialSource.equation c).toData)
  exact H.add (UnaryFn.const 2)

private theorem square_degree {m : ℕ} (i : Fin m) (a : ℝ) :
    ((X i-C a : MvPolynomial (Fin m) ℝ)^2).totalDegree≤2 := by
  apply (totalDegree_pow _ _).trans
  have H : (X i-C a : MvPolynomial (Fin m) ℝ).totalDegree≤1 :=
    (totalDegree_sub _ _).trans (by simp)
  exact Nat.mul_le_mul_left 2 H

theorem polynomial_degree (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) :
    (polynomial c a r).totalDegree≤degreeBudget c := by
  have H2 : 2≤degreeBudget c := by unfold degreeBudget; omega
  unfold polynomial
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · exact (LeanCanny.Algebra.PolynomialMapDegree.degree_le _ _).trans
        ((Term.totalDegree_finitePolynomial _ _).trans ((Term.degreeBound_le_dataSize _).trans (Nat.le_add_right _ 2)))
    · apply (totalDegree_finsetSum_le (fun i _ => square_degree (centerIndex c i) (a i))).trans H2
  · exact (square_degree _ _).trans H2

theorem finite_critical_fiber (c : List Bool) (a : Fin (d c) → ℝ) (r s : ℝ) (hs : s≠0) :
    {x | ∀ j, eval x (pderiv j (CoercivePolynomialSampling.regularization
      (polynomial c a r) (degreeBudget c) s))=0}.Finite :=
  LeanCanny.Algebra.CoerciveCriticalFibers.finite_critical_points _ _ (polynomial_degree c a r) s hs

end LeanCanny.Connectivity.FormulaSignSlotCenteredRadialLimits
