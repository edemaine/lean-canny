/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.DomainSquarefree
public import LeanCanny.Geometry.PolynomialCoordinateProper
public import LeanCanny.Geometry.LocalProperRootBranches
/-! # Complete branches of real-coefficient parameter equations

Actual nonzero coordinate equations, including identically repeated factors,
produce squarefree auxiliary rows and explicit finite cuts. No regularity or
properness premise remains: both follow from these rows away from the cuts.
Only the open interval is retained, so extraneous endpoint roots need no lift.
-/
@[expose] public section
namespace LeanCanny.Geometry.RealParameterRootBranches
open Set Polynomial LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*}
noncomputable def auxiliary (p : Polynomial (Polynomial ℝ)) := DomainSquarefree.polynomial p
noncomputable def cut (p : Polynomial (Polynomial ℝ)) : Polynomial ℝ :=
  DomainSquarefree.exceptional p * (auxiliary p).leadingCoeff

theorem cut_ne_zero (p : Polynomial (Polynomial ℝ)) (hp : p≠0) : cut p≠0 :=
  mul_ne_zero (DomainSquarefree.exceptional_ne_zero p hp)
    (Polynomial.leadingCoeff_ne_zero.mpr (DomainSquarefree.polynomial_ne_zero p hp))

noncomputable def bad (p : ι → Polynomial (Polynomial ℝ)) : Set ℝ := {r | ∃ i, (cut (p i)).eval r=0}
variable [Fintype ι]
theorem finite_bad (p : ι → Polynomial (Polynomial ℝ)) (hp : ∀ i, p i≠0) : (bad p).Finite := by
  have H := Set.finite_iUnion (fun i => Polynomial.finite_setOfPred_isRoot (cut_ne_zero (p i) (hp i)))
  exact H.subset (fun r ⟨i,hi⟩ => Set.mem_iUnion.mpr ⟨i,hi⟩)

noncomputable def system (p : ι → Polynomial (Polynomial ℝ)) :=
  PolynomialRootFamily.value (UnivariateRootFamily.diagonal (fun i => auxiliary (p i)))

omit [Fintype ι] in
theorem conditions (p : ι → Polynomial (Polynomial ℝ)) (r : ℝ) (hr : r∉bad p) (i : ι) :
    (DomainSquarefree.exceptional (p i)).eval r≠0 ∧ (auxiliary (p i)).leadingCoeff.eval r≠0 := by
  have H : (cut (p i)).eval r≠0 := fun HZ => hr ⟨i,HZ⟩
  simpa only [cut,Polynomial.eval_mul,mul_ne_zero_iff] using H

omit [Fintype ι] in
theorem roots (p : ι → Polynomial (Polynomial ℝ)) (r : ℝ) (hr : r∉bad p) (x : ι → ℝ) :
    system p (r,x)=0 ↔ ∀ i, (p i).eval₂ (Polynomial.evalRingHom r) (x i)=0 := by
  constructor
  · intro H i
    apply (DomainSquarefree.roots_iff (Polynomial.evalRingHom r) (p i) (conditions p r hr i).1 (x i)).mp
    simpa only [system,UnivariateRootFamily.value_diagonal,Pi.zero_apply,auxiliary] using congrFun H i
  · intro H
    funext i
    rw [system,UnivariateRootFamily.value_diagonal,Pi.zero_apply]
    exact (DomainSquarefree.roots_iff (Polynomial.evalRingHom r) (p i) (conditions p r hr i).1 (x i)).mpr (H i)

variable [DecidableEq ι]
theorem regular (p : ι → Polynomial (Polynomial ℝ)) (r : ℝ) (hr : r∉bad p) (x : ι → ℝ)
    (hx : system p (r,x)=0) :
    (fderiv ℝ (system p) (r,x) ∘L ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)).IsInvertible := by
  apply UnivariateRootFamily.regular_diagonal _ r x _ hx
  intro i
  exact DomainSquarefree.separable (Polynomial.evalRingHom r) (p i) (conditions p r hr i).1

omit [DecidableEq ι] in
theorem proper (p : ι → Polynomial (Polynomial ℝ)) (a b : ℝ) (h : ∀ r∈Ioo a b, r∉bad p) :
    IsProperMap (RootBranches.projection (system p) a b) :=
  PolynomialCoordinateProper.proper_restriction _ (Ioo a b) (fun i r hr => (conditions p r (h r hr) i).2)

theorem finite_index (p : ι → Polynomial (Polynomial ℝ)) (a b : ℝ) (t₀ : Ioo a b)
    (h : ∀ r∈Ioo a b, r∉bad p) : Finite (RootBranches.Index (system p) a b t₀) := by
  apply LocalProperRootBranches.finite_index (system p) a b t₀ (proper p a b h)
  · intro z _
    exact (PolynomialRootFamily.contDiff_value _ 1).contDiffAt
  · intro z hz
    exact regular p z.val.1 (h _ hz) z.val.2 z.property

theorem branches (p : ι → Polynomial (Polynomial ℝ)) (a b : ℝ) (t₀ : Ioo a b)
    (h : ∀ r∈Ioo a b, r∉bad p) :
    ∃ curve : RootBranches.Index (system p) a b t₀ → C(Ioo a b, ι → ℝ),
      (∀ i, curve i t₀=i.val.val.val.2) ∧
      (∀ i t j, (p j).eval₂ (Polynomial.evalRingHom t.val) (curve i t j)=0) ∧
      ∀ t : Ioo a b, ∀ x, (∀ j, (p j).eval₂ (Polynomial.evalRingHom t.val) (x j)=0) ↔ ∃! i, curve i t=x := by
  obtain ⟨curve,HA,HR,HC⟩ := LocalProperRootBranches.exists_anchored_branches (system p) a b t₀ (proper p a b h)
    (fun _ _ => (PolynomialRootFamily.contDiff_value _ 1).contDiffAt)
    (fun z hz => regular p z.val.1 (h _ hz) z.val.2 z.property)
  exact ⟨curve,HA,(fun i t => (roots p t.val (h _ t.property) _).mp (HR i t)),
    fun t x => ((roots p t.val (h _ t.property) x).symm.trans (HC t x))⟩
end LeanCanny.Geometry.RealParameterRootBranches
