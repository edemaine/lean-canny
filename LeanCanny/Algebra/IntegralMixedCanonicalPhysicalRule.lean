/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCanonicalDilationRoot
public import LeanCanny.Algebra.IntegralMixedCriticalRealExtension

/-! # A physical command at one retained sweep height

The virtual sweep's formal parameter is replaced by one actual affine bank
expression. This constructs a single physical instruction. It does not claim
that this one retained height represents an entire parameter trajectory.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCanonicalDilation
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
variable {n k m S B : ℕ} {P : SpatialSource (n+1)} {ι : Type}

def retainedRule (hkn : k≤n) (select : Fin k → Fin m) (e : AffineExpr) : CriticalRule (n+1) :=
  { (rule hkn select).critical with heights := fun i => if i=0 then e else heightExpr select i }

theorem retained_frozen (x : State P S B m ι) (hm : m≤S) (hkn : k≤n) (select : Fin k → Fin m)
    (e : AffineExpr) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (values : Fin m → ℝ)
    (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (old : Fin n → ℝ) (v : ℝ)
    (Hparam : ∀ j : Fin n, ∀ hj : j.val<k, old j=values (select ⟨j.val,hj⟩)) :
    ∀ i, i.val<(retainedRule hkn select e).offset.val →
      ((data x hm (retainedRule hkn select e)).scales i:ℝ)*
        point (k:=k) x (φ (expression x e)) old v i=
      φ (expression x ((retainedRule hkn select e).heights i)) := by
  intro i hi
  have HF := frozen x hm hkn select φ values H (φ (expression x e)) old v Hparam i hi
  change ((data x hm (rule hkn select).critical).scales i:ℝ)*_= _
  rw [HF]
  by_cases H0 : i=0
  · subst i
    simp [heightValue,rule,heightExpr_zero,expression,retainedRule]
  · simp only [heightValue,rule,H0,ite_false,add_zero,retainedRule]

end LeanCanny.Algebra.IntegralMixedCanonicalDilation
