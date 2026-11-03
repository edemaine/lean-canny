/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRelativeCutSpecialized
/-! # A sweep's unused companion coordinate can match its encoded cut index

The original causal record shares field4 between critical.coordinate and the
chosen cut coordinate. A sweep uses an explicit coordinate argument instead
of that critical companion field. Retargeting preserves every actual factor,
selected-component guard, chosen degree and scalar birth exactly.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSweepRetarget
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedRelativeCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def rule (r : Rule n) (k : ℕ) : Rule n:={r with critical:={r.critical with coordinate:=k}}

theorem data_eq (x : State P S B m ι) (hm : m≤S) (r : Rule n) (k : ℕ) :
    data x hm (rule r k).critical=data x hm r.critical:=rfl

theorem coordinate_eq (x : State P S B m ι) (hm : m≤S) (r : Rule n) (k : ℕ)
    (j : Fin (n-r.critical.offset.val+1)) : coordinate x hm (rule r k) j=coordinate x hm r j:=rfl

def kind (r : Rule n) (k : ℕ) : Kind P r→Kind P (rule r k)
  | .coordinate j c=>.coordinate j c
  | .squarefree j c=>.squarefree j c
  | .value j c=>.value j c
  | .limitCoordinate j c=>.limitCoordinate j c

theorem factor_eq (x : State P S B m ι) (hm : m≤S) (r : Rule n) (k : ℕ) (c : Kind P r) :
    factor x hm (rule r k) (kind r k c)=factor x hm r c:=by
  cases c <;> rfl

theorem valid_iff (x : State P S B m ι) (hm : m≤S) (r : Rule n) (k : ℕ)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) :
    Valid x hm (rule r k) φ (kind r k c)↔Valid x hm r φ c:=by
  cases c <;> rfl

theorem selectedDegree_eq (x : State P S B m ι) (hm : m≤S) (r : Rule n) (k : ℕ)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) :
    selectedDegree x hm (rule r k) φ (kind r k c)=selectedDegree x hm r φ c:=by
  unfold selectedDegree
  rw [factor_eq]

variable [Fintype ι]

theorem step_eq (x : State P S B m ι) (hm : m≤S) (r : Rule n) (k : ℕ) (c : Kind P r) (d : ℕ) :
    step x hm (rule r k) (kind r k c) d=step x hm r c d:=by
  unfold step
  rw [factor_eq]

end LeanCanny.Algebra.IntegralMixedSweepRetarget
