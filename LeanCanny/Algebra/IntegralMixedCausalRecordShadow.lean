/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalRecord
public import LeanCanny.Algebra.IntegralMixedCriticalScalarShadow
/-! # Scalar shadows preserve the next causal instruction exactly

The native critical birth retains physical rows. The geometric shadow need
not realize those rows: identical scalar banks give the same next source,
affine rule, original headers and inserted current-Q slope.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalRecordBits
open IntegralMixedHistory
open scoped Classical

theorem instantiate_shadow {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n) (next : Record n B) :
    instantiate (relativeScalarStep x hm r) next=instantiate (criticalStep x hm r) next :=
  instantiate_congr _ _ next (relativeScalar_denominator_eq_critical x hm r)

theorem shadow_header {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n) (next : Record n B) :
    IntegralMixedCommandHeaderBits.command (instantiate (relativeScalarStep x hm r) next).command=next.template.header :=
  instantiate_header _ _

theorem shadow_body {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n) (next : Record n B) :
    commandBody (instantiate (relativeScalarStep x hm r) next).command=next.template.body :=
  instantiate_body _ _
end LeanCanny.Algebra.IntegralMixedCausalRecordBits
