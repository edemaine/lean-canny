/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalPointSignature
/-! # Actual companion bank quotients read back the complete signature -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalFrame.Descriptor
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedPointCompanion IntegralMixedFullHistoryScript IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B birth : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem realized_point_value (d : Descriptor n birth) (x : State P S B birth ι)
    (g : Free d.frame.frozen) (z : ι→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old : Fin birth→ℝ) (p : Fin (n+1)→ℝ) (hp : p∈slice P d.frame old)
    (room : birth+d.orderedFree.length≤S+1)
    (R : Realized x d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i)) g z φ old p d.orderedFree room)
    (i : Fin (n+1)) :
    let result:=run x d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i)) g d.orderedFree room
    let ref : Fin (birth+d.orderedFree.length):=
      ⟨(d.pointReference i).val,by rw [d.orderedFree_length];exact (d.pointReference i).isLt⟩
    R.hom (result.bank.numerator ref)/(result.bank.denominator ref:ℝ)=p i :=
  (R.quotients _).trans (d.point_values P old p hp i)

end LeanCanny.Geometry.IntegralMixedChronologicalFrame.Descriptor
