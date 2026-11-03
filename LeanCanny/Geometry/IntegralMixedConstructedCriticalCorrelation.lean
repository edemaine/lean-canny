/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedMatchedOptionalAnchorCaptures
public import LeanCanny.Geometry.IntegralMixedFullBankPoint
/-! # Constructed anchors and captures satisfy their actual scalar correlations

The readbacks use one full tuple. Each creating block keeps its own physical
power; retained selected quotients are not replaced by annihilator roots.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedPointCompanion
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralHistorySampler
open UniformIntegralPowerSchedule IntegralMixedOptionalEndpoints
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]
variable (x :State P S B m ι) (frozen :Finset (Fin (n+1))) (double :Fin (n+1)→Bool)
  (rows :Fin (n+1)→IntegralMixedCausalRowConstructor.Row m) (g :Free frozen)
  (z :ι→ℝ) (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (old :Fin m→ℝ)
  (p :Fin (n+1)→ℝ) (js :List (Free frozen)) (room :m+js.length≤S+1)
  (R :Realized x frozen double rows g z φ old p js room)

theorem Realized.selected_correlation
    (HC :Canonical (run x frozen double rows g js room)) (k :Fin js.length) :
    IntegralMixedFullBankPoint.point (run x frozen double rows g js room) R.tuple
      ⟨k.val,by have :=k.isLt;omega⟩=
      R.tuple (blockColumn frozen double rows g js k (js.get k).val)^
        physical S (2^B) (m+(js.length-1-k.val)):=by
  have HQ:=IntegralMixedCanonicalBankPoint.quotient_eq (run x frozen double rows g js room) HC
    (R.tuple∘(run x frozen double rows g js room).sampler.scalar) R.hom R.generators
      ⟨k.val,by have :=k.isLt;omega⟩
  exact HQ.symm.trans ((R.quotients _).trans
    ((values_get p old js k).trans (R.blocks k (js.get k).val).symm))

theorem Realized.all_coordinate_correlation
    (k l :Fin js.length) (i :Fin (n+1)) :
    R.tuple (blockColumn frozen double rows g js k i)^physical S (2^B) (m+(js.length-1-k.val))=
      R.tuple (blockColumn frozen double rows g js l i)^physical S (2^B) (m+(js.length-1-l.val)):=by
  exact (R.blocks k i).trans (R.blocks l i).symm

end LeanCanny.Geometry.IntegralMixedPointCompanion

namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra IntegralMixedHistory IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]

omit [Fintype ι] in
theorem PhysicalEndpointRecord.selected_correlation
    (x :State P S B m ι)
    (born :State P S B (m+1) ((ι⊕FlatAffineCriticalStage.Variables (n+1))⊕Unit))
    (embedding :x.sampler.scalarPrefix.carrier→ₐ[ℤ]born.sampler.scalarPrefix.carrier)
    (decoder :Prop) (z :ι→ℝ) (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old :Fin m→ℝ) (p :Fin (n+1)→ℝ) (j :Fin (n+1))
    (R :PhysicalEndpointRecord x born embedding decoder z φ old p j) (HC :Canonical born) :
    IntegralMixedFullBankPoint.point born R.tuple 0=
      R.tuple (Sum.inl (FlatAffineCriticalStage.ambient j))^UniformIntegralPowerSchedule.physical S (2^B) m:=by
  have HQ:=IntegralMixedCanonicalBankPoint.quotient_eq born HC
    (R.tuple∘born.sampler.scalar) R.hom R.generators 0
  exact HQ.symm.trans ((R.quotients 0).trans (R.physical j).symm)

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
