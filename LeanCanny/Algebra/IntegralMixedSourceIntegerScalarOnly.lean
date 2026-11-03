/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
public import LeanCanny.Algebra.IntegralMixedFramedScalarOnly

/-! # Charged integer preludes preserve the literal scalar-only sampler -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem commands_noncritical (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool→ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) (c : Instruction (P.ambient root) (P.width root))
    (hc : c∈commands P Q hq S count hz hd root) : c.command.isCritical=false := by
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc
  rfl

theorem scalarOnly (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool→ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) {horizon : ℕ} {ι : Type} [Fintype ι]
    (initial : State (Q root) horizon (P.width root) 0 ι) (H : IntegralHistorySampler.ScalarOnly initial.sampler)
    (hc : (commands P Q hq S count hz hd root).length≤horizon+1) :
    IntegralHistorySampler.ScalarOnly (run initial (commands P Q hq S count hz hd root) hc).sampler :=
  scalarOnly_run initial H _ hc (commands_noncritical P Q hq S count hz hd root)

end LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
