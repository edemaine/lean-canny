/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedScalarOnly

/-! # Complete all-root validation for actual scalar-only framed histories

The canonical system is the actual prefix, and the variable equivalence
identifies it with the actual physical square system. Its existing infinity
certificate supplies nonzero coordinate annihilators retaining EVERY root.
No derivative or Jacobian hypothesis is used, including when m is zero.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open IntegralMixedHistory IntegralHistorySampler
open scoped Classical
variable {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem scalarVariables_degrees (initial : State P S B 0 ι) (H : ScalarOnly initial.sampler)
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1)
    (hc : ∀ c∈cs, c.command.isCritical=false) (i : Fin cs.length) :
    (run initial cs hcs).sampler.degrees ((scalarVariables initial H cs hcs hc).symm i)=
      (run initial cs hcs).sampler.scalarPrefix.degrees i :=
  (scalarOnly_run initial H cs hcs hc).degrees i

theorem scalarVariables_noInfinity (initial : State P S B 0 ι) (H : ScalarOnly initial.sampler)
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1)
    (hc : ∀ c∈cs, c.command.isCritical=false) :
    AffineFiniteCoordinates.NoInfinity
      (PolynomialSystemReindex.system (scalarVariables initial H cs hcs hc) (run initial cs hcs).sampler.rows)
      ((run initial cs hcs).sampler.degrees ∘ (scalarVariables initial H cs hcs hc).symm) := by
  have HR := funext (scalarVariables_rows initial H cs hcs hc)
  have HD : (run initial cs hcs).sampler.degrees ∘ (scalarVariables initial H cs hcs hc).symm=
      (run initial cs hcs).sampler.scalarPrefix.degrees :=
    funext (scalarVariables_degrees initial H cs hcs hc)
  rw [HR,HD]
  exact (run initial cs hcs).sampler.scalarPrefix.noInfinity

theorem canonical_annihilator_nonzero (initial : State P S B 0 ι)
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1) (i : Fin cs.length) :
    UniformIntegralPrefix.annihilator (run initial cs hcs).sampler.scalarPrefix i≠0 :=
  UniformIntegralPrefix.annihilator_ne_zero _ i

theorem canonical_annihilator_complete (initial : State P S B 0 ι)
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1) {K : Type*} [Field K]
    (z : Fin cs.length→K)
    (hz : ∀ i, ((run initial cs hcs).sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom K) z=0)
    (i : Fin cs.length) :
    (UniformIntegralPrefix.annihilator (run initial cs hcs).sampler.scalarPrefix i).eval₂
      (Int.castRingHom K) (z i)=0 :=
  UniformIntegralPrefix.annihilator_root _ z hz i

theorem physical_annihilator_complete (initial : State P S B 0 ι) (H : ScalarOnly initial.sampler)
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1)
    (hc : ∀ c∈cs, c.command.isCritical=false) {K : Type*} [Field K]
    (z : Index ι cs→K) (hz : ∀ j, ((run initial cs hcs).sampler.rows j).eval₂ (Int.castRingHom K) z=0)
    (i : Fin cs.length) :
    (UniformIntegralPrefix.annihilator (run initial cs hcs).sampler.scalarPrefix i).eval₂
      (Int.castRingHom K) (z ((run initial cs hcs).sampler.scalar i))=0 := by
  apply canonical_annihilator_complete initial cs hcs (z ∘ (run initial cs hcs).sampler.scalar) ?_ i
  intro j
  have HR := hz ((run initial cs hcs).sampler.scalar j)
  rw [(scalarOnly_run initial H cs hcs hc).rows j,MvPolynomial.eval₂_rename] at HR
  exact HR

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
