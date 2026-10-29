/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.OriginalRootArcs
public import LeanCanny.Geometry.SquarefreeRootFamily

/-! # Complete arcs for coordinate equations with repeated roots

Outside a constructed finite set of parameter values, squarefree coordinate
equations give finite complete branches. Properness of the original root
projection bounds their coordinates. Each branch extends to roots of the
original equations at both endpoints, where the auxiliary equations may have
additional roots. Properness is an explicit hypothesis; no effective recursive
cover or polynomial-space branch encoding is supplied here.
-/

@[expose] public section
namespace LeanCanny.Connectivity.SquarefreeRootArcs
open Set Geometry LeanCanny.Algebra
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_anchored_arcs (p : ι → Polynomial (Polynomial ℤ)) (hp : ∀ i, p i ≠ 0)
    (a b : ℝ) (t₀ : Ioo a b)
    (hproper : IsProperMap (RootProjection.projection (SquarefreeRootFamily.value p)))
    (ht : ∀ t ∈ Ioo a b, ∀ i, SymbolicScaledSquarefree.scalarEvaluation t
      (SymbolicScaledSquarefree.exceptional (p i)) ≠ 0) :
    Finite (RootBranches.Index
      (SquarefreeRootFamily.value (fun i => SymbolicScaledSquarefree.polynomial (p i))) a b t₀) ∧
    ∃ curve : RootBranches.Index
        (SquarefreeRootFamily.value (fun i => SymbolicScaledSquarefree.polynomial (p i))) a b t₀ →
        ℝ → ι → ℝ,
      (∀ j, curve j t₀.val = j.val.val.val.2) ∧
      (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
      (∀ j t, t ∈ Icc a b → SquarefreeRootFamily.value p (t, curve j t) = 0) ∧
      (∀ t : Ioo a b, ∀ x, SquarefreeRootFamily.value p (t.val, x) = 0 ↔
        ∃! j, curve j t.val = x) ∧
      ∀ j, FrontierCover.Accessible ((fun t => (t, curve j t)) '' Ioo a b) := by
  apply OriginalRootArcs.exists_anchored_arcs
    (SquarefreeRootFamily.value p)
    (SquarefreeRootFamily.value (fun i => SymbolicScaledSquarefree.polynomial (p i))) a b t₀
    (p := fun i => SquarefreeRootFamily.endpointEquation (p i))
  · intro t ht' x
    exact (SquarefreeRootFamily.roots_away p t x (ht t ht')).symm
  · exact SquarefreeRootFamily.continuous_value p
  · exact hproper
  · intro z _
    exact (PolynomialRootFamily.contDiff_value _ 1).contDiffAt
  · intro z hz
    exact SquarefreeRootFamily.regular_away p z.val.1 z.val.2 (ht _ hz) z.property
  · intro i
    exact SquarefreeRootFamily.endpointEquation_ne_zero (hp i)
  · intro z _ i
    rw [SquarefreeRootFamily.value_endpointEquation]
    have H := congrFun z.property i
    change SquarefreeRootFamily.value p (z.val.1, z.val.2) i = 0 at H
    rwa [SquarefreeRootFamily.value_apply] at H

end LeanCanny.Connectivity.SquarefreeRootArcs
