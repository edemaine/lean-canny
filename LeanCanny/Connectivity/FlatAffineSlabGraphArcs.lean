/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSlabGraphContextInterval
public import LeanCanny.Connectivity.FlatAffineHeightArcs

/-! # Actual complete branch families from accepted native slab contexts

Native context checks identify a bounded original gap. Its computed exceptional
polynomial supplies complete anchored arcs, including their singular endpoint
limits. Neither a branch family nor its completeness is an input assumption.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphArcs
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def original (c : List Bool) : List Bool := pairFst (pairFst (source c))
noncomputable def equation (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (c : List Bool)
    (t : ℝ) (x : Fin (count F (original c)) → ℝ) : Prop :=
  FlatAffineEndpointMidpoint.equation F height (pairFst (source c)) t x

theorem value_iff_equation (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (c : List Bool)
    (t : ℝ) (x : Fin (count F (original c)) → ℝ) :
    PolynomialGridValues.value (IntegerGridArcs.realRows (FlatAffineHeightArcs.rows F height (original c))) (t, x) = 0 ↔
      equation F height c t x := by
  rw [funext_iff]
  simp only [IntegerGridArcs.real_value, Pi.zero_apply]
  rw [FlatAffineHeightArcs.rows, AffineConstantParameterShift.roots_iff]
  simp only [equation, FlatAffineEndpointMidpoint.equation, original, apply_ite,
    SymbolicScaledSquarefree.scalarEvaluation, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_zero]

noncomputable abbrev Index (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) :=
  PolynomialGridArcs.Fiber (IntegerGridArcs.realRows (FlatAffineHeightArcs.rows F height (original c)))
    (FlatAffineSlabGraphContext.sampleValue F cone height false c)

theorem native_avoids (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (t : ℝ)
    (ht : t ∈ Ioo (FlatAffineSlabGraphContext.endpointValue F cone height false c)
      (FlatAffineSlabGraphContext.endpointValue F cone height true c)) :
    SymbolicScaledSquarefree.scalarEvaluation t (FlatAffineHeightSlabExceptional.polynomial F height (original c)) ≠ 0 := by
  have HG : t ∈ OrderedRealCells.gap (FlatAffineSlabGraphContext.roots F cone height c)
      (FlatAffineSlabGraphContext.gapIndex F cone height c hc) := by
    rw [FlatAffineSlabGraphContext.gap_eq_interval F cone height c hc]
    exact ht
  have HN := OrderedRealCells.gap_no_root _ _ HG
  exact (FlatAffineHeightCells.mem_roots_iff F cone height (original c) t).not.mp HN

theorem avoids (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (t : ℝ)
    (ht : t ∈ Ioo (FlatAffineSlabGraphContext.endpointValue F cone height false c)
      (FlatAffineSlabGraphContext.endpointValue F cone height true c)) :
    SymbolicScaledSquarefree.scalarEvaluation t (FlatAffineHeightArcs.exceptional F height (original c)) ≠ 0 :=
  FlatAffineHeightSlabExceptional.avoids (SymbolicScaledSquarefree.scalarEvaluation t) F cone height (original c)
    (native_avoids F cone height c hc t ht)

theorem coordinate_trailing_avoids (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (t : ℝ)
    (ht : t ∈ Ioo (FlatAffineSlabGraphContext.endpointValue F cone height false c)
      (FlatAffineSlabGraphContext.endpointValue F cone height true c)) :
    SymbolicScaledSquarefree.scalarEvaluation t (FlatAffineHeightCoordinateTrailing.polynomial F height (original c)) ≠ 0 :=
  FlatAffineHeightSlabExceptional.coordinate_trailing_avoids (SymbolicScaledSquarefree.scalarEvaluation t) F height (original c)
    (native_avoids F cone height c hc t ht)

theorem anchored_arcs (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) :
    Finite (Index F cone height c) ∧
    ∃ curve : Index F cone height c → ℝ → Fin (count F (original c)) → ℝ,
      (∀ j, curve j (FlatAffineSlabGraphContext.sampleValue F cone height false c) = j.val) ∧
      (∀ j, ContinuousOn (curve j) (Icc (FlatAffineSlabGraphContext.endpointValue F cone height false c)
        (FlatAffineSlabGraphContext.endpointValue F cone height true c))) ∧
      (∀ j t, t ∈ Icc (FlatAffineSlabGraphContext.endpointValue F cone height false c)
        (FlatAffineSlabGraphContext.endpointValue F cone height true c) → equation F height c t (curve j t)) ∧
      (∀ t : Ioo (FlatAffineSlabGraphContext.endpointValue F cone height false c)
          (FlatAffineSlabGraphContext.endpointValue F cone height true c), ∀ x,
        equation F height c t.val x ↔ ∃! j, curve j t.val = x) ∧
      ∀ j, FrontierCover.Accessible ((fun t => (t, curve j t)) '' Ioo
        (FlatAffineSlabGraphContext.endpointValue F cone height false c)
        (FlatAffineSlabGraphContext.endpointValue F cone height true c)) := by
  let t₀ : Ioo (FlatAffineSlabGraphContext.endpointValue F cone height false c)
      (FlatAffineSlabGraphContext.endpointValue F cone height true c) :=
    ⟨FlatAffineSlabGraphContext.sampleValue F cone height false c, FlatAffineSlabGraphContext.samples_between F cone height false c hc⟩
  obtain ⟨hfin, curve, ha, hcont, hroot, hcomplete, haccess⟩ := FlatAffineHeightArcs.anchored_arcs F cone height (original c)
    _ _ t₀ (fun t ht => avoids F cone height c hc t ht)
  refine ⟨hfin, curve, ha, hcont, ?_, ?_, haccess⟩
  · intro j t ht
    exact (value_iff_equation F height c t (curve j t)).mp (hroot j t ht)
  · intro t x
    exact (value_iff_equation F height c t.val x).symm.trans (hcomplete t x)

end LeanCanny.Connectivity.FlatAffineSlabGraphArcs
