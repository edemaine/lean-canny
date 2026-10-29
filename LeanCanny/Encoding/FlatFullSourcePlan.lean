/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceTower
public import LeanCanny.Computation.PolyTimeQuantifiers

/-! # Native validation of flat sampling plans

Every requested block is nonempty and contained in the original coordinates,
and its pivot lies in that block. Validation scans input-dependent depth in
native polynomial time. These checks ensure that each stage includes the
original source equation, not just its derivative differences.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourcePlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open FlatFullSourceTower (Inputs arity stage free)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

def pivotValue (F : Inputs) (u : List Bool) (k : ℕ) : ℕ := (F.pivot u k).val
attribute [local irreducible] pivotValue

def Valid (F : Inputs) (u : List Bool) : Prop := ∀ k < F.depth u,
  0 < F.dim (stage u k) ∧ F.offset (stage u k) + F.dim (stage u k) ≤ arity F u ∧
    F.offset (stage u k) ≤ pivotValue F u k ∧ pivotValue F u k < F.offset (stage u k) + F.dim (stage u k)

def stageQuery (q : List Bool) : List Bool := pair (pairFst q) (BinaryNatCode.encode (pairSnd q).length)
theorem stageQuery_FP : stageQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP

theorem valid_FP {F : Inputs} (h : F.Access) : FPPred (Valid F) := by
  have hd := BinaryFn.ofUnary (h.dim.comp stageQuery_FP)
  have ho : BinaryFn (fun q => F.offset (stageQuery q)) := h.offset.comp stageQuery_FP
  have hb : BinaryFn (fun q => pivotValue F (pairFst (stageQuery q)) (Nat.fromBitsLE (pairSnd (stageQuery q)))) := by
    unfold pivotValue
    exact h.pivot.comp stageQuery_FP
  have hn := BinaryFn.ofUnary ((FlatFullSourceTower.arity_unary h).comp pairFst_mem_FP)
  have hp := ((BinaryFn.const 0).lt hd).and (((ho.add hd).le hn).and ((ho.le hb).and (hb.lt (ho.add hd))))
  apply (FPPred.forall_lt h.depth hp).of_iff
  intro u
  simp only [Valid, stageQuery, stage, pairFst_pair, pairSnd_pair,
    List.length_replicate, MacaulayBits.fromBits_encode]

theorem pivot_mem (F : Inputs) (u : List Bool) (h : Valid F u) (k : ℕ) (hk : k < F.depth u) :
    F.pivot u k ∈ free F u k := by
  have H := h k hk
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [pivotValue] using H.2.2⟩

theorem newest_source_zero {K : Type*} [CommRing K] (φ : ℤ →+* K)
    (F : Inputs) (u : List Bool) (k : ℕ) (hk : F.depth u = k + 1)
    (hplan : Valid F u) (z : Fin (FlatFullSourceTower.count F u) → K)
    (hz : ∀ i, (FlatFullSourceTower.system F u i).eval₂ φ z = 0) :
    (BoundedFullCriticalSamples.polynomial F.source u).eval₂ φ
      (FlatCriticalTower.current (arity F u) (F.depth u)
        (z ∘ TriangularPolynomialIndexing.enumerate (arity F u) (F.depth u))) = 0 := by
  have H := (FlatCriticalTower.roots_iff φ (BoundedFullCriticalSamples.polynomial F.source u)
    (free F u) (F.pivot u) (FlatFullSourceTower.direction F u) (F.depth u) z).mp hz
  have hp := pivot_mem F u hplan k (by omega)
  have aux : ∀ (d : ℕ) (w : TriangularPolynomialTower.Variables (arity F u) d → K), d = k + 1 →
      FlatCriticalTower.Steps φ (BoundedFullCriticalSamples.polynomial F.source u)
        (free F u) (F.pivot u) (FlatFullSourceTower.direction F u) d w →
      (BoundedFullCriticalSamples.polynomial F.source u).eval₂ φ
        (FlatCriticalTower.current (arity F u) d w) = 0 := by
    intro d w hd hs
    subst d
    have HC := hs.2.1 (F.pivot u k) hp
    have hw : FlatCriticalTower.current (arity F u) (k + 1) w = fun i => w (Sum.inr i) := funext fun _ => rfl
    rw [hw]
    simpa only [FlatFullSourceTower.arity, ProjectionCriticalFamily.spatialEquation, ite_true,
      Function.comp_def] using HC
  exact aux _ _ hk H

end LeanCanny.Encoding.FlatFullSourcePlan
