/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FiniteImageRank
public import LeanCanny.Geometry.SymbolicRootCurveOrder

/-! # Distinct actual-fiber ranks are constant along retained branches

Only values realized by the finite branch family are counted. Repeated
coordinate values are counted once. Pairwise coordinate comparisons are
constant away from the constructed scalar exceptions, so these ranks give
persistent branch records without enumerating extraneous coordinate roots.
-/

@[expose] public section
namespace LeanCanny.Geometry.AlgebraicFiberImageRank
open Set LeanCanny.Algebra
open scoped Classical
variable {J ι : Type*} [Fintype J] [LinearOrder J]

noncomputable def rank (curve : J → ι → ℝ) (j : J) (i : ι) : ℕ :=
  FiniteImageRank.rank Finset.univ (fun k => curve k i) (curve j i)

theorem rank_eq {a b : ℝ} (p : ι → Polynomial (Polynomial ℤ))
    (havoid : ∀ u ∈ Ioo a b, ∀ i, SymbolicScaledSquarefree.scalarEvaluation u
      (SymbolicScaledSquarefree.exceptional (p i)) ≠ 0)
    (curve : J → C(Ioo a b, ι → ℝ))
    (hroot : ∀ j u i, (p i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation u.val) (curve j u i) = 0)
    (j : J) (s t : Ioo a b) : rank (fun k => curve k s) j = rank (fun k => curve k t) j := by
  funext i
  apply FiniteImageRank.rank_eq_of_comparisons
  · intro k _ l _
    exact (SymbolicRootCurveOrder.coordinate_comparison_iff (p i) (fun u hu => havoid u hu i)
      (curve k) (curve l) i (fun u => hroot k u i) (fun u => hroot l u i) s t).1
  · intro k _
    exact (SymbolicRootCurveOrder.coordinate_comparison_iff (p i) (fun u hu => havoid u hu i)
      (curve k) (curve j) i (fun u => hroot k u i) (fun u => hroot j u i) s t).2

theorem rank_eq_iff (curve : J → ι → ℝ) (j k : J) : rank curve j = rank curve k ↔ curve j = curve k := by
  constructor
  · intro he
    funext i
    exact (FiniteImageRank.rank_eq_iff Finset.univ (fun l => curve l i) j k (Finset.mem_univ _) (Finset.mem_univ _)).mp
      (congrFun he i)
  · intro he
    funext i
    exact congrArg (FiniteImageRank.rank Finset.univ (fun l => curve l i)) (congrFun he i)

theorem rank_injective (curve : J → ι → ℝ) (hc : Function.Injective curve) : Function.Injective (rank curve) := by
  intro j k he
  exact hc ((rank_eq_iff curve j k).mp he)

end LeanCanny.Geometry.AlgebraicFiberImageRank
