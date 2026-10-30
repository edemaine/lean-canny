import LeanCanny.Connectivity.AffineShiftSlab

/-! Singular endpoint merging and isolated endpoint roots.
Run with `lake env lean -DwarningAsError=true scripts/CheckFiniteFiberSlabs.lean`.
-/

open LeanCanny LeanCanny.Connectivity Set
open scoped Classical

namespace MergingSlabRegression
private def H (t x : ℝ) := x = t ∨ x = -t
private def curve (j : Bool) (t : ℝ) : ℝ := if j then t else -t

private lemma continuous_curve (j : Bool) : ContinuousOn (curve j) (Icc (0 : ℝ) 1) := by
  cases j
  · exact continuous_neg.continuousOn
  · exact continuous_id.continuousOn

private lemma root (j : Bool) (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) : H t (curve j t) := by
  cases j <;> simp [H, curve]

private lemma complete (t : ℝ) (_ : t ∈ Ioo (0 : ℝ) 1) (x : ℝ) (hx : H t x) :
    ∃ j, curve j t = x := by
  rcases hx with h | h
  · exact ⟨true, h.symm⟩
  · exact ⟨false, h.symm⟩

private lemma injective (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    Function.Injective (fun j => curve j t) := by
  intro i j hij
  cases i <;> cases j
  · rfl
  · have h : -t = t := hij
    exfalso
    linarith [ht.1]
  · have h : t = -t := hij
    exfalso
    linarith [ht.1]
  · rfl

private lemma finite_fiber (t : ℝ) : Finite (FiniteFiberSlab.Fiber H t) := by
  have h : {x : ℝ | H t x} = {t, -t} := by ext x; simp [H]
  exact (h ▸ (Set.toFinite {t, -t})).to_subtype

-- The two interior branches do not have an edge directly.
example : ¬FiniteFiberSlab.Edge H curve 0 1 (.inl false) (.inl true) := by
  change ¬(false = true)
  decide

-- They are joined through their common singular endpoint at zero.
example : Relation.ReflTransGen (FiniteFiberSlab.Edge H curve 0 1) (.inl false) (.inl true) := by
  let z : FiniteFiberSlab.Fiber H 0 := ⟨0, Or.inl rfl⟩
  apply (Relation.ReflTransGen.single (b := .inr (.inl z)) ?_).trans
    (Relation.ReflTransGen.single ?_)
  · change curve false 0 = 0
    simp [curve]
  · change curve true 0 = 0
    simp [curve]

-- The graph path supplies an actual path in the entire singular closed slab.
example : JoinedIn (univ : Set (SlabCover.Space H 0 1))
    ⟨((1 : ℝ) / 2, -(1 / 2)), by norm_num, Or.inr rfl⟩
    ⟨((1 : ℝ) / 2, 1 / 2), by norm_num, Or.inl rfl⟩ := by
  let : Finite (FiniteFiberSlab.Fiber H 0) := finite_fiber 0
  let : Finite (FiniteFiberSlab.Fiber H 1) := finite_fiber 1
  have hwalk : Relation.ReflTransGen (FiniteFiberSlab.Edge H curve 0 1) (.inl false) (.inl true) := by
    let z : FiniteFiberSlab.Fiber H 0 := ⟨0, Or.inl rfl⟩
    exact (Relation.ReflTransGen.single (b := .inr (.inl z)) (by simp [FiniteFiberSlab.Edge, curve, z])).trans
      (Relation.ReflTransGen.single (by simp [FiniteFiberSlab.Edge, curve, z]))
  apply (FiniteFiberSlab.joinedIn_iff_reachable H (by norm_num : (0 : ℝ) < 1) curve
    continuous_curve root complete injective (i := .inl false) (j := .inl true) ?_ ?_).mpr hwalk
  · exact ⟨(1 : ℝ) / 2, by norm_num, rfl⟩
  · exact ⟨(1 : ℝ) / 2, by norm_num, rfl⟩

end MergingSlabRegression

namespace IsolatedEndpointRegression
private def H (t x : ℝ) := t = 0 ∧ x = 0
private def curve (j : Empty) : ℝ → ℝ := j.elim

-- No interior branch is needed to cover an isolated singular endpoint root.
example (z : SlabCover.Space H 0 1) : ∃ i, z ∈ FiniteFiberSlab.piece H curve 0 1 i := by
  apply FiniteFiberSlab.cover H curve
  intro t ht x hx
  exact (ne_of_gt ht.1 hx.1).elim

-- The root remains a vertex, rather than being lost with the empty interior.
example : (FiniteFiberSlab.piece H curve 0 1
    (.inr (.inl (⟨0, rfl, rfl⟩ : FiniteFiberSlab.Fiber H 0)))).Nonempty := by
  apply FiniteFiberSlab.nonempty_piece H (by norm_num : (0 : ℝ) < 1) curve
  intro j
  exact j.elim

end IsolatedEndpointRegression
