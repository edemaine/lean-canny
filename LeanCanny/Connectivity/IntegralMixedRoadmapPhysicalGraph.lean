/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.IntegralMixedRoadmapPointReachability
public import Mathlib.Data.Set.Finite.List

/-! # The actual finite roadmap graph on physical points

Edges retain existential native certificates. Entire-point identity edges
let a walk switch between independently sampled representatives. This
erases word choices without assuming that their ordinals remain constant.
-/

@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapPhysicalGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term} (hn : UnaryFn n)
  (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)

def Word (c : List Bool) := {q : List Bool //
  IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q ∧ IntegralMixedRoadmapAtomic.candidate q = c}

noncomputable def point (c : List Bool) (w : Word hn ht ha hR0 c) : Fin (n (pairFst c) + 3 + 1) → ℝ :=
  pointAt hn ht ha hR0 c w.val w.property.1 w.property.2

noncomputable def vertices (c : List Bool) := Set.range (point hn ht ha hR0 c)

noncomputable def Edge (c : List Bool) (x y : Fin (n (pairFst c) + 3 + 1) → ℝ) : Prop :=
  ∃ a b : Word hn ht ha hR0 c,
    point hn ht ha hR0 c a = x ∧ point hn ht ha hR0 c b = y ∧
      IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0 a.val b.val

noncomputable def Reachable (c : List Bool) (x y : Fin (n (pairFst c) + 3 + 1) → ℝ) : Prop :=
  x ∈ vertices hn ht ha hR0 c ∧ Relation.ReflTransGen (Edge hn ht ha hR0 c) x y

theorem word_finite (c : List Bool) : Finite (Word hn ht ha hR0 c) := by
  change Finite {q : List Bool // IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q ∧
    IntegralMixedRoadmapAtomic.candidate q = c}
  apply Set.Finite.to_subtype (s := {q : List Bool | IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q ∧
    IntegralMixedRoadmapAtomic.candidate q = c})
  apply (List.finite_length_le Bool (IntegralMixedRoadmapAtomic.byteBudget hn ht ha hR0 (pairFst c))).subset
  intro q hq
  change q.length ≤ IntegralMixedRoadmapAtomic.byteBudget hn ht ha hR0 (pairFst c)
  have ho : IntegralMixedRoadmapAtomic.original q = pairFst c := congrArg pairFst hq.2
  simpa only [ho] using IntegralMixedRoadmapAtomic.byte_bound hn ht ha hR0 q hq.1

theorem vertices_finite (c : List Bool) : (vertices hn ht ha hR0 c).Finite := by
  let : Finite (Word hn ht ha hR0 c) := word_finite hn ht ha hR0 c
  exact Set.finite_range _

theorem edge_reachable {c : List Bool} {x y : Fin (n (pairFst c) + 3 + 1) → ℝ}
    (h : Edge hn ht ha hR0 c x y) : PointReachable hn ht ha hR0 c x y := by
  obtain ⟨a, b, ha, hb, he⟩ := h
  exact ⟨a.val, b.val, a.property.1, b.property.1, a.property.2, b.property.2, ha, hb,
    a.property.1, b.property.1, a.property.2, b.property.2, Relation.ReflTransGen.single he⟩

private theorem map_raw_path (c : List Bool) {a b : List Bool}
    (h : Relation.ReflTransGen (IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0) a b)
    (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc : IntegralMixedRoadmapAtomic.candidate a = c) (hd : IntegralMixedRoadmapAtomic.candidate b = c) :
    Relation.ReflTransGen (Edge hn ht ha hR0 c)
      (pointAt hn ht ha hR0 c a hA hc) (pointAt hn ht ha hR0 c b hB hd) := by
  induction h with
  | refl => exact .refl
  | @tail b d path edge ih =>
    have hv := (IntegralMixedRoadmapEdge.valid hn ht ha hR0 b d edge).1
    have he : IntegralMixedRoadmapAtomic.candidate b = c :=
      (IntegralMixedRoadmapEdge.candidate_eq hn ht ha hR0 b d edge).trans hd
    exact (ih hv he).tail ⟨⟨b, hv, he⟩, ⟨d, hB, hd⟩, rfl, rfl, edge⟩

theorem reachable_iff (c : List Bool) (x y : Fin (n (pairFst c) + 3 + 1) → ℝ) :
    Reachable hn ht ha hR0 c x y ↔ PointReachable hn ht ha hR0 c x y := by
  constructor
  · rintro ⟨hx, path⟩
    induction path with
    | refl =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨a.val, a.val, a.property.1, a.property.1, a.property.2, a.property.2, rfl, rfl,
        a.property.1, a.property.1, a.property.2, a.property.2, Relation.ReflTransGen.refl⟩
    | tail _ edge ih => exact PointReachable.trans hn ht ha hR0 ih (edge_reachable hn ht ha hR0 edge)
  · rintro ⟨a, b, hA, hB, hc, hd, rfl, rfl, hr⟩
    exact ⟨⟨⟨a, hA, hc⟩, rfl⟩, map_raw_path hn ht ha hR0 c hr.2.2.2.2 hA hB hc hd⟩

theorem reachable_iff_raw (c a b : List Bool)
    (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc : IntegralMixedRoadmapAtomic.candidate a = c) (hd : IntegralMixedRoadmapAtomic.candidate b = c) :
    Reachable hn ht ha hR0 c (pointAt hn ht ha hR0 c a hA hc)
      (pointAt hn ht ha hR0 c b hB hd) ↔ RawReachable hn ht ha hR0 c a b :=
  (reachable_iff hn ht ha hR0 c _ _).trans (point_reachable_iff_raw hn ht ha hR0 c a b hA hB hc hd)

theorem vertices_subset_zero (c : List Bool) :
    vertices hn ht ha hR0 c ⊆ zeroSet (n := n) (t := t) (R0 := R0) c := by
  rintro x ⟨w, rfl⟩
  exact pointAt_zero hn ht ha hR0 c w.val w.property.1 w.property.2

theorem reachable_joined {c : List Bool} {x y : Fin (n (pairFst c) + 3 + 1) → ℝ}
    (h : Reachable hn ht ha hR0 c x y) :
    JoinedIn (zeroSet (n := n) (t := t) (R0 := R0) c) x y :=
  PointReachable.joined hn ht ha hR0 ((reachable_iff hn ht ha hR0 c x y).mp h)

end LeanCanny.Connectivity.IntegralMixedRoadmapPhysicalGraph
