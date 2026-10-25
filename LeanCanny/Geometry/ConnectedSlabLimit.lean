/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Connected limits of slab components

For a proper real-valued map, a set with connected arbitrarily short tails
has a compact connected limit in the endpoint fiber. No regularity at the
endpoint, finite set of possible limits, or path selection is assumed.
-/

@[expose] public section

namespace LeanCanny.Geometry.ConnectedSlabLimit
open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- Decreasing compact connected sets have connected intersection, including
the empty intersection. Compactness supplies uniform separated neighborhoods. -/
theorem isPreconnected_iInter {ι : Type*} [Nonempty ι] (K : ι → Set X)
    (hdir : Directed (· ⊇ ·) K) (hcompact : ∀ i, IsCompact (K i))
    (hconn : ∀ i, IsPreconnected (K i)) : IsPreconnected (⋂ i, K i) := by
  classical
  have hclosed : IsClosed (⋂ i, K i) := isClosed_iInter (fun i => (hcompact i).isClosed)
  have hc : IsCompact (⋂ i, K i) :=
    (hcompact (Classical.arbitrary ι)).of_isClosed_subset hclosed (iInter_subset _ _)
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hclosed]
  intro u v hu hv hcover hdis
  have hdis' : Disjoint ((⋂ i, K i) ∩ u) ((⋂ i, K i) ∩ v) :=
    hdis.mono inter_subset_right inter_subset_right
  obtain ⟨U, V, hU, hV, huU, hvV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact
    (hc.inter_right hu) (hc.inter_right hv) hdis'
  have hsub : (⋂ i, K i) ⊆ U ∪ V := by
    intro x hx
    exact (hcover hx).imp (fun h => huU ⟨hx, h⟩) (fun h => hvV ⟨hx, h⟩)
  obtain ⟨i, hi⟩ := exists_subset_nhds_of_isCompact hdir hcompact
    ((hU.union hV).mem_nhdsSet.mpr hsub)
  rcases (hconn i).subset_or_subset hU hV hUV hi with h | h
  · left
    intro x hx
    rcases hcover hx with hxu | hxv
    · exact hxu
    · exact False.elim (Set.disjoint_left.mp hUV (h (mem_iInter.mp hx i)) (hvV ⟨hx, hxv⟩))
  · right
    intro x hx
    rcases hcover hx with hxu | hxv
    · exact False.elim (Set.disjoint_left.mp hUV (huU ⟨hx, hxu⟩) (h (mem_iInter.mp hx i)))
    · exact hxv

variable (p : X → ℝ) {a b : ℝ} {s : Set X}

def tail (s : Set X) (c : ℝ) : Set X := s ∩ p ⁻¹' Ioo a c

omit [T2Space X] in
/-- The endpoint limit is the intersection of all closed short tails. -/
theorem endpoint_eq_iInter (hp : Continuous p) (hab : a < b)
    (hs : s ⊆ p ⁻¹' Ioo a b) :
    closure s ∩ p ⁻¹' {a} = ⋂ c : Ioo a b, closure (tail p (a := a) s c.val) := by
  ext x
  constructor
  · rintro ⟨hx, hpx⟩
    apply mem_iInter.mpr
    intro c
    have hopen := hp.isOpen_preimage (Iio c.val) isOpen_Iio
    have hm : x ∈ closure (s ∩ p ⁻¹' Iio c.val) :=
      hopen.closure_inter ⟨hx, by change p x < c.val; rw [show p x = a from hpx]; exact c.property.1⟩
    apply closure_mono ?_ hm
    intro y hy
    exact ⟨hy.1, (hs hy.1).1, hy.2⟩
  · intro hx
    let c₀ : Ioo a b := ⟨(a + b) / 2, by constructor <;> linarith⟩
    have hxc := mem_iInter.mp hx c₀
    refine ⟨closure_mono inter_subset_left hxc, ?_⟩
    have hbound (c : Ioo a b) : p x ∈ Icc a c.val := by
      apply closure_minimal (t := p ⁻¹' Icc a c.val) ?_
        (isClosed_Icc.preimage hp) (mem_iInter.mp hx c)
      intro y hy
      exact Ioo_subset_Icc_self hy.2
    change p x = a
    apply le_antisymm ?_ (hbound c₀).1
    by_contra h
    have hax : a < p x := lt_of_not_ge h
    obtain ⟨c, hac, hcx⟩ := exists_between (lt_min hab hax)
    have hc : c ∈ Ioo a b := ⟨hac, hcx.trans_le (min_le_left _ _)⟩
    exact (not_lt_of_ge (hbound ⟨c, hc⟩).2) (hcx.trans_le (min_le_right _ _))

omit [T2Space X] in
/-- Properness bounds every closed tail, even at a critical endpoint. -/
theorem isCompact_closed_tail (hp : IsProperMap p) (hs : s ⊆ p ⁻¹' Ioo a b)
    (c : Ioo a b) : IsCompact (closure (tail p (a := a) s c.val)) := by
  apply (hp.isCompact_preimage (isCompact_Icc (a := a) (b := b))).of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ (isClosed_Icc.preimage hp.continuous)
  intro x hx
  exact Ioo_subset_Icc_self (hs hx.1)

/-- The whole endpoint limit, rather than just a chosen subsequential limit,
is connected. This includes limits containing more than one point. -/
theorem isPreconnected_endpoint (hp : IsProperMap p) (hab : a < b)
    (hs : s ⊆ p ⁻¹' Ioo a b)
    (hconn : ∀ c : Ioo a b, IsPreconnected (tail p (a := a) s c.val)) :
    IsPreconnected (closure s ∩ p ⁻¹' {a}) := by
  let : Nonempty (Ioo a b) := ⟨⟨(a + b) / 2, by constructor <;> linarith⟩⟩
  rw [endpoint_eq_iInter p hp.continuous hab hs]
  apply isPreconnected_iInter _ ?_ (isCompact_closed_tail p hp hs) (fun c => (hconn c).closure)
  intro c d
  refine ⟨⟨min c.val d.val, lt_min c.property.1 d.property.1,
    (min_le_left _ _).trans_lt c.property.2⟩, ?_, ?_⟩
  · exact closure_mono (fun _ h => ⟨h.1, h.2.1, h.2.2.trans_le (min_le_left _ _)⟩)
  · exact closure_mono (fun _ h => ⟨h.1, h.2.1, h.2.2.trans_le (min_le_right _ _)⟩)

omit [T2Space X] in
theorem isCompact_endpoint (hp : IsProperMap p) :
    IsCompact (closure s ∩ p ⁻¹' {a}) :=
  (hp.isCompact_preimage isCompact_singleton).inter_left isClosed_closure

/-- If each short tail is nonempty, a connected component cannot disappear
before reaching the endpoint fiber. -/
theorem isConnected_endpoint (hp : IsProperMap p) (hab : a < b)
    (hs : s ⊆ p ⁻¹' Ioo a b)
    (hconn : ∀ c : Ioo a b, IsConnected (tail p (a := a) s c.val)) :
    IsConnected (closure s ∩ p ⁻¹' {a}) := by
  refine ⟨?_, isPreconnected_endpoint p hp hab hs (fun c => (hconn c).isPreconnected)⟩
  rw [endpoint_eq_iInter p hp.continuous hab hs]
  let : Nonempty (Ioo a b) := ⟨⟨(a + b) / 2, by constructor <;> linarith⟩⟩
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ ?_
    (fun c => (hconn c).nonempty.closure) (isCompact_closed_tail p hp hs)
    (fun _ => isClosed_closure)
  intro c d
  refine ⟨⟨min c.val d.val, lt_min c.property.1 d.property.1,
    (min_le_left _ _).trans_lt c.property.2⟩, ?_, ?_⟩
  · exact closure_mono (fun _ h => ⟨h.1, h.2.1, h.2.2.trans_le (min_le_left _ _)⟩)
  · exact closure_mono (fun _ h => ⟨h.1, h.2.1, h.2.2.trans_le (min_le_right _ _)⟩)

/-- Reflection gives the upper-endpoint version without endpoint regularity. -/
theorem isConnected_endpoint_right (hp : IsProperMap p) (hab : a < b)
    (hs : s ⊆ p ⁻¹' Ioo a b)
    (hconn : ∀ c : Ioo a b, IsConnected (s ∩ p ⁻¹' Ioo c.val b)) :
    IsConnected (closure s ∩ p ⁻¹' {b}) := by
  have hproper : IsProperMap (fun x => -p x) := (Homeomorph.neg ℝ).isProperMap.comp hp
  have hsub : s ⊆ (fun x => -p x) ⁻¹' Ioo (-b) (-a) := by
    intro x hx
    have h := hs hx
    constructor <;> linarith [h.1, h.2]
  have htail (c : Ioo (-b) (-a)) :
      IsConnected (tail (fun x => -p x) (a := -b) s c.val) := by
    have hc : -c.val ∈ Ioo a b := by constructor <;> linarith [c.property.1, c.property.2]
    have he : tail (fun x => -p x) (a := -b) s c.val = s ∩ p ⁻¹' Ioo (-c.val) b := by
      ext x
      change (x ∈ s ∧ -b < -p x ∧ -p x < c.val) ↔ (x ∈ s ∧ -c.val < p x ∧ p x < b)
      constructor <;> rintro ⟨hx, h₁, h₂⟩ <;> exact ⟨hx, by linarith, by linarith⟩
    rw [he]
    exact hconn ⟨-c.val, hc⟩
  have H := isConnected_endpoint (fun x => -p x) hproper (by linarith : -b < -a) hsub htail
  have he : (fun x => -p x) ⁻¹' {-b} = p ⁻¹' {b} := by ext x; simp
  rwa [he] at H

end LeanCanny.Geometry.ConnectedSlabLimit
