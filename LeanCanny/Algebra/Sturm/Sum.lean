/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: Algebra/Polynomial/Sturm/Sum.lean.
Changes: selected proof slice, project namespace, real specialization where needed,
and compatibility with the pinned Mathlib. See STURM_SOURCES.md.
-/
module

public import LeanCanny.Algebra.Sturm.Local
public import LeanCanny.Algebra.Sturm.Jumps

/-! # Signed root sums for alternating Sturm chains

The local jumps of an alternating chain telescope to a signed sum over the roots
of its first polynomial in an open interval. Only those roots must be simple;
the endpoints may be roots of interior entries, but not of the first entry.
-/

public section

namespace LeanCanny.Algebra.Sturm

open Polynomial List

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The finite union of the roots of all entries of a polynomial list. -/
private noncomputable def rootsFinset (cs : List (Polynomial R)) : Finset R :=
  cs.toFinset.biUnion (fun q => q.roots.toFinset)

omit [IsStrictOrderedRing R] in
private theorem mem_rootsFinset {cs : List (Polynomial R)} (hne : ∀ q ∈ cs, q ≠ 0) {x : R} :
    x ∈ rootsFinset cs ↔ ∃ q ∈ cs, q.eval x = 0 := by
  simp only [rootsFinset, Finset.mem_biUnion, List.mem_toFinset, Multiset.mem_toFinset]
  exact exists_congr fun q => and_congr_right fun hq => Polynomial.mem_roots (hne q hq)

namespace IsAlternating



/-- Moving right from a nonroot of the head changes no variations until the
next chain zero, even if an interior entry vanishes at the endpoint. -/
private theorem eq_right {cs : List (Polynomial ℝ)} (h : IsAlternating cs) {a c : ℝ} (hac : a < c)
    (ha : ∀ p, cs.head? = some p → p.eval a ≠ 0)
    (hz : ∀ x, a < x → x ≤ c → x ∉ rootsFinset cs) :
    signVariationsAt cs a = signVariationsAt cs c := by
  symm
  refine h.signVariationsAt_eq c a ?_ ha ?_
  · intro q hq hqc
    exact hz c hac le_rfl ((mem_rootsFinset h.nonzero).mpr ⟨q, hq, hqc⟩)
  · intro q hq hqa
    symm
    apply sign_eval_const _ hac.le
    intro x hx hqx
    rcases hx.1.eq_or_lt with hax | hax
    · exact hqa (hax ▸ hqx)
    · exact hz x hax hx.2 ((mem_rootsFinset h.nonzero).mpr ⟨q, hq, hqx⟩)

/-- The corresponding left-endpoint identity. -/
private theorem eq_left {cs : List (Polynomial ℝ)} (h : IsAlternating cs) {c b : ℝ} (hcb : c < b)
    (hb : ∀ p, cs.head? = some p → p.eval b ≠ 0)
    (hz : ∀ x, c ≤ x → x < b → x ∉ rootsFinset cs) :
    signVariationsAt cs c = signVariationsAt cs b := by
  refine h.signVariationsAt_eq c b ?_ hb ?_
  · intro q hq hqc
    exact hz c le_rfl hcb ((mem_rootsFinset h.nonzero).mpr ⟨q, hq, hqc⟩)
  · intro q hq hqb
    apply sign_eval_const _ hcb.le
    intro x hx hqx
    rcases hx.2.eq_or_lt with hxb | hxb
    · exact hqb (hxb ▸ hqx)
    · exact hz x hx.1 hxb ((mem_rootsFinset h.nonzero).mpr ⟨q, hq, hqx⟩)

/-- The signed variation formula with endpoints away from every chain zero. -/
private theorem sum_sign_of_nonzero {p q : Polynomial ℝ} {cs : List (Polynomial ℝ)}
    (h : IsAlternating (p :: q :: cs))
    {a b : ℝ} (hsimple : ∀ r, a < r → r < b → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (hab : a < b) (ha : a ∉ rootsFinset (p :: q :: cs))
    (hb : b ∉ rootsFinset (p :: q :: cs)) :
    (signVariationsAt (p :: q :: cs) a : ℤ) - signVariationsAt (p :: q :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) := by
  classical
  set chain := p :: q :: cs
  let w : ℝ → ℤ := fun r => if p.eval r = 0 then
    (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) else 0
  have hsum := sum_jumps (a₀ := a) (b₀ := b)
    (rootsFinset chain) (fun x => (signVariationsAt chain x : ℤ)) w
    (fun a b _ _ hab hn => by
      congr 1
      apply signVariationsAt_const chain hab.le
      intro s hs x hx hz
      exact hn x ((mem_rootsFinset h.nonzero).mpr ⟨s, hs, hz⟩) hx)
    (fun a r b haa hbb har hrb _ hn => by
      have hz : ∀ s ∈ chain, ∀ x ∈ Set.Icc a b, x ≠ r → s.eval x ≠ 0 := by
        intro s hs x hx hxr hsx
        exact hxr (hn x ((mem_rootsFinset h.nonzero).mpr ⟨s, hs, hsx⟩) hx)
      by_cases hr : p.eval r = 0
      · simpa [w, hr] using h.root_jump har hrb hr
          (hsimple r (haa.trans_lt har) (hrb.trans_le hbb) hr) hz
      · have hsame := h.signVariationsAt_nonroot har hrb (fun s hs => by cases hs; exact hr) hz
        simp only [w, chain, ite_eq_right hr, hsame.1.trans hsame.2, sub_self]) hab ha hb
  rw [hsum]
  let A := p.roots.toFinset.filter (fun r => a < r ∧ r < b)
  let B := (rootsFinset chain).filter (fun r => a < r ∧ r < b)
  have hAB : A ⊆ B := by
    intro r hr
    obtain ⟨hr, hi⟩ := Finset.mem_filter.mp hr
    have hpr : p.eval r = 0 := (Polynomial.mem_roots (h.nonzero p (by simp [chain]))).mp
      (Multiset.mem_toFinset.mp hr)
    exact Finset.mem_filter.mpr ⟨(mem_rootsFinset h.nonzero).mpr ⟨p, by simp [chain], hpr⟩, hi⟩
  have hrestrict : ∑ r ∈ A, w r = ∑ r ∈ B, w r := by
    apply Finset.sum_subset hAB
    intro r hr hn
    have hpr : p.eval r ≠ 0 := by
      intro hz
      apply hn
      exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots (h.nonzero p (by simp [chain]))).mpr hz),
        (Finset.mem_filter.mp hr).2⟩
    simp [w, hpr]
  rw [← hrestrict]
  apply Finset.sum_congr rfl
  intro r hr
  have hpr : p.eval r = 0 := (Polynomial.mem_roots (h.nonzero p (by simp [chain]))).mp
    (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1)
  simp [w, hpr]

/-- The signed Sturm formula on an interval whose endpoints are not roots of
the head polynomial. Interior entries may vanish at either endpoint. -/
theorem sum_sign {p q : Polynomial ℝ} {cs : List (Polynomial ℝ)}
    (h : IsAlternating (p :: q :: cs))
    {a b : ℝ} (hsimple : ∀ r, a < r → r < b → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (signVariationsAt (p :: q :: cs) a : ℤ) - signVariationsAt (p :: q :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) := by
  classical
  set chain := p :: q :: cs
  obtain ⟨m, ham, hmb⟩ := exists_between hab
  obtain ⟨c, hac, hcm, hc⟩ := exists_right_gap (rootsFinset chain) ham
  obtain ⟨d, hmd, hdb, hd⟩ := exists_left_gap (rootsFinset chain) hmb
  have hcd := hcm.trans hmd
  have hcZ : c ∉ rootsFinset chain := fun hz => (hc c hz hac).false
  have hdZ : d ∉ rootsFinset chain := fun hz => (hd d hz hdb).false
  have haV : signVariationsAt chain a = signVariationsAt chain c :=
    h.eq_right hac (fun s hs => by cases hs; exact ha)
      (fun x hax hxc hx => (hc x hx hax).not_ge hxc)
  have hbV : signVariationsAt chain d = signVariationsAt chain b :=
    h.eq_left hdb (fun s hs => by cases hs; exact hb)
      (fun x hdx hxb hx => (hd x hx hxb).not_ge hdx)
  have hfilters : p.roots.toFinset.filter (fun r => a < r ∧ r < b) =
      p.roots.toFinset.filter (fun r => c < r ∧ r < d) := by
    ext r
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hr, har, hrb⟩
      have hrZ : r ∈ rootsFinset chain := (mem_rootsFinset h.nonzero).mpr
        ⟨p, by simp [chain], (Polynomial.mem_roots (h.nonzero p (by simp [chain]))).mp
          (Multiset.mem_toFinset.mp hr)⟩
      exact ⟨hr, hc r hrZ har, hd r hrZ hrb⟩
    · rintro ⟨hr, hcr, hrd⟩
      exact ⟨hr, hac.trans hcr, hrd.trans hdb⟩
  rw [hfilters]
  rw [haV, ← hbV]
  exact h.sum_sign_of_nonzero
    (fun r hcr hrd => hsimple r (hac.trans hcr) (hrd.trans hdb)) hcd hcZ hdZ

end IsAlternating

end LeanCanny.Algebra.Sturm
