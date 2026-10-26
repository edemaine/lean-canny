/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexInterleavedQuery
public import LeanCanny.Computation.PolyTimeArithmetic

/-! # Independent formula witnesses over shared spatial inputs

Two parity copies of the formulas have separate witnesses. Their first finite
blocks are linked to the same source wires. The source circuit is retained
once; the link writer and both formula copies have native polynomial-time costs.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.RealQuery.Interleaved.Duplicated
open LeanCanny.Computation LeanCanny.Encoding LeanCanny.Encoding.Brackets
open scoped Classical

def port (f : ℕ → ℕ) (i : ℕ) : ℕ := f (i / 2)

def merge (a b : ℕ → ℝ) (i : ℕ) : ℝ := if i % 2 = 0 then a (i / 2) else b (i / 2)

theorem merge_even (a b : ℕ → ℝ) (i : ℕ) : merge a b (even i) = a i := by
  simp [merge, even, Nat.mul_comm]

theorem merge_odd (a b : ℕ → ℝ) (i : ℕ) : merge a b (odd i) = b i := by
  have hm : (2 * i + 1) % 2 = 1 := by omega
  have hd : (2 * i + 1) / 2 = i := by omega
  simp only [merge, odd, hm, one_ne_zero, ite_false, hd]

def combine (p q : Formula) : Formula :=
  .and (p.rename (Interleave.index false)) (q.rename (Interleave.index true))

theorem combine_holds (p q : Formula) (x : ℕ → ℝ) :
    (combine p q).Holds x ↔ p.Holds (fun i => x (even i)) ∧ q.Holds (fun i => x (odd i)) := by
  simp only [combine, Formula.Holds, Formula.holds_rename, Function.comp_def, Interleave.index,
    Bool.toNat_false, Bool.toNat_true, Nat.add_zero, even, odd]

theorem combine_mem_FP {p q : List Bool → Formula}
    (hp : (fun c => (p c).encode) ∈ FP) (hq : (fun c => (q c).encode) ∈ FP) :
    (fun c => (combine (p c) (q c)).encode) ∈ FP := by
  have h := Codec.taggedTwo_mem_FP 4 (mem_FP_comp hp (Interleave.renameBits_mem_FP false))
    (mem_FP_comp hq (Interleave.renameBits_mem_FP true))
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, Interleave.renameBits_encode]
  simp only [combine, Formula.encode, Formula.toData, Codec.taggedTwo_toBits]

theorem port_unary {f : List Bool → ℕ → ℕ}
    (hf : UnaryFn (fun c => f (pairFst c) (pairSnd c).length)) :
    UnaryFn (fun c => port (f (pairFst c)) (pairSnd c).length) := by
  have hi := (UnaryFn.length pairSnd_mem_FP).div (UnaryFn.const 2)
  apply (hf.comp (mem_FP_pair pairFst_mem_FP hi.mem_FP)).of_eq
  intro c
  simp only [port, pairFst_pair, pairSnd_pair, List.length_replicate]

theorem realizes_iff (n start : ℕ) (f : ℕ → ℕ) (prior : List Gate) (x : ℕ → ℝ) :
    PortRealizes (2 * n) start (port f) prior x ↔
      PortRealizes n start f prior (fun i => x (even i)) ∧ ∀ i < n, x (even i) = x (odd i) := by
  constructor
  · rintro ⟨env, hg, hr, hi⟩
    have he : ∀ i < n, env (f i) = (x (even i) : ℂ) := by
      intro i h
      have hv := hi (even i) (by unfold even; omega)
      have hd : even i / 2 = i := by unfold even; omega
      simpa only [port, hd] using hv
    refine ⟨⟨env, hg, hr, he⟩, ?_⟩
    intro i h
    have hv := hi (odd i) (by unfold odd; omega)
    have hd : odd i / 2 = i := by unfold odd; omega
    rw [port, hd] at hv
    exact Complex.ofReal_injective ((he i h).symm.trans hv)
  · rintro ⟨⟨env, hg, hr, hi⟩, hh⟩
    refine ⟨env, hg, hr, ?_⟩
    intro i h
    have hq : i / 2 < n := by omega
    change env (f (i / 2)) = (x i : ℂ)
    rw [hi (i / 2) hq]
    apply congrArg Complex.ofReal
    change x (even (i / 2)) = x i
    by_cases hm : i % 2 = 0
    · have he : even (i / 2) = i := by unfold even; omega
      rw [he]
    · rw [hh (i / 2) hq]
      have he : odd (i / 2) = i := by unfold odd; omega
      rw [he]

theorem satisfiable_iff (n start : ℕ) (f : ℕ → ℕ) (prior : List Gate) (p q : Formula) :
    PortSatisfiable (2 * n) start (port f) prior (combine p q) ↔
      ∃ a b : ℕ → ℝ, PortRealizes n start f prior a ∧
        (∀ i < n, a i = b i) ∧ p.Holds a ∧ q.Holds b := by
  rw [portSatisfiable_iff]
  constructor
  · rintro ⟨x, hx, hp⟩
    obtain ⟨hr, he⟩ := (realizes_iff n start f prior x).mp hx
    obtain ⟨hp, hq⟩ := (combine_holds p q x).mp hp
    exact ⟨fun i => x (even i), fun i => x (odd i), hr, he, hp, hq⟩
  · rintro ⟨a, b, hr, he, hp, hq⟩
    refine ⟨merge a b, (realizes_iff n start f prior _).mpr ⟨?_, ?_⟩, ?_⟩
    · simpa only [merge_even] using hr
    · simpa only [merge_even, merge_odd] using he
    · apply (combine_holds p q _).mpr
      simpa only [merge_even, merge_odd] using And.intro hp hq

theorem evaluator {n start fresh : List Bool → ℕ} {f : List Bool → ℕ → ℕ}
    {prior : List Bool → List Gate} {p q : List Bool → Formula}
    (hn : UnaryFn n) (hs : UnaryFn start) (hfresh : UnaryFn fresh)
    (hf : UnaryFn (fun c => f (pairFst c) (pairSnd c).length))
    (hprior : (fun c => encode (prior c)) ∈ FP)
    (hp : (fun c => (p c).encode) ∈ FP) (hq : (fun c => (q c).encode) ∈ FP)
    (hb : ∀ c i, i < n c → f c i < start c) (hsf : ∀ c, start c ≤ fresh c)
    (ha : ∀ c g, g ∈ prior c → g.arity ≤ fresh c) :
    SpaceFunction (fun c => [decide (PortSatisfiable (2 * n c) (start c) (port (f c)) (prior c) (combine (p c) (q c)))]) := by
  have hport : ∀ c i, i < 2 * n c → port (f c) i < start c := by
    intro c i hi
    exact hb c (i / 2) (by omega)
  exact port_evaluator_of_real ((UnaryFn.const 2).mul hn) hs hfresh (port_unary hf) hprior
    (combine_mem_FP hp hq) (fun c i hi => Or.inr (hport c i hi)) hsf
    (fun c i hi => (hport c i hi).trans_le (hsf c)) ha

end LeanCanny.ETR.ComplexCircuit.RealQuery.Interleaved.Duplicated
