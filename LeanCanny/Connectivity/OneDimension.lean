/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.ZeroDimension
public import Mathlib.Topology.Order.IntermediateValue

/-! # Whole-space connectivity in one dimension by an ETR gap query

A subset of the real line is preconnected precisely when it has no missing
point strictly between two of its points. The gap has an existential formula
using three disjoint copies of the input. Its writer is polynomial time, so
the completed ETR decider gives a native polynomial-space base case for every
Boolean input, including empty, singular, and unbounded realizations.
-/

@[expose] public section

namespace LeanCanny.Connectivity.OneDimension
open ETR Computation Turing.MultiTapeTM Set
open scoped Classical

def realSet (p : Formula) : Set ℝ :=
  {x | p.Holds (Formula.extend (fun _ : Fin 1 => x))}

theorem holds_rename_one (p : Formula) (hp : p.arity ≤ 1) (f : ℕ → ℕ) (env : ℕ → ℝ) :
    (p.rename f).Holds env ↔ p.Holds (Formula.extend (fun _ : Fin 1 => env (f 0))) := by
  rw [Formula.holds_rename]
  apply p.holds_congr
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  simp only [Function.comp_apply, Formula.extend, Nat.zero_lt_succ, dite_true]

def less (i j : ℕ) : Formula :=
  .ltZero (.add (.var i) (.mul (.const (-1)) (.var j)))

theorem less_holds (i j : ℕ) (env : ℕ → ℝ) :
    (less i j).Holds env ↔ env i < env j := by
  simp only [less, Formula.Holds, Term.eval, Int.cast_neg, Int.cast_one, neg_one_mul,
    ← sub_eq_add_neg, sub_neg]

def gapQuery (p : Formula) : Formula :=
  .and (p.rename (Interleave.index false))
    (.and (p.rename (Interleave.index true))
      (.and (.not ((p.rename (Interleave.index true)).rename (Interleave.index false)))
        (.and (less 0 2) (less 2 1))))

theorem gap_holds (p : Formula) (hp : p.arity ≤ 1) (env : ℕ → ℝ) :
    (gapQuery p).Holds env ↔
      env 0 ∈ realSet p ∧ env 1 ∈ realSet p ∧ env 2 ∉ realSet p ∧
        env 0 < env 2 ∧ env 2 < env 1 := by
  have h2 : ((p.rename (Interleave.index true)).rename (Interleave.index false)).Holds env ↔
      env 2 ∈ realSet p := by
    rw [Formula.holds_rename]
    simpa only [Function.comp_apply, Interleave.index, Bool.toNat_false, Bool.toNat_true,
      Nat.mul_zero, Nat.zero_add, Nat.mul_one, realSet, mem_ofPred_eq] using
        holds_rename_one p hp (Interleave.index true) (env ∘ Interleave.index false)
  simp only [gapQuery, Formula.Holds, holds_rename_one p hp, h2, less_holds,
    Interleave.index, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero,
    Nat.zero_add, realSet, mem_ofPred_eq]

theorem gap_satisfiable (p : Formula) (hp : p.arity ≤ 1) :
    (gapQuery p).Satisfiable ↔
      ∃ x y z : ℝ, x ∈ realSet p ∧ y ∈ realSet p ∧ z ∉ realSet p ∧ x < z ∧ z < y := by
  constructor
  · rintro ⟨env, h⟩
    exact ⟨env 0, env 1, env 2, (gap_holds p hp env).mp h⟩
  · rintro ⟨x, y, z, hx, hy, hz, hxy, hyz⟩
    refine ⟨fun k => if k = 0 then x else if k = 1 then y else z, ?_⟩
    apply (gap_holds p hp _).mpr
    simpa using And.intro hx (And.intro hy (And.intro hz (And.intro hxy hyz)))

theorem preconnected_iff (p : Formula) :
    IsPreconnected (Description.mk 1 p).realization ↔ IsPreconnected (realSet p) := by
  let e := Homeomorph.piUnique (fun _ : Fin 1 => ℝ)
  have he : e '' (Description.mk 1 p).realization = realSet p := by
    rw [e.image_eq_preimage_symm]
    rfl
  rw [← e.isPreconnected_image, he]

theorem connected_iff (p : Formula) :
    (Description.mk 1 p).Connected ↔ p.arity ≤ 1 ∧ ¬ (gapQuery p).Satisfiable := by
  constructor
  · rintro ⟨hw, hconn⟩
    refine ⟨hw, ?_⟩
    rintro hgap
    obtain ⟨x, y, z, hx, hy, hz, hxz, hzy⟩ := (gap_satisfiable p hw).mp hgap
    exact hz ((preconnected_iff p).mp hconn |>.Icc_subset hx hy ⟨hxz.le, hzy.le⟩)
  · rintro ⟨hw, hgap⟩
    refine ⟨hw, (preconnected_iff p).mpr ?_⟩
    apply OrdConnected.isPreconnected
    apply ordConnected_of_Ioo
    intro x hx y hy _ z hz
    by_contra hbad
    exact hgap ((gap_satisfiable p hw).mpr ⟨x, y, z, hx, hy, hbad, hz.1, hz.2⟩)

def gapBits (bits : List Bool) : List Bool :=
  Codec.taggedTwo 4 (Interleave.renameBits false bits)
    (Codec.taggedTwo 4 (Interleave.renameBits true bits)
      (Codec.taggedTwo 4 (Codec.taggedOne 3 (Interleave.renameBits false (Interleave.renameBits true bits)))
        (Codec.taggedTwo 4 (less 0 2).encode (less 2 1).encode)))

theorem gapBits_mem_FP : gapBits ∈ FP :=
  Codec.taggedTwo_mem_FP 4 (Interleave.renameBits_mem_FP false)
    (Codec.taggedTwo_mem_FP 4 (Interleave.renameBits_mem_FP true)
      (Codec.taggedTwo_mem_FP 4 (Codec.taggedOne_mem_FP 3
        (mem_FP_comp (Interleave.renameBits_mem_FP true) (Interleave.renameBits_mem_FP false)))
        (Codec.taggedTwo_mem_FP 4 (constFn_mem_FP _) (constFn_mem_FP _))))

theorem gapBits_encode (p : Formula) : gapBits p.encode = (gapQuery p).encode := by
  unfold gapBits
  rw [Interleave.renameBits_encode, Interleave.renameBits_encode, Interleave.renameBits_encode]
  simp only [gapQuery, Formula.encode, Formula.toData,
    Codec.taggedTwo_toBits, Codec.taggedOne_toBits]

theorem gapQuery_computable {α : Type} {enc : α ↪ List Bool} {p : α → Formula}
    (hp : ComputableTidilyInPolyTime (fun a => (p a).encode) enc encBits) :
    ComputableTidilyInPolyTime (fun a => (gapQuery (p a)).encode) enc encBits := by
  apply (gapBits_mem_FP.comp hp).of_enc_eq
  intro a
  exact (gapBits_encode (p a)).symm

/-- The one-dimensional Boolean base case charges the input writer and
rejects out-of-dimension variables before interpreting the gap query. -/
theorem connected_computable {α : Type} {enc : α ↪ List Bool} {p : α → Formula}
    (hp : ComputableTidilyInPolyTime (fun a => (p a).encode) enc encBits) :
    ComputableInPolySpace (fun a => decide (Description.mk 1 (p a)).Connected) enc encBool := by
  have hsat := satisfiable_computable (gapQuery_computable hp)
  have hf : ComputableInPolySpace (fun _ : α => false) enc encBool := .of_tidyPolyTime (.const false)
  have ht : ComputableInPolySpace (fun _ : α => true) enc encBool := .of_tidyPolyTime (.const true)
  have harity := ComputableTidilyInPolyTime.comp FormulaArity.value_unary hp
  have hone : ComputableTidilyInPolyTime (fun _ : α => 1) enc encUnary := .const 1
  have hwell := ComputableInPolySpace.of_tidyPolyTime
    (ComputableTidilyInPolyTime.unary_le' harity hone)
  apply (hwell.ite (hsat.ite hf ht) hf).congr
  intro a
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq, FormulaArity.value_encode, connected_iff]
  by_cases hw : (p a).arity ≤ 1 <;> by_cases hs : (gapQuery (p a)).Satisfiable <;> simp [hw, hs]

end LeanCanny.Connectivity.OneDimension
