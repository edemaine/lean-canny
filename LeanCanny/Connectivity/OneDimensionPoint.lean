/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.OneDimension
public import Mathlib.Analysis.Convex.PathConnected

/-! # Real-line point connectivity by an existential separating-point query

Singleton endpoint validation retains irrational endpoints. After membership
tests for both endpoints, a path exists exactly when there is no missing
point strictly between them. All query writers and the native space bound
are uniform in the three input formulas.
-/

@[expose] public section

namespace LeanCanny.Connectivity.OneDimension
open ETR Computation Turing.MultiTapeTM Set
open scoped Classical

theorem tuple_eq_const (x : Fin 1 → ℝ) : (fun _ : Fin 1 => x 0) = x := by
  funext i
  exact congrArg x (Subsingleton.elim _ _)

theorem holds_env_one (p : Formula) (hp : p.arity ≤ 1) (env : ℕ → ℝ) :
    p.Holds env ↔ env 0 ∈ realSet p := by
  apply p.holds_congr
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  simp [Formula.extend]

theorem realSet_tuple (p : Formula) (x : Fin 1 → ℝ) :
    x 0 ∈ realSet p ↔ p.Holds (Formula.extend x) := by rw [realSet, mem_ofPred_eq, tuple_eq_const]

theorem joinedIn_real_iff {S : Set ℝ} (x y : ℝ) :
    JoinedIn S x y ↔ x ∈ S ∧ y ∈ S ∧
      ∀ z, (x < z ∧ z < y) ∨ (y < z ∧ z < x) → z ∈ S := by
  constructor
  · intro h
    refine ⟨h.source_mem, h.target_mem, ?_⟩
    intro z hz
    have hpre := isPreconnected_range h.somePath.continuous
    have hsub : range h.somePath ⊆ S := by rintro _ ⟨t, rfl⟩; exact h.somePath_mem t
    rcases hz with hz | hz
    · exact hsub (hpre.Icc_subset h.somePath.source_mem_range h.somePath.target_mem_range ⟨hz.1.le, hz.2.le⟩)
    · exact hsub (hpre.Icc_subset h.somePath.target_mem_range h.somePath.source_mem_range ⟨hz.1.le, hz.2.le⟩)
  · rintro ⟨hx, hy, hmid⟩
    have hsub : uIcc x y ⊆ S := by
      intro z hz
      by_cases hzx : z = x
      · simpa only [hzx] using hx
      by_cases hzy : z = y
      · simpa only [hzy] using hy
      rcases mem_uIcc.mp hz with hz | hz
      · exact hmid z (.inl ⟨lt_of_le_of_ne hz.1 (Ne.symm hzx), lt_of_le_of_ne hz.2 hzy⟩)
      · exact hmid z (.inr ⟨lt_of_le_of_ne hz.1 (Ne.symm hzy), lt_of_le_of_ne hz.2 hzx⟩)
    exact (((convex_uIcc x y).isPathConnected ⟨x, left_mem_uIcc⟩).joinedIn
      x left_mem_uIcc y right_mem_uIcc).mono hsub

theorem joinedIn_tuple_iff (p : Formula) (x y : Fin 1 → ℝ) :
    JoinedIn (Description.mk 1 p).realization x y ↔ JoinedIn (realSet p) (x 0) (y 0) := by
  let e := Homeomorph.piUnique (fun _ : Fin 1 => ℝ)
  have he : e '' (Description.mk 1 p).realization = realSet p := by
    rw [e.image_eq_preimage_symm]
    rfl
  constructor
  · intro h
    have hj := h.map e.continuous.continuousOn
    rwa [he] at hj
  · intro h
    have hx : x ∈ (Description.mk 1 p).realization := (realSet_tuple p x).mp h.source_mem
    have hy : y ∈ (Description.mk 1 p).realization := (realSet_tuple p y).mp h.target_mem
    apply (e.isInducing.joinedIn_image hx hy).mp
    rwa [he]

def betweenQuery : Formula := .or (.and (less 0 2) (less 2 1)) (.and (less 1 2) (less 2 0))

def separationQuery (p s t : Formula) : Formula :=
  .and (s.rename (Interleave.index false))
    (.and (t.rename (Interleave.index true))
      (.and (.not ((p.rename (Interleave.index true)).rename (Interleave.index false))) betweenQuery))

theorem separation_holds (p s t : Formula) (hp : p.arity ≤ 1) (hs : s.arity ≤ 1) (ht : t.arity ≤ 1)
    (env : ℕ → ℝ) : (separationQuery p s t).Holds env ↔
      env 0 ∈ realSet s ∧ env 1 ∈ realSet t ∧ env 2 ∉ realSet p ∧
        ((env 0 < env 2 ∧ env 2 < env 1) ∨ (env 1 < env 2 ∧ env 2 < env 0)) := by
  have h2 : ((p.rename (Interleave.index true)).rename (Interleave.index false)).Holds env ↔
      env 2 ∈ realSet p := by
    rw [Formula.holds_rename]
    simpa only [Function.comp_apply, Interleave.index, Bool.toNat_false, Bool.toNat_true,
      Nat.mul_zero, Nat.zero_add, Nat.mul_one, realSet, mem_ofPred_eq] using
        holds_rename_one p hp (Interleave.index true) (env ∘ Interleave.index false)
  simp only [separationQuery, Formula.Holds, holds_rename_one s hs, holds_rename_one t ht,
    h2, betweenQuery, less_holds, Interleave.index, Bool.toNat_false, Bool.toNat_true,
    Nat.mul_zero, Nat.zero_add, realSet, mem_ofPred_eq]

theorem separation_satisfiable (p s t : Formula) (hp : p.arity ≤ 1)
    {x y : Fin 1 → ℝ} (hs : Denotes 1 s x) (ht : Denotes 1 t y) :
    (separationQuery p s t).Satisfiable ↔ ∃ z : ℝ, z ∉ realSet p ∧
      ((x 0 < z ∧ z < y 0) ∨ (y 0 < z ∧ z < x 0)) := by
  constructor
  · rintro ⟨env, h⟩
    obtain ⟨ha, hb, hz, hbetween⟩ := (separation_holds p s t hp hs.1 ht.1 env).mp h
    have hax : (fun _ : Fin 1 => env 0) = x := (hs.2 _).mp ha
    have hby : (fun _ : Fin 1 => env 1) = y := (ht.2 _).mp hb
    refine ⟨env 2, hz, ?_⟩
    simpa only [← congrFun hax 0, ← congrFun hby 0] using hbetween
  · rintro ⟨z, hz, hbetween⟩
    let env : ℕ → ℝ := fun k => if k = 0 then x 0 else if k = 1 then y 0 else z
    refine ⟨env, (separation_holds p s t hp hs.1 ht.1 env).mpr ?_⟩
    have hx : x 0 ∈ realSet s := (realSet_tuple s x).mpr ((hs.2 x).mpr rfl)
    have hy : y 0 ∈ realSet t := (realSet_tuple t y).mpr ((ht.2 y).mpr rfl)
    simpa only [env, ite_true, Nat.reduceEqDiff, ite_false] using
      And.intro hx (And.intro hy (And.intro hz hbetween))

theorem memberQuery_iff (p s : Formula) (hp : p.arity ≤ 1) {x : Fin 1 → ℝ} (hs : Denotes 1 s x) :
    (Formula.and p s).Satisfiable ↔ x ∈ (Description.mk 1 p).realization := by
  constructor
  · rintro ⟨env, hpEnv, hsEnv⟩
    have he : (fun _ : Fin 1 => env 0) = x := (hs.2 _).mp ((holds_env_one s hs.1 env).mp hsEnv)
    have hx := (holds_env_one p hp env).mp hpEnv
    change p.Holds (Formula.extend x)
    rwa [realSet, mem_ofPred_eq, he] at hx
  · intro hx
    exact ⟨Formula.extend x, hx, (hs.2 x).mpr rfl⟩

theorem point_iff (p s t : Formula) :
    (PointQuery.mk ⟨1, p⟩ s t).Reachable ↔
      p.arity ≤ 1 ∧ (∃ x : Fin 1 → ℝ, Denotes 1 s x) ∧
        (∃ y : Fin 1 → ℝ, Denotes 1 t y) ∧
        (Formula.and p s).Satisfiable ∧ (Formula.and p t).Satisfiable ∧
          ¬ (separationQuery p s t).Satisfiable := by
  constructor
  · rintro ⟨hw, x, y, hs, ht, hj⟩
    refine ⟨hw, ⟨x, hs⟩, ⟨y, ht⟩, (memberQuery_iff p s hw hs).mpr hj.source_mem,
      (memberQuery_iff p t hw ht).mpr hj.target_mem, ?_⟩
    intro hsep
    obtain ⟨z, hz, hbetween⟩ := (separation_satisfiable p s t hw hs ht).mp hsep
    exact hz (((joinedIn_real_iff _ _).mp ((joinedIn_tuple_iff p x y).mp hj)).2.2 z hbetween)
  · rintro ⟨hw, ⟨x, hs⟩, ⟨y, ht⟩, hxs, hyt, hsep⟩
    refine ⟨hw, x, y, hs, ht, (joinedIn_tuple_iff p x y).mpr ((joinedIn_real_iff _ _).mpr
      ⟨(realSet_tuple p x).mpr ((memberQuery_iff p s hw hs).mp hxs),
        (realSet_tuple p y).mpr ((memberQuery_iff p t hw ht).mp hyt), ?_⟩)⟩
    intro z hz
    by_contra hbad
    exact hsep ((separation_satisfiable p s t hw hs ht).mpr ⟨z, hbad, hz⟩)

def separationBits (packet : List Bool) : List Bool :=
  Codec.taggedTwo 4 (Interleave.renameBits false (LeanCanny.pairFst (LeanCanny.pairSnd packet)))
    (Codec.taggedTwo 4 (Interleave.renameBits true (LeanCanny.pairSnd (LeanCanny.pairSnd packet)))
      (Codec.taggedTwo 4
        (Codec.taggedOne 3 (Interleave.renameBits false (Interleave.renameBits true (LeanCanny.pairFst packet))))
          betweenQuery.encode))

theorem separationBits_mem_FP : separationBits ∈ FP := by
  have hs := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (Interleave.renameBits_mem_FP false)
  have ht := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (Interleave.renameBits_mem_FP true)
  have hp := mem_FP_comp (mem_FP_comp pairFst_mem_FP (Interleave.renameBits_mem_FP true))
    (Interleave.renameBits_mem_FP false)
  exact Codec.taggedTwo_mem_FP 4 hs (Codec.taggedTwo_mem_FP 4 ht
    (Codec.taggedTwo_mem_FP 4 (Codec.taggedOne_mem_FP 3 hp) (constFn_mem_FP _)))

theorem separationBits_pair (p s t : Formula) :
    separationBits (LeanCanny.pair p.encode (LeanCanny.pair s.encode t.encode)) =
      (separationQuery p s t).encode := by
  simp only [separationBits, pairFst_pair, pairSnd_pair]
  rw [Interleave.renameBits_encode, Interleave.renameBits_encode, Interleave.renameBits_encode,
    Interleave.renameBits_encode]
  simp only [separationQuery, Formula.encode, Formula.toData,
    Codec.taggedTwo_toBits, Codec.taggedOne_toBits]

theorem separationQuery_computable {α : Type} {enc : α ↪ List Bool} {p s t : α → Formula}
    (hp : ComputableTidilyInPolyTime (fun a => (p a).encode) enc encBits)
    (hs : ComputableTidilyInPolyTime (fun a => (s a).encode) enc encBits)
    (ht : ComputableTidilyInPolyTime (fun a => (t a).encode) enc encBits) :
    ComputableTidilyInPolyTime (fun a => (separationQuery (p a) (s a) (t a)).encode) enc encBits := by
  have hargs := pair_computable hp (pair_computable hs ht)
  apply (separationBits_mem_FP.comp hargs).of_enc_eq
  intro a
  exact (separationBits_pair (p a) (s a) (t a)).symm

theorem andQuery_computable {α : Type} {enc : α ↪ List Bool} {p s : α → Formula}
    (hp : ComputableTidilyInPolyTime (fun a => (p a).encode) enc encBits)
    (hs : ComputableTidilyInPolyTime (fun a => (s a).encode) enc encBits) :
    ComputableTidilyInPolyTime (fun a => (Formula.and (p a) (s a)).encode) enc encBits := by
  apply ((Codec.taggedTwo_mem_FP 4 pairFst_mem_FP pairSnd_mem_FP).comp
    (pair_computable hp hs)).of_enc_eq
  intro a
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, Formula.encode, Formula.toData,
    Codec.taggedTwo_toBits]

/-- Native point connectivity for arbitrary Boolean formulas in one coordinate,
including irrational singleton endpoints and malformed endpoint descriptions. -/
theorem point_computable {α : Type} [Inhabited α] {enc : α ↪ List Bool}
    {p s t : α → Formula}
    (hp : ComputableTidilyInPolyTime (fun a => (p a).encode) enc encBits)
    (hs : ComputableTidilyInPolyTime (fun a => (s a).encode) enc encBits)
    (ht : ComputableTidilyInPolyTime (fun a => (t a).encode) enc encBits) :
    ComputableTidilyInPolySpace
      (fun a => decide (PointQuery.mk ⟨1, p a⟩ (s a) (t a)).Reachable) enc encBool := by
  have hone : ComputableTidilyInPolyTime (fun _ : α => 1) enc encUnary := .const 1
  have hsource := EndpointValidation.exists_denotes_computable hs hone
  have htarget := EndpointValidation.exists_denotes_computable ht hone
  have hsourceMem := satisfiable_computable (andQuery_computable hp hs)
  have htargetMem := satisfiable_computable (andQuery_computable hp ht)
  have hsep := satisfiable_computable (separationQuery_computable hp hs ht)
  have hf : ComputableTidilyInPolySpace (fun _ : α => false) enc encBool := .of_polyTime (.const false)
  have htrue : ComputableTidilyInPolySpace (fun _ : α => true) enc encBool := .of_polyTime (.const true)
  have harity := ComputableTidilyInPolyTime.comp FormulaArity.value_unary hp
  have hwell := ComputableTidilyInPolySpace.of_polyTime
    (ComputableTidilyInPolyTime.unary_le' harity hone)
  apply (hwell.ite (hsource.ite (htarget.ite (hsourceMem.ite
    (htargetMem.ite (hsep.ite hf htrue) hf) hf) hf) hf) hf).congr
  intro a
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq, FormulaArity.value_encode, point_iff]
  by_cases hw : (p a).arity ≤ 1 <;>
    by_cases hs : ∃ x : Fin 1 → ℝ, Denotes 1 (s a) x <;>
      by_cases ht : ∃ y : Fin 1 → ℝ, Denotes 1 (t a) y <;>
        by_cases hsm : (Formula.and (p a) (s a)).Satisfiable <;>
          by_cases htm : (Formula.and (p a) (t a)).Satisfiable <;>
            by_cases hsep : (separationQuery (p a) (s a) (t a)).Satisfiable <;>
              simp [hw, hs, ht, hsm, htm, hsep]

end LeanCanny.Connectivity.OneDimension
