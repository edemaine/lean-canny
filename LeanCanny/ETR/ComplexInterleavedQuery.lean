/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexRealWitnesses
public import LeanCanny.ETR.ComplexCircuitReindex
public import LeanCanny.ETR.ComplexCircuitBuilders
public import LeanCanny.ETR.ComplexPowerSize

/-! # Disjoint formula witnesses and shared circuit wires

Formula variables use even wires and the entire circuit uses odd wires.
Addition gates identify only the designated spatial inputs. Thus arbitrary
formula witnesses remain disjoint from every circuit auxiliary, using the
existing native parity reindexers instead of a new formula substitution pass.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.RealQuery.Interleaved
open LeanCanny.Computation LeanCanny.Encoding LeanCanny.Encoding.Brackets
open scoped Classical

def even (i : ℕ) : ℕ := 2 * i
def odd (i : ℕ) : ℕ := 2 * i + 1
def links (inputs fresh : ℕ) : List Gate :=
  (List.range inputs).map (fun i => .add (odd i) (even i) (odd fresh))
def gates (inputs fresh : ℕ) (prior : List Gate) : List Gate :=
  prior.map (Gate.reindex odd) ++ [.constant (odd fresh) 0] ++ links inputs fresh

def InputSatisfiable (inputs start : ℕ) (prior : List Gate) (p : Formula) : Prop :=
  ∃ x : ℕ → ℝ, ∃ env : ℕ → ℂ, (∀ g ∈ prior, g.Holds env) ∧
    (∀ i < start, (env i).im = 0) ∧ (∀ i < inputs, env i = (x i : ℂ)) ∧ p.Holds x

private def merge (fresh : ℕ) (x : ℕ → ℝ) (env : ℕ → ℂ) (i : ℕ) : ℂ :=
  if i % 2 = 0 then (x (i / 2) : ℂ) else if i / 2 = fresh then 0 else env (i / 2)

private theorem merge_even (fresh : ℕ) (x : ℕ → ℝ) (env : ℕ → ℂ) (i : ℕ) :
    merge fresh x env (even i) = (x i : ℂ) := by simp [merge, even, Nat.mul_comm]
private theorem merge_odd (fresh : ℕ) (x : ℕ → ℝ) (env : ℕ → ℂ) (i : ℕ) :
    merge fresh x env (odd i) = if i = fresh then 0 else env i := by
  have hm : (2 * i + 1) % 2 = 1 := by omega
  have hd : (2 * i + 1) / 2 = i := by omega
  simp only [merge, odd, hm, one_ne_zero, ite_false, hd]

theorem correct (inputs start fresh : ℕ) (prior : List Gate) (p : Formula)
    (hn : inputs ≤ start) (hs : start ≤ fresh) (hg : ∀ g ∈ prior, g.arity ≤ fresh) :
    WithConstraints (2 * start) (gates inputs fresh prior) (p.rename even) ↔
      InputSatisfiable inputs start prior p := by
  constructor
  · rintro ⟨env, hall, hr, hp⟩
    have hzero : env (odd fresh) = 0 := by
      simpa only [Gate.Holds, Int.cast_zero] using hall (.constant (odd fresh) 0) (by simp [gates])
    refine ⟨fun i => (env (even i)).re, fun i => env (odd i), ?_, ?_, ?_, ?_⟩
    · intro g hg
      exact (Gate.reindex_holds odd g env).mp (hall _ (by
        simp only [gates, List.mem_append]
        exact Or.inl (Or.inl (List.mem_map.mpr ⟨g, hg, rfl⟩))))
    · intro i hi
      exact hr (odd i) (by unfold odd; omega)
    · intro i hi
      have he : env (odd i) = env (even i) + env (odd fresh) :=
        hall (.add (odd i) (even i) (odd fresh)) (by
          simp only [gates, List.mem_append]
          exact Or.inr (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
      rw [hzero, add_zero] at he
      change env (odd i) = Complex.ofReal ((env (even i)).re)
      apply Complex.ext
      · simpa only [Complex.ofReal_re] using congrArg Complex.re he
      · simpa only [Complex.ofReal_im] using hr (odd i) (by unfold odd; omega)
    · exact (Formula.holds_rename _ _ p).mp hp
  · rintro ⟨x, env, hprior, hr, hinput, hp⟩
    let env' : ℕ → ℂ := merge fresh x env
    have hodd : ∀ i < fresh, env' (odd i) = env i := by
      intro i hi
      exact (merge_odd fresh x env i).trans (ite_eq_right (by omega))
    have heven : ∀ i, env' (even i) = (x i : ℂ) := merge_even fresh x env
    have hzero : env' (odd fresh) = 0 := by simp only [env', merge_odd, ite_true]
    refine ⟨env', ?_, ?_, ?_⟩
    · intro g hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · rcases List.mem_append.mp hmem with hmem | hmem
        · obtain ⟨base, hbase, rfl⟩ := List.mem_map.mp hmem
          apply (Gate.reindex_holds odd base env').mpr
          exact (base.holds_congr env (fun i => env' (odd i))
            (fun i hi => (hodd i (hi.trans_le (hg base hbase))).symm)).mp (hprior base hbase)
        · obtain rfl := List.mem_singleton.mp hmem
          simpa only [Gate.Holds, Int.cast_zero] using hzero
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmem
        change env' (odd i) = env' (even i) + env' (odd fresh)
        rw [hodd i ((List.mem_range.mp hi).trans_le (hn.trans hs)), heven, hzero, add_zero]
        exact hinput i (List.mem_range.mp hi)
    · intro i hi
      by_cases hm : i % 2 = 0
      · simp only [env', merge, hm, ite_true, Complex.ofReal_im]
      · have hd : i / 2 < start := by omega
        have hf : i / 2 ≠ fresh := by omega
        simpa only [env', merge, hm, ite_false, hf] using hr (i / 2) hd
    · apply (Formula.holds_rename _ _ p).mpr
      simpa only [Function.comp_def, heven, Complex.ofReal_re] using hp

theorem encode_mem_FP {inputs fresh : List Bool → ℕ} {prior : List Bool → List Gate}
    (hn : UnaryFn inputs) (hf : UnaryFn fresh) (hp : (fun c => encode (prior c)) ∈ FP) :
    (fun c => encode (gates (inputs c) (fresh c) (prior c))) ∈ FP := by
  have hi := UnaryFn.length pairSnd_mem_FP
  have ho := ((UnaryFn.const 2).mul hi).add (UnaryFn.const 1)
  have hmap := Reindex.encode_mem_FP (index := fun _ i => odd i) ho (constFn_mem_FP []) hp
  have hz := constantGateBits_mem_FP (((UnaryFn.const 2).mul hf).add (UnaryFn.const 1))
    (constFn_mem_FP (Term.const 0).toData.toBits)
  have hlinks := flatMap_range_mem_FP (arithmeticGateBits_mem_FP 1 ho ((UnaryFn.const 2).mul hi)
    (((UnaryFn.const 2).mul (hf.comp pairFst_mem_FP)).add (UnaryFn.const 1))) hn.mem_FP
  have h := mem_FP_comp (appendFn_mem_FP
    (appendFn_mem_FP (mem_FP_comp hmap contents_mem_FP) hz) hlinks) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, contents_encode, constantGateBits_encode,
    List.length_replicate, pairFst_pair, pairSnd_pair, addGateBits_encode]
  simp only [gates, encode_eq_wrap, forest_append, forest_cons, forest_nil, List.append_nil]
  simp only [links, forest, List.map_map, List.flatten_eq_flatMap, List.flatMap_map,
    Function.comp_def, id_eq, even, odd]
  rfl

theorem evaluator {inputs start fresh : List Bool → ℕ} {prior : List Bool → List Gate} {p : List Bool → Formula}
    (hn : UnaryFn inputs) (hs : UnaryFn start) (hf : UnaryFn fresh)
    (hprior : (fun c => encode (prior c)) ∈ FP) (hp : (fun c => (p c).encode) ∈ FP)
    (hns : ∀ c, inputs c ≤ start c) (hsf : ∀ c, start c ≤ fresh c)
    (ha : ∀ c g, g ∈ prior c → g.arity ≤ fresh c) :
    SpaceFunction (fun c => [decide (InputSatisfiable (inputs c) (start c) (prior c) (p c))]) := by
  have hp' : (fun c => ((p c).rename even).encode) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hp (Interleave.renameBits_mem_FP false)) (fun c => by
      rw [Function.comp_apply, Interleave.renameBits_encode]; rfl)
  apply (constraint_evaluator ((UnaryFn.const 2).mul hs) (encode_mem_FP hn hf hprior) hp').congr
  funext c
  rw [correct _ _ _ _ _ (hns c) (hsf c) (ha c)]

end LeanCanny.ETR.ComplexCircuit.RealQuery.Interleaved
