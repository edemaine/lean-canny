/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.UnaryModularIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # Collecting polynomially many modular oracle values at one fixed level -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM
open scoped Classical

@[expose] noncomputable def unaryModularList (n p : ℕ) (f : ℕ → ℕ) : List ℕ :=
  (List.range n).map (fun i => f i % p)

/-- All stateful handlers obey the storage bound, because each returned
oracle value is reduced before it is appended to the output list. -/
theorem unaryModularList_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    {count modulus : α → ℕ} {f : α × ℕ → ℕ}
    (hcount : ComputableInPolyTime count enc encUnary)
    (hmod : ComputableInPolyTime modulus enc encNat) (hpos : ∀ w, 0 < modulus w)
    (hf : f ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => unaryModularList (count w) (modulus w) (fun i => f (w, i))) ∈
      CountingFunction a enc (encList encNat) := by
  let stateEncoding := encPair encNat (encList encNat)
  let callEncoding := encPair enc stateEncoding
  have hf' : (fun q : α × (ℕ × List ℕ) => f (q.1, q.2.1)) ∈
      CountingFunction a callEncoding encNat := CountingFunction.preprocess hf (by fun_prop)
  obtain ⟨A, hA, program, hprogram, heq⟩ := hf'
  let body (w : α) (s : ℕ × List ℕ) : WordQueryComp Unit (ℕ × List ℕ) :=
    (fun v => (s.1 + 1, s.2 ++ [v % modulus w])) <$> program (w, s)
  have hi : ComputableInPolyTime
      (fun q : (α × (ℕ × List ℕ)) × ℕ => q.1.2.1 + 1)
      (encPair callEncoding encNat) encNat := by fun_prop
  have hv : ComputableInPolyTime
      (fun q : (α × (ℕ × List ℕ)) × ℕ => q.2 % modulus q.1.1)
      (encPair callEncoding encNat) encNat :=
    ComputableInPolyTime.binary_mod.comp ((ComputableInPolyTime.snd _ _).prod
      (hmod.comp (by fun_prop)))
  have ht : ComputableInPolyTime
      (fun q : (α × (ℕ × List ℕ)) × ℕ => q.1.2.2)
      (encPair callEncoding encNat) (encList encNat) := by fun_prop
  have hpost := hi.prod (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listAppend' ht.tidy
      (ComputableTidilyInPolyTime.cons' hv.tidy (ComputableTidilyInPolyTime.const []))))
  have hstep : IsOraclePPTOn callEncoding stateEncoding (fun q : α × (ℕ × List ℕ) =>
      OracleComp.interpret ProbOracleComp.query (body q.1 q.2)) := by
    simp only [body, OracleComp.interpret_map]
    exact hprogram.map_with' hpost
  have hcanonical := (ComputableInPolyTime.unary_to_binary.comp hcount).prod
    (ComputableInPolyTime.replicate hcount hmod)
  have hpreserve (w : α) (i : ℕ) (s : ℕ × List ℕ) (_hi : i < count w)
      (hinv : s.1 = i ∧ s.2.length = i ∧ ∀ v ∈ s.2, v < modulus w)
      (next : ℕ × List ℕ)
      (hnext : next ∈ OracleComp.support (OracleComp.interpret ProbOracleComp.query (body w s))) :
      next.1 = i + 1 ∧ next.2.length = i + 1 ∧ ∀ v ∈ next.2, v < modulus w := by
    simp only [body, OracleComp.interpret_map] at hnext
    obtain ⟨v, _hv, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    refine ⟨by simp only; omega, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hinv.2.2 x hx
    · have he : x = v % modulus w := List.mem_singleton.mp hx
      exact he ▸ Nat.mod_lt _ (hpos w)
  have hbound (w : α) (i : ℕ) (s : ℕ × List ℕ) (hi : i ≤ count w)
      (hinv : s.1 = i ∧ s.2.length = i ∧ ∀ v ∈ s.2, v < modulus w) :
      (stateEncoding s).length ≤
        (stateEncoding (count w, List.replicate (count w) (modulus w))).length := by
    have hx : s.1.size ≤ (count w).size := Nat.size_le_size (by omega)
    have hl := length_encList_le encNat s.2 (b := (encNat (modulus w)).length)
      (fun v hv => by
        simpa only [encNat_apply, Nat.size_eq_bits_len] using
          Nat.size_le_size (hinv.2.2 v hv).le)
    have hr : (encList encNat (List.replicate (count w) (modulus w))).length =
        count w * (2 * (encNat (modulus w)).length + 1) := by
      simp only [length_encList, List.map_replicate, List.sum_replicate, smul_eq_mul]
    simp only [stateEncoding, length_encPair, hr, encNat_apply, Nat.size_eq_bits_len] at hl ⊢
    rw [hinv.2.1] at hl
    nlinarith
  have hloop := (IsOraclePPTOn.iterateWith_spec'
    (step := fun w s => OracleComp.interpret ProbOracleComp.query (body w s))
    hcount (ComputableInPolyTime.const ((0 : ℕ), ([] : List ℕ))) hstep
    (fun w i s => s.1 = i ∧ s.2.length = i ∧ ∀ v ∈ s.2, v < modulus w)
    (fun _ => ⟨rfl, rfl, by simp⟩) hpreserve hcanonical.polyBounded_length hbound).1
  refine ⟨A, hA, (fun w => Prod.snd <$> OracleComp.iterate (count w) (body w) (0, [])), ?_, ?_⟩
  · simp only [OracleComp.interpret_map, OracleComp.interpret_iterate]
    exact hloop.map' (ComputableInPolyTime.snd encNat (encList encNat))
  · intro w
    rw [OracleComp.interpret_map]
    change (OracleComp.interpret (m := Id) (languageOracle A)
      (OracleComp.iterate (count w) (body w) (0, []))).2 = _
    rw [OracleComp.interpret_id_iterate]
    simp only [body, OracleComp.interpret_map, heq]
    change ((fun s : ℕ × List ℕ => (s.1 + 1, s.2 ++ [f (w, s.1) % modulus w]))^[count w] (0, [])).2 = _
    have hiter (k : ℕ) :
        ((fun s : ℕ × List ℕ => (s.1 + 1, s.2 ++ [f (w, s.1) % modulus w]))^[k] (0, [])) =
          (k, (List.range k).map (fun i => f (w, i) % modulus w)) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply', ih]
        simp only [List.range_succ, List.map_append, List.map_singleton]
    exact congrArg Prod.snd (hiter (count w))

end LeanCanny.CountingHierarchy
