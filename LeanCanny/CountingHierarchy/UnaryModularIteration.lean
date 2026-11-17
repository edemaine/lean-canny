/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Arithmetic
public import CslibFrontier.Computability.Probabilistic.Oracle.Composition
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! # Unary bounded modular loops preserve one fixed counting oracle

The accumulator is reduced after every step. The supported-state invariant
therefore bounds storage under every stateful handler, independently of the
values returned by the step's oracle program.
-/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM
open scoped Classical

@[expose] noncomputable def unaryModularIteration {α : Type} (count modulus : α → ℕ)
    (f : α × (ℕ × ℕ) → ℕ) (w : α) : ℕ :=
  ((fun s : ℕ × ℕ => (s.1 + 1, f (w, s) % modulus w))^[count w] (0, 0)).2

/-- Polynomially many adaptive modular steps use one fixed oracle at the
 original level. The bound counts iterations in unary and moduli in binary. -/
theorem unaryModularIteration_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (count modulus : α → ℕ) (f : α × (ℕ × ℕ) → ℕ)
    (hcount : ComputableInPolyTime count enc encUnary)
    (hmod : ComputableInPolyTime modulus enc encNat) (hpos : ∀ w, 0 < modulus w)
    (hf : f ∈ CountingFunction a (encPair enc (encPair encNat encNat)) encNat) :
    unaryModularIteration count modulus f ∈ CountingFunction a enc encNat := by
  obtain ⟨A, hA, program, hprogram, heq⟩ := hf
  let stateEncoding := encPair encNat encNat
  let callEncoding := encPair enc stateEncoding
  let body (w : α) (s : ℕ × ℕ) : WordQueryComp Unit (ℕ × ℕ) :=
    (fun v => (s.1 + 1, v % modulus w)) <$> program (w, s)
  have hpost : ComputableInPolyTime
      (fun q : (α × (ℕ × ℕ)) × ℕ => (q.1.2.1 + 1, q.2 % modulus q.1.1))
      (encPair callEncoding encNat) stateEncoding := by
    have hi : ComputableInPolyTime (fun q : (α × (ℕ × ℕ)) × ℕ => q.1.2.1)
        (encPair callEncoding encNat) encNat := by fun_prop
    have hm : ComputableInPolyTime (fun q : (α × (ℕ × ℕ)) × ℕ => modulus q.1.1)
        (encPair callEncoding encNat) encNat := hmod.comp (by fun_prop)
    exact (ComputableInPolyTime.binary_add' hi (.const 1)).prod
      (ComputableInPolyTime.binary_mod.comp ((ComputableInPolyTime.snd _ _).prod hm))
  have hstep : IsOraclePPTOn callEncoding stateEncoding (fun q : α × (ℕ × ℕ) =>
      OracleComp.interpret ProbOracleComp.query (body q.1 q.2)) := by
    simp only [body, OracleComp.interpret_map]
    exact hprogram.map_with' hpost
  have hcanonical : ComputableInPolyTime (fun w => (count w, modulus w)) enc stateEncoding :=
    (ComputableInPolyTime.unary_to_binary.comp hcount).prod hmod
  have hpreserve (w : α) (i : ℕ) (s : ℕ × ℕ) (_hi : i < count w)
      (hinv : s.1 = i ∧ s.2 < modulus w) (next : ℕ × ℕ)
      (hnext : next ∈ OracleComp.support (OracleComp.interpret ProbOracleComp.query (body w s))) :
      next.1 = i + 1 ∧ next.2 < modulus w := by
    simp only [body, OracleComp.interpret_map] at hnext
    obtain ⟨v, _hv, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    exact ⟨by simp only; omega, Nat.mod_lt _ (hpos w)⟩
  have hbound (w : α) (i : ℕ) (s : ℕ × ℕ) (hi : i ≤ count w)
      (hinv : s.1 = i ∧ s.2 < modulus w) :
      (stateEncoding s).length ≤ (stateEncoding (count w, modulus w)).length := by
    have hx : s.1.size ≤ (count w).size := Nat.size_le_size (by omega)
    have hy : s.2.size ≤ (modulus w).size := Nat.size_le_size hinv.2.le
    simp only [stateEncoding, length_encPair, encNat_apply, Nat.size_eq_bits_len]
    omega
  have hloop := (IsOraclePPTOn.iterateWith_spec'
    (step := fun w s => OracleComp.interpret ProbOracleComp.query (body w s))
    hcount (ComputableInPolyTime.const ((0 : ℕ), (0 : ℕ))) hstep
    (fun w i s => s.1 = i ∧ s.2 < modulus w)
    (fun w => ⟨rfl, hpos w⟩) hpreserve hcanonical.polyBounded_length hbound).1
  refine ⟨A, hA, (fun w => Prod.snd <$> OracleComp.iterate (count w) (body w) (0, 0)), ?_, ?_⟩
  · simp only [OracleComp.interpret_map, OracleComp.interpret_iterate]
    exact hloop.map' (ComputableInPolyTime.snd encNat encNat)
  · intro w
    rw [OracleComp.interpret_map]
    change (OracleComp.interpret (m := Id) (languageOracle A)
      (OracleComp.iterate (count w) (body w) (0, 0))).2 = _
    rw [OracleComp.interpret_id_iterate]
    simp only [body, OracleComp.interpret_map, heq, unaryModularIteration]
    rfl

end LeanCanny.CountingHierarchy
