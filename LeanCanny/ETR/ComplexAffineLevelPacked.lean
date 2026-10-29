/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexAffineLevelEncoding
public import LeanCanny.ETR.ComplexAffineLevelSymbolic

/-! # A fixed output wire for each ancestral level

The selected level is copied to one final wire, independent of its tag. Later
affine stages can reference it using only dimension and the slot offset.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.AffineLevel
open LeanCanny.Encoding.Brackets MvPolynomial
open scoped Classical

def packedOutput (C : Inputs) : ℕ := C.base + (program C).length

def packedProgram (C : Inputs) : List Operation := program C ++ [.add (output C) C.base]
def packedGates (C : Inputs) : List Gate := StraightLine.gates C.base (packedProgram C)

theorem packed_length (C : Inputs) : (packedProgram C).length = 9 * C.count + 10 := by
  simp only [packedProgram, List.length_append, List.length_cons, List.length_nil, program_length]

theorem packed_output_eq (C : Inputs) : packedOutput C = C.base + 9 * C.count + 9 := by
  rw [packedOutput, program_length]
  omega

theorem packed_wellFormed (C : Inputs) (h : C.Valid) : StraightLine.WellFormed C.base (packedProgram C) := by
  rw [packedProgram, StraightLine.wellFormed_append]
  refine ⟨wellFormed C h, ?_⟩
  exact ⟨⟨output_lt C, by rw [program_length]; omega⟩, trivial⟩

theorem packed_gates_eq (C : Inputs) : packedGates C = gates C ++ [.add (packedOutput C) (output C) C.base] := by
  rw [packedGates, packedProgram, StraightLine.gates_append]
  rfl

theorem packed_output_sound (C : Inputs) (env : ℕ → ℂ) (hg : ∀ g ∈ packedGates C, g.Holds env) :
    env (packedOutput C) = value C env := by
  have hold : ∀ g ∈ gates C, g.Holds env := fun g h => hg g (by rw [packed_gates_eq]; exact List.mem_append_left _ h)
  have hz : env C.base = 0 := by
    simpa only [Gate.Holds, Int.cast_zero] using hold (.constant C.base 0) (by rw [gates_eq]; simp)
  have H := hg (.add (packedOutput C) (output C) C.base) (by rw [packed_gates_eq]; simp)
  change env (packedOutput C) = env (output C) + env C.base at H
  rw [output_sound C env hold, hz, add_zero] at H
  exact H

theorem packed_output_lt (C : Inputs) : packedOutput C < C.base + (packedProgram C).length := by
  rw [packed_output_eq, packed_length]
  omega

theorem packed_exists_completion (C : Inputs) (h : C.Valid) (x : ℕ → ℂ) :
    ∃ env : ℕ → ℂ, (∀ i < C.base, env i = x i) ∧ (∀ g ∈ packedGates C, g.Holds env) ∧ env (packedOutput C) = value C x := by
  obtain ⟨env, hp, hg⟩ := StraightLine.exists_completion x C.base (packedProgram C) (packed_wellFormed C h)
  exact ⟨env, hp, hg, (packed_output_sound C env hg).trans (value_congr C h env x hp)⟩

theorem packed_symbolic (D : Inputs) (h : D.Valid) (wire : ℕ → MvPolynomial ℕ ℤ) :
    Differential.symbolicRun wire D.base (packedProgram D) (packedOutput D) = polynomial D wire := by
  apply Differential.eq_of_eval_complex
  intro x
  let W := Differential.symbolicRun wire D.base (packedProgram D)
  let env : ℕ → ℂ := fun i => (W i).eval₂ (Int.castRingHom ℂ) x
  have hR : Differential.Realizes W D.base (packedProgram D) :=
    Differential.symbolicRun_realizes wire D.base (packedProgram D) (packed_wellFormed D h)
  have hg : ∀ g ∈ packedGates D, g.Holds env := Differential.realizes_gates_eval W D.base (packedProgram D) hR x
  have hp (i : ℕ) (hi : i < D.base) : env i = (wire i).eval₂ (Int.castRingHom ℂ) x := by
    dsimp only [env, W]
    rw [Differential.symbolicRun_preserves_before wire D.base (packedProgram D) i hi]
  exact (packed_output_sound D env hg).trans ((value_congr D h env _ hp).trans (polynomial_eval D wire x).symm)

theorem packed_encode_FP {F : List Bool → Inputs} (h : Inputs.PolyTime F) :
    (fun c => encode (packedGates (F c))) ∈ FP := by
  have hout := h.base.add (length_unary h)
  have hc := arithmeticGateBits_mem_FP 1 hout (output_unary h) h.base
  have H := mem_FP_comp (appendFn_mem_FP (mem_FP_comp (program_encode_FP h) contents_mem_FP) hc) wrap_mem_FP
  apply mem_FP_of_eq H
  intro c
  simp only [Function.comp_apply, contents_encode, addGateBits_encode]
  rw [encode_eq_wrap, packed_gates_eq, forest_append]
  simp only [forest_cons, forest_nil, List.append_nil]
  rfl

theorem packed_output_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) : UnaryFn (fun c => packedOutput (F c)) :=
  h.base.add (length_unary h)

end LeanCanny.ETR.ComplexCircuit.AffineLevel
