/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexKernelRowEncoding

/-! # Shared affine dot-product rows

These rows subtract a linear combination of existing input wires from an
existing value, or subtract an existing level from that linear combination.
Normal coefficients remain shared wire references.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.AffineRow
open LeanCanny.Encoding.Brackets
open scoped Classical BigOperators

def difference (zWire base inputBase count value : ℕ) (coefficients : ℕ → ℕ) : List Operation :=
  KernelRow.program zWire base inputBase count value (KernelRow.sumWire zWire base count) (-1) (fun _ => zWire) coefficients

def height (zWire base inputBase count level : ℕ) (coefficients : ℕ → ℕ) : List Operation :=
  KernelRow.program zWire base inputBase count (KernelRow.sumWire zWire base count) level (-1) (fun _ => zWire) coefficients

def stride (count : ℕ) : ℕ := 4 * count + 3
abbrev output := KernelRow.criticalWire

theorem output_lt_end (base width count q : ℕ) (hq : q < count) :
    output (base + q * stride width) width < base + count * stride width := by
  have hm := Nat.mul_le_mul_right (stride width) (show q + 1 ≤ count from hq)
  rw [Nat.add_mul, Nat.one_mul] at hm
  unfold output KernelRow.criticalWire stride at *
  omega

theorem difference_length (zWire base inputBase count value : ℕ) (coefficients : ℕ → ℕ) :
    (difference zWire base inputBase count value coefficients).length = stride count := KernelRow.program_length ..

theorem height_length (zWire base inputBase count level : ℕ) (coefficients : ℕ → ℕ) :
    (height zWire base inputBase count level coefficients).length = stride count := KernelRow.program_length ..

private theorem wellFormed_internal (zWire base inputBase count value gradient : ℕ) (coefficients : ℕ → ℕ)
    (hz : zWire < base) (he : ∀ k < count, coefficients k < base) (hu : inputBase + count ≤ base)
    (hv : value < base + (1 + 4 * count)) (hg : gradient < base + (1 + 4 * count)) :
    StraightLine.WellFormed base (KernelRow.program zWire base inputBase count value gradient (-1) (fun _ => zWire) coefficients) := by
  rw [KernelRow.program, StraightLine.wellFormed_append, KernelRow.prefix_length]
  refine ⟨KernelRow.prefix_wellFormed _ _ _ _ _ _ _ hz (fun _ _ => hz) he hu, ?_⟩
  simp only [StraightLine.WellFormed, Operation.InputsBelow]
  exact ⟨⟨by omega, hg⟩, ⟨by omega, by omega⟩, trivial⟩

private theorem sumWire_lt (zWire base count : ℕ) (hz : zWire < base) :
    KernelRow.sumWire zWire base count < base + (1 + 4 * count) := by
  unfold KernelRow.sumWire
  split_ifs <;> omega

theorem difference_wellFormed (zWire base inputBase count value : ℕ) (coefficients : ℕ → ℕ)
    (hz : zWire < base) (he : ∀ k < count, coefficients k < base)
    (hu : inputBase + count ≤ base) (hv : value < base) :
    StraightLine.WellFormed base (difference zWire base inputBase count value coefficients) :=
  wellFormed_internal _ _ _ _ _ _ _ hz he hu (by omega) (sumWire_lt _ _ _ hz)

theorem height_wellFormed (zWire base inputBase count level : ℕ) (coefficients : ℕ → ℕ)
    (hz : zWire < base) (he : ∀ k < count, coefficients k < base)
    (hu : inputBase + count ≤ base) (hl : level < base) :
    StraightLine.WellFormed base (height zWire base inputBase count level coefficients) :=
  wellFormed_internal _ _ _ _ _ _ _ hz he hu (sumWire_lt _ _ _ hz) (by omega)

theorem difference_sound (zWire base inputBase count value : ℕ) (coefficients : ℕ → ℕ) (env : ℕ → ℂ)
    (hz : env zWire = 0)
    (hg : ∀ g ∈ StraightLine.gates base (difference zWire base inputBase count value coefficients), g.Holds env) :
    env (output base count) = env value - ∑ k ∈ Finset.range count, env (coefficients k) * env (inputBase + k) := by
  obtain ⟨hs, hv⟩ := KernelRow.sound zWire base inputBase count value (KernelRow.sumWire zWire base count)
    (-1) (fun _ => zWire) coefficients env hz hg
  simpa [hs, hz, sub_eq_add_neg] using hv

theorem height_sound (zWire base inputBase count level : ℕ) (coefficients : ℕ → ℕ) (env : ℕ → ℂ)
    (hz : env zWire = 0)
    (hg : ∀ g ∈ StraightLine.gates base (height zWire base inputBase count level coefficients), g.Holds env) :
    env (output base count) = (∑ k ∈ Finset.range count, env (coefficients k) * env (inputBase + k)) - env level := by
  obtain ⟨hs, hv⟩ := KernelRow.sound zWire base inputBase count (KernelRow.sumWire zWire base count) level
    (-1) (fun _ => zWire) coefficients env hz hg
  simpa [hs, hz, sub_eq_add_neg] using hv

theorem difference_encode_FP {zWire base inputBase count value : List Bool → ℕ} {coefficients : List Bool → ℕ → ℕ}
    (hz : UnaryFn zWire) (hb : UnaryFn base) (hu : UnaryFn inputBase) (hn : UnaryFn count) (hv : UnaryFn value)
    (he : UnaryFn (fun q => coefficients (pairFst q) (pairSnd q).length)) :
    (fun c => encode (StraightLine.gates (base c) (difference (zWire c) (base c) (inputBase c) (count c) (value c) (coefficients c)))) ∈ FP :=
  KernelRow.encode_mem_FP (first := fun c _ => zWire c) (entry := coefficients) hz hb hu hn hv
    (KernelRow.sumWire_unary hz hb hn) (constFn_mem_FP (Term.const (-1)).toData.toBits) (hz.comp pairFst_mem_FP) he

theorem height_encode_FP {zWire base inputBase count level : List Bool → ℕ} {coefficients : List Bool → ℕ → ℕ}
    (hz : UnaryFn zWire) (hb : UnaryFn base) (hu : UnaryFn inputBase) (hn : UnaryFn count) (hl : UnaryFn level)
    (he : UnaryFn (fun q => coefficients (pairFst q) (pairSnd q).length)) :
    (fun c => encode (StraightLine.gates (base c) (height (zWire c) (base c) (inputBase c) (count c) (level c) (coefficients c)))) ∈ FP :=
  KernelRow.encode_mem_FP (first := fun c _ => zWire c) (entry := coefficients) hz hb hu hn
    (KernelRow.sumWire_unary hz hb hn) hl (constFn_mem_FP (Term.const (-1)).toData.toBits) (hz.comp pairFst_mem_FP) he

end LeanCanny.ETR.ComplexCircuit.AffineRow
