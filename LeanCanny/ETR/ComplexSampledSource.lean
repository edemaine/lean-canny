/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexFrozenEncoding
public import LeanCanny.ETR.ComplexSamplePowerEncoding
public import LeanCanny.ETR.ComplexDyadicCircuit

/-! # The actual regularized sampled Fermat source circuit

A frozen low term, the full sampled pure-power sum, and the dyadic scale form
one acyclic source program. Both exponent words remain binary; the scale is
computed on shared wires and is never written as a giant integer literal.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open MvPolynomial
open scoped Classical BigOperators

theorem Dyadic.realized_output (wire : ℕ → MvPolynomial ℕ ℤ) (source start : ℕ) (bits : List Bool)
    (hr : Differential.Realizes wire start (program source start bits)) :
    wire (output start bits) = C ((2 : ℤ) ^ Nat.fromBitsLE bits) * wire source - 1 := by
  apply Differential.eq_of_eval_complex
  intro x
  have h := sound source start bits (fun i => (wire i).eval₂ (Int.castRingHom ℂ) x)
    (by rw [← gates_eq]; exact Differential.realizes_gates_eval wire start _ hr x)
  simpa only [eval₂_sub, eval₂_mul, eval₂_C, eval₂_one, eval₂_pow, map_pow, Int.coe_castRingHom, Int.cast_ofNat] using h

namespace SampledSource

def powerStart (start : ℕ) (t : Term) : ℕ := start + Source.count t + 1
def joinStart (start m : ℕ) (t : Term) (bits : List Bool) : ℕ :=
  powerStart start t + 1 + (m + 1) * Infinity.stride bits
def dyadicStart (start m : ℕ) (t : Term) (bits : List Bool) : ℕ := joinStart start m t bits + 3

def joinProgram (oldStart start m : ℕ) (a : ℤ) (t : Term) (bits : List Bool) : List Operation :=
  [.constant a,
    .mul (joinStart start m t bits) (SamplePowers.output m start (powerStart start t) bits),
    .add (FrozenSource.output oldStart start t) (joinStart start m t bits + 1)]

def program (oldStart start m : ℕ) (sample a : ℤ) (t : Term) (bits exponent : List Bool) : List Operation :=
  FrozenSource.program oldStart start sample t ++
    (SamplePowers.program m start (powerStart start t) bits ++ (joinProgram oldStart start m a t bits ++
      Dyadic.program (joinStart start m t bits + 2) (dyadicStart start m t bits) exponent))

def output (start m : ℕ) (t : Term) (bits exponent : List Bool) : ℕ := Dyadic.output (dyadicStart start m t bits) exponent

noncomputable def polynomial (m : ℕ) (sample a : ℤ) (t : Term) (bits exponent : List Bool) : MvPolynomial ℕ ℤ :=
  C ((2 : ℤ) ^ Nat.fromBitsLE exponent) *
    (FrozenSource.polynomial sample t + C a *
      ((C sample) ^ (Nat.fromBitsLE bits + 1) + ∑ i ∈ Finset.range m, X i ^ (Nat.fromBitsLE bits + 1))) - 1

theorem polynomial_eval (m : ℕ) (sample a : ℤ) (t : Term) (bits exponent : List Bool) (x : ℕ → ℂ) :
    (polynomial m sample a t bits exponent).eval₂ (Int.castRingHom ℂ) x =
      (2 : ℂ) ^ Nat.fromBitsLE exponent * (t.eval (FrozenSource.inputs sample x) + (a : ℂ) *
        ((sample : ℂ) ^ (Nat.fromBitsLE bits + 1) + ∑ i ∈ Finset.range m, x i ^ (Nat.fromBitsLE bits + 1))) - 1 := by
  simp only [polynomial, eval₂_sub, eval₂_mul, eval₂_add, eval₂_C, eval₂_one, eval₂_pow, eval₂_sum,
    eval₂_X, FrozenSource.polynomial_eval, map_pow, Int.coe_castRingHom, Int.cast_ofNat]

theorem frozen_next (oldStart start : ℕ) (sample : ℤ) (t : Term) :
    start + (FrozenSource.program oldStart start sample t).length = powerStart start t := by
  rw [FrozenSource.program_length]
  unfold powerStart
  omega

theorem power_next (start m : ℕ) (t : Term) (bits : List Bool) :
    powerStart start t + (SamplePowers.program m start (powerStart start t) bits).length = joinStart start m t bits := by
  rw [SamplePowers.program_length]
  unfold joinStart
  omega

theorem join_length (oldStart start m : ℕ) (a : ℤ) (t : Term) (bits : List Bool) :
    (joinProgram oldStart start m a t bits).length = 3 := rfl

theorem gates_eq (oldStart start m : ℕ) (sample a : ℤ) (t : Term) (bits exponent : List Bool) :
    StraightLine.gates start (program oldStart start m sample a t bits exponent) =
      StraightLine.gates start (FrozenSource.program oldStart start sample t) ++
        (StraightLine.gates (powerStart start t) (SamplePowers.program m start (powerStart start t) bits) ++
          ([.constant (joinStart start m t bits) a,
            .mul (joinStart start m t bits + 1) (joinStart start m t bits)
              (SamplePowers.output m start (powerStart start t) bits),
            .add (joinStart start m t bits + 2) (FrozenSource.output oldStart start t) (joinStart start m t bits + 1)] ++
            Dyadic.gates (joinStart start m t bits + 2) (dyadicStart start m t bits) exponent)) := by
  rw [program, StraightLine.gates_append, frozen_next, StraightLine.gates_append,
    power_next, StraightLine.gates_append, join_length]
  simp only [dyadicStart]
  rw [Dyadic.gates_eq]
  rfl

theorem join_wellFormed (oldStart start m : ℕ) (a : ℤ) (t : Term) (bits : List Bool)
    (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start) :
    StraightLine.WellFormed (joinStart start m t bits) (joinProgram oldStart start m a t bits) := by
  have hf := FrozenSource.output_lt oldStart start 0 t ht hs
  rw [frozen_next] at hf
  have hp := SamplePowers.output_lt m start (powerStart start t) bits
  rw [power_next] at hp
  have hnext : powerStart start t ≤ joinStart start m t bits := by unfold joinStart; omega
  simp only [joinProgram, StraightLine.WellFormed, Operation.InputsBelow]
  exact ⟨trivial, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, trivial⟩

theorem wellFormed (oldStart start m : ℕ) (sample a : ℤ) (t : Term) (bits exponent : List Bool)
    (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start) (hm : m ≤ start) :
    StraightLine.WellFormed start (program oldStart start m sample a t bits exponent) := by
  rw [program, StraightLine.wellFormed_append, frozen_next, StraightLine.wellFormed_append,
    power_next, StraightLine.wellFormed_append, join_length]
  exact ⟨FrozenSource.wellFormed oldStart start sample t ht hs,
    SamplePowers.wellFormed m start _ bits (by unfold powerStart; omega) (by unfold powerStart; omega),
    join_wellFormed oldStart start m a t bits ht hs,
    Dyadic.wellFormed _ _ (by omega) exponent⟩

theorem program_length (oldStart start m : ℕ) (sample a : ℤ) (t : Term) (bits exponent : List Bool) :
    (program oldStart start m sample a t bits exponent).length =
      Source.count t + (m + 1) * Infinity.stride bits + 2 * exponent.length + 10 := by
  simp only [program, List.length_append, FrozenSource.program_length, SamplePowers.program_length,
    join_length, Dyadic.program_length]
  omega

theorem output_lt (oldStart start m : ℕ) (sample a : ℤ) (t : Term) (bits exponent : List Bool) :
    output start m t bits exponent < start + (program oldStart start m sample a t bits exponent).length := by
  rw [program_length]
  unfold output Dyadic.output Dyadic.productWire Power.output dyadicStart joinStart powerStart
  omega

theorem realized_output (wire : ℕ → MvPolynomial ℕ ℤ) (oldStart start m : ℕ) (sample a : ℤ)
    (t : Term) (bits exponent : List Bool) (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start) (hm : m ≤ start)
    (hin : ∀ i < start, wire i = X i)
    (hr : Differential.Realizes wire start (program oldStart start m sample a t bits exponent)) :
    wire (output start m t bits exponent) = polynomial m sample a t bits exponent := by
  rw [program, Differential.realizes_append, frozen_next, Differential.realizes_append,
    power_next, Differential.realizes_append, join_length] at hr
  have hlow := FrozenSource.realized_output wire oldStart start sample t ht hs hin hr.1
  have hpower := SamplePowers.realized_output wire m start (powerStart start t) bits hr.2.1
  have hsample : wire start = C sample := hr.1.1
  rw [hsample] at hpower
  have hsum : (∑ i ∈ Finset.range m, wire i ^ (Nat.fromBitsLE bits + 1)) =
      ∑ i ∈ Finset.range m, (X i : MvPolynomial ℕ ℤ) ^ (Nat.fromBitsLE bits + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hin i ((Finset.mem_range.mp hi).trans_le hm)]
  rw [hsum] at hpower
  have hj := hr.2.2.1
  have hc : wire (joinStart start m t bits) = C a := hj.1
  have hp : wire (joinStart start m t bits + 1) =
      wire (joinStart start m t bits) * wire (SamplePowers.output m start (powerStart start t) bits) := hj.2.1
  have ha : wire (joinStart start m t bits + 2) =
      wire (FrozenSource.output oldStart start t) + wire (joinStart start m t bits + 1) := hj.2.2.1
  have hd := Dyadic.realized_output wire (joinStart start m t bits + 2) (dyadicStart start m t bits) exponent hr.2.2.2
  rw [ha, hp, hc, hlow, hpower] at hd
  exact hd

theorem symbolic_output (oldStart start m : ℕ) (sample a : ℤ) (t : Term) (bits exponent : List Bool)
    (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start) (hm : m ≤ start) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start
      (program oldStart start m sample a t bits exponent) (output start m t bits exponent) =
        polynomial m sample a t bits exponent :=
  realized_output _ oldStart start m sample a t bits exponent ht hs hm
    (fun i hi => Differential.symbolicRun_preserves_before _ _ _ i hi)
    (Differential.symbolicRun_realizes _ _ _ (wellFormed oldStart start m sample a t bits exponent ht hs hm))

end SampledSource
end LeanCanny.ETR.ComplexCircuit
