/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexBoundedSource

/-! # The bounded source after its original polynomial has been computed

The original polynomial and swept coordinate are existing wires. This tail
works with a variable coordinate as well as a literal sample. It computes
the sphere energy, both shifts and scales, and the full pure-power source.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.BoundedTail
open MvPolynomial
open scoped Classical BigOperators

def lowStart (start m : ℕ) : ℕ := start + 1 + (m + 1) * 8
def powerStart (start m : ℕ) (radius scale shift : List Bool) : ℕ :=
  BoundedLow.output (lowStart start m) radius scale shift + 1
def joinStart (start m : ℕ) (radius scale shift bits : List Bool) : ℕ :=
  powerStart start m radius scale shift + 1 + (m + 3) * Infinity.stride bits

def program (source sample start m : ℕ) (radius scale shift bits exponent : List Bool) : List Operation :=
  SamplePowers.program m sample start [true] ++
    (BoundedLow.program source (SamplePowers.output m sample start [true]) (lowStart start m) radius scale shift ++
      (SamplePowers.program (m + 2) sample (powerStart start m radius scale shift) bits ++
        ([.add (BoundedLow.output (lowStart start m) radius scale shift)
          (SamplePowers.output (m + 2) sample (powerStart start m radius scale shift) bits)] ++
          Dyadic.program (joinStart start m radius scale shift bits) (joinStart start m radius scale shift bits + 1) exponent)))
def output (start m : ℕ) (radius scale shift bits exponent : List Bool) : ℕ :=
  Dyadic.output (joinStart start m radius scale shift bits + 1) exponent
def energyOutput (start m : ℕ) (radius : List Bool) : ℕ :=
  ZeroEnergy.output (BoundedLow.energyStart (lowStart start m) radius)

noncomputable def energy (m : ℕ) (q a : MvPolynomial ℕ ℤ) (radius : List Bool) : MvPolynomial ℕ ℤ :=
  q ^ 2 + (a ^ 2 + ∑ i ∈ Finset.range m, X i ^ 2 - C ((2 : ℤ) ^ Nat.fromBitsLE radius)) ^ 2
noncomputable def polynomial (m : ℕ) (q a : MvPolynomial ℕ ℤ)
    (radius scale shift bits exponent : List Bool) : MvPolynomial ℕ ℤ :=
  C ((2 : ℤ) ^ Nat.fromBitsLE exponent) *
    (BoundedLow.polynomial q (a ^ 2 + ∑ i ∈ Finset.range m, X i ^ 2) radius scale shift +
      (a ^ (Nat.fromBitsLE bits + 1) + ∑ i ∈ Finset.range (m + 2), X i ^ (Nat.fromBitsLE bits + 1))) - 1

theorem radial_next (sample start m : ℕ) :
    start + (SamplePowers.program m sample start [true]).length = lowStart start m := by
  rw [SamplePowers.program_length]
  norm_num only [Infinity.stride, List.length_cons, List.length_nil]
  unfold lowStart
  omega
theorem low_next (source sample start m : ℕ) (radius scale shift : List Bool) :
    lowStart start m + (BoundedLow.program source (SamplePowers.output m sample start [true])
      (lowStart start m) radius scale shift).length = powerStart start m radius scale shift := BoundedLow.next_eq ..
theorem power_next (sample start m : ℕ) (radius scale shift bits : List Bool) :
    powerStart start m radius scale shift +
      (SamplePowers.program (m + 2) sample (powerStart start m radius scale shift) bits).length =
        joinStart start m radius scale shift bits := by
  rw [SamplePowers.program_length]
  unfold joinStart
  rw [show m + 2 + 1 = m + 3 by omega]
  omega

theorem program_length (source sample start m : ℕ) (radius scale shift bits exponent : List Bool) :
    (program source sample start m radius scale shift bits exponent).length =
      8 * (m + 1) + 2 * radius.length + 2 * scale.length + 2 * shift.length +
        (m + 3) * Infinity.stride bits + 2 * exponent.length + 24 := by
  simp only [program, List.length_append, List.length_cons, List.length_nil, SamplePowers.program_length,
    BoundedLow.program_length, Dyadic.program_length, Infinity.stride]
  ring

theorem wellFormed (source sample start m : ℕ) (radius scale shift bits exponent : List Bool)
    (hq : source < start) (ha : sample < start) (hm : m + 2 ≤ start) :
    StraightLine.WellFormed start (program source sample start m radius scale shift bits exponent) := by
  rw [program, StraightLine.wellFormed_append, radial_next, StraightLine.wellFormed_append,
    low_next, StraightLine.wellFormed_append, power_next, StraightLine.wellFormed_append]
  have hr := SamplePowers.output_lt m sample start [true]
  rw [radial_next] at hr
  have hl : start ≤ lowStart start m := by unfold lowStart; omega
  have hp : lowStart start m < powerStart start m radius scale shift := by
    unfold powerStart BoundedLow.output ScaleShift.output BoundedLow.joinStart BoundedLow.shiftStart
      BoundedLow.scaleStart BoundedLow.energyStart
    omega
  have hall := SamplePowers.output_lt (m + 2) sample (powerStart start m radius scale shift) bits
  rw [power_next] at hall
  have hj : powerStart start m radius scale shift ≤ joinStart start m radius scale shift bits := by unfold joinStart; omega
  refine ⟨SamplePowers.wellFormed m sample start _ ha (by omega),
    BoundedLow.wellFormed _ _ _ _ _ _ (by omega) hr,
    SamplePowers.wellFormed (m + 2) sample _ bits (by omega) (by omega), ?_, ?_⟩
  · simp only [StraightLine.WellFormed, Operation.InputsBelow]
    unfold powerStart at hj
    exact ⟨⟨by omega, hall⟩, trivial⟩
  · exact Dyadic.wellFormed _ _ (by simp) exponent

theorem output_lt (source sample start m : ℕ) (radius scale shift bits exponent : List Bool) :
    output start m radius scale shift bits exponent < start + (program source sample start m radius scale shift bits exponent).length := by
  rw [program_length]
  unfold output Dyadic.output Dyadic.productWire Power.output joinStart powerStart BoundedLow.output ScaleShift.output
    BoundedLow.joinStart BoundedLow.shiftStart BoundedLow.scaleStart BoundedLow.energyStart lowStart Infinity.stride
  omega

theorem energyOutput_lt (source sample start m : ℕ) (radius scale shift bits exponent : List Bool) :
    energyOutput start m radius < start + (program source sample start m radius scale shift bits exponent).length := by
  rw [program_length]
  unfold energyOutput ZeroEnergy.output BoundedLow.energyStart lowStart
  omega

theorem realized_output (wire : ℕ → MvPolynomial ℕ ℤ) (source sample start m : ℕ)
    (radius scale shift bits exponent : List Bool) (hin : ∀ i < m + 2, wire i = X i)
    (hr : Differential.Realizes wire start (program source sample start m radius scale shift bits exponent)) :
    wire (output start m radius scale shift bits exponent) = polynomial m (wire source) (wire sample) radius scale shift bits exponent := by
  rw [program, Differential.realizes_append, radial_next, Differential.realizes_append, low_next,
    Differential.realizes_append, power_next, Differential.realizes_append] at hr
  have hrad := BoundedSource.realized_powers wire m sample start (m + 2) [true] (by omega) hin hr.1
  simp only [show Nat.fromBitsLE [true] + 1 = 2 from rfl] at hrad
  have hlow := BoundedLow.realized_output wire _ _ _ radius scale shift hr.2.1
  rw [hrad] at hlow
  have hpower := BoundedSource.realized_powers wire (m + 2) sample (powerStart start m radius scale shift)
    (m + 2) bits le_rfl hin hr.2.2.1
  have hjoin : wire (joinStart start m radius scale shift bits) =
      wire (BoundedLow.output (lowStart start m) radius scale shift) +
        wire (SamplePowers.output (m + 2) sample (powerStart start m radius scale shift) bits) := hr.2.2.2.1.1
  have hd := Dyadic.realized_output wire _ _ exponent hr.2.2.2.2
  rw [hjoin, hlow, hpower] at hd
  exact hd

theorem realized_energy (wire : ℕ → MvPolynomial ℕ ℤ) (source sample start m : ℕ)
    (radius scale shift bits exponent : List Bool) (hin : ∀ i < m + 2, wire i = X i)
    (hr : Differential.Realizes wire start (program source sample start m radius scale shift bits exponent)) :
    wire (energyOutput start m radius) = energy m (wire source) (wire sample) radius := by
  rw [program, Differential.realizes_append, radial_next, Differential.realizes_append, low_next] at hr
  have hrad := BoundedSource.realized_powers wire m sample start (m + 2) [true] (by omega) hin hr.1
  simp only [show Nat.fromBitsLE [true] + 1 = 2 from rfl] at hrad
  have hl := hr.2.1
  rw [BoundedLow.program, Differential.realizes_append, BoundedLow.radius_next,
    Differential.realizes_append, BoundedLow.energy_next] at hl
  have hR := BinaryScale.realized_output wire (lowStart start m) radius hl.1
  have he := ZeroEnergy.realized_output wire source _ _ _ hl.2.1
  rw [hrad, hR] at he
  exact he

end LeanCanny.ETR.ComplexCircuit.BoundedTail
