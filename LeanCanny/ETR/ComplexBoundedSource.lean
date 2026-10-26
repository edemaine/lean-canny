/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexBoundedLow

/-! # The complete sampled bounded regular source circuit

The original term, the sphere energy, its scale and shift, the full pure-power
sum, and the outer regularization use one acyclic operation list. Exponents
are binary words throughout, including the radius and both regularizations.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.BoundedSource
open MvPolynomial
open scoped Classical BigOperators

def radialStart (start : ℕ) (t : Term) : ℕ := SampledSource.powerStart start t
def lowStart (start m : ℕ) (t : Term) : ℕ := SampledSource.joinStart start m t [true]
def powerStart (start m : ℕ) (t : Term) (radius scale shift : List Bool) : ℕ :=
  BoundedLow.output (lowStart start m t) radius scale shift + 1
def joinStart (start m : ℕ) (t : Term) (radius scale shift bits : List Bool) : ℕ :=
  powerStart start m t radius scale shift + 1 + (m + 3) * Infinity.stride bits

def program (oldStart start m : ℕ) (sample : ℤ) (t : Term)
    (radius scale shift bits exponent : List Bool) : List Operation :=
  FrozenSource.program oldStart start sample t ++
    (SamplePowers.program m start (radialStart start t) [true] ++
      (BoundedLow.program (FrozenSource.output oldStart start t)
        (SamplePowers.output m start (radialStart start t) [true]) (lowStart start m t) radius scale shift ++
        (SamplePowers.program (m + 2) start (powerStart start m t radius scale shift) bits ++
          ([.add (BoundedLow.output (lowStart start m t) radius scale shift)
            (SamplePowers.output (m + 2) start (powerStart start m t radius scale shift) bits)] ++
            Dyadic.program (joinStart start m t radius scale shift bits)
              (joinStart start m t radius scale shift bits + 1) exponent))))

def output (start m : ℕ) (t : Term) (radius scale shift bits exponent : List Bool) : ℕ :=
  Dyadic.output (joinStart start m t radius scale shift bits + 1) exponent

noncomputable def polynomial (m : ℕ) (sample : ℤ) (t : Term)
    (radius scale shift bits exponent : List Bool) : MvPolynomial ℕ ℤ :=
  C ((2 : ℤ) ^ Nat.fromBitsLE exponent) *
    (BoundedLow.polynomial (FrozenSource.polynomial sample t)
      ((C sample) ^ 2 + ∑ i ∈ Finset.range m, X i ^ 2) radius scale shift +
      ((C sample) ^ (Nat.fromBitsLE bits + 1) + ∑ i ∈ Finset.range (m + 2), X i ^ (Nat.fromBitsLE bits + 1))) - 1

theorem frozen_next (oldStart start : ℕ) (sample : ℤ) (t : Term) :
    start + (FrozenSource.program oldStart start sample t).length = radialStart start t :=
  SampledSource.frozen_next oldStart start sample t
theorem radial_next (start m : ℕ) (t : Term) :
    radialStart start t + (SamplePowers.program m start (radialStart start t) [true]).length = lowStart start m t :=
  SampledSource.power_next start m t [true]
theorem low_next (oldStart start m : ℕ) (t : Term) (radius scale shift : List Bool) :
    lowStart start m t + (BoundedLow.program (FrozenSource.output oldStart start t)
      (SamplePowers.output m start (radialStart start t) [true]) (lowStart start m t) radius scale shift).length =
        powerStart start m t radius scale shift := BoundedLow.next_eq _ _ _ _ _ _
theorem power_next (start m : ℕ) (t : Term) (radius scale shift bits : List Bool) :
    powerStart start m t radius scale shift +
      (SamplePowers.program (m + 2) start (powerStart start m t radius scale shift) bits).length =
        joinStart start m t radius scale shift bits := by
  rw [SamplePowers.program_length]
  unfold joinStart
  rw [show m + 2 + 1 = m + 3 by omega]
  omega

theorem program_length (oldStart start m : ℕ) (sample : ℤ) (t : Term)
    (radius scale shift bits exponent : List Bool) :
    (program oldStart start m sample t radius scale shift bits exponent).length =
      Source.count t + 8 * (m + 1) + 2 * radius.length + 2 * scale.length + 2 * shift.length +
        (m + 3) * Infinity.stride bits + 2 * exponent.length + 25 := by
  simp only [program, List.length_append, List.length_cons, List.length_nil, FrozenSource.program_length,
    SamplePowers.program_length, BoundedLow.program_length, Dyadic.program_length, Infinity.stride]
  ring

theorem wellFormed (oldStart start m : ℕ) (sample : ℤ) (t : Term)
    (radius scale shift bits exponent : List Bool) (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start)
    (hm : m + 2 ≤ start) : StraightLine.WellFormed start
      (program oldStart start m sample t radius scale shift bits exponent) := by
  rw [program, StraightLine.wellFormed_append, frozen_next, StraightLine.wellFormed_append,
    radial_next, StraightLine.wellFormed_append, low_next, StraightLine.wellFormed_append,
    power_next, StraightLine.wellFormed_append]
  have hq := FrozenSource.output_lt oldStart start sample t ht hs
  rw [frozen_next] at hq
  have hr := SamplePowers.output_lt m start (radialStart start t) [true]
  rw [radial_next] at hr
  have hR : start < radialStart start t := by unfold radialStart SampledSource.powerStart; omega
  have hl : radialStart start t ≤ lowStart start m t := by
    unfold lowStart SampledSource.joinStart radialStart
    omega
  have hp : lowStart start m t < powerStart start m t radius scale shift := by
    unfold powerStart BoundedLow.output ScaleShift.output BoundedLow.joinStart BoundedLow.shiftStart
      BoundedLow.scaleStart BoundedLow.energyStart
    omega
  have hall := SamplePowers.output_lt (m + 2) start (powerStart start m t radius scale shift) bits
  rw [power_next] at hall
  have hj : powerStart start m t radius scale shift ≤ joinStart start m t radius scale shift bits := by
    unfold joinStart; omega
  refine ⟨FrozenSource.wellFormed oldStart start sample t ht hs,
    SamplePowers.wellFormed m start _ _ hR (by omega),
    BoundedLow.wellFormed _ _ _ _ _ _ (by omega) hr,
    SamplePowers.wellFormed (m + 2) start _ bits (by omega) (by omega), ?_, ?_⟩
  · simp only [StraightLine.WellFormed, Operation.InputsBelow]
    unfold powerStart at hj
    exact ⟨⟨by omega, hall⟩, trivial⟩
  · exact Dyadic.wellFormed _ _ (by simp) exponent

theorem output_lt (oldStart start m : ℕ) (sample : ℤ) (t : Term)
    (radius scale shift bits exponent : List Bool) :
    output start m t radius scale shift bits exponent <
      start + (program oldStart start m sample t radius scale shift bits exponent).length := by
  rw [program_length]
  unfold output Dyadic.output Dyadic.productWire Power.output joinStart powerStart BoundedLow.output ScaleShift.output
    BoundedLow.joinStart BoundedLow.shiftStart BoundedLow.scaleStart BoundedLow.energyStart lowStart
    SampledSource.joinStart SampledSource.powerStart Infinity.stride
  norm_num only [List.length_cons, List.length_nil]
  omega

theorem realized_powers (wire : ℕ → MvPolynomial ℕ ℤ) (m sampleWire start bound : ℕ) (bits : List Bool)
    (hm : m ≤ bound) (hin : ∀ i < bound, wire i = X i)
    (hr : Differential.Realizes wire start (SamplePowers.program m sampleWire start bits)) :
    wire (SamplePowers.output m sampleWire start bits) = wire sampleWire ^ (Nat.fromBitsLE bits + 1) +
      ∑ i ∈ Finset.range m, X i ^ (Nat.fromBitsLE bits + 1) := by
  rw [SamplePowers.realized_output wire m sampleWire start bits hr]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hin i ((Finset.mem_range.mp hi).trans_le hm)]

theorem realized_output (wire : ℕ → MvPolynomial ℕ ℤ) (oldStart start m : ℕ) (sample : ℤ) (t : Term)
    (radius scale shift bits exponent : List Bool) (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start)
    (hm : m + 2 ≤ start) (hin : ∀ i < start, wire i = X i)
    (hr : Differential.Realizes wire start (program oldStart start m sample t radius scale shift bits exponent)) :
    wire (output start m t radius scale shift bits exponent) = polynomial m sample t radius scale shift bits exponent := by
  rw [program, Differential.realizes_append, frozen_next, Differential.realizes_append,
    radial_next, Differential.realizes_append, low_next, Differential.realizes_append,
    power_next, Differential.realizes_append] at hr
  have hq := FrozenSource.realized_output wire oldStart start sample t ht hs hin hr.1
  have hsamp : wire start = C sample := hr.1.1
  have hrad := realized_powers wire m start (radialStart start t) start [true] (by omega) hin hr.2.1
  simp only [hsamp, show Nat.fromBitsLE [true] + 1 = 2 from rfl] at hrad
  have hlow := BoundedLow.realized_output wire _ _ _ radius scale shift hr.2.2.1
  rw [hq, hrad] at hlow
  have hpower := realized_powers wire (m + 2) start (powerStart start m t radius scale shift) start bits hm hin hr.2.2.2.1
  rw [hsamp] at hpower
  have hjoin : wire (joinStart start m t radius scale shift bits) =
      wire (BoundedLow.output (lowStart start m t) radius scale shift) +
        wire (SamplePowers.output (m + 2) start (powerStart start m t radius scale shift) bits) := hr.2.2.2.2.1.1
  have hdyadic := Dyadic.realized_output wire _ _ exponent hr.2.2.2.2.2
  rw [hjoin, hlow, hpower] at hdyadic
  exact hdyadic

theorem symbolic_output (oldStart start m : ℕ) (sample : ℤ) (t : Term)
    (radius scale shift bits exponent : List Bool) (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start)
    (hm : m + 2 ≤ start) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start
      (program oldStart start m sample t radius scale shift bits exponent)
      (output start m t radius scale shift bits exponent) = polynomial m sample t radius scale shift bits exponent :=
  realized_output _ oldStart start m sample t radius scale shift bits exponent ht hs hm
    (fun i hi => Differential.symbolicRun_preserves_before _ _ _ i hi)
    (Differential.symbolicRun_realizes _ _ _ (wellFormed oldStart start m sample t radius scale shift bits exponent ht hs hm))

end LeanCanny.ETR.ComplexCircuit.BoundedSource
