/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexBoundedTailEncoding
public import LeanCanny.ETR.ComplexCircuitFreezeSlice

/-! # The full bounded regular source with a variable swept coordinate

The original term is compiled into shared wires with its first coordinate
redirected to a parameter input. The bounded tail then builds the whole
regular source. The parameter remains a variable throughout the circuit.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.BoundedFullSource
open MvPolynomial
open scoped Classical

def termProgram (inputs parameter start : ℕ) (t : Term) : List Operation :=
  CircuitFreeze.program inputs parameter start (Source.program inputs t)
def sourceOutput (inputs parameter start : ℕ) (t : Term) : ℕ :=
  CircuitFreeze.output inputs parameter start (Source.output inputs t)
def tailStart (start : ℕ) (t : Term) : ℕ := start + Source.count t

def program (inputs parameter start m : ℕ) (t : Term) (radius scale shift bits exponent : List Bool) : List Operation :=
  termProgram inputs parameter start t ++
    BoundedTail.program (sourceOutput inputs parameter start t) parameter (tailStart start t) m radius scale shift bits exponent
def output (start m : ℕ) (t : Term) (radius scale shift bits exponent : List Bool) : ℕ :=
  BoundedTail.output (tailStart start t) m radius scale shift bits exponent
def energyOutput (start m : ℕ) (t : Term) (radius : List Bool) : ℕ :=
  BoundedTail.energyOutput (tailStart start t) m radius

noncomputable def polynomial (parameter m : ℕ) (t : Term) (radius scale shift bits exponent : List Bool) : MvPolynomial ℕ ℤ :=
  BoundedTail.polynomial m (CircuitFreeze.substitution parameter t.toPolynomial) (X parameter) radius scale shift bits exponent
noncomputable def energy (parameter m : ℕ) (t : Term) (radius : List Bool) : MvPolynomial ℕ ℤ :=
  BoundedTail.energy m (CircuitFreeze.substitution parameter t.toPolynomial) (X parameter) radius

theorem termProgram_length (inputs parameter start : ℕ) (t : Term) : (termProgram inputs parameter start t).length = Source.count t := by
  rw [termProgram, CircuitFreeze.program_length, Source.program_length]
theorem termProgram_next (inputs parameter start : ℕ) (t : Term) :
    start + (termProgram inputs parameter start t).length = tailStart start t := by rw [termProgram_length]; rfl

theorem sourceOutput_lt (inputs parameter start : ℕ) (t : Term) (ht : t.arity ≤ inputs)
    (hp : parameter < start) (hs : inputs ≤ start + 1) : sourceOutput inputs parameter start t < tailStart start t := by
  have ho : Source.output inputs t < inputs + (Source.program inputs t).length := by
    simpa only [Source.program_length] using Source.output_lt inputs t ht
  have h := CircuitFreeze.output_lt inputs parameter start (Source.output inputs t) (Source.program inputs t) hp hs ho
  simpa only [sourceOutput, CircuitFreeze.program_length, Source.program_length, tailStart] using h

theorem wellFormed (inputs parameter start m : ℕ) (t : Term) (radius scale shift bits exponent : List Bool)
    (ht : t.arity ≤ inputs) (hp : parameter < start) (hs : inputs ≤ start + 1) (hm : m + 2 ≤ start) :
    StraightLine.WellFormed start (program inputs parameter start m t radius scale shift bits exponent) := by
  rw [program, StraightLine.wellFormed_append, termProgram_next]
  have hl : start ≤ tailStart start t := by unfold tailStart; omega
  exact ⟨CircuitFreeze.wellFormed inputs parameter start _ (Source.wellFormed inputs t ht) hp hs,
    BoundedTail.wellFormed _ _ _ _ _ _ _ _ _ (sourceOutput_lt inputs parameter start t ht hp hs) (by omega) (by omega)⟩

theorem output_lt (inputs parameter start m : ℕ) (t : Term) (radius scale shift bits exponent : List Bool) :
    output start m t radius scale shift bits exponent < start + (program inputs parameter start m t radius scale shift bits exponent).length := by
  rw [program, List.length_append, ← Nat.add_assoc, termProgram_next]
  exact BoundedTail.output_lt _ _ _ _ _ _ _ _ _

theorem energyOutput_lt (inputs parameter start m : ℕ) (t : Term) (radius scale shift bits exponent : List Bool) :
    energyOutput start m t radius < start + (program inputs parameter start m t radius scale shift bits exponent).length := by
  rw [program, List.length_append, ← Nat.add_assoc, termProgram_next]
  exact BoundedTail.energyOutput_lt _ _ _ _ _ _ _ _ _

theorem realized_source (wire : ℕ → MvPolynomial ℕ ℤ) (inputs parameter start : ℕ) (t : Term)
    (ht : t.arity ≤ inputs) (hp : parameter < start) (hs : inputs ≤ start + 1)
    (hin : ∀ i < start, wire i = X i) (hr : Differential.Realizes wire start (termProgram inputs parameter start t)) :
    wire (sourceOutput inputs parameter start t) = CircuitFreeze.substitution parameter t.toPolynomial := by
  have ho : Source.output inputs t < inputs + (Source.program inputs t).length := by
    simpa only [Source.program_length] using Source.output_lt inputs t ht
  have h := CircuitFreeze.realized_output wire inputs parameter start (Source.output inputs t) (Source.program inputs t)
    (Source.wellFormed inputs t ht) hp hs ho hin hr
  rw [Source.symbolicRun_output inputs t ht] at h
  exact h

theorem realized_output (wire : ℕ → MvPolynomial ℕ ℤ) (inputs parameter start m : ℕ) (t : Term)
    (radius scale shift bits exponent : List Bool) (ht : t.arity ≤ inputs) (hp : parameter < start)
    (hs : inputs ≤ start + 1) (hm : m + 2 ≤ start) (hin : ∀ i < start, wire i = X i)
    (hr : Differential.Realizes wire start (program inputs parameter start m t radius scale shift bits exponent)) :
    wire (output start m t radius scale shift bits exponent) = polynomial parameter m t radius scale shift bits exponent := by
  rw [program, Differential.realizes_append, termProgram_next] at hr
  have hq := realized_source wire inputs parameter start t ht hp hs hin hr.1
  have hout := BoundedTail.realized_output wire _ _ _ m radius scale shift bits exponent (fun i hi => hin i (hi.trans_le hm)) hr.2
  rw [hq, hin parameter hp] at hout
  exact hout

theorem realized_energy (wire : ℕ → MvPolynomial ℕ ℤ) (inputs parameter start m : ℕ) (t : Term)
    (radius scale shift bits exponent : List Bool) (ht : t.arity ≤ inputs) (hp : parameter < start)
    (hs : inputs ≤ start + 1) (hm : m + 2 ≤ start) (hin : ∀ i < start, wire i = X i)
    (hr : Differential.Realizes wire start (program inputs parameter start m t radius scale shift bits exponent)) :
    wire (energyOutput start m t radius) = energy parameter m t radius := by
  rw [program, Differential.realizes_append, termProgram_next] at hr
  have hq := realized_source wire inputs parameter start t ht hp hs hin hr.1
  have hout := BoundedTail.realized_energy wire _ _ _ m radius scale shift bits exponent (fun i hi => hin i (hi.trans_le hm)) hr.2
  rw [hq, hin parameter hp] at hout
  exact hout

theorem symbolic_output (inputs parameter start m : ℕ) (t : Term) (radius scale shift bits exponent : List Bool)
    (ht : t.arity ≤ inputs) (hp : parameter < start) (hs : inputs ≤ start + 1) (hm : m + 2 ≤ start) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start
      (program inputs parameter start m t radius scale shift bits exponent) (output start m t radius scale shift bits exponent) =
        polynomial parameter m t radius scale shift bits exponent :=
  realized_output _ inputs parameter start m t radius scale shift bits exponent ht hp hs hm
    (fun i hi => Differential.symbolicRun_preserves_before _ _ _ i hi)
    (Differential.symbolicRun_realizes _ _ _ (wellFormed inputs parameter start m t radius scale shift bits exponent ht hp hs hm))

theorem symbolic_energy (inputs parameter start m : ℕ) (t : Term) (radius scale shift bits exponent : List Bool)
    (ht : t.arity ≤ inputs) (hp : parameter < start) (hs : inputs ≤ start + 1) (hm : m + 2 ≤ start) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start
      (program inputs parameter start m t radius scale shift bits exponent) (energyOutput start m t radius) = energy parameter m t radius :=
  realized_energy _ inputs parameter start m t radius scale shift bits exponent ht hp hs hm
    (fun i hi => Differential.symbolicRun_preserves_before _ _ _ i hi)
    (Differential.symbolicRun_realizes _ _ _ (wellFormed inputs parameter start m t radius scale shift bits exponent ht hp hs hm))

end LeanCanny.ETR.ComplexCircuit.BoundedFullSource
