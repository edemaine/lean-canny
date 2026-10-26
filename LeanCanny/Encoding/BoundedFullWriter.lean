/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullIdentity
public import LeanCanny.Encoding.BoundedSourceWriter
public import LeanCanny.Geometry.BoundedMarkedComponents

/-! # Native full-source generation from original term, dimension and radius

The swept coordinate is input `dimension + 3`; the remaining coordinates
occupy the preceding inputs. Both the regular-source polynomial and the
marking polynomial are computed on shared wires. No record or sample reader
is needed to encode this full family.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullWriter
open LeanCanny.Geometry LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Algebra MvPolynomial

structure Readers where
  source : List Bool → List Bool
  dim : List Bool → ℕ
  radius : List Bool → ℕ
structure Readers.PolyTime (P : Readers) : Prop where
  source : P.source ∈ FP
  dim : UnaryFn P.dim
  radius : BinaryFn P.radius

def Readers.comp (P : Readers) (f : List Bool → List Bool) : Readers :=
  ⟨P.source ∘ f, P.dim ∘ f, P.radius ∘ f⟩

theorem Readers.PolyTime.comp {P : Readers} (h : P.PolyTime) {f : List Bool → List Bool} (hf : f ∈ FP) :
    (P.comp f).PolyTime := by
  refine ⟨?_, ?_, ?_⟩
  · change (P.source ∘ f) ∈ FP
    exact mem_FP_comp (f := f) (g := P.source) hf h.source
  · exact h.dim.comp hf
  · exact h.radius.comp hf

def controls (P : Readers) : BoundedSourceWriter.Readers := ⟨P.source, fun _ => [], P.dim, P.radius⟩
theorem controls_polyTime {P : Readers} (h : P.PolyTime) : (controls P).PolyTime :=
  ⟨h.source, constFn_mem_FP [], h.dim, h.radius⟩

noncomputable def size (P : Readers) : List Bool → ℕ := BoundedSourceWriter.size (controls P)
noncomputable def original (P : Readers) (c : List Bool) : MvPolynomial (Fin (P.dim c)) ℤ := BoundedSourceWriter.original (controls P) c

theorem size_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) : size (P.comp f) c = size P (f c) := rfl
theorem original_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    original (P.comp f) c = original P (f c) := rfl
def parameter (P : Readers) (c : List Bool) : ℕ := P.dim c + 3
noncomputable def start (P : Readers) (c : List Bool) : ℕ := max (size P c) (P.dim c + 4)
noncomputable def degree (P : Readers) : List Bool → ℕ := BoundedSourceWriter.degree (controls P)
noncomputable def scaleExponent (P : Readers) : List Bool → ℕ := BoundedSourceWriter.scaleExponent (controls P)
noncomputable def shiftExponent (P : Readers) : List Bool → ℕ := BoundedSourceWriter.shiftExponent (controls P)
noncomputable def regularizationExponent (P : Readers) : List Bool → ℕ := BoundedSourceWriter.regularizationExponent (controls P)

noncomputable def program (P : Readers) (c : List Bool) : List Operation :=
  BoundedFullSource.program (size P c) (parameter P c) (start P c) (P.dim c + 1) (TermView.term (P.source c))
    (2 * P.radius c).bits (scaleExponent P c).bits (shiftExponent P c).bits (degree P c - 1).bits (regularizationExponent P c).bits
noncomputable def output (P : Readers) (c : List Bool) : ℕ :=
  BoundedFullSource.output (start P c) (P.dim c + 1) (TermView.term (P.source c))
    (2 * P.radius c).bits (scaleExponent P c).bits (shiftExponent P c).bits (degree P c - 1).bits (regularizationExponent P c).bits
noncomputable def markOutput (P : Readers) (c : List Bool) : ℕ :=
  BoundedFullSource.energyOutput (start P c) (P.dim c + 1) (TermView.term (P.source c)) (2 * P.radius c).bits

theorem size_unary {P : Readers} (h : P.PolyTime) : UnaryFn (size P) := BoundedSourceWriter.size_unary (controls_polyTime h)
theorem parameter_unary {P : Readers} (h : P.PolyTime) : UnaryFn (parameter P) := h.dim.add (UnaryFn.const 3)
theorem start_unary {P : Readers} (h : P.PolyTime) : UnaryFn (start P) := (size_unary h).max (h.dim.add (UnaryFn.const 4))
theorem degree_binary {P : Readers} (h : P.PolyTime) : BinaryFn (degree P) := BoundedSourceWriter.degree_binary (controls_polyTime h)
theorem scaleExponent_binary {P : Readers} (h : P.PolyTime) : BinaryFn (scaleExponent P) := BoundedSourceWriter.scaleExponent_binary (controls_polyTime h)
theorem shiftExponent_binary {P : Readers} (h : P.PolyTime) : BinaryFn (shiftExponent P) := BoundedSourceWriter.shiftExponent_binary (controls_polyTime h)
theorem regularizationExponent_binary {P : Readers} (h : P.PolyTime) : BinaryFn (regularizationExponent P) :=
  BoundedSourceWriter.regularizationExponent_binary (controls_polyTime h)

theorem encode_mem_FP {P : Readers} (h : P.PolyTime) :
    (fun c => encode (StraightLine.gates (start P c) (program P c))) ∈ FP :=
  BoundedFullSource.encode_mem_FP h.source (parameter_unary h) (start_unary h) (h.dim.add (UnaryFn.const 1))
    ((BinaryFn.const 2).mul h.radius).bits_mem_FP (scaleExponent_binary h).bits_mem_FP (shiftExponent_binary h).bits_mem_FP
    ((degree_binary h).sub (BinaryFn.const 1)).bits_mem_FP (regularizationExponent_binary h).bits_mem_FP
theorem output_unary {P : Readers} (h : P.PolyTime) : UnaryFn (output P) :=
  BoundedFullSource.output_unary h.source (start_unary h) (h.dim.add (UnaryFn.const 1))
    ((BinaryFn.const 2).mul h.radius).bits_mem_FP (scaleExponent_binary h).bits_mem_FP (shiftExponent_binary h).bits_mem_FP
    ((degree_binary h).sub (BinaryFn.const 1)).bits_mem_FP (regularizationExponent_binary h).bits_mem_FP
theorem markOutput_unary {P : Readers} (h : P.PolyTime) : UnaryFn (markOutput P) :=
  BoundedFullSource.energyOutput_unary h.source (start_unary h) (h.dim.add (UnaryFn.const 1))
    ((BinaryFn.const 2).mul h.radius).bits_mem_FP
theorem length_unary {P : Readers} (h : P.PolyTime) : UnaryFn (fun c => (program P c).length) :=
  BoundedFullSource.length_unary h.source (h.dim.add (UnaryFn.const 1))
    ((BinaryFn.const 2).mul h.radius).bits_mem_FP (scaleExponent_binary h).bits_mem_FP (shiftExponent_binary h).bits_mem_FP
    ((degree_binary h).sub (BinaryFn.const 1)).bits_mem_FP (regularizationExponent_binary h).bits_mem_FP

theorem parameter_lt_start (P : Readers) (c : List Bool) : parameter P c < start P c :=
  (show P.dim c + 3 < P.dim c + 4 by omega).trans_le (Nat.le_max_right ..)
theorem input_bound (P : Readers) (c : List Bool) : size P c ≤ start P c + 1 :=
  (Nat.le_max_left ..).trans (Nat.le_succ _)
theorem spatial_bound (P : Readers) (c : List Bool) : P.dim c + 1 + 2 ≤ start P c :=
  (show P.dim c + 1 + 2 ≤ P.dim c + 4 by omega).trans (Nat.le_max_right ..)

theorem wellFormed (P : Readers) (c : List Bool) : StraightLine.WellFormed (start P c) (program P c) :=
  BoundedFullSource.wellFormed _ _ _ _ _ _ _ _ _ _ (Term.arity_le_dataSize _)
    (parameter_lt_start P c) (input_bound P c) (spatial_bound P c)
theorem output_lt (P : Readers) (c : List Bool) : output P c < start P c + (program P c).length :=
  BoundedFullSource.output_lt _ _ _ _ _ _ _ _ _ _
theorem markOutput_lt (P : Readers) (c : List Bool) : markOutput P c < start P c + (program P c).length :=
  BoundedFullSource.energyOutput_lt _ _ _ _ _ _ _ _ _ _

theorem original_degree (P : Readers) (c : List Bool) : (original P c).totalDegree ≤ size P c :=
  BoundedSourceWriter.original_degree (controls P) c
theorem original_mass (P : Readers) (c : List Bool) : MvMass.mass (original P c) ≤ 2 ^ size P c :=
  BoundedSourceWriter.original_mass (controls P) c

theorem source_identity (P : Readers) (c : List Bool) (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (start P c) (program P c) (output P c) =
      CircuitFreeze.substitution (parameter P c) (rename Fin.val
        (BoundedRegularSource.polynomial (original P c) (size P c) (size P c) (P.radius c))) := by
  rw [program, output, BoundedFullSource.symbolic_output (size P c) (parameter P c) (start P c) (P.dim c + 1)
    (TermView.term (P.source c)) _ _ _ _ _ (Term.arity_le_dataSize _) (parameter_lt_start P c) (input_bound P c) (spatial_bound P c)]
  exact BoundedFullIdentity.polynomial_identity _ _ (Term.toPolynomial_eq_rename_finitePolynomial _ _ ht) _ _ _ _

theorem mark_identity (P : Readers) (c : List Bool) (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (start P c) (program P c) (markOutput P c) =
      CircuitFreeze.substitution (parameter P c) (rename Fin.val (BoundedRegularSource.markPolynomial (original P c) (P.radius c))) := by
  rw [program, markOutput, BoundedFullSource.symbolic_energy (size P c) (parameter P c) (start P c) (P.dim c + 1)
    (TermView.term (P.source c)) _ _ _ _ _ (Term.arity_le_dataSize _) (parameter_lt_start P c) (input_bound P c) (spatial_bound P c)]
  exact BoundedFullIdentity.energy_identity _ _ (Term.toPolynomial_eq_rename_finitePolynomial _ _ ht) _ _

end LeanCanny.Encoding.BoundedFullWriter
