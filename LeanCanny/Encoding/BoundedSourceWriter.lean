/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedSampledIdentity
public import LeanCanny.Encoding.BoundedRegularControls
public import LeanCanny.Encoding.FermatTermPreparation
public import LeanCanny.ETR.ComplexBoundedPSPACE

/-! # The actual bounded source writer from encoded original terms

Normalized syntax supplies degree and mass allowances. The record supplies
the frozen sample. Only original syntax, unary dimension, binary radius and
the record reader need native cost certificates.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedSourceWriter
open LeanCanny.Geometry LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Algebra MvPolynomial

structure Readers where
  source : List Bool → List Bool
  record : List Bool → List Bool
  dim : List Bool → ℕ
  radius : List Bool → ℕ

structure Readers.PolyTime (P : Readers) : Prop where
  source : P.source ∈ FP
  record : P.record ∈ FP
  dim : UnaryFn P.dim
  radius : BinaryFn P.radius

def Readers.precomp (P : Readers) (f : List Bool → List Bool) : Readers :=
  ⟨P.source ∘ f, P.record ∘ f, P.dim ∘ f, P.radius ∘ f⟩

theorem Readers.PolyTime.precomp {P : Readers} (h : P.PolyTime) {f : List Bool → List Bool} (hf : f ∈ FP) :
    (P.precomp f).PolyTime := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mem_FP_comp (f := f) (g := P.source) hf h.source
  · exact mem_FP_comp (f := f) (g := P.record) hf h.record
  · exact UnaryFn.comp (f := P.dim) (g := f) h.dim hf
  · exact h.radius.comp (FP.computable hf)

noncomputable def size (P : Readers) (c : List Bool) : ℕ := (TermView.term (P.source c)).toData.size
noncomputable def original (P : Readers) (c : List Bool) : MvPolynomial (Fin (P.dim c)) ℤ :=
  (TermView.term (P.source c)).finitePolynomial (P.dim c)
noncomputable def start (P : Readers) (c : List Bool) : ℕ := max (size P c) (P.dim c + 3)
noncomputable def degree (P : Readers) (c : List Bool) : ℕ := BoundedZeroSource.powerDegree (size P c)
noncomputable def scaleExponent (P : Readers) (c : List Bool) : ℕ :=
  BoundedZeroSource.perturbationExponent (P.dim c) (size P c) (size P c) (P.radius c)
noncomputable def shiftExponent (P : Readers) (c : List Bool) : ℕ :=
  BoundedZeroSource.penaltyExponent (P.dim c) (size P c) (P.radius c)
noncomputable def regularizationExponent (P : Readers) (c : List Bool) : ℕ :=
  BoundedRegularSource.regularizationExponent (P.dim c) (size P c) (size P c) (P.radius c)
noncomputable def sample (P : Readers) (c : List Bool) : ℤ :=
  FermatSweepCertificate.sample (P.dim c + 2) (degree P c) (P.record c)

noncomputable def lower (P : Readers) (c : List Bool) : MvPolynomial (Fin (P.dim c + 4)) ℤ :=
  IntegerRegularSource.lower (BoundedRegularSource.lower (original P c) (size P c) (size P c) (P.radius c))
    (degree P c) (BoundedRegularSource.sourceMassExponent (P.dim c) (size P c) (size P c) (P.radius c))
noncomputable def leading (P : Readers) (c : List Bool) : ℤ :=
  IntegerRegularSource.leading (P.dim c + 3) 1 (degree P c)
    (BoundedRegularSource.sourceMassExponent (P.dim c) (size P c) (size P c) (P.radius c))

noncomputable def program (P : Readers) (c : List Bool) : List Operation :=
  BoundedSource.program (size P c) (start P c) (P.dim c + 1) (sample P c) (TermView.term (P.source c))
    (2 * P.radius c).bits (scaleExponent P c).bits (shiftExponent P c).bits
    (degree P c - 1).bits (regularizationExponent P c).bits
noncomputable def output (P : Readers) (c : List Bool) : ℕ :=
  BoundedSource.output (start P c) (P.dim c + 1) (TermView.term (P.source c))
    (2 * P.radius c).bits (scaleExponent P c).bits (shiftExponent P c).bits
    (degree P c - 1).bits (regularizationExponent P c).bits

theorem size_unary {P : Readers} (h : P.PolyTime) : UnaryFn (size P) := FrozenSource.source_start_unary h.source
theorem start_unary {P : Readers} (h : P.PolyTime) : UnaryFn (start P) := (size_unary h).max (h.dim.add (UnaryFn.const 3))
theorem degree_binary {P : Readers} (h : P.PolyTime) : BinaryFn (degree P) :=
  BoundedZeroControls.powerDegree_binary (BinaryFn.ofUnary (size_unary h))
theorem scaleExponent_binary {P : Readers} (h : P.PolyTime) : BinaryFn (scaleExponent P) :=
  BoundedZeroControls.perturbationExponent_binary h.dim (BinaryFn.ofUnary (size_unary h)) (BinaryFn.ofUnary (size_unary h)) h.radius
theorem shiftExponent_binary {P : Readers} (h : P.PolyTime) : BinaryFn (shiftExponent P) :=
  BoundedZeroControls.penaltyExponent_binary h.dim (BinaryFn.ofUnary (size_unary h)) h.radius
theorem regularizationExponent_binary {P : Readers} (h : P.PolyTime) : BinaryFn (regularizationExponent P) :=
  BoundedRegularControls.regularizationExponent_binary h.dim (BinaryFn.ofUnary (size_unary h)) (BinaryFn.ofUnary (size_unary h)) h.radius
theorem sample_literal_mem_FP {P : Readers} (h : P.PolyTime) :
    (fun c => (Term.const (sample P c)).toData.toBits) ∈ FP :=
  Term.nat_toBits_mem_FP (FermatFrozenSource.sample_binary (h.dim.add (UnaryFn.const 2)) (degree_binary h) h.record)

theorem encode_mem_FP {P : Readers} (h : P.PolyTime) :
    (fun c => encode (StraightLine.gates (start P c) (program P c))) ∈ FP :=
  BoundedSource.encode_mem_FP h.source (start_unary h) (h.dim.add (UnaryFn.const 1)) (sample_literal_mem_FP h)
    ((BinaryFn.const 2).mul h.radius).bits_mem_FP (scaleExponent_binary h).bits_mem_FP (shiftExponent_binary h).bits_mem_FP
    ((degree_binary h).sub (BinaryFn.const 1)).bits_mem_FP (regularizationExponent_binary h).bits_mem_FP

theorem output_unary {P : Readers} (h : P.PolyTime) : UnaryFn (output P) :=
  BoundedSource.output_unary h.source (start_unary h) (h.dim.add (UnaryFn.const 1))
    ((BinaryFn.const 2).mul h.radius).bits_mem_FP (scaleExponent_binary h).bits_mem_FP (shiftExponent_binary h).bits_mem_FP
    ((degree_binary h).sub (BinaryFn.const 1)).bits_mem_FP (regularizationExponent_binary h).bits_mem_FP

theorem length_unary {P : Readers} (h : P.PolyTime) : UnaryFn (fun c => (program P c).length) :=
  BoundedSource.length_unary h.source (h.dim.add (UnaryFn.const 1))
    ((BinaryFn.const 2).mul h.radius).bits_mem_FP (scaleExponent_binary h).bits_mem_FP (shiftExponent_binary h).bits_mem_FP
    ((degree_binary h).sub (BinaryFn.const 1)).bits_mem_FP (regularizationExponent_binary h).bits_mem_FP

theorem wellFormed (P : Readers) (c : List Bool) : StraightLine.WellFormed (start P c) (program P c) :=
  BoundedSource.wellFormed _ _ _ _ _ _ _ _ _ _ (Term.arity_le_dataSize _) (Nat.le_max_left ..) (Nat.le_max_right ..)
theorem output_lt (P : Readers) (c : List Bool) : output P c < start P c + (program P c).length :=
  BoundedSource.output_lt _ _ _ _ _ _ _ _ _ _

theorem original_degree (P : Readers) (c : List Bool) : (original P c).totalDegree ≤ size P c :=
  (Term.totalDegree_finitePolynomial _ _).trans (Term.degreeBound_le_dataSize _)
theorem original_mass (P : Readers) (c : List Bool) : MvMass.mass (original P c) ≤ 2 ^ size P c :=
  Term.finitePolynomial_mass _ _

theorem source_identity (P : Readers) (c : List Bool) (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (start P c) (program P c) (output P c)).map
        (Int.castRingHom ℂ) = rename Fin.val
          ((CoordinateSlicePolynomial.family (BoundedRegularSource.polynomial (original P c) (size P c) (size P c) (P.radius c))).map
            (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (sample P c : ℂ))) := by
  rw [program, output, BoundedSource.symbolic_output (size P c) (start P c) (P.dim c + 1) (sample P c)
    (TermView.term (P.source c)) (2 * P.radius c).bits (scaleExponent P c).bits (shiftExponent P c).bits
      (degree P c - 1).bits (regularizationExponent P c).bits
        (Term.arity_le_dataSize _) (Nat.le_max_left ..) (Nat.le_max_right ..)]
  exact BoundedSampledIdentity.source_identity _ _ (Term.toPolynomial_eq_rename_finitePolynomial _ _ ht) _ _ _ _

theorem sampled_source_identity (P : Readers) (c : List Bool) (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (start P c) (program P c) (output P c)).map
        (Int.castRingHom ℂ) = rename Fin.val
          (FermatSweepCertificate.sampledPolynomial ((lower P c).map (Int.castRingHom ℚ)) (leading P c : ℚ)
            (degree P c) (P.record c)) := by
  rw [source_identity P c ht]
  exact congrArg (rename Fin.val) (BoundedSampledIdentity.slice_fermat_eq (lower P c) (leading P c) (degree P c) (P.record c))

theorem polynomial_source_identity (P : Readers) (c : List Bool) (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    (BoundedSource.polynomial (P.dim c + 1) (sample P c) (TermView.term (P.source c))
      (2 * P.radius c).bits (scaleExponent P c).bits (shiftExponent P c).bits
      (degree P c - 1).bits (regularizationExponent P c).bits).map (Int.castRingHom ℂ) = rename Fin.val
        (FermatSweepCertificate.sampledPolynomial ((lower P c).map (Int.castRingHom ℚ)) (leading P c : ℚ)
          (degree P c) (P.record c)) :=
  (BoundedSampledIdentity.source_identity _ _ (Term.toPolynomial_eq_rename_finitePolynomial _ _ ht) _ _ _ _).trans
    (congrArg (rename Fin.val) (BoundedSampledIdentity.slice_fermat_eq (lower P c) (leading P c) (degree P c) (P.record c)))

theorem regular {L : Type*} [Field L] [Algebra ℚ L] (P : Readers) (c : List Bool) (x : Fin (P.dim c + 4) → L)
    (hx : (BoundedRegularSource.polynomial (original P c) (size P c) (size P c) (P.radius c)).eval₂
      (Int.castRingHom L) x = 0) :
    ∃ j, (pderiv j (BoundedRegularSource.polynomial (original P c) (size P c) (size P c) (P.radius c))).eval₂
      (Int.castRingHom L) x ≠ 0 :=
  BoundedRegularSource.regular _ _ _ _ (original_degree P c) (original_mass P c) x hx

end LeanCanny.Encoding.BoundedSourceWriter
