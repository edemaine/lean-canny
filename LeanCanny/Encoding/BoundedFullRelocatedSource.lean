/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullWriter
public import LeanCanny.Encoding.BoundedFullGeometry
public import LeanCanny.ETR.ComplexInputRelocationEncoding

/-! # The original full source after a parent input block

The native circuit computes the same ambient source and marking polynomial
in a child block. Its source and derivative identities use the original
polynomials, retaining shared gates throughout.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullRelocatedSource
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Geometry MvPolynomial
open LeanCanny.Encoding.Brackets

noncomputable def program (P : BoundedFullWriter.Readers) (offset base : List Bool → ℕ) (c : List Bool) : List Operation :=
  InputRelocation.program (offset c) (base c) (BoundedFullWriter.start P c) (BoundedFullWriter.program P c)

noncomputable def output (P : BoundedFullWriter.Readers) (base : List Bool → ℕ) (c : List Bool) : ℕ :=
  base c + 1 + BoundedFullWriter.output P c

noncomputable def markOutput (P : BoundedFullWriter.Readers) (base : List Bool → ℕ) (c : List Bool) : ℕ :=
  base c + 1 + BoundedFullWriter.markOutput P c

theorem length_unary {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (offset base : List Bool → ℕ) : UnaryFn (fun c => (program P offset base c).length) :=
  (((UnaryFn.const 1).add (BoundedFullWriter.start_unary h)).add (BoundedFullWriter.length_unary h)).of_eq
    (fun _ => (InputRelocation.program_length _ _ _ _).symm)

theorem output_unary {P : BoundedFullWriter.Readers} (h : P.PolyTime) {base : List Bool → ℕ}
    (hb : UnaryFn base) : UnaryFn (output P base) :=
  (hb.add (UnaryFn.const 1)).add (BoundedFullWriter.output_unary h)

theorem markOutput_unary {P : BoundedFullWriter.Readers} (h : P.PolyTime) {base : List Bool → ℕ}
    (hb : UnaryFn base) : UnaryFn (markOutput P base) :=
  (hb.add (UnaryFn.const 1)).add (BoundedFullWriter.markOutput_unary h)

theorem encode_mem_FP {P : BoundedFullWriter.Readers} (h : P.PolyTime) {offset base : List Bool → ℕ}
    (ho : UnaryFn offset) (hb : UnaryFn base) :
    (fun c => encode (StraightLine.gates (base c) (program P offset base c))) ∈ FP :=
  InputRelocation.program_encode_mem_FP ho hb (BoundedFullWriter.start_unary h) (BoundedFullWriter.encode_mem_FP h)

theorem wellFormed (P : BoundedFullWriter.Readers) (offset base : List Bool → ℕ) (c : List Bool)
    (ho : offset c + BoundedFullWriter.start P c ≤ base c) :
    StraightLine.WellFormed (base c) (program P offset base c) :=
  InputRelocation.wellFormed _ _ _ _ ho (BoundedFullWriter.wellFormed P c)

theorem output_lt (P : BoundedFullWriter.Readers) (offset base : List Bool → ℕ) (c : List Bool) :
    output P base c < base c + (program P offset base c).length := by
  have h := BoundedFullWriter.output_lt P c
  unfold output program
  rw [InputRelocation.program_length]
  omega

theorem markOutput_lt (P : BoundedFullWriter.Readers) (offset base : List Bool → ℕ) (c : List Bool) :
    markOutput P base c < base c + (program P offset base c).length := by
  have h := BoundedFullWriter.markOutput_lt P c
  unfold markOutput program
  rw [InputRelocation.program_length]
  omega

noncomputable def polynomial (P : BoundedFullWriter.Readers) (c : List Bool) :=
  BoundedFullGeometry.polynomial (BoundedFullWriter.original P c) (BoundedFullWriter.size P c)
    (BoundedFullWriter.size P c) (P.radius c)

theorem source_identity (P : BoundedFullWriter.Readers) (offset base : List Bool → ℕ) (c : List Bool)
    (ho : offset c + BoundedFullWriter.start P c ≤ base c)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (base c)
      (program P offset base c) (output P base c) =
        rename (fun i : Fin (P.dim c + 4) => offset c + i.val) (polynomial P c) := by
  rw [program, output, InputRelocation.symbolic _ _ _ _ ho (BoundedFullWriter.wellFormed P c) _ (BoundedFullWriter.output_lt P c),
    BoundedFullGeometry.source_identity P c ht, rename_rename]
  rfl

theorem mark_identity (P : BoundedFullWriter.Readers) (offset base : List Bool → ℕ) (c : List Bool)
    (ho : offset c + BoundedFullWriter.start P c ≤ base c)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (base c)
      (program P offset base c) (markOutput P base c) =
        rename (fun i : Fin (P.dim c + 4) => offset c + i.val)
          (BoundedFullGeometry.markPolynomial (BoundedFullWriter.original P c) (P.radius c)) := by
  rw [program, markOutput, InputRelocation.symbolic _ _ _ _ ho (BoundedFullWriter.wellFormed P c) _ (BoundedFullWriter.markOutput_lt P c),
    BoundedFullGeometry.mark_identity P c ht, rename_rename]
  rfl

theorem derivative_identity (P : BoundedFullWriter.Readers) (offset base : List Bool → ℕ) (c : List Bool)
    (ho : offset c + BoundedFullWriter.start P c ≤ base c)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) (j : Fin (P.dim c + 4)) :
    pderiv (offset c + j.val) (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (base c)
      (program P offset base c) (output P base c)) =
        rename (fun i : Fin (P.dim c + 4) => offset c + i.val) (pderiv j (polynomial P c)) := by
  rw [source_identity P offset base c ho ht]
  exact pderiv_rename (fun i k h => Fin.val_injective (Nat.add_left_cancel h)) j _

end LeanCanny.Encoding.BoundedFullRelocatedSource
