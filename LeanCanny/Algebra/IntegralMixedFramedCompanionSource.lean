/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryProducer
public import LeanCanny.Algebra.PaddedIntegralGeneratorSource
/-! # Literal creating companions of changing-source instructions

The source uses the actual retained older state, reframed at its own creating
instruction. Earlier commands remain interpreted under their original sources.
This is a semantic source description, not an assumed matrix evaluator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction)
open scoped Classical

noncomputable abbrev bank (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedFramedHistoryFamilyBits.family P D H

noncomputable def source (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    PaddedIntegralGeneratorSource.Source where
  arity := (bank P D H).birth
  width := (bank P D H).width
  carrier key := ((bank P D H).state key).sampler.scalarPrefix.carrier
  ring key := ((bank P D H).state key).sampler.scalarPrefix.ring
  nontrivial key := ((bank P D H).state key).sampler.scalarPrefix.nontrivial
  basis key := ((bank P D H).state key).sampler.scalarPrefix.basis
  polynomial key := IntegralMixedFullHistoryScript.polynomial ((bank P D H).state key)
    ((bank P D H).birth_bound key) (instruction P D key).command
  degree key := IntegralMixedFullHistoryScript.degree ((bank P D H).state key)
    ((bank P D H).birth_bound key) (instruction P D key).command

noncomputable def leading (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) : ℤ :=
  IntegralMixedFullHistoryScript.leading ((bank P D H).state key) ((bank P D H).birth_bound key) (instruction P D key).command

noncomputable def rank (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  count ((source P D H).arity (IntegralMixedVirtualTaskBits.saved P q)+1) ((source P D H).width (IntegralMixedVirtualTaskBits.saved P q))
noncomputable def row (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : Fin (rank P D H q) :=
  ⟨get P .row q%rank P D H q,Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
noncomputable def col (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : Fin (rank P D H q) :=
  ⟨get P .col q%rank P D H q,Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  residueBits ((source P D H).matrix (IntegralMixedVirtualTaskBits.saved P q) (row P D H q) (col P D H q) : ZMod (modulus P q))

attribute [local irreducible] PaddedIntegralGeneratorSource.Source.matrix

theorem value_canonical (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z=value P D H q := by
  unfold value
  exact ⟨_,rfl⟩

noncomputable def matrixAt (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool)
    (p : Polynomial ((bank P D H).state key).sampler.scalarPrefix.carrier) (d : ℕ) :
    Matrix (Fin (count ((bank P D H).birth key+1) ((bank P D H).width key)))
      (Fin (count ((bank P D H).birth key+1) ((bank P D H).width key))) ℤ := by
  let _ := ((bank P D H).state key).sampler.scalarPrefix.ring
  let _ := ((bank P D H).state key).sampler.scalarPrefix.nontrivial
  exact Algebra.leftMulMatrix (PaddedIntegralParameterExtension.coordinateBasis
    ((bank P D H).state key).sampler.scalarPrefix.basis p d).finBasis (AdjoinRoot.root _)

theorem source_matrix (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (source P D H).matrix key=matrixAt P D H key ((source P D H).polynomial key) ((source P D H).degree key) := by
  unfold PaddedIntegralGeneratorSource.Source.matrix source matrixAt
  rfl

end LeanCanny.Algebra.IntegralMixedFramedCompanionBits
