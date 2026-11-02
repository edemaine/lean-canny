/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeSpace
public import LeanCanny.Algebra.FermatLevelFramedTiltedSyntax
public import LeanCanny.Algebra.IntegralMixedFramedIntegerSyntax
/-! # Original syntax supplies all leaves of the changing-source controller

The original terms, unit-selector bodies, and integer words are read at the
full saved key. Large powers remain implicit binary exponents. Source identities
are literal polynomial and rule identities; no interpreted matrix, current
height, or recursive evaluator cost is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction)
open scoped Classical

structure Syntax (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  unit : IntegralMixedFramedUnitControlsBits.Controls P D H
  term : List Bool → ETR.Term
  frozen : List Bool → ℕ
  tilt : List Bool → ℕ
  exponent : List Bool → ℕ
  term_FP : (fun key => (term key).toData.toBits) ∈ FP
  frozen_native : UnaryFn frozen
  tilt_native : UnaryFn tilt
  exponent_native : BinaryFn exponent
  term_scope : ∀ key, (term key).arity+1 ≤ FermatLevelFramedSpatialBits.ambient P key
  tilt_scope : ∀ key, tilt key+2 ≤ FermatLevelFramedSpatialBits.ambient P key
  low : ∀ key, (instruction P D key).source.low = FermatLevelFramedTiltedSyntax.low P term frozen tilt exponent key
  integerWord : List Bool → List Bool
  integer_FP : integerWord ∈ FP
  integer : ∀ key, ETR.IntegerUnivariateTermSource.polynomial integerWord key = IntegralMixedFramedIntegerBits.polynomial P D key
  nodes : List Bool → ℕ
  factor : List Bool → ℕ
  seed : List Bool → ℕ
  nodes_native : BinaryFn nodes
  factor_native : BinaryFn factor
  seed_native : BinaryFn seed

noncomputable def Controls.ofSyntax (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Syntax P D H) : Controls P D H where
  scalar := IntegralMixedFramedFullScalarBits.Controls.ofUnit P a D H s.unit
  critical := FermatLevelFramedTiltedSyntax.controls P a D H s.unit.tables s.unit.native s.unit.represents
    s.term s.frozen s.tilt s.exponent s.term_FP s.frozen_native s.tilt_native s.exponent_native
    s.term_scope s.tilt_scope s.low
  normalization := {
    tables := s.unit.tables
    native := s.unit.native
    represents := s.unit.represents
    nodes := s.nodes
    factor := s.factor
    seed := s.seed
    nodes_native := s.nodes_native
    factor_native := s.factor_native
    seed_native := s.seed_native }
  producer := IntegralMixedFramedIntegerSyntaxBits.controls P a D H s.unit.tables s.unit.native s.unit.represents
    s.integerWord s.integer_FP s.integer

theorem syntax_model_space (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Syntax P D H)
    (hb : Bounds P D H (Controls.ofSyntax P a D H s)) :
    SpaceFunction (machine P a D H (Controls.ofSyntax P a D H s)).model :=
  model_space P a D H (Controls.ofSyntax P a D H s) hb

end LeanCanny.Algebra.IntegralMixedFramedNativeBits
