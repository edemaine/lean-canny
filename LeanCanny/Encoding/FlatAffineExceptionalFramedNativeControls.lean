/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalFramedIntegerOriginal
public import LeanCanny.Algebra.IntegralMixedFramedNativeSyntax
/-! # Original syntax and the actual initial bank supply all seven routines

The actual initial integer polynomials use their established original-source
readers, rather than an assumed polynomial word or interpreted coefficient
cost. Other original terms, source identities and unit-selector records are
read at the full saved key. The concrete frontend still supplies its literal
source/rule/header representation and the original script size bounds.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalFramedNative
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan instruction)
open IntegralMixedFramedHistoryScript (Instruction)
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width)
open FlatAffineExceptionalFramedIntegerPrelude (plan)
open scoped Classical

structure Body (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  unit : IntegralMixedFramedUnitControlsBits.Controls P D H
  term : List Bool → ETR.Term
  frozen : List Bool → ℕ
  tilt : List Bool → ℕ
  exponent : List Bool → ℕ
  term_FP : (fun key => (term key).toData.toBits)∈FP
  frozen_native : UnaryFn frozen
  tilt_native : UnaryFn tilt
  exponent_native : BinaryFn exponent
  term_scope : ∀ key, (term key).arity+1≤FermatLevelFramedSpatialBits.ambient P key
  tilt_scope : ∀ key, tilt key+2≤FermatLevelFramedSpatialBits.ambient P key
  low : ∀ key, (instruction P D key).source.low=FermatLevelFramedTiltedSyntax.low P term frozen tilt exponent key
  nodes : List Bool → ℕ
  factor : List Bool → ℕ
  seed : List Bool → ℕ
  nodes_native : BinaryFn nodes
  factor_native : BinaryFn factor
  seed_native : BinaryFn seed

noncomputable def bodyControls (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Body P D H)
    (hi : IntegralMixedIntegerFamilyBits.Original P (IntegralMixedFramedIntegerBits.polynomial P D)) :
    IntegralMixedFramedNativeBits.Controls P D H where
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
  producer := {
    tables := s.unit.tables
    native := s.unit.native
    represents := s.unit.represents
    integer := hi }

noncomputable def controls (P : Parameters) (a : Access P) (base : Plan P)
    {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (input : List Bool → List Bool) (hi : input∈FP)
    (later : (root : List Bool) → List (Instruction (P.ambient root) (P.width root)))
    (hW : ∀ root, width F (input root)≤P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2≤P.cap root+1)
    (hno : ∀ root c, c∈later root → c.command.context≠0)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P (plan P base F C h input later hW hroom))
    (s : Body P (plan P base F C h input later hW hroom) H) :
    IntegralMixedFramedNativeBits.Controls P (plan P base F C h input later hW hroom) H :=
  bodyControls P a _ H s
    (FlatAffineExceptionalFramedIntegerOriginal.original P a base hF C h hh input hi later hW hroom hno)

theorem model_space (P : Parameters) (a : Access P) (base : Plan P)
    {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (input : List Bool → List Bool) (hi : input∈FP)
    (later : (root : List Bool) → List (Instruction (P.ambient root) (P.width root)))
    (hW : ∀ root, width F (input root)≤P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2≤P.cap root+1)
    (hno : ∀ root c, c∈later root → c.command.context≠0)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P (plan P base F C h input later hW hroom))
    (s : Body P (plan P base F C h input later hW hroom) H)
    (hb : IntegralMixedFramedNativeBits.Bounds P (plan P base F C h input later hW hroom) H
      (controls P a base hF C h hh input hi later hW hroom hno H s)) :
    SpaceFunction (IntegralMixedFramedNativeBits.machine P a (plan P base F C h input later hW hroom) H
      (controls P a base hF C h hh input hi later hW hroom hno H s)).model :=
  IntegralMixedFramedNativeBits.model_space P a _ H _ hb

end LeanCanny.Encoding.FlatAffineExceptionalFramedNative
