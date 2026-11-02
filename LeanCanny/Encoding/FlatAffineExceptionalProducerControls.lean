/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalIntegerMetadata
public import LeanCanny.Algebra.IntegralMixedHeaderPhysicalMetadata
public import LeanCanny.Algebra.IntegralMixedFullProducerSpaceCanonical
/-! # Actual initial-bank histories supply all relaxed producer controls

Original integer coefficients and exact degrees are charged in space. The
initial bank headers are generated without evaluating those polynomials.
Later syntax, fallback-table readback and uniform room/width planning are
explicit parameters; this is not an end-to-end frontend totalization claim.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalIntegerProducer
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width)
open IntegralMixedCommandHeaderBits
open scoped Classical

theorem controls (P : Parameters) (a : Access P) (base : IntegralMixedFullHistoryFamilyBits.Data P)
    {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (input : List Bool → List Bool) (hi : input ∈ FP)
    (later : (root : List Bool) → List (Command (base.spatial root) (P.width root)))
    (hlater : (fun root => words (later root)) ∈ FP)
    (hW : ∀ root, width F (input root) ≤ P.width root)
    (hroom : ∀ root, (later root).length + births F (input root) + 2 ≤ P.cap root + 1)
    (hno : ∀ root c, c ∈ later root → c.context ≠ 0)
    (fallback : List Bool → List Bool) (hfallback : fallback ∈ FP)
    (hr : ∀ key, WordList.get (fallback (pairFst key)) (IntegralMixedHeaderTablesBits.fallbackIndex P key) =
      encode (IntegralMixedCommandHeaderBits.selection (base.fallback key))) :
    IntegralMixedFullProducerSpaceBits.Controls P (data P base F C h input later hW hroom) := by
  let D := data P base F C h input later hW hroom
  let T : IntegralMixedHeaderTablesBits.Tables := ⟨fun root => words (D.rules root), fallback⟩
  have HA : IntegralMixedHeaderTablesBits.Access T :=
    ⟨FlatAffineExceptionalIntegerHeaders.data_headers_FP P base hF C h input hi later hlater hW hroom, hfallback⟩
  have HR : IntegralMixedHeaderTablesBits.Represents P D T := ⟨fun _ => rfl, hr⟩
  exact {
    full := IntegralMixedHeaderTablesBits.fullMetadata P a D T HA HR
    integer := original P a base hF C h hh input hi later hW hroom hno
    physical := IntegralMixedHeaderTablesBits.physicalInputMetadata P a D T HA HR }

end LeanCanny.Encoding.FlatAffineExceptionalIntegerProducer
