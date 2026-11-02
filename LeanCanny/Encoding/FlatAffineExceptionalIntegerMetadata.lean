/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalIntegerHeaders
/-! # Metadata for the constructed actual initial-bank history

The initial command-header writer is derived rather than supplied. The
remaining word writer describes later critical/cut syntax. Fallback table
construction and its exact total readback remain explicit frontend work.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalIntegerHeaders
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width)
open IntegralMixedCommandHeaderBits
open scoped Classical

theorem metadata (P : Parameters) (a : Access P) (base : IntegralMixedFullHistoryFamilyBits.Data P)
    {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (input : List Bool → List Bool) (hi : input ∈ FP)
    (later : (root : List Bool) → List (Command (base.spatial root) (P.width root)))
    (hlater : (fun root => words (later root)) ∈ FP)
    (hW : ∀ root, width F (input root) ≤ P.width root)
    (hroom : ∀ root, (later root).length + births F (input root) + 2 ≤ P.cap root + 1)
    (fallback : List Bool → List Bool) (hfallback : fallback ∈ FP)
    (hr : ∀ key, WordList.get (fallback (pairFst key)) (IntegralMixedHeaderTablesBits.fallbackIndex P key) =
      encode (IntegralMixedCommandHeaderBits.selection (base.fallback key))) :
    IntegralMixedFullHistoryFamilyBits.Metadata P
        (FlatAffineExceptionalIntegerProducer.data P base F C h input later hW hroom) ∧
      IntegralMixedRawKindBits.Metadata (IntegralMixedFullHistoryFamilyBits.family P
        (FlatAffineExceptionalIntegerProducer.data P base F C h input later hW hroom)) := by
  let D := FlatAffineExceptionalIntegerProducer.data P base F C h input later hW hroom
  let T : IntegralMixedHeaderTablesBits.Tables := ⟨fun root => words (D.rules root), fallback⟩
  have HA : IntegralMixedHeaderTablesBits.Access T :=
    ⟨data_headers_FP P base hF C h input hi later hlater hW hroom, hfallback⟩
  have HR : IntegralMixedHeaderTablesBits.Represents P D T := ⟨fun _ => rfl, hr⟩
  exact ⟨IntegralMixedHeaderTablesBits.fullMetadata P a D T HA HR,
    IntegralMixedHeaderTablesBits.rawMetadata P a D T HA HR⟩

end LeanCanny.Encoding.FlatAffineExceptionalIntegerHeaders
