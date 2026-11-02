/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCanonicalCompleteVertex
public import LeanCanny.Encoding.IntegralFramedCompleteSquare
public import LeanCanny.Algebra.IntegralMixedFramedScalarPrefix

/-! # Joint-root labels for actual framed prefixes with critical instructions

One complete-prefix vertex encodes the entire correlated old bank. The
underlying square system is the literal actual native coefficient prefix,
with no chosen coordinate roots or physical critical-root lift.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedPrefixVertex
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedStepHeight
open IntegralMixedCanonicalCompleteVertex

 theorem exists_vertex (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (h : FamilyInputs P D L F C) (key : List Bool→List Bool)
    (hpos : ∀ u,0<(family P D H).birth (key u)) (u : List Bool)
    (z : Fin ((family P D H).birth (key u))→ℝ)
    (hz : ∀ i,(((family P D H).state (key u)).sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : ((family P D H).state (key u)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (((family P D H).state (key u)).sampler.scalarPrefix.basis.generator i)=
      z i^UniformIntegralPowerSchedule.weights (P.cap (pairFst (key u))+1) (2^P.width (pairFst (key u)))
        ((family P D H).birth (key u)) i) :
    let Q:=IntegralFramedCompleteSquare.input P D H L F C h key hpos
    ∃ w : List Bool,∃ hw : SquareSampleCompleteVertices.Valid Q u w,
      w.length=SquareSampleCompleteVertices.width Q u ∧ tuple Q u w hw rfl=z ∧
      ∀ i,φ (((family P D H).state (key u)).bank.numerator i)/
          (((family P D H).state (key u)).bank.denominator i:ℝ)=
        IntegralMixedCanonicalBankPoint.point ((family P D H).state (key u)) (tuple Q u w hw rfl) i :=
  IntegralMixedCanonicalCompleteVertex.exists_vertex ((family P D H).state (key u)) (family_canonical P D H (key u))
    (IntegralFramedCompleteSquare.input P D H L F C h key hpos)
    (IntegralFramedCompleteSquare.complete P D H L F C h key hpos) u rfl
    (IntegralFramedCompleteSquare.rows_heq P D H L F C h key hpos u) z hz φ hφ

end LeanCanny.Geometry.IntegralMixedFramedPrefixVertex
