/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
public import LeanCanny.Algebra.IntegralMixedRetainedRealBound
public import LeanCanny.Encoding.IntegralFramedCompleteSquare
public import LeanCanny.Encoding.SquareSampleCompleteVertices

/-! # Actual joint prefix roots have original-controlled bank coordinates

The interpreting hom is constructed from the joint row root. The retained
matrix height then bounds its characteristic polynomial, and actual nonzero
integer denominators cannot enlarge the real quotient.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedBankPointBound
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedBankObservation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

theorem point_bound {n S B m G : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (HC : Canonical x) (HG : x.bank.Bounds G)
    (z : Fin m→ℝ) (hz : ∀ i,(x.sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ) z=0) (i : ℕ) :
    |(ofState x).point (extend z) i|≤(2:ℝ)^IntegralMixedRetainedRealBound.height (FixedWidthPolynomial.count m B) G := by
  by_cases hi : i<m
  · obtain ⟨φ,hφ⟩:=x.sampler.scalarPrefix.interpret ℝ z hz
    rw [point_ofState x z ⟨i,hi⟩,←IntegralMixedCanonicalBankPoint.quotient_eq x HC z φ hφ ⟨i,hi⟩]
    exact IntegralMixedRetainedRealBound.quotient x HG φ ⟨i,hi⟩
  · change |if h : i<m then (extend z i)^UniformIntegralPowerSchedule.weights S (2^B) m ⟨i,h⟩/
        (x.bank.denominator ⟨i,h⟩:ℝ) else 0|≤_
    rw [dite_eq_right hi,abs_zero]
    positivity

noncomputable def height (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (key : List Bool) : ℕ :=
  IntegralMixedRetainedRealBound.height
    (FixedWidthPolynomial.count ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth key) (P.width (pairFst key)))
    (IntegralMixedFramedStepHeight.familyHeight P L F C key)

theorem height_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    {L F C : List Bool→ℕ} (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) :
    BinaryFn (height P D H L F C) := by
  have HB : UnaryFn (fun key=>(IntegralMixedFramedHistoryFamilyBits.family P D H).birth key) :=
    UnaryFn.of_eq (IntegralMixedFullHistoryFamilyBits.prefix_unary P a)
      (fun key=>(IntegralMixedFramedHistoryFamilyBits.family_birth P D H key).symm)
  exact IntegralMixedRetainedRealBound.height_binary
    (((BinaryFn.const 2).powUnary (a.width.comp pairFst_mem_FP)).powUnary HB)
    (IntegralMixedFramedStepHeight.familyHeight_binary P a hL hF hC)

theorem sample_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool)
    (hpos : ∀ u,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key u))
    (u w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralFramedCompleteSquare.input P D H L F C h key hpos) u w)
    (i : ℕ) :
    |(ofState ((IntegralMixedFramedHistoryFamilyBits.family P D H).state (key u))).point
      (extend (SquareSampleCompleteVertices.candidate (IntegralFramedCompleteSquare.input P D H L F C h key hpos) u w hw).val) i|≤
      (2:ℝ)^height P D H L F C (key u) := by
  apply point_bound _ (IntegralMixedFramedHistoryFamilyBits.family_canonical P D H (key u))
    (IntegralMixedFramedStepHeight.family_bank_bounds P D H L F C h (key u))
  exact (SquareSampleCompleteVertices.candidate _ u w hw).property

end LeanCanny.Geometry.IntegralMixedFramedBankPointBound
