/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest
public import LeanCanny.Algebra.IntegralCoordinateEvaluation
/-! # Native suffix signs specialize through the same old interpretation

A powered canonical representative is evaluated at the literal terminal
tail. This is exactly the old algebra element under the interpretation
constructed from that tail; no separate root or coordinate combination
is substituted.
-/
@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteSuffixElement
open LeanCanny.Algebra LeanCanny.Computation MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [CommRing A] {m N : ℕ}

theorem evaluation (b : IntegralCoordinateBasis A m N) (v : A) (S d : ℕ)
    (φ : A→ₐ[ℤ]ℝ) (z : Fin (d+m)→ℝ)
    (hφ : ∀ i,φ (b.generator i)=z (FixedWidthSuffixLiftBits.shift d i)^
      UniformIntegralPowerSchedule.weights S N m i) :
    (rename (FixedWidthSuffixLiftBits.shift d)
      (CoordinatePowerSubstitution.substitute (UniformIntegralPowerSchedule.weights S N m) (b.representative v))).eval₂
        (Int.castRingHom ℝ) z=φ v := by
  rw [FixedWidthSuffixLiftBits.evaluation,CoordinatePowerSubstitution.eval_substitute]
  have HE:=b.representative_eval_algHom v φ
  change (b.representative v).eval₂ (Int.castRingHom ℝ) (fun i=>φ (b.generator i))=φ v at HE
  simpa only [hφ] using HE

theorem packet {F : SquareSampleInput.Inputs} (T : SquareSampleCompleteSuffixPolynomialTest.Source F)
    (c w d : List Bool) (hv : SquareSampleCompleteVertices.Valid F c w)
    (b : IntegralCoordinateBasis A (T.arity c d) N) (v : A) (S : ℕ) (φ : A→ₐ[ℤ]ℝ)
    (hp : T.polynomial c d=CoordinatePowerSubstitution.substitute
      (UniformIntegralPowerSchedule.weights S N (T.arity c d)) (b.representative v))
    (hφ : ∀ i,φ (b.generator i)=
      (SquareSampleCompleteVertices.candidate F c w hv).val
        (Fin.cast (T.dimension c d) (FixedWidthSuffixLiftBits.shift (T.newer c d) i))^
          UniformIntegralPowerSchedule.weights S N (T.arity c d) i) :
    SquareSampleCompleteIndexedPolynomialTest.value F (SquareSampleCompleteSuffixPolynomialTest.test T)
      (pair (pair c w) d)=InfinitesimalSign.encode (SignType.sign (φ v)) := by
  rw [SquareSampleCompleteSuffixPolynomialTest.packet T c w d hv,hp,
    CoordinatePowerSubstitution.eval_substitute]
  have HE:=b.representative_eval_algHom v φ
  change (b.representative v).eval₂ (Int.castRingHom ℝ) (fun i=>φ (b.generator i))=φ v at HE
  rw [←funext hφ,HE]

end LeanCanny.Encoding.SquareSampleCompleteSuffixElement
