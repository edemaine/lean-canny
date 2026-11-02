/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCanonicalBankPoint
public import LeanCanny.Encoding.SquareSampleCompleteVertices

/-! # Complete native vertices retain a canonical joint bank point

A vertex is chosen from an actual simultaneous row root. Completeness of
coordinate annihilators gives its short ordinal word, while candidate_word
recovers the same joint tuple and hence the same bank quotients.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedCanonicalCompleteVertex
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open scoped Classical

theorem transport_roots {a b : ℕ} (h : a=b)
    (f : Fin a→MvPolynomial (Fin a) ℤ) (g : Fin b→MvPolynomial (Fin b) ℤ)
    (he : HEq f g) (z : Fin b→ℝ)
    (hz : ∀ i,(g i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∀ i,(f i).eval₂ (Int.castRingHom ℝ) (z ∘ Fin.cast h)=0 := by
  cases h
  have H : f=g := eq_of_heq he
  cases H
  exact hz

noncomputable def root {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (F : SquareSampleInput.Inputs) (u : List Bool)
    (hm : F.count u=m) (hr : HEq (F.system u) x.sampler.scalarPrefix.rows)
    (z : Fin m→ℝ) (hz : ∀ i,(x.sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    SquareSampleComplete.Roots F u :=
  ⟨z ∘ Fin.cast hm,transport_roots hm _ _ hr z hz⟩

noncomputable def tuple (F : SquareSampleInput.Inputs) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F u w) {m : ℕ} (hm : F.count u=m) : Fin m→ℝ :=
  (SquareSampleCompleteVertices.candidate F u w hw).val ∘ Fin.cast hm.symm

private theorem cast_cancel {a b : ℕ} (h : a=b) (z : Fin b→ℝ) :
    (z ∘ Fin.cast h) ∘ Fin.cast h.symm=z := by
  cases h
  rfl

theorem exists_vertex {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (H : Canonical x) (F : SquareSampleInput.Inputs)
    (hF : SquareSampleComplete.Complete F) (u : List Bool)
    (hm : F.count u=m) (hr : HEq (F.system u) x.sampler.scalarPrefix.rows)
    (z : Fin m→ℝ) (hz : ∀ i,(x.sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=
      z i^UniformIntegralPowerSchedule.weights S (2^B) m i) :
    ∃ w : List Bool, ∃ hw : SquareSampleCompleteVertices.Valid F u w,
      w.length=SquareSampleCompleteVertices.width F u ∧ tuple F u w hw hm=z ∧
      ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=
        IntegralMixedCanonicalBankPoint.point x (tuple F u w hw hm) i := by
  let r:=root x F u hm hr z hz
  let w:=SquareSampleCompleteVertices.word F hF u r
  have hw:=SquareSampleCompleteVertices.word_valid F hF u r
  have HT : tuple F u w hw hm=z := by
    unfold tuple
    rw [SquareSampleCompleteVertices.candidate_word]
    exact cast_cancel hm z
  refine ⟨w,hw,?_,HT,?_⟩
  · exact (Classical.choose hw).1
  · intro i
    rw [HT]
    exact IntegralMixedCanonicalBankPoint.quotient_eq x H z φ hφ i

end LeanCanny.Geometry.IntegralMixedCanonicalCompleteVertex
