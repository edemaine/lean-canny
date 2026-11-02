/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutCoefficientElement
public import LeanCanny.Algebra.IntegralMixedFramedChoiceProbePolynomial
/-! # All coefficient probes have one actual old algebra and power schedule -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutCoefficientPolynomialKey
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

noncomputable def polynomial (G : IntegralMixedCutSource.Family) (S : ℕ) (key : List Bool) (e k : ℕ) :=
  CoordinatePowerSubstitution.substitute (UniformIntegralPowerSchedule.weights S (2^G.width key) (G.birth key))
    (((G.state key).sampler.scalarPrefix.basis).representative
      ((IntegralMixedRelativeCuts.factor (G.state key) (G.birth_bound key) (G.rule key)
        (IntegralMixedRelativeCuts.atChoice (G.rule key) (G.kind key) k)).coeff e))

private theorem key_congr (G : IntegralMixedCutSource.Family) (S T : ℕ) (u v : List Bool)
    (hS : S=T) (hu : u=v) (e k : ℕ) : HEq (polynomial G S u e k) (polynomial G T v e k) := by
  cases hS
  cases hu
  rfl

theorem active (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (hq : IntegralMixedFramedFullCutProbeBits.Active P q) :
    IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H q=
      polynomial (family P D H) (IntegralMixedFramedChoiceProbeSourceBits.horizon P q)
        (IntegralMixedVirtualTaskBits.saved P q) (get P .coefficient q) (IntegralMixedRawKindChoiceBits.requested P q) := by
  unfold IntegralMixedFramedChoiceProbeSourceBits.polynomial IntegralCoordinateCoefficientBits.Family.poweredPolynomial
    IntegralCoordinateCoefficientBits.Family.polynomial polynomial
  simp only [IntegralMixedFramedChoiceProbeSourceBits.source,ite_eq_left hq]

theorem packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (e k : ℕ) (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (he : e≤2^P.width (RankedHistoryTask.root c)) (hk : k≤2^P.width (RankedHistoryTask.root c)) :
    HEq (IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H
      (IntegralMixedCutCoefficientQueryBits.query P (pair c (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)))))
      (polynomial (family P D H) (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
        (IntegralMixedVirtualTaskBits.saved P c) e k) := by
  let q:=IntegralMixedCutCoefficientQueryBits.query P (pair c (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)))
  have hqa : IntegralMixedFramedFullCutProbeBits.Active P q :=
    (IntegralMixedCutCoefficientQueryBits.query_active P _).mpr (by simpa only [pairFst_pair] using ha)
  have HE:=active P D H q hqa
  unfold IntegralMixedRawKindChoiceBits.requested at HE
  rw [IntegralMixedCutCoefficientQueryBits.coefficient_packet P c e k he,
    IntegralMixedCutCoefficientQueryBits.choice_packet P c e k hk] at HE
  have HS : IntegralMixedVirtualTaskBits.saved P q=IntegralMixedVirtualTaskBits.saved P c :=
    (IntegralMixedCutCoefficientQueryBits.query_saved P _).trans
      (congrArg (IntegralMixedVirtualTaskBits.saved P) (pairFst_pair _ _))
  have HH : IntegralMixedFramedChoiceProbeSourceBits.horizon P q=IntegralMixedFramedChoiceProbeSourceBits.horizon P c :=
    congrArg (fun root=>P.cap root+1) ((IntegralMixedCutCoefficientQueryBits.query_root P _).trans (congrArg RankedHistoryTask.root (pairFst_pair _ _)))
  exact (heq_of_eq HE).trans (key_congr _ _ _ _ _ HH HS e k)

theorem evaluation (G : IntegralMixedCutSource.Family) (S : ℕ) (key : List Bool) (e k : ℕ)
    (φ : (G.state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : Fin (G.birth key)→ℝ)
    (hφ : ∀ i,φ ((G.state key).sampler.scalarPrefix.basis.generator i)=
      z i^UniformIntegralPowerSchedule.weights S (2^G.width key) (G.birth key) i) :
    (polynomial G S key e k).eval₂ (Int.castRingHom ℝ) z=
      φ ((IntegralMixedRelativeCuts.factor (G.state key) (G.birth_bound key) (G.rule key)
        (IntegralMixedRelativeCuts.atChoice (G.rule key) (G.kind key) k)).coeff e) := by
  have HS:=CoordinatePowerSubstitution.eval_substitute (Int.castRingHom ℝ)
    (UniformIntegralPowerSchedule.weights S (2^G.width key) (G.birth key))
    (((G.state key).sampler.scalarPrefix.basis).representative
      ((IntegralMixedRelativeCuts.factor (G.state key) (G.birth_bound key) (G.rule key)
        (IntegralMixedRelativeCuts.atChoice (G.rule key) (G.kind key) k)).coeff e)) z
  have HE:=((G.state key).sampler.scalarPrefix.basis).representative_eval_algHom
    ((IntegralMixedRelativeCuts.factor (G.state key) (G.birth_bound key) (G.rule key)
        (IntegralMixedRelativeCuts.atChoice (G.rule key) (G.kind key) k)).coeff e) φ
  change (((G.state key).sampler.scalarPrefix.basis).representative
    ((IntegralMixedRelativeCuts.factor (G.state key) (G.birth_bound key) (G.rule key)
        (IntegralMixedRelativeCuts.atChoice (G.rule key) (G.kind key) k)).coeff e)).eval₂ (Int.castRingHom ℝ)
      (fun i=>φ ((G.state key).sampler.scalarPrefix.basis.generator i))=_ at HE
  exact HS.trans (by simpa only [hφ] using HE)

end LeanCanny.Algebra.IntegralMixedCutCoefficientPolynomialKey
