/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutCoefficientSign
public import LeanCanny.Algebra.IntegralMixedCutCoefficientPolynomialKey
/-! # Every finite cut test specializes through one fixed old homomorphism

Local coefficient/choice indices change neither the old algebra nor its
power schedule. Casts only identify finite coordinate types; all tests
use the literal same old tail of the successor point.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutCommonParent
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedCutCoefficientPolynomialKey.polynomial IntegralMixedFramedChoiceProbeSourceBits.polynomial

private theorem eval_head_congr {a b t : ℕ} (p : MvPolynomial (Fin a) ℤ) (q : MvPolynomial (Fin b) ℤ)
    (hp : HEq p q) (ha : a+1=t) (hb : b+1=t) (z : Fin t→ℝ) :
    p.eval₂ (Int.castRingHom ℝ) (fun i=>z (Fin.cast ha i.succ))=
      q.eval₂ (Int.castRingHom ℝ) (fun i=>z (Fin.cast hb i.succ)) := by
  have hab : a=b := Nat.add_right_cancel (ha.trans hb.symm)
  cases hab
  have hpq:=eq_of_heq hp
  cases hpq
  rfl

private theorem source_query_congr (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (u v : List Bool) (he : u=v) :
    HEq (IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H u)
      (IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H v) := by
  cases he
  rfl

private theorem test_query (P : Parameters) (c d : List Bool) :
    IntegralFramedCutCoefficientTest.query P (pair c d)=IntegralMixedCutCoefficientQueryBits.query P (pair c d) := by
  unfold IntegralFramedCutCoefficientTest.query
  rw [pairFst_pair,pairSnd_pair]


theorem dimension (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (c : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c) :
    (family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)+1=
      (IntegralFramedCutSuccessor.input P D H L F C hs).count c := by
  rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth c]
  exact (IntegralFramedCutSuccessor.active_count P D H c ha).symm

theorem evaluation (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (c : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c) (e k : ℕ)
    (he : e≤2^P.width (RankedHistoryTask.root c)) (hk : k≤2^P.width (RankedHistoryTask.root c))
    (z : Fin ((IntegralFramedCutSuccessor.input P D H L F C hs).count c)→ℝ)
    (φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis.generator i)=
      z (Fin.cast (dimension P D H L F C hs c ha) i.succ)^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
          (2^(family P D H).width (IntegralMixedVirtualTaskBits.saved P c))
          ((family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)) i) :
    (IntegralFramedCutCoefficientTest.polynomial P D H L F C hs c (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))).eval₂
      (Int.castRingHom ℝ) z=φ ((IntegralMixedRelativeCuts.factor ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).birth_bound _) ((family P D H).rule _)
        (IntegralMixedRelativeCuts.atChoice ((family P D H).rule _) ((family P D H).kind _) k)).coeff e) := by
  have HP : HEq
      (IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H
        (IntegralFramedCutCoefficientTest.query P (pair c (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)))))
      (IntegralMixedCutCoefficientPolynomialKey.polynomial (family P D H)
        (IntegralMixedFramedChoiceProbeSourceBits.horizon P c) (IntegralMixedVirtualTaskBits.saved P c) e k) := by
    exact (source_query_congr P D H _ _ (test_query P c _)).trans
      (IntegralMixedCutCoefficientPolynomialKey.packet P D H c e k ha he hk)
  have HE:=eval_head_congr _ _ HP
    (IntegralFramedCutCoefficientTest.dimension_pair P D H L F C hs c
      (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)) ha)
    (dimension P D H L F C hs c ha) z
  exact (IntegralFramedCutCoefficientTest.polynomial_eval P D H L F C hs c
    (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)) ha z).trans
      (HE.trans (IntegralMixedCutCoefficientPolynomialKey.evaluation (family P D H)
        (IntegralMixedFramedChoiceProbeSourceBits.horizon P c) (IntegralMixedVirtualTaskBits.saved P c) e k φ
        (fun i=>z (Fin.cast (dimension P D H L F C hs c ha) i.succ)) hφ))

end LeanCanny.Encoding.IntegralFramedCutCommonParent
