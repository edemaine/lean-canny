/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSquarePoint
public import LeanCanny.Algebra.IntegralMixedFramedIntegerRealization
/-! # One full complete vertex retains every value of an actual realization

Unlike scalar-only sampling this retains all physical and multiplier
rows. Realizes supplies an actual full-row root; a fresh complete word is
chosen for the reindexed SAME tuple and reads all bank quotients together.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open IntegralMixedFramedPhysicalIndex (enumerate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
  (c : List Bool) (values : ℕ→ℝ)

theorem exists_realized (hv : IntegralMixedIntegerRealization.Realizes ((family P D H).state (key c)) values) :
    ∃w,∃hw : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w,
      w.length=SquareSampleCompleteVertices.width (input P D H L F C hs key hpos) c ∧
      ∀i : Fin ((family P D H).birth (key c)),point P D H L F C hs key hpos c w hw i=values i.val :=by
  obtain ⟨y,φ,hy,hφ,hvalues⟩:=hv
  let e:=enumerate (commands P D (key c))
  let z : Fin (count P D (key c))→ℝ:=y∘e.symm
  have HE : z∘e=y :=by funext i; exact congrArg y (e.symm_apply_apply i)
  have HZ : ∀i,((sampler P D H (key c)).rows i).eval₂ (Int.castRingHom ℝ) z=0 :=by
    apply (PolynomialSystemReindex.roots_iff (Int.castRingHom ℝ) e
      ((family P D H).state (key c)).sampler.rows z).mpr
    rw [HE]
    exact hy
  obtain ⟨w,hw,hz⟩:=exists_joint P D H L F C hs key hpos c z HZ
  refine ⟨w,hw,(Classical.choose hw).1,fun i=>?_⟩
  have HP:=LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.quotient_eq
    ((family P D H).state (key c)) (IntegralMixedFramedHistoryFamilyBits.family_canonical P D H (key c))
    (y∘((family P D H).state (key c)).sampler.scalar) φ hφ i
  have HR : point P D H L F C hs key hpos c w hw i=
      LeanCanny.Geometry.IntegralMixedFullBankPoint.point ((family P D H).state (key c)) y i :=by
    unfold point LeanCanny.Geometry.IntegralMixedFullBankPoint.indexedPoint
    rw [hz]
    change LeanCanny.Geometry.IntegralMixedFullBankPoint.point ((family P D H).state (key c)) (z∘e) i=_
    rw [HE]
  exact HR.trans (HP.symm.trans (hvalues i))
end LeanCanny.Encoding.IntegralFramedPhysicalSquare
