/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalRealizedVertex
public import LeanCanny.Algebra.IntegralMixedFramedRunObservation
/-! # A fresh complete word preserves the entire prescribed physical tuple

This strengthens bank-value-only realization readback. Every raw physical,
multiplier and scalar column is retained, so equations used by historical
guards can be read on the same tuple after completion.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open IntegralMixedFramedPhysicalIndex (enumerate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P :Parameters) (D :Plan P) (H :IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C :List Bool→ℕ) (hs :IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key :List Bool→List Bool) (hpos :∀c,0<(family P D H).birth (key c))
  (c :List Bool)

theorem exists_raw (y :(family P D H).physical (key c)→ℝ)
    (hy :∀i,(((family P D H).state (key c)).sampler.rows i).eval₂
      (Int.castRingHom ℝ) y=0) :
    ∃w,∃hw :SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w,
      w.length=SquareSampleCompleteVertices.width (input P D H L F C hs key hpos) c ∧
      rawPoint P D H L F C hs key hpos c w hw=y :=by
  let e:=enumerate (commands P D (key c))
  let z :Fin (count P D (key c))→ℝ:=y∘e.symm
  have HE :z∘e=y:=by funext i;exact congrArg y (e.symm_apply_apply i)
  have HZ :∀i,((sampler P D H (key c)).rows i).eval₂ (Int.castRingHom ℝ) z=0:=by
    apply (PolynomialSystemReindex.roots_iff (Int.castRingHom ℝ) e
      ((family P D H).state (key c)).sampler.rows z).mpr
    rw [HE]
    exact hy
  obtain ⟨w,hw,hz⟩:=exists_joint P D H L F C hs key hpos c z HZ
  refine ⟨w,hw,(Classical.choose hw).1,?_⟩
  change joint P D H L F C hs key hpos c w hw∘e=y
  rw [hz]
  exact HE

theorem exists_exact (y :(family P D H).physical (key c)→ℝ)
    (φ :((family P D H).state (key c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hy :∀i,(((family P D H).state (key c)).sampler.rows i).eval₂
      (Int.castRingHom ℝ) y=0)
    (hφ :∀i,φ (((family P D H).state (key c)).sampler.scalarPrefix.basis.generator i)=
      y (((family P D H).state (key c)).sampler.scalar i)^
        UniformIntegralPowerSchedule.weights ((family P D H).cap (key c))
          (2^(family P D H).width (key c)) ((family P D H).birth (key c)) i) :
    ∃w,∃hw :SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w,
      w.length=SquareSampleCompleteVertices.width (input P D H L F C hs key hpos) c ∧
      rawPoint P D H L F C hs key hpos c w hw=y ∧
      ∀i,point P D H L F C hs key hpos c w hw i=
        φ (((family P D H).state (key c)).bank.numerator i)/
          (((family P D H).state (key c)).bank.denominator i:ℝ) :=by
  obtain ⟨w,hw,hlen,hr⟩:=exists_raw P D H L F C hs key hpos c y hy
  refine ⟨w,hw,hlen,hr,?_⟩
  intro i
  change LeanCanny.Geometry.IntegralMixedFullBankPoint.point
    ((family P D H).state (key c)) (rawPoint P D H L F C hs key hpos c w hw) i=_
  rw [hr]
  exact (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.quotient_eq
    ((family P D H).state (key c))
    (IntegralMixedFramedHistoryFamilyBits.family_canonical P D H (key c))
    (y∘((family P D H).state (key c)).sampler.scalar) φ hφ i).symm

private theorem observation_commands (root :List Bool) (cs ds :List (IntegralMixedFramedHistoryScript.Instruction
    (P.ambient root) (P.width root)))
    (hc :cs.length≤P.cap root+1+1) (hd :ds.length≤P.cap root+1+1) (he :cs=ds) :
    IntegralMixedFramedRunObservation.ofCommands (IntegralMixedFramedHistoryFamilyBits.initial P D root) cs hc=
      IntegralMixedFramedRunObservation.ofCommands (IntegralMixedFramedHistoryFamilyBits.initial P D root) ds hd:=by
  cases he
  rfl

/-- Sample the literal natural full-run tuple; no ordinal is reused. -/
theorem exists_full_observation (root :List Bool) (hr :pairFst (key c)=root)
    (hc :IntegralMixedFramedHistoryFamilyBits.prefixLength P (key c)=(D.rules root).length)
    (z :ℕ→ℝ)
    (hz :(IntegralMixedFramedRunObservation.ofCommands
      (IntegralMixedFramedHistoryFamilyBits.initial P D root) (D.rules root)
        (by have HH:=D.room root;omega)).Roots z) :
    ∃w,∃hw :SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w,
      w.length=SquareSampleCompleteVertices.width (input P D H L F C hs key hpos) c ∧
      ∀i :Fin (count P D (key c)),joint P D H L F C hs key hpos c w hw i=z i.val :=by
  cases hr
  have HC :commands P D (key c)=D.rules (pairFst (key c)):=by
    unfold commands
    rw [hc,IntegralMixedFramedHistoryScript.paddedPast_full]
  have HO:=observation_commands P D (pairFst (key c)) (commands P D (key c)) (D.rules (pairFst (key c)))
    (((family P D H).birth_bound (key c)).trans (Nat.le_succ _))
    (by have HH:=D.room (pairFst (key c));omega) HC
  have HZ :∀i,(((family P D H).state (key c)).sampler.rows i).eval₂ (Int.castRingHom ℝ)
      (fun j=>z (enumerate (commands P D (key c)) j).val)=0:=
    (IntegralMixedFramedRunObservation.roots_actual _ _ _ z).mp
      ((congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.Roots z) HO).mpr hz)
  obtain ⟨w,hw,hlen,he⟩:=exists_raw P D H L F C hs key hpos c _ HZ
  refine ⟨w,hw,hlen,?_⟩
  intro i
  have HI:=congrFun he ((enumerate (commands P D (key c))).symm i)
  simpa only [rawPoint,Function.comp_apply,Equiv.apply_symm_apply] using HI

theorem point_of_joint_natural (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w)
    (z :ℕ→ℝ)
    (hz :∀i :Fin (count P D (key c)),joint P D H L F C hs key hpos c w hw i=z i.val)
    (i :Fin ((family P D H).birth (key c))) :
    point P D H L F C hs key hpos c w hw i=
      (IntegralMixedFramedRunObservation.ofCommands
        (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst (key c)))
        (commands P D (key c)) (((family P D H).birth_bound (key c)).trans (Nat.le_succ _))).point z i.val:=by
  have HP:=IntegralMixedFramedRunObservation.point_actual
    (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst (key c)))
    (commands P D (key c)) (((family P D H).birth_bound (key c)).trans (Nat.le_succ _)) z i
  refine Eq.trans ?_ HP.symm
  change LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point ((family P D H).state (key c))
    (fun j=>joint P D H L F C hs key hpos c w hw
      (enumerate (commands P D (key c)) (((family P D H).state (key c)).sampler.scalar j))) i=_
  exact congrArg (fun f=>LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
    ((family P D H).state (key c)) f i)
      (funext fun j=>hz (enumerate (commands P D (key c)) (((family P D H).state (key c)).sampler.scalar j)))

end LeanCanny.Encoding.IntegralFramedPhysicalSquare
