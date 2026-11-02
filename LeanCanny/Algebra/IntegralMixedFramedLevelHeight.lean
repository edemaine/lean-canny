/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedStepHeight
public import LeanCanny.Algebra.IntegralMixedCausalLevelLowHeight
/-! # Actual level-source instructions meet the framed birth-height interface

The implicit coefficient 2^E was selected earlier, with E bounded by F*G at
the current birth. Several births may therefore reuse the same spatial source.
The literal LOW is bounded at F*G+1, leaving the extra unit required by the
mixed step theorem inside (F+2)*G. Original degree and auxiliary caps stay fixed.
Only the frontend original-term size and command syntax bounds remain explicit.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedStepHeight
open IntegralMixedHistory IntegralMixedFramedHistoryScript MvPolynomial

theorem level_coefficient {n G F E : ℕ} (P : SpatialSource n)
    (HM : MvMass.mass P.low≤2^G) (hF : 1≤F) (hE : E≤F*G) (e : Fin (n+2) →₀ ℕ) :
    (((FermatLevelLift.source P ((2:ℤ)^E)).low).coeff e).natAbs≤2^(F*G+1) := by
  have HGE : G≤F*G := by nlinarith
  calc
    _ ≤ MvMass.mass (FermatLevelLift.source P ((2:ℤ)^E)).low := MvMass.coeff_le _ _
    _ ≤ MvMass.mass P.low+2^E := IntegralMixedCausalLevelLowHeight.level_mass P _
    _ ≤ 2^G+2^E := Nat.add_le_add_right HM _
    _ ≤ 2^(F*G)+2^(F*G) := Nat.add_le_add (Nat.pow_le_pow_right (by decide) HGE)
      (Nat.pow_le_pow_right (by decide) hE)
    _ = _ := by rw [pow_succ]; omega

theorem level_instruction_bounds {n B G F E W D L : ℕ} (old : SpatialSource n) (c : Instruction (n+1) B)
    (hF : 1≤F) (hE : E≤F*G) (HM : MvMass.mass old.low≤2^G)
    (HP : old.leading.natAbs.size≤G) (hW : old.degree.size≤W) (hD : old.degree≤D)
    (hCap : IntegralMixedExceptionalBounds.auxiliaryCap (n+2) old.degree≤2^B)
    (hsource : c.source=FermatLevelLift.source old ((2:ℤ)^E))
    (hc : IntegralMixedFullScriptHeight.CommandBounds G L c.command) : InstructionBounds G F W D L c := by
  have HGE : G≤F*G+1 := by nlinarith
  refine ⟨?_,?_,?_,?_,?_,command_bounds_mono HGE c.command hc⟩
  · intro e
    rw [hsource]
    exact level_coefficient old HM hF hE e
  · rw [hsource]
    exact HP.trans HGE
  · simpa only [hsource,FermatLevelLift.source] using hW
  · simpa only [hsource,FermatLevelLift.source] using hD
  · simpa only [hsource,FermatLevelLift.source] using hCap

theorem tilted_level_instruction_bounds {n k d B G F E W D L : ℕ} (u : Fin n) (t : ETR.Term)
    (ht : t.degreeBound≤d) (c : Instruction (n+1) B) (hG : 1≤G) (hF : 1≤F) (hE : E≤F*G)
    (hsize : (FixedLeadingTiltedSource.lowTerm k d u.val t).toData.size≤G)
    (hW : (FixedLeadingTiltedSource.degree d).size≤W) (hD : FixedLeadingTiltedSource.degree d≤D)
    (hCap : IntegralMixedExceptionalBounds.auxiliaryCap (n+2) (FixedLeadingTiltedSource.degree d)≤2^B)
    (hsource : c.source=FermatLevelLift.source (FixedLeadingTiltedSource.source k d u t ht) ((2:ℤ)^E))
    (hc : IntegralMixedFullScriptHeight.CommandBounds G L c.command) : InstructionBounds G F W D L c := by
  apply level_instruction_bounds (FixedLeadingTiltedSource.source k d u t ht) c hF hE _ _ hW hD hCap hsource hc
  · exact ((FixedLeadingTiltedSource.lowTerm k d u.val t).finitePolynomial_mass (n+1)).trans
      (Nat.pow_le_pow_right (by decide) hsize)
  · change (1:ℤ).natAbs.size≤G
    simpa only [Int.natAbs_one,Nat.size_one] using hG

end LeanCanny.Algebra.IntegralMixedFramedStepHeight
