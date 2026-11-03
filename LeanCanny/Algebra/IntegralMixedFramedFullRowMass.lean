/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalRowStepMass
public import LeanCanny.Algebra.IntegralMixedFramedRowMassControls
/-! # Every actual full framed sampler row has an original numeric mass bound

Unlike scalar-prefix row bounds, this induction includes all physical and
multiplier blocks introduced by critical commands. The initial physical
index is empty; old rows survive by renaming at every step.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalRowBudget
open LeanCanny.Encoding LeanCanny.Computation MvPolynomial IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedStepHeight
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem run_mass {n S B : ℕ} {P : SpatialSource n}
    (initial : State P S B 0 (Fin 0)) (cs : List (Instruction n B)) (hcs : cs.length≤S+1)
    (W D L F C J : ℕ) (hb : ScriptBounds S W D L F C cs) (hJ : cs.length≤J)
    (i : Index (Fin 0) cs) :
    MvMass.mass ((run initial cs hcs).sampler.rows i)≤
      2^exponent n S B W D L F (height n S B W D L F C J) := by
  induction cs with
  | nil => exact Fin.elim0 i
  | cons c cs ih =>
    have HT : cs.length≤S+1 := by simp only [List.length_cons] at hcs; omega
    have HM : cs.length≤S := by simp only [List.length_cons] at hcs; omega
    have HJ : cs.length≤J := by simp only [List.length_cons] at hJ; omega
    have HJ1 : cs.length+1≤J := by simpa only [List.length_cons] using hJ
    let x:=reframe (run initial cs HT) c.source c.source_cap
    let H:=height n S B W D L F C J
    have HP : 1≤H := height_positive n S B W D L F C J
    have H0 : height n S B W D L F C cs.length≤H := height_mono n S B W D L F C HJ
    have H1 : height n S B W D L F C (cs.length+1)≤H := height_mono n S B W D L F C HJ1
    have HX : x.bank.Bounds H := (run_bounds initial cs HT W D L F C hb.1).mono H0
    have HN : (IntegralMixedFullHistoryScript.step x HM c.command).bank.Bounds H :=
      (run_bounds initial (c::cs) hcs W D L F C hb).mono H1
    have HC : F*height n S B W D L F C cs.length+1≤sourceC F H := by unfold sourceC; nlinarith
    exact full_step x HM c.command W D L F H HP HX
      (fun e=>(hb.2.low e).trans (Nat.pow_le_pow_right (by decide) HC))
      (hb.2.leading.trans HC) hb.2.width hb.2.degree
      (command_bounds_mono HC c.command hb.2.command) (ih HT hb.1 HJ) HN i

def familyMass (P : Parameters) (L F C : List Bool→ℕ) (root : List Bool) :=
  exponent (P.ambient root) (P.cap root+1) (P.width root) (P.sourceWidth root) (P.degree root)
    (L root) (F root)
    (height (P.ambient root) (P.cap root+1) (P.width root) (P.sourceWidth root) (P.degree root)
      (L root) (F root) (C root) (P.cap root+2))

theorem family_mass (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool→ℕ)
    (h : FamilyInputs P D L F C) (key : List Bool)
    (i : (IntegralMixedFramedHistoryFamilyBits.family P D H).physical key) :
    MvMass.mass (((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.rows i)≤
      2^familyMass P L F C (pairFst key) := by
  have HB:=padded_bounds (h.script (pairFst key))
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)) (h.default (pairFst key))
    (IntegralMixedFramedHistoryFamilyBits.prefixLength P key)
  exact run_mass (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key))
    (IntegralMixedFramedHistoryFamilyBits.commands P D key)
    (((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key).trans (Nat.le_succ _))
    (P.sourceWidth (pairFst key)) (P.degree (pairFst key)) (L (pairFst key)) (F (pairFst key)) (C (pairFst key))
    (P.cap (pairFst key)+2) HB
    (((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key).trans (Nat.le_succ _)) i

end LeanCanny.Algebra.IntegralMixedPhysicalRowBudget
