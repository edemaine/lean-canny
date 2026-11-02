/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRunHeight
public import LeanCanny.Algebra.PaddedIntegralEquationMass

/-! # Actual framed-run row mass from the derived bank height

Every supported command uses the rootStep bank constructor. Its fresh
numerator is the raw companion root, unlike the inverse-scaled numerator of
HeightBank.step. The proved next-bank bound therefore bounds the new monic
row directly; variable renaming retains every old row's mass.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedStepHeight
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedFullHistoryScript
open UniformIntegralPrefix UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem step_raw_root_height (x : State P S B m ι) (hm : m≤S)
    (c : IntegralMixedFullHistoryScript.Command P B) (H : ℕ)
    (HB : (IntegralMixedFullHistoryScript.step x hm c).bank.Bounds H)
    (r s : Fin (FixedWidthPolynomial.count (m+1) B)) :
    (Algebra.leftMulMatrix
      (PaddedIntegralParameterExtension.coordinateBasis x.sampler.scalarPrefix.basis
        (polynomial x hm c) (degree x hm c)).finBasis (AdjoinRoot.root _) r s).natAbs≤2^H := by
  cases c <;> exact HB.numerator 0 r s

theorem step_head_row_mass (x : State P S B m ι) (hm : m≤S)
    (c : IntegralMixedFullHistoryScript.Command P B) (H : ℕ)
    (HB : (IntegralMixedFullHistoryScript.step x hm c).bank.Bounds H) :
    MvMass.mass ((IntegralMixedFullHistoryScript.step x hm c).sampler.scalarPrefix.rows 0)≤
      2^PaddedIntegralParameterExtension.rowMassHeight m B H := by
  have HM := PaddedIntegralParameterExtension.equation_row_mass x.sampler.scalarPrefix.basis
    (polynomial x hm c) (degree x hm c) H (weights S (2^B) m) (birth S (2^B) m)
    (step_raw_root_height x hm c H HB)
  have HR := congrArg (fun Q : Prefix S (2^B) (m+1)=>Q.rows 0) (step_prefix x hm c)
  rw [HR]
  exact (MvMass.rename_le (UniformIntegralPrefixRows.layout m) _).trans HM

theorem step_old_row_mass (x : State P S B m ι) (hm : m≤S)
    (c : IntegralMixedFullHistoryScript.Command P B) (i : Fin m) :
    MvMass.mass ((IntegralMixedFullHistoryScript.step x hm c).sampler.scalarPrefix.rows i.succ)≤
      MvMass.mass (x.sampler.scalarPrefix.rows i) := by
  have HR := congrArg (fun Q : Prefix S (2^B) (m+1)=>Q.rows i.succ) (step_prefix x hm c)
  rw [HR]
  exact MvMass.rename_le Fin.succ _

theorem height_mono (n S B W D L F C : ℕ) {i j : ℕ} (hij : i≤j) :
    height n S B W D L F C i≤height n S B W D L F C j :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by have := growth_pos n S B W D L F; omega) hij)

def rowMass (n S B W D L F C j : ℕ) : ℕ :=
  PaddedIntegralParameterExtension.rowMassHeight S B (height n S B W D L F C j)

theorem run_row_mass {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (cs : List (IntegralMixedFramedHistoryScript.Instruction n B))
    (hcs : cs.length≤S+1) (W D L F C : ℕ) (hb : ScriptBounds S W D L F C cs)
    (i : Fin cs.length) :
    MvMass.mass ((IntegralMixedFramedHistoryScript.run initial cs hcs).sampler.scalarPrefix.rows i)≤
      2^rowMass n S B W D L F C cs.length := by
  induction cs with
  | nil => exact Fin.elim0 i
  | cons c cs ih =>
    have HT : cs.length≤S+1 := by simp only [List.length_cons] at hcs; omega
    have HM : cs.length≤S := by simp only [List.length_cons] at hcs; omega
    let x := reframe (IntegralMixedFramedHistoryScript.run initial cs HT) c.source c.source_cap
    have HB : (IntegralMixedFullHistoryScript.step x HM c.command).bank.Bounds
        (height n S B W D L F C (cs.length+1)) := run_bounds initial (c::cs) hcs W D L F C hb
    refine Fin.cases ?_ (fun j=>?_) i
    · exact (step_head_row_mass x HM c.command _ HB).trans
        (Nat.pow_le_pow_right (by decide) (by
          unfold rowMass PaddedIntegralParameterExtension.rowMassHeight
          simp only [List.length_cons]
          nlinarith))
    · apply (step_old_row_mass x HM c.command j).trans
      apply (ih HT hb.1 j).trans
      exact Nat.pow_le_pow_right (by decide) (by
        unfold rowMass PaddedIntegralParameterExtension.rowMassHeight
        exact Nat.add_le_add_right (Nat.add_le_add_right
          (height_mono n S B W D L F C (Nat.le_succ cs.length)) _) _)

end LeanCanny.Algebra.IntegralMixedFramedStepHeight
