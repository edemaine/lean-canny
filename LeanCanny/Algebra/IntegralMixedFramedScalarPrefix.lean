/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryScript

/-! # Every actual framed run has its literal scalar-prefix square sampler

Physical critical rows are omitted only in the geometric scalar shadow.
The coefficient algebra, prefix equations and retained bank remain those of
the actual native run, including when the script contains critical commands.
No absolute annihilator root is lifted to a physical critical point.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedScalarPrefix
open IntegralMixedHistory IntegralHistorySampler IntegralMixedFramedHistoryScript
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def canonicalize (x : State P S B m ι) : State P S B m (Fin m) where
  sampler:=ofPrefix x.sampler.scalarPrefix
  bank:=x.bank
  denominator_ne_zero:=x.denominator_ne_zero
  critical_cap:=x.critical_cap

theorem canonicalize_prefix (x : State P S B m ι) :
    (canonicalize x).sampler.scalarPrefix=x.sampler.scalarPrefix := rfl

theorem canonicalize_bank (x : State P S B m ι) : (canonicalize x).bank=x.bank := rfl

theorem canonicalize_rows (x : State P S B m ι) (i : Fin m) :
    (canonicalize x).sampler.rows i=x.sampler.scalarPrefix.rows i := rfl

theorem canonicalize_reframe {n' : ℕ} (x : State P S B m ι) (Q : SpatialSource n')
    (hQ : PurePowerReductionBounds.dimension (n'+1) Q.degree≤2^B) :
    canonicalize (reframe x Q hQ)=reframe (canonicalize x) Q hQ := rfl

noncomputable def advance [Fintype ι] (x : State P S B m ι) (hm : m≤S)
    (c : IntegralMixedFullHistoryScript.Command P B) : State P S B (m+1) (Fin (m+1)) :=
  canonicalize (IntegralMixedFullHistoryScript.step x hm c)

theorem advance_rows [Fintype ι] (x : State P S B m ι) (hm : m≤S)
    (c : IntegralMixedFullHistoryScript.Command P B) (i : Fin (m+1)) :
    (advance x hm c).sampler.rows i=
      (UniformIntegralPrefix.step x.sampler.scalarPrefix hm (Nat.two_pow_pos B)
        (IntegralMixedFullHistoryScript.polynomial x hm c) (IntegralMixedFullHistoryScript.degree x hm c)).rows i := by
  change (IntegralMixedFullHistoryScript.step x hm c).sampler.scalarPrefix.rows i=_
  rw [IntegralMixedFullHistoryScript.step_prefix]

noncomputable def run [Fintype ι] (initial : State P S B 0 ι)
    (cs : List (Instruction n B)) (h : cs.length≤S+1) :
    State (source P cs) S B cs.length (Fin cs.length) :=
  canonicalize (IntegralMixedFramedHistoryScript.run initial cs h)

theorem run_eq [Fintype ι] (initial : State P S B 0 ι)
    (cs : List (Instruction n B)) (h : cs.length≤S+1) :
    run initial cs h=canonicalize (IntegralMixedFramedHistoryScript.run initial cs h) := rfl

theorem run_rows [Fintype ι] (initial : State P S B 0 ι)
    (cs : List (Instruction n B)) (h : cs.length≤S+1) (i : Fin cs.length) :
    (run initial cs h).sampler.rows i=
      (IntegralMixedFramedHistoryScript.run initial cs h).sampler.scalarPrefix.rows i := by
  rw [run_eq]
  rfl

theorem run_bank [Fintype ι] (initial : State P S B 0 ι)
    (cs : List (Instruction n B)) (h : cs.length≤S+1) :
    HEq (run initial cs h).bank (IntegralMixedFramedHistoryScript.run initial cs h).bank := by
  rw [run_eq]
  rfl

theorem run_canonical [Fintype ι] (initial : State P S B 0 ι) (HI : Canonical initial)
    (cs : List (Instruction n B)) (h : cs.length≤S+1) : Canonical (run initial cs h) := by
  rw [run_eq]
  exact IntegralMixedFramedHistoryScript.run_canonical initial HI cs h

end LeanCanny.Algebra.IntegralMixedFramedScalarPrefix
