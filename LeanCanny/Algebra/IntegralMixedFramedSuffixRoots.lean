/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPaddedRoots
/-! # Every earlier framed prefix uses the same terminal root suffix

The original full history and default instruction remain fixed. Source
changes are interpreted at their chronological creating instruction.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open IntegralMixedHistory UniformIntegralPrefix
set_option backward.isDefEq.respectTransparency false

variable {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

private theorem roots_birth_congr (x : State P S B 0 ι) (default : Instruction n B)
    (cs : List (Instruction n B)) (a b : ℕ) (ha : a≤S+1) (hb : b≤S+1) (he : a=b) (z : ℕ→ℝ) :
    RootsAt (run x (paddedPast default cs a) (by rw [paddedPast_length]; exact ha)).sampler.scalarPrefix z ↔
      RootsAt (run x (paddedPast default cs b) (by rw [paddedPast_length]; exact hb)).sampler.scalarPrefix z := by
  cases he
  rfl

theorem padded_roots_suffix (x : State P S B 0 ι) (default : Instruction n B)
    (cs : List (Instruction n B)) (birth newer : ℕ) (hb : birth+newer≤S+1) (z : ℕ→ℝ)
    (hz : RootsAt (run x (paddedPast default cs (birth+newer)) (by rw [paddedPast_length]; exact hb)).sampler.scalarPrefix z) :
    RootsAt (run x (paddedPast default cs birth) (by rw [paddedPast_length]; omega)).sampler.scalarPrefix
      (fun i=>z (i+newer)) := by
  induction newer generalizing z with
  | zero => simpa only [Nat.add_zero] using hz
  | succ newer IH =>
    have HH : RootsAt (run x (paddedPast default cs ((birth+newer)+1))
        (by rw [paddedPast_length]; omega)).sampler.scalarPrefix z := by
      exact (roots_birth_congr x default cs (birth+(newer+1)) ((birth+newer)+1) hb (by omega) (by omega) z).mp hz
    have HP:=padded_roots_parent x default cs (birth+newer) (by omega) z HH
    have HR:=IH (by omega) (fun i=>z (i+1)) HP
    simpa only [Nat.add_assoc] using HR

theorem exists_suffix_interpretation (x : State P S B 0 ι) (default : Instruction n B)
    (cs : List (Instruction n B)) (birth newer : ℕ) (hb : birth+newer≤S+1) (z : ℕ→ℝ)
    (hz : RootsAt (run x (paddedPast default cs (birth+newer)) (by rw [paddedPast_length]; exact hb)).sampler.scalarPrefix z) :
    ∃ φ : (run x (paddedPast default cs birth) (by rw [paddedPast_length]; omega)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀ i,φ ((run x (paddedPast default cs birth) (by rw [paddedPast_length]; omega)).sampler.scalarPrefix.basis.generator i)=
        z (i.val+newer)^UniformIntegralPowerSchedule.weights S (2^B) (paddedPast default cs birth).length i := by
  let old:=(run x (paddedPast default cs birth) (by rw [paddedPast_length]; omega)).sampler.scalarPrefix
  have HR:=padded_roots_suffix x default cs birth newer hb z hz
  have HI:=old.interpret ℝ (fun i=>z (i.val+newer)) HR
  exact HI

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
