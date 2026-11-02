/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedDefaultRealExtension
public import LeanCanny.Algebra.IntegralMixedFramedHistoryFamily

/-! # The first padded framed birth is the actual default integer X

The terminal birth reuses the initial source honestly. Its zero scalar
extends the actual old hom and physical tuple. No extra encoded instruction
is inserted into the original script table.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory UniformIntegralPowerSchedule
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralCriticalHistoryTask
open scoped Classical

noncomputable def zeroInstruction {n S B : ℕ} {P : SpatialSource n} {ι : Type}
    (initial : State P S B 0 ι) : Instruction n B where
  source := P
  source_cap := initial.critical_cap
  command := IntegralMixedFullHistoryScript.defaultCommand

theorem defaultInstruction_eq (P : Parameters) (D : Plan P) (root : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root=
      zeroInstruction (IntegralMixedFramedHistoryFamilyBits.initial P D root) := rfl

theorem paddedPast_after {n B : ℕ} (default : Instruction n B) (cs : List (Instruction n B)) :
    paddedPast default cs (cs.length+1)=default::cs := by
  unfold paddedPast past
  rw [show cs.length+1-cs.length=1 by omega,List.replicate_one]
  rw [List.take_of_length_le (by simp)]
  simp only [List.reverse_reverse,List.singleton_append]

noncomputable def commandsAt (P : Parameters) (D : Plan P) (root : List Bool) (birth : ℕ) :
    List (Instruction (P.ambient root) (P.width root)) :=
  paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) birth

theorem commandsAt_congr (P : Parameters) (D : Plan P) (r s : List Bool) (i j : ℕ)
    (hr : r=s) (hb : i=j) : HEq (commandsAt P D r i) (commandsAt P D s j) := by
  cases hr
  cases hb
  rfl

theorem commands_terminal (P : Parameters) (D : Plan P) (root : List Bool) (m : ℕ)
    (hm : m≤P.cap root) (hlen : (D.rules root).length=m) :
    HEq (IntegralMixedFramedHistoryFamilyBits.commands P D (IntegralMixedFramedHistoryFamilyBits.keyAt root (m+1) []))
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root::D.rules root) := by
  have HC := commandsAt_congr P D _ root _ (m+1)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_root root (m+1) [])
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root (m+1) [] (Nat.succ_le_succ hm))
  have HA : commandsAt P D root (m+1)=
      IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root::D.rules root := by
    rw [←hlen]
    exact paddedPast_after _ _
  exact HC.trans (heq_of_eq HA)

theorem run_zero_real_extend {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (cs : List (Instruction n B)) (hcs : cs.length≤S+1) (hm : cs.length≤S)
    (z : Index ι cs→ℝ) (hz : ∀ i,((run initial cs hcs).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : (run initial cs hcs).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ ((run initial cs hcs).sampler.scalarPrefix.basis.generator i)=
      z ((run initial cs hcs).sampler.scalar i)^weights S (2^B) cs.length i) :
    let hnew : (zeroInstruction initial::cs).length≤S+1 := by simp only [List.length_cons]; omega
    ∃ y : (Index ι cs⊕Unit)→ℝ,
    ∃ ψ : (run initial (zeroInstruction initial::cs) hnew).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,((run initial (zeroInstruction initial::cs) hnew).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀ i,y (Sum.inl i)=z i) ∧ y (Sum.inr ())=0 ∧
      ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀ i,ψ ((run initial (zeroInstruction initial::cs) hnew).sampler.scalarPrefix.basis.generator i)=
        y ((run initial (zeroInstruction initial::cs) hnew).sampler.scalar i)^weights S (2^B) (cs.length+1) i) ∧
      ψ ((run initial (zeroInstruction initial::cs) hnew).bank.numerator 0)/
        ((run initial (zeroInstruction initial::cs) hnew).bank.denominator 0:ℝ)=0 ∧
      ∀ i,ψ ((run initial (zeroInstruction initial::cs) hnew).bank.numerator i.succ)/
        ((run initial (zeroInstruction initial::cs) hnew).bank.denominator i.succ:ℝ)=
        φ ((run initial cs hcs).bank.numerator i)/((run initial cs hcs).bank.denominator i:ℝ) :=
  default_real_extend (reframe (run initial cs hcs) P initial.critical_cap) hm z hz φ hφ

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
