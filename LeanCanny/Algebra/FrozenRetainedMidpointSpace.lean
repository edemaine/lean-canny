/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FrozenAffineMidpointSpace
public import LeanCanny.Algebra.FixedWidthBlockRowSpace
public import LeanCanny.Algebra.FrozenAffineMass

/-! # Native midpoint rows inside a retained finite variable block -/

@[expose] public section
namespace LeanCanny.Algebra.FrozenRetainedMidpointBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def polynomial {n : ℕ} (i : Fin n) : MvPolynomial (Fin (1 * (3 * n + 1) + 1)) ℤ :=
  rename (FrozenAffineCopies.block (0 : Fin 1)) (FrozenAffineCopies.midpoint i)

theorem degree_le {n : ℕ} (i : Fin n) : (polynomial i).totalDegree ≤ 1 :=
  (totalDegree_rename_le _ _).trans (FrozenAffineCopies.midpoint_degree i)

theorem mass_le {n : ℕ} (i : Fin n) : MvMass.mass (polynomial i) ≤ 4 :=
  (MvMass.rename_le _ _).trans (FrozenAffineCopies.midpoint_mass i)

theorem evaluator {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W)
    (index : (c : List Bool) → Fin (N c)) (hi : UnaryFn (fun c => (index c).val))
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (fun c => 1 * (3 * N c + 1) + 1) W
      (fun c => polynomial (index c)) target modulus) := by
  let A := fun c => 3 * N c + 1
  let B := fun c => 1 * A c + 1
  have hA : UnaryFn A := ((UnaryFn.const 3).mul hN).add (UnaryFn.const 1)
  have hB : UnaryFn B := ((UnaryFn.const 1).mul hA).add (UnaryFn.const 1)
  have hfit (c : List Bool) : 1 + A c ≤ B c := by dsimp only [B]; omega
  have P := FrozenAffineMidpointBits.evaluator (hN.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP)
    (fun q => index (pairFst q)) (hi.comp pairFst_mem_FP) pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hm)
  have E := FixedWidthBlockRowBits.evaluator hA hB (UnaryFn.const 1) hW hfit
    (fun c => FrozenAffineCopies.midpoint (index c)) target modulus ht P
  refine E.congr (funext fun c => ?_)
  have he : FrozenAffineCopies.block (0 : Fin 1) = BlockRenameCoefficient.shift (A c) (B c) 1 (hfit c) := by
    funext j
    apply Fin.ext
    change j.val + A c * 0 + 1 = 1 + j.val
    omega
  simp only [FixedWidthRowBits.value, polynomial, he]
  rfl

end LeanCanny.Algebra.FrozenRetainedMidpointBits
