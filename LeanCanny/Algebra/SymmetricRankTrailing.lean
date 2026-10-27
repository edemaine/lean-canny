/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Eigenspace.Zero

/-! # Rank of a symmetric matrix from its lowest characteristic coefficient

Over an ordered field, a symmetric matrix has the same kernel as its square.
Its generalized zero eigenspace is therefore its kernel. Consequently the
characteristic polynomial's trailing degree is exactly the nullity, including
empty and zero matrices. This avoids any spectral approximation.
-/

@[expose] public section
namespace LeanCanny.Algebra.SymmetricRankTrailing
open LinearMap Module Polynomial
open scoped Classical

private theorem maxGen_zero_eq_ker {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (h : ker (f ^ 2) = ker f) : f.maxGenEigenspace 0 = ker f := by
  have h1 : ker (f ^ 1) = ker (f ^ (1 : ℕ).succ) := by simpa only [pow_one] using h.symm
  ext x
  simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, mem_ker]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
      simp only [pow_zero, Module.End.one_apply] at hn
      rw [hn, map_zero]
    | succ n =>
      have hk : ker (f ^ (n + 1)) = ker f := by
        simpa only [pow_one, Nat.add_comm] using (Module.End.ker_pow_constant h1 n).symm
      have hx : x ∈ ker (f ^ (n + 1)) := hn
      change x ∈ ker f
      rwa [← hk]
  · intro hx
    exact ⟨1, by simpa only [pow_one] using hx⟩

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [DecidableEq ι] in
theorem kernel_square (A : Matrix ι ι K) (hA : A.IsSymm) :
    ker (A.mulVecLin ^ 2) = ker A.mulVecLin := by
  calc
    ker (A.mulVecLin ^ 2) = ker (A * A).mulVecLin := by
      rw [pow_two, Matrix.mulVecLin_mul]
      rfl
    _ = ker (A.transpose * A).mulVecLin := by rw [hA]
    _ = _ := Matrix.ker_mulVecLin_transpose_mul_self A

theorem trailing_eq_nullity (A : Matrix ι ι K) (hA : A.IsSymm) :
    A.charpoly.natTrailingDegree = Module.finrank K (ker A.mulVecLin) := by
  have h := LinearMap.finrank_maxGenEigenspace_zero_eq A.mulVecLin
  rw [maxGen_zero_eq_ker A.mulVecLin (kernel_square A hA), Matrix.charpoly_mulVecLin] at h
  exact h.symm

theorem rank_add_trailing (A : Matrix ι ι K) (hA : A.IsSymm) :
    A.rank + A.charpoly.natTrailingDegree = Fintype.card ι := by
  rw [trailing_eq_nullity A hA]
  simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_range_add_finrank_ker A.mulVecLin

theorem rank_eq_sub_trailing (A : Matrix ι ι K) (hA : A.IsSymm) :
    A.rank = Fintype.card ι - A.charpoly.natTrailingDegree := by
  have h := rank_add_trailing A hA
  omega

end LeanCanny.Algebra.SymmetricRankTrailing
