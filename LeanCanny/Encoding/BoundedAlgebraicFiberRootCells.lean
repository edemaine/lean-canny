/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberLocalSign
public import LeanCanny.Algebra.PolynomialSignInterval

/-! # Native signs on cells between consecutive algebraic-fiber roots

Two consecutive real-order labels leave no root between them. If a test is
zero or divides the root polynomial after specialization, its sign throughout
that entire open cell is the native right-sided sign at the left endpoint.
No rational sample point or numeric root-isolation certificate is needed.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberRootCells
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial Set
open BoundedAlgebraicSlice
open scoped Classical

theorem no_root_between (P : Readers) (F : Family) (u : List Bool)
    (r s : Fin (RootCount.count P F u)) (hrs : s.val = r.val + 1) (y : ℝ)
    (hy : y ∈ Ioo (BoundedAlgebraicFiberRoot.root P F u r).val (BoundedAlgebraicFiberRoot.root P F u s).val) :
    y ∉ RootCount.roots P F u := by
  intro hyr
  obtain ⟨j, hj⟩ := BoundedAlgebraicFiberRoot.root_surjective P F u ⟨y, hyr⟩
  have hjv : (BoundedAlgebraicFiberRoot.root P F u j).val = y := congrArg Subtype.val hj
  have hlo : r < j := (BoundedAlgebraicFiberRoot.root_strictMono P F u).lt_iff_lt.mp (by rw [hjv]; exact hy.1)
  have hhi : j < s := (BoundedAlgebraicFiberRoot.root_strictMono P F u).lt_iff_lt.mp (by rw [hjv]; exact hy.2)
  change r.val < j.val at hlo
  change j.val < s.val at hhi
  omega

theorem interval_packet (P : Readers) (F G : Family) (u : List Bool)
    (r s : Fin (RootCount.count P F u)) (hrs : s.val = r.val + 1)
    (hG : specialized P G u = 0 ∨ specialized P G u ∣ specialized P F u)
    (y : ℝ) (hy : y ∈ Ioo (BoundedAlgebraicFiberRoot.root P F u r).val (BoundedAlgebraicFiberRoot.root P F u s).val) :
    BoundedAlgebraicFiberLocalSign.value P F G false (pair u (BinaryNatCode.encode r.val)) =
      InfinitesimalSign.encode (SignType.sign ((specialized P G u).eval y)) := by
  rw [BoundedAlgebraicFiberLocalSign.right_packet]
  rcases hG with hG | hG
  · simp only [hG, PolynomialLocalSign.right, map_zero, Polynomial.trailingCoeff_zero, sign_zero, Polynomial.eval_zero]
  · have hF : specialized P F u ≠ 0 := Polynomial.ne_zero_of_mem_roots
      (Multiset.mem_toFinset.mp (BoundedAlgebraicFiberRoot.root P F u r).property)
    have hz : ∀ z ∈ Ioo (BoundedAlgebraicFiberRoot.root P F u r).val (BoundedAlgebraicFiberRoot.root P F u s).val,
        (specialized P G u).eval z ≠ 0 := by
      intro z hz hgz
      have hfz : (specialized P F u).eval z = 0 := by
        obtain ⟨Q, hQ⟩ := hG
        rw [hQ, Polynomial.eval_mul, hgz, zero_mul]
      exact no_root_between P F u r s hrs z hz
        (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hF).mpr hfz))
    exact congrArg InfinitesimalSign.encode
      (PolynomialLocalSign.sign_eq_right_on_interval (specialized P G u) _ _ (hy.1.trans hy.2) hz y hy).symm

end LeanCanny.Encoding.BoundedAlgebraicFiberRootCells
