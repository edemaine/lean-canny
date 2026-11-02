/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRegularCoverCard
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Native original-only width for the constructed descending cover

This computes the numeric width, not a membership algorithm or an enumeration
of real critical roots. The latter still has to use correlated joint-root
records rather than independent coordinate-root choices.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedFrozenFrameCoverWidth
open LeanCanny.Geometry LeanCanny.Geometry.IntegralMixedFrozenFrame LeanCanny.Algebra

def width (n B : ℕ) : ℕ := (n+1)*(coverFactor n B).size

theorem factor_binary {n B : List Bool→ℕ} (hn : UnaryFn n) (hB : UnaryFn B) :
    BinaryFn (fun q=>coverFactor (n q) (B q)) := by
  let N:=hn.add (UnaryFn.const 1)
  let T:=(BinaryFn.const 2).powUnary hB
  let M:=(BinaryFn.const 2).powUnary (hB.mul N)
  exact (((((BinaryFn.const 3).mul (BinaryFn.ofUnary N)).add (BinaryFn.const 1)).mul T).add
    (BinaryFn.const 1)).mul (M.add (BinaryFn.const 2)) |>.add T |>.add (BinaryFn.const 1)

theorem width_unary {n B : List Bool→ℕ} (hn : UnaryFn n) (hB : UnaryFn B) :
    UnaryFn (fun q=>width (n q) (B q)) :=
  (hn.add (UnaryFn.const 1)).mul ((UnaryFn.length (factor_binary hn hB).bits_mem_FP).of_eq
    (fun q=>BinaryNatCode.length_encode (coverFactor (n q) (B q))))

theorem factor_pow_le (n B k : ℕ) (hk : k≤n+1) :
    (coverFactor n B)^k≤2^width n B := by
  calc
    _≤(2^(coverFactor n B).size)^k:=Nat.pow_le_pow_left (Nat.lt_size_self _).le _
    _=2^((coverFactor n B).size*k):=by rw [pow_mul]
    _≤2^((coverFactor n B).size*(n+1)):=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hk)
    _=2^width n B:=by rw [width,Nat.mul_comm (n+1)]

theorem originalWidth_unary {R : BoundedFullWriter.Readers} (hR : R.PolyTime) :
    UnaryFn (originalWidth R) :=
  (UnaryFn.length (IntegralMixedExceptionalBounds.auxiliaryCap_binary (hR.dim.add (UnaryFn.const 4))
    (BoundedFullWriter.degree_binary hR)).bits_mem_FP).of_eq
      (fun q=>BinaryNatCode.length_encode (IntegralMixedExceptionalBounds.auxiliaryCap
        (R.dim q+4) (BoundedRegularLowModularTerm.source R q).degree))

noncomputable def regularWidth (R : BoundedFullWriter.Readers) (q : List Bool) : ℕ :=
  width (R.dim q+3) (originalWidth R q)

theorem regularWidth_unary {R : BoundedFullWriter.Readers} (hR : R.PolyTime) :
    UnaryFn (regularWidth R) := width_unary (hR.dim.add (UnaryFn.const 3)) (originalWidth_unary hR)

theorem regularWidth_polynomial {R : BoundedFullWriter.Readers} (hR : R.PolyTime) :
    ∃ p : Polynomial ℕ,∀ q,regularWidth R q≤p.eval q.length := by
  obtain ⟨p,HP⟩:=output_length_poly_of_mem_FP (regularWidth_unary hR).mem_FP
  exact ⟨p,fun q=>by simpa only [List.length_replicate] using HP q⟩

theorem regular_zero_cover_card (R : BoundedFullWriter.Readers) (q : List Bool) :
    ∃ I : Type,Finite I ∧ Nat.card I≤2^width (R.dim q+3) (originalWidth R q) ∧
      Nonempty (LeanCanny.Connectivity.ClopenPathCover
        {y : Fin (R.dim q+4)→ℝ | (BoundedRegularSource.polynomial (BoundedFullWriter.original R q)
          (BoundedFullWriter.size R q) (BoundedFullWriter.size R q) (R.radius q)).eval₂ (Int.castRingHom ℝ) y=0} I) := by
  obtain ⟨I,HI,HC,HD⟩:=regular_zero_cover_original_card R q
  exact ⟨I,HI,HC.trans (factor_pow_le _ _ _ (by omega)),HD⟩

end LeanCanny.Encoding.IntegralMixedFrozenFrameCoverWidth
