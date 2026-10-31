/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBlockMomentEntry

/-! # Correct native block entries for augmented matrix moments

The routing program reads only original coefficient blocks. Applying a
zero-preserving coefficient map commutes with the augmented moment layout;
binary quotient and remainder identify its outer vertex and old basis rank.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBlockMomentBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem matrixFin_map {R T : Type*} [Semiring R] [Semiring T] {n : ℕ}
    (f : R → T) (hf : f 0 = 0) (row col : Fin n → R) (A : Matrix (Fin n) (Fin n) R) :
    (MatrixMoment.matrixFin row col A).map f =
      MatrixMoment.matrixFin (f ∘ row) (f ∘ col) (A.map f) := by
  ext i j
  obtain ⟨p, rfl⟩ := (MatrixMoment.vertexEquiv n).surjective i
  obtain ⟨q, rfl⟩ := (MatrixMoment.vertexEquiv n).surjective j
  rw [Matrix.map_apply, MatrixMoment.matrixFin_apply_vertex, MatrixMoment.matrixFin_apply_vertex]
  rcases p with a | (i | c) <;> rcases q with d | (j | e) <;>
    simp [MatrixMoment.matrix, MatrixMoment.withSink, MatrixMoment.sourceRow, Matrix.fromBlocks, hf]

noncomputable def Family.powerMatrix (F : Family) (c : List Bool) :
    Matrix (Fin ((F.dimension c + 2) * F.rank c)) (Fin ((F.dimension c + 2) * F.rank c)) ℤ := by
  letI := F.ring c
  exact IntegralCoefficientBlocks.blockHom (F.basis c) (F.dimension c + 2)
    (MatrixMoment.matrixFin (F.row c) (F.column c) (F.matrix c))

theorem outer_packet (F : Family) (c : List Bool)
    (i j : Fin ((F.dimension c + 2) * F.rank c)) :
    outerPacket F (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      pair (context c i.modNat.val j.modNat.val)
        (pair (BinaryNatCode.encode i.divNat.val) (BinaryNatCode.encode j.divNat.val)) := by
  simp only [outerPacket, MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem entry_correct (F : Family) (a : Access F) (c : List Bool)
    (i j : Fin ((F.dimension c + 2) * F.rank c)) :
    entryProgram F a (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((F.powerMatrix c i j : ℤ) : ZMod (F.modulus c)) := by
  let := F.ring c
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  let ρ : F.carrier c → ZMod (F.modulus c) := fun x => (Algebra.leftMulMatrix (F.basis c) x i.modNat j.modNat : ℤ)
  have Hρ : ρ 0 = 0 := by
    change ((Algebra.leftMulMatrix (F.basis c) 0 i.modNat j.modNat : ℤ) : ZMod (F.modulus c)) = 0
    rw [map_zero, Matrix.zero_apply, Int.cast_zero]
  have HD : (bitsAccess F a).dimension (context c i.modNat.val j.modNat.val) = BinaryNatCode.encode (F.dimension c) := by
    simp only [bitsAccess, context, pairFst_pair]
  have HR (v : Fin (F.dimension c)) : (bitsAccess F a).row
      (pair (context c i.modNat.val j.modNat.val) (BinaryNatCode.encode v.val)) = residueBits (ρ (F.row c v)) :=
    a.row_eq c v i.modNat j.modNat
  have HC (v : Fin (F.dimension c)) : (bitsAccess F a).column
      (pair (context c i.modNat.val j.modNat.val) (BinaryNatCode.encode v.val)) = residueBits (ρ (F.column c v)) :=
    a.column_eq c v i.modNat j.modNat
  have HE (v w : Fin (F.dimension c)) : (bitsAccess F a).entry
      (pair (context c i.modNat.val j.modNat.val) (pair (BinaryNatCode.encode v.val) (BinaryNatCode.encode w.val))) =
      residueBits (ρ (F.matrix c v w)) := a.entry_eq c v w i.modNat j.modNat
  have H := MatrixMoment.EntryBits.entry_correct (bitsAccess F a) (context c i.modNat.val j.modNat.val)
    (F.modulus c) (F.dimension c) (ρ ∘ F.row c) (ρ ∘ F.column c) ((F.matrix c).map ρ) HD HR HC HE i.divNat j.divNat
  rw [entryProgram, Function.comp_apply, outer_packet]
  rw [H, ← matrixFin_map ρ Hρ, Matrix.map_apply]
  have HB := IntegralCoefficientBlocks.block_entry (F.basis c)
    (MatrixMoment.matrixFin (F.row c) (F.column c) (F.matrix c)) i.divNat j.divNat i.modNat j.modNat
  have HI : finProdFinEquiv (i.divNat, i.modNat) = i := finProdFinEquiv.apply_symm_apply i
  have HJ : finProdFinEquiv (j.divNat, j.modNat) = j := finProdFinEquiv.apply_symm_apply j
  rw [HI, HJ] at HB
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (F.modulus c))) HB.symm

end LeanCanny.Algebra.IntegralBlockMomentBits
