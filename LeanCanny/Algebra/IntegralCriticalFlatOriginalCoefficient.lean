/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatMonomial
public import LeanCanny.Algebra.IntegralCriticalOriginalCoefficient

/-! # Original integer coefficient leaves on flat tasks

An integer polynomial mapped into the actual parameter algebra has scalar
diagonal multiplication matrices. The only computational premise is the
original integer coefficient residue reader. Native FP and charged
polynomial-space certificates are kept separate.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatOriginalCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def index (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralClearedCoefficientBits.Source)
    (f : IntegralCriticalHistoryTask.Field) (c : List Bool) : Fin (S.rank c) :=
  ⟨IntegralCriticalHistoryTask.get P f c % S.rank c,
    Nat.mod_lt _ (Nat.zero_le _ |>.trans_lt (S.row c).isLt)⟩

noncomputable def packet (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralClearedCoefficientBits.Source)
    (c : List Bool) : List Bool :=
  pair (IntegralClearedCoefficientBits.context c (index P S .row c).val (index P S .col c).val)
    (BinaryNatCode.encode (IntegralCriticalHistoryTask.get P .sourceIndex c))

theorem packet_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralClearedCoefficientBits.Source) (b : IntegralClearedCoefficientBits.Access S) : packet P S ∈ FP :=
  mem_FP_pair (mem_FP_pair id_mem_FP
    (mem_FP_pair ((IntegralCriticalHistoryTask.get_binary P a .row).mod b.rank).bits_mem_FP
      ((IntegralCriticalHistoryTask.get_binary P a .col).mod b.rank).bits_mem_FP))
    (IntegralCriticalHistoryTask.get_binary P a .sourceIndex).bits_mem_FP

noncomputable def value (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralClearedCoefficientBits.Source)
    (scalar : List Bool → List Bool) : List Bool → List Bool :=
  IntegralCriticalOriginalCoefficientBits.reader scalar ∘ packet P S

theorem value_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralClearedCoefficientBits.Source) (b : IntegralClearedCoefficientBits.Access S)
    (scalar : List Bool → List Bool) (hs : scalar ∈ FP) : value P S scalar ∈ FP :=
  mem_FP_comp (f := packet P S) (g := IntegralCriticalOriginalCoefficientBits.reader scalar)
    (packet_FP P a S b) (IntegralCriticalOriginalCoefficientBits.reader_FP scalar hs)

theorem value_space (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralClearedCoefficientBits.Source) (b : IntegralClearedCoefficientBits.Access S)
    (scalar : List Bool → List Bool) (hs : SpaceFunction scalar) : SpaceFunction (value P S scalar) :=
  (IntegralCriticalOriginalCoefficientBits.reader_space scalar hs).precompose (packet P S) (packet_FP P a S b)

noncomputable def coefficient (S : IntegralClearedCoefficientBits.Source)
    (integer : ∀ c, MvPolynomial (Fin (S.arity c)) ℤ) (c : List Bool) (k : ℕ) : ℤ :=
  (integer c).coeff (RationalSubstitution.Indexed.exponentVector (S.arity c)
    (FixedWidthPolynomial.entry (S.sourceWidth c) k))

theorem reader_packet (S : IntegralClearedCoefficientBits.Source)
    (integer : ∀ c, MvPolynomial (Fin (S.arity c)) ℤ)
    (hp : ∀ c, letI := S.ring c; S.polynomial c = (integer c).map (Int.castRingHom (S.carrier c)))
    (scalar : List Bool → List Bool)
    (hs : ∀ c k, scalar (pair c (BinaryNatCode.encode k)) = residueBits (coefficient S integer c k : ZMod (S.modulus c)))
    (c : List Bool) (k : ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    IntegralCriticalOriginalCoefficientBits.reader scalar
      (pair (IntegralClearedCoefficientBits.context c r.val t.val) (BinaryNatCode.encode k)) =
      residueBits ((Algebra.leftMulMatrix (S.basis c) ((S.polynomial c).coeff
        (RationalSubstitution.Indexed.exponentVector (S.arity c) (FixedWidthPolynomial.entry (S.sourceWidth c) k)))
        r t : ℤ) : ZMod (S.modulus c)) := by
  let := S.ring c
  rw [hp, MvPolynomial.coeff_map]
  change _ = residueBits ((Algebra.leftMulMatrix (S.basis c) (coefficient S integer c k : S.carrier c) r t : ℤ) : ZMod (S.modulus c))
  simp only [map_intCast, Matrix.intCast_apply, Int.cast_id]
  simp only [IntegralCriticalOriginalCoefficientBits.reader, IntegralCriticalOriginalCoefficientBits.sameIndex,
    IntegralCriticalOriginalCoefficientBits.rowWord, IntegralCriticalOriginalCoefficientBits.colWord,
    IntegralCriticalOriginalCoefficientBits.scalarQuery, IntegralCriticalOriginalCoefficientBits.original,
    IntegralClearedCoefficientBits.context, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  by_cases h : r = t
  · subst t
    rw [ite_eq_left rfl, ite_eq_left rfl]
    exact hs c k
  · rw [ite_eq_right (fun he => h (Fin.ext he)), ite_eq_right h]
    simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

theorem actual_value (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralClearedCoefficientBits.Source)
    (integer : ∀ c, MvPolynomial (Fin (S.arity c)) ℤ)
    (hp : ∀ c, letI := S.ring c; S.polynomial c = (integer c).map (Int.castRingHom (S.carrier c)))
    (scalar : List Bool → List Bool)
    (hs : ∀ c k, scalar (pair c (BinaryNatCode.encode k)) = residueBits (coefficient S integer c k : ZMod (S.modulus c)))
    (c : List Bool) :
    letI := S.ring c
    value P S scalar c = residueBits ((Algebra.leftMulMatrix (S.basis c) ((S.polynomial c).coeff
      (RationalSubstitution.Indexed.exponentVector (S.arity c)
        (FixedWidthPolynomial.entry (S.sourceWidth c) (IntegralCriticalHistoryTask.get P .sourceIndex c))))
      (index P S .row c) (index P S .col c) : ℤ) : ZMod (S.modulus c)) :=
  reader_packet S integer hp scalar hs c _ (index P S .row c) (index P S .col c)

end LeanCanny.Algebra.IntegralCriticalFlatOriginalCoefficientBits
