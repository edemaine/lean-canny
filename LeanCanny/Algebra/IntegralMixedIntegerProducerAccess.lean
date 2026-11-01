/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerSource
/-! # Native integer-producer metadata and original scalar coefficient entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerProducerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

structure Metadata (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) : Prop where
  degree : BinaryFn (fun key => (polynomial P D key).natDegree)

theorem birth_unary (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) :
    UnaryFn (fun q => (bank P D).birth (IntegralMixedVirtualTaskBits.saved P q)) :=
  (IntegralMixedFullHistoryFamilyBits.family_birth_unary P a D).comp (IntegralMixedVirtualTaskBits.saved_FP P a)

theorem width_unary (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) :
    UnaryFn (fun q => (bank P D).width (IntegralMixedVirtualTaskBits.saved P q)) :=
  (a.width.comp pairFst_mem_FP).comp (IntegralMixedVirtualTaskBits.saved_FP P a)

theorem newRank_binary (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) : BinaryFn (newRank P D) :=
  BinaryFn.of_bits (mem_FP_of_eq (countCode_mem_FP ((birth_unary P a D).add (UnaryFn.const 1)) (width_unary P a D))
    (fun q => countCode_code _ _ q))

theorem oldRank_binary (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) : BinaryFn (oldRank P D) :=
  BinaryFn.of_bits (mem_FP_of_eq (countCode_mem_FP (birth_unary P a D) (width_unary P a D)) (fun q => countCode_code _ _ q))

noncomputable def entryAt (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (k r t : ℕ) : List Bool :=
  residueBits ((family P D).coefficient q k
    ⟨r % count ((family P D).arity q) ((family P D).width q), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % count ((family P D).arity q) ((family P D).width q), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩)

noncomputable def entry (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (z : List Bool) : List Bool :=
  entryAt P D (pairFst z) (Nat.fromBitsLE (IntegralPowerProductBits.factorWord z))
    (Nat.fromBitsLE (IntegralPowerProductBits.rowWord z)) (Nat.fromBitsLE (IntegralPowerProductBits.colWord z))

attribute [local irreducible] PaddedIntegralGeneratorFinBits.Family.coefficient entryAt

theorem entry_packet (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (k : ℕ)
    (r t : Fin (count ((family P D).arity q) ((family P D).width q))) :
    entry P D (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      residueBits ((family P D).coefficient q k r t) := by
  unfold entry
  simp only [pairFst_pair, IntegralPowerProductBits.factorWord, IntegralPowerProductBits.rowWord,
    IntegralPowerProductBits.colWord, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold entryAt
  simp only [Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]

noncomputable def access (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Metadata P D) :
    PaddedIntegralGeneratorFinBits.Access (family P D) where
  arity := birth_unary P a D
  width := width_unary P a D
  degree := h.degree.comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  modulus := modulus_binary P a
  row := (get_binary P a .row).mod (newRank_binary P a D)
  col := (get_binary P a .col).mod (newRank_binary P a D)
  entry := entry P D
  entry_eq := entry_packet P D

noncomputable def scalarAccess (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Metadata P D) :
    IntegralScalarGeneratorBits.Access (scalarFamily P D) :=
  IntegralScalarGeneratorBits.finAccess (family P D) (access P a D h)
    (leadingInteger P D) (leading_coefficient P D) (fun q => residueBits (leadingInteger P D q : ZMod (modulus P q))) (fun _ => rfl)

noncomputable def rawScalar (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : List Bool :=
  residueBits ((polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).coeff (get P .coefficient q) : ZMod (modulus P q))

theorem coefficient_matrix (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (k : ℕ) :
    (family P D).coefficient q k =
      ((polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).coeff k : ZMod (modulus P q)) •
        (1 : Matrix (Fin (oldRank P D q)) (Fin (oldRank P D q)) (ZMod (modulus P q))) :=
  IntegralIntegerCompanionBits.coefficient_eq (family P D)
    (fun q => polynomial P D (IntegralMixedVirtualTaskBits.saved P q)) (fun _ => rfl) q k

end LeanCanny.Algebra.IntegralMixedIntegerProducerBits
