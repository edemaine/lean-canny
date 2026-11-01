/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalProducerActual
public import LeanCanny.Algebra.IntegralScalarGeneratorChargedPost
/-! # The actual physical critical polynomial as a native scalar companion source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalUpperBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def newRank (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  count (F.birth (IntegralMixedPhysicalTaskBits.saved P q) + 1) (F.width (IntegralMixedPhysicalTaskBits.saved P q))

theorem newRank_pos (P : Parameters) (F : Family) (q : List Bool) : 0 < newRank P F q := pow_pos (Nat.two_pow_pos _) _

noncomputable def family (P : Parameters) (F : Family) : PaddedIntegralGeneratorFinBits.Family where
  arity q := F.birth (IntegralMixedPhysicalTaskBits.saved P q)
  width q := F.width (IntegralMixedPhysicalTaskBits.saved P q)
  carrier q := (F.state (IntegralMixedPhysicalTaskBits.saved P q)).sampler.scalarPrefix.carrier
  ring q := (F.state (IntegralMixedPhysicalTaskBits.saved P q)).sampler.scalarPrefix.ring
  nontrivial q := (F.state (IntegralMixedPhysicalTaskBits.saved P q)).sampler.scalarPrefix.nontrivial
  basis q := (F.state (IntegralMixedPhysicalTaskBits.saved P q)).sampler.scalarPrefix.basis
  polynomial q := (critical P F).annihilator q
  degree q := IntegralClearedCriticalBounds.dimension (critical P F) q
  modulus := modulus P
  modulus_ne_zero := modulus_ne_zero P
  row q := ⟨get P .row q % newRank P F q, Nat.mod_lt _ (newRank_pos P F q)⟩
  col q := ⟨get P .col q % newRank P F q, Nat.mod_lt _ (newRank_pos P F q)⟩

noncomputable def leadingInteger (P : Parameters) (F : Family) (q : List Bool) : ℤ :=
  IntegralClearedCriticalLeadingBits.integer (critical P F) q

theorem leading_coefficient (P : Parameters) (F : Family) (q : List Bool) :
    letI := (family P F).ring q
    ((family P F).polynomial q).coeff ((family P F).degree q) =
      (leadingInteger P F q : (family P F).carrier q) :=
  IntegralClearedCriticalLeadingBits.coefficient (critical P F) q

noncomputable def scalarFamily (P : Parameters) (F : Family) : IntegralScalarGeneratorBits.Family :=
  IntegralScalarGeneratorBits.finFamily (family P F) (leadingInteger P F) (leading_coefficient P F)

noncomputable def entryAt (P : Parameters) (F : Family) (q : List Bool) (k r t : ℕ) : List Bool :=
  residueBits ((family P F).coefficient q k
    ⟨r % count ((family P F).arity q) ((family P F).width q),
      Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % count ((family P F).arity q) ((family P F).width q),
      Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩)

noncomputable def entry (P : Parameters) (F : Family) (z : List Bool) : List Bool :=
  entryAt P F (pairFst z) (Nat.fromBitsLE (IntegralPowerProductBits.factorWord z))
    (Nat.fromBitsLE (IntegralPowerProductBits.rowWord z)) (Nat.fromBitsLE (IntegralPowerProductBits.colWord z))

attribute [local irreducible] PaddedIntegralGeneratorFinBits.Family.coefficient leadingInteger entryAt

theorem entry_packet (P : Parameters) (F : Family) (q : List Bool) (k : ℕ)
    (r t : Fin (count ((family P F).arity q) ((family P F).width q))) :
    entry P F (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      residueBits ((family P F).coefficient q k r t) := by
  unfold entry
  simp only [pairFst_pair, IntegralPowerProductBits.factorWord, IntegralPowerProductBits.rowWord,
    IntegralPowerProductBits.colWord, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold entryAt
  simp only [Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]

noncomputable def access (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) :
    PaddedIntegralGeneratorFinBits.Access (family P F) where
  arity := h.birth.comp (IntegralMixedPhysicalTaskBits.saved_FP P a)
  width := h.width.comp (IntegralMixedPhysicalTaskBits.saved_FP P a)
  degree := IntegralClearedCriticalBounds.dimension_binary (critical P F) (criticalAccess P a F h)
  modulus := modulus_binary P a
  row := (get_binary P a .row).mod
    (BinaryFn.of_bits (mem_FP_of_eq
      (countCode_mem_FP ((h.birth.comp (IntegralMixedPhysicalTaskBits.saved_FP P a)).add (UnaryFn.const 1))
        (h.width.comp (IntegralMixedPhysicalTaskBits.saved_FP P a)))
      (fun q => countCode_code _ _ q)))
  col := (get_binary P a .col).mod
    (BinaryFn.of_bits (mem_FP_of_eq
      (countCode_mem_FP ((h.birth.comp (IntegralMixedPhysicalTaskBits.saved_FP P a)).add (UnaryFn.const 1))
        (h.width.comp (IntegralMixedPhysicalTaskBits.saved_FP P a)))
      (fun q => countCode_code _ _ q)))
  entry := entry P F
  entry_eq := entry_packet P F

noncomputable def scalarAccess (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) :
    IntegralScalarGeneratorBits.Access (scalarFamily P F) :=
  IntegralScalarGeneratorBits.finAccess (family P F) (access P a F h)
    (leadingInteger P F) (leading_coefficient P F) (fun q => residueBits (leadingInteger P F q : ZMod (modulus P q))) (fun _ => rfl)

theorem actual_polynomial (P : Parameters) (F : Family) (q : List Bool)
    (hc : ((IntegralMixedPhysicalTaskBits.indices P F).coordinate q).val =
      (F.rule (IntegralMixedPhysicalTaskBits.saved P q)).coordinate %
        (F.ambient (IntegralMixedPhysicalTaskBits.saved P q) - (F.rule (IntegralMixedPhysicalTaskBits.saved P q)).offset.val + 1)) :
    (family P F).polynomial q = IntegralMixedHistory.criticalPolynomial
      (F.state (IntegralMixedPhysicalTaskBits.saved P q)) (F.birth_bound (IntegralMixedPhysicalTaskBits.saved P q))
      (F.rule (IntegralMixedPhysicalTaskBits.saved P q)) :=
  IntegralMixedPhysicalCriticalBits.critical_polynomial (IntegralMixedPhysicalTaskBits.family P F)
    (IntegralMixedPhysicalTaskBits.indices P F) q hc

theorem polynomial_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (family P F).polynomial q = IntegralMixedPhysicalQueryBits.polynomial F (IntegralMixedPhysicalTaskBits.saved P q)
      (IntegralMixedPhysicalTaskBits.coordinate P q) := by
  rw [show (family P F).polynomial q = (critical P F).annihilator q from rfl,
    IntegralMixedPhysicalCriticalBits.annihilator_eq]
  rfl

theorem coefficient_entry (P : Parameters) (F : Family) (q : List Bool) (k : ℕ)
    (r t : Fin (count (F.birth (IntegralMixedPhysicalTaskBits.saved P q)) (F.width (IntegralMixedPhysicalTaskBits.saved P q)))) :
    (family P F).coefficient q k r t =
      (IntegralMixedPhysicalQueryBits.matrixCoefficient F (IntegralMixedPhysicalTaskBits.saved P q)
        (IntegralMixedPhysicalTaskBits.coordinate P q) k r.val t.val : ZMod (modulus P q)) := by
  unfold PaddedIntegralGeneratorFinBits.Family.coefficient
  rw [polynomial_snapshot]
  unfold IntegralMixedPhysicalQueryBits.matrixCoefficient
  simp only [Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]
  rfl

end LeanCanny.Algebra.IntegralMixedPhysicalCompanionBits
