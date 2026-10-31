/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCoefficientBlocks
public import LeanCanny.Algebra.MatrixProductSpace
public import LeanCanny.Computation.PolyTimeBinaryArithmetic

/-! # Original algebra-element sources for products of powers

One original multiplication-matrix entry reader supplies every factor.
Factor positions, exponents, old basis ranks, and product length remain
binary. Query writers keep one copy of the original record.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralPowerProductBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u

structure Family where
  rank : List Bool → ℕ
  carrier : List Bool → Type u
  ring : ∀ c, CommRing (carrier c)
  basis : ∀ c, @Module.Basis (Fin (rank c)) ℤ (carrier c) _ _ ((ring c).toIntAlgebra.toModule)
  factor : ∀ c, ℕ → carrier c
  exponent : List Bool → ℕ → ℕ
  count : List Bool → ℕ
  row : ∀ c, Fin (rank c)
  col : ∀ c, Fin (rank c)
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0

structure Access (F : Family) where
  rank : BinaryFn F.rank
  count : BinaryFn F.count
  modulus : BinaryFn F.modulus
  row : BinaryFn (fun c => (F.row c).val)
  col : BinaryFn (fun c => (F.col c).val)
  exponent : BinaryFn (fun q => F.exponent (pairFst q) (Nat.fromBitsLE (pairSnd q)))
  entry : List Bool → List Bool
  entry_eq : ∀ c s (r t : Fin (F.rank c)),
    letI := F.ring c
    entry (pair c (pair (BinaryNatCode.encode s) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      residueBits ((Algebra.leftMulMatrix (F.basis c) (F.factor c s) r t : ℤ) : ZMod (F.modulus c))

def factorWord (q : List Bool) := pairFst (pairSnd q)
def rowWord (q : List Bool) := pairFst (pairSnd (pairSnd q))
def colWord (q : List Bool) := pairSnd (pairSnd (pairSnd q))

theorem factorWord_FP : factorWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem rowWord_FP : rowWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem colWord_FP : colWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

def exponentQuery (q : List Bool) : List Bool := pair (pairFst q) (factorWord q)

theorem exponentQuery_FP : exponentQuery ∈ FP := mem_FP_pair pairFst_mem_FP factorWord_FP

def oldIndex (F : Family) (word : List Bool → List Bool) (q : List Bool) : Fin (F.rank (pairFst q)) :=
  ⟨Nat.fromBitsLE (word q) % F.rank (pairFst q),
    Nat.mod_lt _ ((Nat.zero_le _).trans_lt (F.row (pairFst q)).isLt)⟩

noncomputable def powerFamily (F : Family) : MatrixPower.ModularFamily where
  dimension q := F.rank (pairFst q)
  modulus q := F.modulus (pairFst q)
  exponent q := F.exponent (pairFst q) (Nat.fromBitsLE (factorWord q))
  row := oldIndex F rowWord
  col := oldIndex F colWord
  matrix q := by
    letI := F.ring (pairFst q)
    exact (Algebra.leftMulMatrix (F.basis (pairFst q)) (F.factor (pairFst q) (Nat.fromBitsLE (factorWord q)))).map
      (Int.castRingHom (ZMod (F.modulus (pairFst q))))
  modulus_ne_zero q := F.modulus_ne_zero (pairFst q)

def entryQuery (p : List Bool) : List Bool :=
  pair (pairFst (pairFst p)) (pair (BinaryNat.normalize (factorWord (pairFst p))) (pairSnd p))

theorem entryQuery_FP : entryQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp (mem_FP_comp (f := pairFst) (g := factorWord) pairFst_mem_FP factorWord_FP)
      BinaryNat.normalize_mem_FP) pairSnd_mem_FP)

theorem entryQuery_packet (q : List Bool) (r t : ℕ) :
    entryQuery (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))) =
      pair (pairFst q) (pair (BinaryNatCode.encode (Nat.fromBitsLE (factorWord q)))
        (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))) := by
  simp only [entryQuery, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]

noncomputable def powerAccess (F : Family) (a : Access F) : MatrixPower.ModularAccess (powerFamily F) where
  dimension q := BinaryNatCode.encode (F.rank (pairFst q))
  modulus q := BinaryNatCode.encode (F.modulus (pairFst q))
  exponent q := BinaryNatCode.encode (F.exponent (pairFst q) (Nat.fromBitsLE (factorWord q)))
  row q := BinaryNatCode.encode (oldIndex F rowWord q).val
  col q := BinaryNatCode.encode (oldIndex F colWord q).val
  entry := a.entry ∘ entryQuery
  dimension_eq _ := rfl
  modulus_eq _ := rfl
  exponent_eq _ := rfl
  row_eq _ := rfl
  col_eq _ := rfl
  entry_eq q r t := by
    rw [Function.comp_apply, entryQuery_packet]
    exact a.entry_eq (pairFst q) (Nat.fromBitsLE (factorWord q)) r t

theorem power_controls (F : Family) (a : Access F) : (powerAccess F a).ControlsPolyTime := by
  have HR : BinaryFn (fun q => F.rank (pairFst q)) := a.rank.comp pairFst_mem_FP
  have HM : BinaryFn (fun q => F.modulus (pairFst q)) := a.modulus.comp pairFst_mem_FP
  have HX : BinaryFn (fun q => F.exponent (pairFst (exponentQuery q)) (Nat.fromBitsLE (pairSnd (exponentQuery q)))) :=
    a.exponent.comp exponentQuery_FP
  have HE : BinaryFn (fun q => F.exponent (pairFst q) (Nat.fromBitsLE (factorWord q))) :=
    BinaryFn.of_eq HX (fun q => by simp only [exponentQuery, pairFst_pair, pairSnd_pair])
  exact ⟨HR.bits_mem_FP, HM.bits_mem_FP, HE.bits_mem_FP,
    ((BinaryFn.fromBits rowWord_FP).mod HR).bits_mem_FP, ((BinaryFn.fromBits colWord_FP).mod HR).bits_mem_FP⟩

theorem power_evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) : SpaceFunction (powerFamily F).value :=
  MatrixPower.ModularAccess.evaluatorWithEntry (powerAccess F a) (power_controls F a) (E.precompose entryQuery entryQuery_FP)

end LeanCanny.Algebra.IntegralPowerProductBits
