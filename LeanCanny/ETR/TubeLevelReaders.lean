/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelPacket
public import LeanCanny.Algebra.ModularAddFP

/-! # Certified coefficient readers for rational tube-level packets

Fixed-width vector access, modular arithmetic, and degree selection give
uniform FP readers for the constant numerator/denominator coordinates and
the variable alpha coordinate. They satisfy the actual regular-system
substitution interface on every packet, including malformed inputs.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeProjectionEncoding
open scoped Classical
open MatrixPower

noncomputable def coordinateRead (target : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthQuery.read arity width target

theorem coordinateRead_mem_FP {target : List Bool → List Bool} (ht : target ∈ FP) : coordinateRead target ∈ FP :=
  FixedWidthQuery.read_mem_FP arity_unary width_unary ht

theorem coordinateRead_packet (target : List Bool → List Bool) (c : List Bool) (i : ℕ) (hi : i < arity c) :
    coordinateRead target (pair c (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (FixedWidthQuery.coordinate width target c i) := by
  rw [coordinateRead, FixedWidthQuery.read_packet, FixedWidthQuery.entry, ite_eq_left hi]

def modulus (p : List Bool) : List Bool := BinaryNat.succ (pairSnd p)
attribute [local irreducible] arity alphaIndex coordinateRead

noncomputable def naturalResidue (target : List Bool → List Bool) (p : List Bool) : List Bool :=
  BinaryNat.mod (pair (coordinateRead target (pairFst p)) (modulus p))

theorem modulus_mem_FP : modulus ∈ FP := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP

theorem naturalResidue_mem_FP {target : List Bool → List Bool} (ht : target ∈ FP) : naturalResidue target ∈ FP := by
  have hx := mem_FP_comp pairFst_mem_FP (coordinateRead_mem_FP ht)
  have h := mem_FP_comp (mem_FP_pair hx modulus_mem_FP) BinaryNat.mod_mem_FP
  exact mem_FP_of_eq (g := naturalResidue target) h (fun _ => rfl)

theorem modulus_packet (q : List Bool) (m : ℕ) (hm : 0 < m) :
    modulus (pair q (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode m := by
  simp only [modulus, pairSnd_pair, BinaryNat.succ_eq_bits, MacaulayBits.fromBits_encode]
  rw [Nat.sub_add_cancel hm]
  rfl

theorem naturalResidue_packet (target : List Bool → List Bool) (c : List Bool) (i m : ℕ)
    (hi : i < arity c) (hm : 0 < m) :
    naturalResidue target (pair (pair c (BinaryNatCode.encode i)) (BinaryNatCode.encode (m - 1))) =
      residueBits (FixedWidthQuery.coordinate width target c i : ZMod m) := by
  rw [naturalResidue, modulus_packet _ m hm, pairFst_pair, coordinateRead_packet _ _ _ hi]
  exact Codec.IntegerResidue.mod_nat_code _ _

noncomputable def integerResidue (p : List Bool) : List Bool :=
  ArithmeticBits.addMod (pair (modulus p) (pair (naturalResidue positiveWord p)
    (ArithmeticBits.negate (pair (modulus p) (naturalResidue negativeWord p)))))

noncomputable def denominatorResidue (p : List Bool) : List Bool :=
  BinaryNat.mod (pair (BinaryNat.succ (coordinateRead denominatorWord (pairFst p))) (modulus p))

attribute [local irreducible] naturalResidue modulus

theorem integerResidue_mem_FP : integerResidue ∈ FP := by
  have hn := mem_FP_comp (mem_FP_pair modulus_mem_FP (naturalResidue_mem_FP negativeWord_mem_FP)) ArithmeticBits.negate_mem_FP
  have h := mem_FP_comp (mem_FP_pair modulus_mem_FP (mem_FP_pair
    (naturalResidue_mem_FP positiveWord_mem_FP) hn)) ArithmeticBits.addMod_mem_FP
  refine mem_FP_of_eq (g := integerResidue) h ?_
  intro p
  simp only [integerResidue, Function.comp_apply]

theorem denominatorResidue_mem_FP : denominatorResidue ∈ FP := by
  have hx := mem_FP_comp pairFst_mem_FP (coordinateRead_mem_FP denominatorWord_mem_FP)
  have hs := mem_FP_comp hx BinaryNat.succ_mem_FP
  have h := mem_FP_comp (mem_FP_pair hs modulus_mem_FP) BinaryNat.mod_mem_FP
  exact mem_FP_of_eq (g := denominatorResidue) h (fun _ => rfl)

theorem integerResidue_packet (c : List Bool) (i m : ℕ) (hi : i < arity c) (hm : 0 < m) :
    integerResidue (pair (pair c (BinaryNatCode.encode i)) (BinaryNatCode.encode (m - 1))) =
      residueBits (integer c i : ZMod m) := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  rw [integerResidue, modulus_packet _ m hm, naturalResidue_packet _ _ _ _ hi hm,
    naturalResidue_packet _ _ _ _ hi hm, ArithmeticBits.negate_residueBits, ArithmeticBits.addMod_residueBits]
  simp only [integer, Int.cast_sub, Int.cast_natCast, positive, negative]
  rw [sub_eq_add_neg]

theorem denominatorResidue_packet (c : List Bool) (i m : ℕ) (hi : i < arity c) (hm : 0 < m) :
    denominatorResidue (pair (pair c (BinaryNatCode.encode i)) (BinaryNatCode.encode (m - 1))) =
      residueBits (denominatorNat c i : ZMod m) := by
  rw [denominatorResidue, modulus_packet _ m hm, pairFst_pair, coordinateRead_packet _ _ _ hi]
  rw [BinaryNat.succ_eq_bits, MacaulayBits.fromBits_encode]
  exact Codec.IntegerResidue.mod_nat_code _ _
attribute [local irreducible] integerResidue denominatorResidue

def context (p : List Bool) : List Bool := pairFst (pairFst (pairFst p))
def index (p : List Bool) : List Bool := pairFst (pairSnd (pairFst p))
def degree (p : List Bool) : List Bool := BinaryNat.normalize (pairSnd (pairSnd (pairFst p)))
def coordinatePacket (p : List Bool) : List Bool := pair (pair (context p) (index p)) (pairSnd p)
noncomputable def alpha (p : List Bool) : Prop :=
  BinaryNat.normalize (index p) = BinaryNatCode.encode (alphaIndex (context p))
noncomputable instance (p : List Bool) : Decidable (alpha p) := inferInstanceAs (Decidable (_ = _))

noncomputable def numeratorValue (p : List Bool) : List Bool :=
  if alpha p then
    if degree p = [true] then ArithmeticBits.one (modulus p) else []
  else if degree p = [] then integerResidue (coordinatePacket p) else []

noncomputable def denominatorValue (p : List Bool) : List Bool :=
  if degree p = [] then
    if alpha p then ArithmeticBits.one (modulus p) else denominatorResidue (coordinatePacket p)
  else []

theorem context_mem_FP : context ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP

theorem index_mem_FP : index ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP

theorem degree_mem_FP : degree ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) BinaryNat.normalize_mem_FP

theorem coordinatePacket_mem_FP : coordinatePacket ∈ FP :=
  mem_FP_pair (mem_FP_pair context_mem_FP index_mem_FP) pairSnd_mem_FP

theorem alpha_fppred : FPPred alpha :=
  Brackets.stringEq_fppred (mem_FP_comp index_mem_FP BinaryNat.normalize_mem_FP)
    (bits_mem_FP (alphaIndex_unary.comp context_mem_FP))

theorem numeratorValue_mem_FP : numeratorValue ∈ FP := by
  have ho := mem_FP_comp modulus_mem_FP ArithmeticBits.one_mem_FP
  have hi := mem_FP_comp coordinatePacket_mem_FP integerResidue_mem_FP
  have h := alpha_fppred.ite_mem_FP
    ((Brackets.stringEq_fppred degree_mem_FP (constFn_mem_FP [true])).ite_mem_FP ho (constFn_mem_FP []))
    ((Brackets.stringEq_fppred degree_mem_FP (constFn_mem_FP [])).ite_mem_FP hi (constFn_mem_FP []))
  exact mem_FP_of_eq (g := numeratorValue) h (fun _ => rfl)

theorem denominatorValue_mem_FP : denominatorValue ∈ FP := by
  have ho := mem_FP_comp modulus_mem_FP ArithmeticBits.one_mem_FP
  have hd := mem_FP_comp coordinatePacket_mem_FP denominatorResidue_mem_FP
  have h := (Brackets.stringEq_fppred degree_mem_FP (constFn_mem_FP [])).ite_mem_FP
    (alpha_fppred.ite_mem_FP ho hd) (constFn_mem_FP [])
  exact mem_FP_of_eq (g := denominatorValue) h (fun _ => rfl)

theorem encode_zero_iff (k : ℕ) : BinaryNatCode.encode k = [] ↔ k = 0 := by
  exact BinaryNat.bits_eq_nil_iff k

theorem encode_one_iff (k : ℕ) : BinaryNatCode.encode k = [true] ↔ k = 1 := by
  change BinaryNatCode.encode k = BinaryNatCode.encode 1 ↔ k = 1
  exact BinaryNatCode.encode_injective.eq_iff

theorem numeratorValue_packet (c : List Bool) (i k m : ℕ)
    (hi : i < arity (pairFst c)) (hm : 0 < m) :
    numeratorValue (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))
      (BinaryNatCode.encode (m - 1))) = residueBits (((numerator (pairFst c) i).coeff k : ℤ) : ZMod m) := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hnorm (r : ℕ) : BinaryNat.normalize (BinaryNatCode.encode r) = BinaryNatCode.encode r := by
    rw [BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode]
    rfl
  simp only [numeratorValue, alpha, context, index, degree, coordinatePacket, pairFst_pair, pairSnd_pair,
    hnorm, BinaryNatCode.encode_injective.eq_iff, encode_zero_iff, encode_one_iff]
  rw [modulus_packet _ m hm]
  by_cases ha : i = alphaIndex (pairFst c)
  · rw [ite_eq_left ha, numerator, ite_eq_left ha, Polynomial.coeff_X]
    by_cases hk : k = 1
    · simp only [hk, ite_true, Int.cast_one]
      exact ArithmeticBits.one_residueBits m
    · simp [hk, Ne.symm hk, residueBits]
  · rw [ite_eq_right ha, numerator, ite_eq_right ha, Polynomial.coeff_C]
    by_cases hk : k = 0
    · simp only [hk, ite_true]
      exact integerResidue_packet (pairFst c) i m hi hm
    · simp [hk, residueBits]

theorem denominatorValue_packet (c : List Bool) (i k m : ℕ)
    (hi : i < arity (pairFst c)) (hm : 0 < m) :
    denominatorValue (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))
      (BinaryNatCode.encode (m - 1))) = residueBits (((denominator (pairFst c) i).coeff k : ℤ) : ZMod m) := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hnorm (r : ℕ) : BinaryNat.normalize (BinaryNatCode.encode r) = BinaryNatCode.encode r := by
    rw [BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode]
    rfl
  simp only [denominatorValue, alpha, context, index, degree, coordinatePacket, pairFst_pair, pairSnd_pair,
    hnorm, BinaryNatCode.encode_injective.eq_iff, encode_zero_iff]
  rw [modulus_packet _ m hm]
  by_cases hk : k = 0
  · rw [ite_eq_left hk]
    by_cases ha : i = alphaIndex (pairFst c)
    · rw [ite_eq_left ha, denominator, ite_eq_left ha, hk, Polynomial.coeff_one_zero, Int.cast_one]
      exact ArithmeticBits.one_residueBits m
    · rw [ite_eq_right ha, denominator, ite_eq_right ha, hk, Polynomial.coeff_C_zero, Int.cast_natCast]
      exact denominatorResidue_packet (pairFst c) i m hi hm
  · rw [ite_eq_right hk, denominator]
    split_ifs <;> simp [Polynomial.coeff_one, hk, residueBits]

noncomputable def readers : TubeParameter.CoordinateReaders pairFst
    (fun c => numerator (pairFst c)) (fun c => denominator (pairFst c)) where
  numerator := numeratorValue
  denominator := denominatorValue
  numeratorEvaluator := LeanCanny.Computation.SpaceFunction.ofFP _ numeratorValue_mem_FP
  denominatorEvaluator := LeanCanny.Computation.SpaceFunction.ofFP _ denominatorValue_mem_FP
  numerator_eq c i hi k m hm := numeratorValue_packet c i k m (by simpa only [arity] using hi) hm
  denominator_eq c i hi k m hm := denominatorValue_packet c i k m (by simpa only [arity] using hi) hm


end LeanCanny.ETR.TubeLevelPacket
