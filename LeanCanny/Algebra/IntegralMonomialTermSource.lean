/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralPowerProductSpace
public import LeanCanny.Algebra.ClearedCoordinateCoefficients
public import LeanCanny.Computation.PolyTimeBinaryRange

/-! # Original sources for one cleared spatial-monomial term

The term is the original coefficient times a common-denominator power
and one coordinate factor power per spatial coordinate. Free coordinate
factors are the denominator; frozen coordinate factors are actual retained
heights. All products use the original parameter algebra.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMonomialTermBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u

structure Source where
  arity : List Bool → ℕ
  rank : List Bool → ℕ
  carrier : List Bool → Type u
  ring : ∀ c, CommRing (carrier c)
  basis : ∀ c, @Module.Basis (Fin (rank c)) ℤ (carrier c) _ _ ((ring c).toIntAlgebra.toModule)
  coefficient : ∀ c, carrier c
  denominator : List Bool → ℤ
  height : ∀ c, ℕ → carrier c
  exponent : List Bool → ℕ → ℕ
  allowance : List Bool → ℕ
  offset : List Bool → ℕ
  free : List Bool → ℕ
  row : ∀ c, Fin (rank c)
  col : ∀ c, Fin (rank c)
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0

def degree (S : Source) (c : List Bool) : ℕ := ∑ i ∈ Finset.range (S.arity c), S.exponent c i

def isFree (S : Source) (c : List Bool) (i : ℕ) : Prop := S.offset c ≤ i ∧ i < S.offset c + S.free c

instance (S : Source) (c : List Bool) (i : ℕ) : Decidable (isFree S c i) :=
  inferInstanceAs (Decidable (_ ∧ _))

noncomputable def factor (S : Source) (c : List Bool) (s : ℕ) : S.carrier c := by
  letI := S.ring c
  exact if s = 0 then S.coefficient c else if s = 1 then (S.denominator c : S.carrier c)
    else if s - 2 < S.arity c then
      if isFree S c (s - 2) then (S.denominator c : S.carrier c) else S.height c (s - 2)
    else 1

def factorExponent (S : Source) (c : List Bool) (s : ℕ) : ℕ :=
  if s = 0 then 1 else if s = 1 then S.allowance c - degree S c else S.exponent c (s - 2)

noncomputable def family (S : Source) : IntegralPowerProductBits.Family where
  rank := S.rank
  carrier := S.carrier
  ring := S.ring
  basis := S.basis
  factor := factor S
  exponent := factorExponent S
  count c := S.arity c + 2
  row := S.row
  col := S.col
  modulus := S.modulus
  modulus_ne_zero := S.modulus_ne_zero

structure Access (S : Source) where
  arity : UnaryFn S.arity
  rank : BinaryFn S.rank
  modulus : BinaryFn S.modulus
  row : BinaryFn (fun c => (S.row c).val)
  col : BinaryFn (fun c => (S.col c).val)
  allowance : BinaryFn S.allowance
  offset : BinaryFn S.offset
  free : BinaryFn S.free
  exponent : BinaryFn (fun q => S.exponent (pairFst q) (Nat.fromBitsLE (pairSnd q)))
  coefficient : List Bool → List Bool
  height : List Bool → List Bool
  denominator : List Bool → List Bool
  coefficient_eq : ∀ c (r t : Fin (S.rank c)),
    letI := S.ring c
    coefficient (pair c (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))) =
      residueBits ((Algebra.leftMulMatrix (S.basis c) (S.coefficient c) r t : ℤ) : ZMod (S.modulus c))
  height_eq : ∀ c i (r t : Fin (S.rank c)),
    letI := S.ring c
    height (pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      residueBits ((Algebra.leftMulMatrix (S.basis c) (S.height c i) r t : ℤ) : ZMod (S.modulus c))
  denominator_eq : ∀ c, denominator c = residueBits (S.denominator c : ZMod (S.modulus c))

def exponentLoop (q : List Bool) : List Bool := pair (pairFst q) (BinaryNatCode.encode (pairSnd q).length)

theorem exponentLoop_FP : exponentLoop ∈ FP := mem_FP_pair pairFst_mem_FP (bits_mem_FP UnaryFn.index)

theorem degree_binary (S : Source) (a : Access S) : BinaryFn (degree S) := by
  have HE : BinaryFn (fun q => S.exponent (pairFst q) (Nat.fromBitsLE (pairSnd q))) := a.exponent
  have HX : BinaryFn (fun q => S.exponent (pairFst (exponentLoop q)) (Nat.fromBitsLE (pairSnd (exponentLoop q)))) :=
    HE.comp exponentLoop_FP
  have HL : BinaryFn (fun q => S.exponent (pairFst q) (pairSnd q).length) :=
    BinaryFn.of_eq HX (fun q => by
      simp only [exponentLoop, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  refine BinaryFn.of_eq (HL.sum a.arity) (fun c => ?_)
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate, degree]

def shiftedExponentQuery (q : List Bool) : List Bool :=
  pair (pairFst q) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q) - 2))

theorem shiftedExponentQuery_FP : shiftedExponentQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP ((BinaryFn.fromBits pairSnd_mem_FP).sub (BinaryFn.const 2)).bits_mem_FP

theorem factorExponent_binary (S : Source) (a : Access S) :
    BinaryFn (fun q => factorExponent S (pairFst q) (Nat.fromBitsLE (pairSnd q))) := by
  have H0 := (BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)
  have H1 := (BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 1)
  have HA : BinaryFn (fun q => S.allowance (pairFst q) - degree S (pairFst q)) :=
    (a.allowance.sub (degree_binary S a)).comp pairFst_mem_FP
  have HX : BinaryFn (fun q => S.exponent (pairFst (shiftedExponentQuery q))
      (Nat.fromBitsLE (pairSnd (shiftedExponentQuery q)))) := a.exponent.comp shiftedExponentQuery_FP
  have HE : BinaryFn (fun q => S.exponent (pairFst q) (Nat.fromBitsLE (pairSnd q) - 2)) :=
    BinaryFn.of_eq HX (fun q => by
      simp only [shiftedExponentQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  exact BinaryFn.ite H0 (BinaryFn.const 1) (BinaryFn.ite H1 HA HE)

end LeanCanny.Algebra.IntegralMonomialTermBits
