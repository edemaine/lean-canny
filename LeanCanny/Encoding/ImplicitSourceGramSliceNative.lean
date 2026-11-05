/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ImplicitSourceCoerciveBoxGram
public import LeanCanny.Encoding.ImplicitSourceGramGrid
public import LeanCanny.Algebra.PolynomialTrailingCoefficientSpace
public import LeanCanny.Computation.SpaceFunctionSpaceBranch
/-! # Native witnessed Gram-slice coefficients preserve every caller modulus -/
@[expose] public section
namespace LeanCanny.Encoding.ImplicitSourceGramSliceNative
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry Polynomial MatrixPower
open IntegralFramedBankPolynomialModel (Source)
open ImplicitSourceGramGrid (header table slice witness)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CoerciveBoxGramEliminant.polynomial ImplicitSourceCoerciveBoxGram.original

def key (c : List Bool) (i : ℕ) := pair (header c) (BinaryNatCode.encode i)
noncomputable def polynomial (S : Source) (c : List Bool) (i : ℕ) : ℤ[X] :=
  let p := (ImplicitSourceCoerciveBoxGram.original S (key c i)).coeff (slice c i)
  if p.coeff (witness c i) = 0 then 1 else p

theorem polynomial_eq (S : Source) (c : List Bool) (i : Fin (ImplicitSourceGramGrid.count S c)) :
    polynomial S c i.val = ImplicitSourceGramGrid.polynomial S c i := by
  have hk : ImplicitSourceCoerciveBoxGram.original S (key c i.val) =
      CoerciveBoxGramEliminant.polynomial (S.polynomial (header c)) (S.degree (header c)) i := by
    unfold key
    rw [ImplicitSourceCoerciveBoxGram.original_packet]
    simp only [ImplicitSourceCoerciveBoxGram.polynomialAt, dite_eq_left i.isLt]
  simp only [polynomial, hk, ImplicitSourceGramGrid.polynomial, CoerciveGramWitnessGrid.polynomial]

private theorem table_entry_FP {read : List Bool → List Bool} {index : List Bool → ℕ}
    (hr : read ∈ FP) (hi : BinaryFn index) :
    (fun q => WordList.get (table (read q)) (index q)) ∈ FP := by
  have htable : (fun q => table (read q)) ∈ FP := mem_FP_comp hr pairSnd_mem_FP
  apply mem_FP_of_eq (mem_FP_comp (mem_FP_pair htable hi.bits_mem_FP) WordList.reader_FP)
  intro q
  exact WordList.reader_packet _ _

private theorem slice_binary {read : List Bool → List Bool} {index : List Bool → ℕ}
    (hr : read ∈ FP) (hi : BinaryFn index) : BinaryFn (fun q => slice (read q) (index q)) :=
  BinaryFn.fromBits (mem_FP_comp (table_entry_FP hr hi) pairFst_mem_FP)
private theorem witness_binary {read : List Bool → List Bool} {index : List Bool → ℕ}
    (hr : read ∈ FP) (hi : BinaryFn index) : BinaryFn (fun q => witness (read q) (index q)) :=
  BinaryFn.fromBits (mem_FP_comp (table_entry_FP hr hi) pairSnd_mem_FP)

private theorem key_FP {read : List Bool → List Bool} {index : List Bool → ℕ}
    (hr : read ∈ FP) (hi : BinaryFn index) : (fun q => key (read q) (index q)) ∈ FP :=
  mem_FP_pair (mem_FP_comp hr pairFst_mem_FP) hi.bits_mem_FP

theorem integer_height (S : Source) (c : List Bool) (i j : ℕ) :
    ((((ImplicitSourceCoerciveBoxGram.original S c).coeff i).coeff j).natAbs.size) ≤
      ImplicitSourceCoerciveBoxGram.massExponent S (pairFst c) + 1 := by
  have hm := (coeff_natAbs_le_coefficientMass ((ImplicitSourceCoerciveBoxGram.original S c).coeff i) j).trans
    ((NestedMass.coeff_le _ _).trans (ImplicitSourceCoerciveBoxGram.original_mass S c))
  simpa only [Nat.size_pow] using Nat.size_le_size hm

noncomputable def value (S : Source) (read : List Bool → List Bool) (index power : List Bool → ℕ)
    (modulus : List Bool → List Bool) (q : List Bool) :=
  residueBits ((((polynomial S (read q) (index q)).coeff (power q)) : ℤ) :
    ZMod (Nat.fromBitsLE (modulus q) + 1))

theorem evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (read : List Bool → List Bool) (index power : List Bool → ℕ) (modulus : List Bool → List Bool)
    (hr : read ∈ FP) (hi : BinaryFn index) (hp : BinaryFn power) (hm : modulus ∈ FP) :
    SpaceFunction (value S read index power modulus) := by
  let p := ImplicitSourceCoerciveBoxGram.original S
  let scalar : List Bool → ℤ := fun q =>
    ((p (key (read q) (index q))).coeff (slice (read q) (index q))).coeff (witness (read q) (index q))
  let z := fun q => pair (pair (key (read q) (index q))
    (BinaryNatCode.encode (slice (read q) (index q)))) (BinaryNatCode.encode (witness (read q) (index q)))
  have hz : z ∈ FP := mem_FP_pair (mem_FP_pair (key_FP hr hi) (slice_binary hr hi).bits_mem_FP)
    (witness_binary hr hi).bits_mem_FP
  have hb : BinaryFn (fun c => ImplicitSourceCoerciveBoxGram.massExponent S (pairFst c) + 1) :=
    BinaryFn.add ((ImplicitSourceCoerciveBoxGram.massExponent_binary S A).comp pairFst_mem_FP) (BinaryFn.const 1)
  have DZ := (PolynomialTrailingCoefficientBits.scalarZeroDecider p
    (ImplicitSourceCoerciveBoxGram.reader S A) hb (integer_height S)).precompose z hz
  have DZ' : SpaceDecider {q | scalar q = 0} := by
    apply DZ.congr
    ext q
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, z, scalar, PolynomialTrailingCoefficientBits.scalar,
      PolynomialTrailingCoefficientBits.base, PolynomialTrailingCoefficientBits.outer,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have EG := ImplicitSourceCoerciveBoxGram.coefficient_evaluator S A (fun q => header (read q)) index power
    (fun q => slice (read q) (index q)) modulus (mem_FP_comp hr pairFst_mem_FP) hi hp (slice_binary hr hi) hm
  let one := fun q => if power q = 0 then ArithmeticBits.one (BinaryNat.succ (modulus q)) else []
  have hsucc : (fun q => BinaryNat.succ (modulus q)) ∈ FP :=
    mem_FP_comp (f := modulus) (g := BinaryNat.succ) hm BinaryNat.succ_mem_FP
  have hone : (fun q => ArithmeticBits.one (BinaryNat.succ (modulus q))) ∈ FP :=
    mem_FP_comp (f := fun q => BinaryNat.succ (modulus q)) (g := ArithmeticBits.one) hsucc ArithmeticBits.one_mem_FP
  have EO : one ∈ FP := (hp.eq (BinaryFn.const 0)).ite_mem_FP
    hone (constFn_mem_FP [])
  apply (SpaceFunction.branchDecider DZ' (SpaceFunction.ofFP one EO) EG).congr
  funext q
  simp only [Set.mem_ofPred_eq]
  dsimp only [value, polynomial]
  by_cases hzero : scalar q = 0
  · simp only [scalar, p] at hzero
    simp only [scalar, p, hzero, ite_true, one]
    rw [BinaryNat.succ_eq_bits]
    by_cases hpower : power q = 0
    · simp only [hpower, ite_true, Polynomial.coeff_one_zero, Int.cast_one]
      exact ArithmeticBits.one_residueBits _
    · simp only [hpower, ite_false, Polynomial.coeff_one, Int.cast_zero, residueBits, ZMod.val_zero,
        BinaryNatCode.encode, Nat.zero_bits]
  · simp only [scalar, p] at hzero
    simp only [key, ImplicitSourceCoerciveBoxGram.original_packet] at hzero
    simp only [scalar, p, ImplicitSourceCoerciveBoxGram.coefficient,
      ImplicitSourceCoerciveBoxGram.residueAt, key, ImplicitSourceCoerciveBoxGram.original_packet,
      hzero, ite_false]

end LeanCanny.Encoding.ImplicitSourceGramSliceNative
