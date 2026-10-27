/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberPencilEntries
public import LeanCanny.Algebra.BerkowitzPolynomialSpace

/-! # Native modular coefficients of the weighted fiber Gram determinant

The input is `pair (pair context degree) modulusPredecessor`. Each original
polynomial-entry query includes the selected-record searches, triple Tarski
moments, modular weights, and signed sum. The polynomial Berkowitz backend
retains those child certificates; no determinant or moment table is supplied.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberPencilCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicFiberWeightedMoments
open MatrixPower
open scoped Classical

def sourceContext (q : List Bool) : List Bool := pairFst (pairFst q)
theorem sourceContext_FP : sourceContext ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

noncomputable def family (P : Readers) (F : BoundedAlgebraicSlice.Family) : BerkowitzPolynomial.ModularFamily where
  dimension q := BoundedAlgebraicFiberPencilEntries.dimension (sourceContext q)
  modulus q := Nat.fromBitsLE (pairSnd q) + 1
  degree q := Nat.fromBitsLE (pairSnd (pairFst q))
  matrix q := (BoundedAlgebraicFiberPencilEntries.matrix P F (sourceContext q)).map
    (Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1))))
  modulus_ne_zero _ := by omega

def signedQuery (e : List Bool) : List Bool :=
  pair (pair (sourceContext (pairFst e))
    (pair (pairFst (pairSnd e)) (pairFst (pairSnd (pairSnd e))))) (pairSnd (pairSnd (pairSnd e)))
theorem signedQuery_FP : signedQuery ∈ FP := by
  have hs := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have ho := mem_FP_comp pairFst_mem_FP sourceContext_FP
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hj := mem_FP_comp hs pairFst_mem_FP
  have hk := mem_FP_comp hs pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair ho (mem_FP_pair hi hj)) hk

noncomputable def read (P : Readers) (F : BoundedAlgebraicSlice.Family) (e : List Bool) : List Bool :=
  SignedIntegerResidue.value (pair (pairSnd (pairFst e))
    (SignStatisticBits.integerCode (BoundedAlgebraicFiberPencilEntries.coefficient P F (signedQuery e))))

attribute [local irreducible] read SignedIntegerResidue.value BoundedAlgebraicFiberPencilEntries.coefficient

theorem read_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (read P F) := by
  have E := (BoundedAlgebraicFiberPencilEntries.evaluator h A ha).precompose signedQuery signedQuery_FP
  have M := SpaceFunction.ofFP (fun e => pairSnd (pairFst e)) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have H := (M.pairOutputs E).postcompose SignedIntegerResidue.value SignedIntegerResidue.value_FP
  apply H.congr
  funext e
  simp only [read, Function.comp_apply]

noncomputable def access (P : Readers) (F : BoundedAlgebraicSlice.Family) : BerkowitzPolynomial.ModularAccess (family P F) where
  dimension q := BinaryNatCode.encode (BoundedAlgebraicFiberPencilEntries.dimension (sourceContext q))
  modulus q := BinaryNat.succ (pairSnd q)
  degree q := BinaryNatCode.encode (Nat.fromBitsLE (pairSnd (pairFst q)))
  entry := read P F
  dimension_eq _ := rfl
  modulus_eq q := BinaryNat.succ_eq_bits _
  degree_eq _ := rfl
  entry_eq q i j d := by
    change Fin (BoundedAlgebraicFiberPencilEntries.dimension (sourceContext q)) at i j
    have hc := BoundedAlgebraicFiberPencilEntries.coefficient_packet P F (sourceContext q) i j d
    simp only [read, signedQuery, pairFst_pair, pairSnd_pair]
    rw [hc, SignedIntegerResidue.packet]
    change residueBits (((BoundedAlgebraicFiberPencilEntries.matrix P F (sourceContext q) i j).coeff d : ℤ) :
      ZMod (Nat.fromBitsLE (pairSnd q) + 1)) =
      residueBits (((BoundedAlgebraicFiberPencilEntries.matrix P F (sourceContext q) i j).map
        (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))).coeff d)
    rw [Polynomial.coeff_map]
    rfl

theorem controls (P : Readers) (F : BoundedAlgebraicSlice.Family) : (access P F).ControlsPolyTime := by
  have hN := BinaryFn.bits_mem_FP (BoundedAlgebraicFiberPencilEntries.dimension_binary.comp sourceContext_FP)
  have hM := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  have hD := BinaryFn.bits_mem_FP (BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))
  exact ⟨hN, hM, hD⟩

noncomputable def value (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) : List Bool :=
  residueBits ((((BoundedAlgebraicFiberPencilEntries.matrix P F (sourceContext q)).det.coeff
    (Nat.fromBitsLE (pairSnd (pairFst q)))) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))

theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P F) := by
  have E := BerkowitzPolynomial.ModularAccess.evaluator (access P F) (controls P F) (read_evaluator h A ha)
  apply E.congr
  funext q
  dsimp only [BerkowitzPolynomial.ModularFamily.value, family]
  change residueBits (((BoundedAlgebraicFiberPencilEntries.matrix P F (sourceContext q)).map
    (Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1))))).det.coeff
      (Nat.fromBitsLE (pairSnd (pairFst q)))) = _
  have hd : ((BoundedAlgebraicFiberPencilEntries.matrix P F (sourceContext q)).map
      (Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1))))).det =
      (BoundedAlgebraicFiberPencilEntries.matrix P F (sourceContext q)).det.map
        (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1))) :=
    ((Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))).map_det _).symm
  rw [hd, Polynomial.coeff_map]
  rfl

theorem value_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (b : List Bool) (k : ℕ) (m : List Bool) :
    value P F (pair (pair b (BinaryNatCode.encode k)) m) =
      residueBits ((((BoundedAlgebraicFiberPencilEntries.matrix P F b).det.coeff k : ℤ)) : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize he : pair (pair b (BinaryNatCode.encode k)) m = q
  have hb : sourceContext q = b := by rw [sourceContext, ← he, pairFst_pair, pairFst_pair]
  have hm : pairSnd q = m := by rw [← he, pairSnd_pair]
  have hk : Nat.fromBitsLE (pairSnd (pairFst q)) = k := by
    rw [← he, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst b
  subst m
  simp only [value, hk]

end LeanCanny.Encoding.BoundedAlgebraicFiberPencilCoefficient
