/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzPolynomialSpace
public import LeanCanny.Algebra.SignedIntegerResidue

/-! # Native determinant coefficients from signed polynomial-matrix entries

A binary dimension and a native reader for one signed integer entry
coefficient suffice. The polynomial Berkowitz backend charges every such
read, including empty matrices and out-of-range coefficient indices.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialMatrixBits
open LeanCanny.Encoding LeanCanny.Computation Polynomial MatrixPower
open scoped Classical

structure Family where
  dimension : List Bool → ℕ
  matrix : (c : List Bool) → Matrix (Fin (dimension c)) (Fin (dimension c)) ℤ[X]

def source (q : List Bool) : List Bool := pairFst (pairFst q)
theorem source_FP : source ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

noncomputable def modular (F : Family) : BerkowitzPolynomial.ModularFamily where
  dimension q := F.dimension (source q)
  modulus q := Nat.fromBitsLE (pairSnd q) + 1
  degree q := Nat.fromBitsLE (pairSnd (pairFst q))
  matrix q := (F.matrix (source q)).map (Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1))))
  modulus_ne_zero _ := by omega

def signedQuery (e : List Bool) : List Bool := pair
  (pair (source (pairFst e)) (pair (pairFst (pairSnd e)) (pairFst (pairSnd (pairSnd e)))))
  (pairSnd (pairSnd (pairSnd e)))
theorem signedQuery_FP : signedQuery ∈ FP := by
  have hs := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have ho := mem_FP_comp pairFst_mem_FP source_FP
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hj := mem_FP_comp hs pairFst_mem_FP
  have hd := mem_FP_comp hs pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair ho (mem_FP_pair hi hj)) hd

def read (code : List Bool → List Bool) (e : List Bool) : List Bool :=
  SignedIntegerResidue.value (pair (pairSnd (pairFst e)) (code (signedQuery e)))

attribute [local irreducible] read SignedIntegerResidue.value

theorem read_evaluator {code : List Bool → List Bool} (E : SpaceFunction code) : SpaceFunction (read code) := by
  have C := E.precompose signedQuery signedQuery_FP
  have M := SpaceFunction.ofFP (fun e => pairSnd (pairFst e)) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have H := (M.pairOutputs C).postcompose SignedIntegerResidue.value SignedIntegerResidue.value_FP
  exact H.congr (funext fun _ => by simp only [read, Function.comp_apply])

def EntryCorrect (F : Family) (code : List Bool → List Bool) : Prop := ∀ c (i j : Fin (F.dimension c)) d,
  code (pair (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) (BinaryNatCode.encode d)) =
    SignStatisticBits.integerCode ((F.matrix c i j).coeff d)

noncomputable def access (F : Family) (code : List Bool → List Bool) (hcode : EntryCorrect F code) :
    BerkowitzPolynomial.ModularAccess (modular F) where
  dimension q := BinaryNatCode.encode (F.dimension (source q))
  modulus q := BinaryNat.succ (pairSnd q)
  degree q := BinaryNatCode.encode (Nat.fromBitsLE (pairSnd (pairFst q)))
  entry := read code
  dimension_eq _ := rfl
  modulus_eq _ := BinaryNat.succ_eq_bits _
  degree_eq _ := rfl
  entry_eq q i j d := by
    change Fin (F.dimension (source q)) at i j
    simp only [read, signedQuery, pairFst_pair, pairSnd_pair]
    rw [hcode (source q) i j d, SignedIntegerResidue.packet]
    change residueBits (((F.matrix (source q) i j).coeff d : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) =
      residueBits (((F.matrix (source q) i j).map (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))).coeff d)
    rw [Polynomial.coeff_map]
    rfl

theorem controls (F : Family) (code : List Bool → List Bool) (hcode : EntryCorrect F code)
    (hN : BinaryFn F.dimension) : (access F code hcode).ControlsPolyTime := by
  have hD := BinaryFn.bits_mem_FP (hN.comp source_FP)
  have hM := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  have hK := BinaryFn.bits_mem_FP (BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))
  exact ⟨hD, hM, hK⟩

noncomputable def value (F : Family) (q : List Bool) : List Bool :=
  residueBits ((((F.matrix (source q)).det.coeff (Nat.fromBitsLE (pairSnd (pairFst q)))) : ℤ) :
    ZMod (Nat.fromBitsLE (pairSnd q) + 1))

theorem evaluator (F : Family) {code : List Bool → List Bool} (E : SpaceFunction code)
    (hcode : EntryCorrect F code) (hN : BinaryFn F.dimension) : SpaceFunction (value F) := by
  have H := BerkowitzPolynomial.ModularAccess.evaluator (access F code hcode) (controls F code hcode hN) (read_evaluator E)
  apply H.congr
  funext q
  dsimp only [BerkowitzPolynomial.ModularFamily.value, modular]
  have hd : ((F.matrix (source q)).map
      (Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1))))).det =
      (F.matrix (source q)).det.map (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1))) :=
    ((Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))).map_det _).symm
  rw [hd, Polynomial.coeff_map]
  rfl

theorem value_packet (F : Family) (c : List Bool) (k : ℕ) (m : List Bool) :
    value F (pair (pair c (BinaryNatCode.encode k)) m) =
      residueBits (((F.matrix c).det.coeff k : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize he : pair (pair c (BinaryNatCode.encode k)) m = q
  have hc : source q = c := by rw [source, ← he, pairFst_pair, pairFst_pair]
  have hm : pairSnd q = m := by rw [← he, pairSnd_pair]
  have hk : Nat.fromBitsLE (pairSnd (pairFst q)) = k := by
    rw [← he, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst c
  subst m
  simp only [value, hk]

end LeanCanny.Algebra.IntegerPolynomialMatrixBits
