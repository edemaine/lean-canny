/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralParameterInverseSpace
public import LeanCanny.Algebra.MatrixPolynomialEntryCorrect

/-! # Native inverse-polynomial matrices from original integer entries

Characteristic-coefficient scans construct the inverse polynomial. A
streamed matrix polynomial evaluator then applies it to the original
matrix. Both computations retain the original modular entry reader's
space charge. No inverse polynomial or matrix is supplied as input.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralInverseMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Berkowitz
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (F : IntegerFamily) (c : List Bool) : Polynomial ℤ :=
  IntegralParameterInverse.inverse (F.matrix c).charpoly

theorem polynomial_degree (F : IntegerFamily) (c : List Bool) : (polynomial F c).natDegree < F.dimension c + 1 := by
  have H := IntegralParameterInverse.natDegree_inverse_le (F.matrix c).charpoly
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at H
  exact Nat.lt_succ_of_le H

noncomputable def family (F : IntegerFamily) (row col : (c : List Bool) → Fin (F.dimension c))
    (modulus : List Bool → List Bool) : MatrixPolynomialEntryBits.Family where
  dimension := F.dimension
  count c := F.dimension c + 1
  modulus c := Nat.fromBitsLE (modulus c) + 1
  row := row
  col := col
  matrix c := (F.matrix c).map (Int.castRingHom _)
  coefficient c k := ((polynomial F c).coeff k : ℤ)
  modulus_ne_zero _ := by omega

def entryQuery (modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (pairFst q) (modulus (pairFst q))) (pairSnd q)

theorem entryQuery_FP (modulus : List Bool → List Bool) (hm : modulus ∈ FP) : entryQuery modulus ∈ FP :=
  mem_FP_pair (mem_FP_pair pairFst_mem_FP (mem_FP_comp pairFst_mem_FP hm)) pairSnd_mem_FP

def coefficientQuery (modulus : List Bool → List Bool) (q : List Bool) : List Bool := entryQuery modulus q

theorem inverse_packet (F : IntegerFamily) (c mw : List Bool) (k : ℕ) :
    IntegralParameterInverseBits.value F (pair (pair c mw) (BinaryNatCode.encode k)) =
      residueBits (((polynomial F c).coeff k : ℤ) : ZMod (Nat.fromBitsLE mw + 1)) := by
  generalize hz : pair (pair c mw) (BinaryNatCode.encode k) = q
  have hc : IntegralParameterInverseBits.base q = c := by
    rw [IntegralParameterInverseBits.base, ← hz, pairFst_pair, pairFst_pair]
  have hm : IntegralParameterInverseBits.modulus q = mw := by
    rw [IntegralParameterInverseBits.modulus, ← hz, pairFst_pair, pairSnd_pair]
  have hk : Nat.fromBitsLE (pairSnd q) = k := by rw [← hz, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst c
  subst mw
  simp only [IntegralParameterInverseBits.value, polynomial, hk]

noncomputable def access (F : IntegerFamily) (a : IntegerAccess F) (ha : a.ControlsPolyTime)
    (row col : (c : List Bool) → Fin (F.dimension c)) (modulus : List Bool → List Bool)
    (hr : BinaryFn (fun c => (row c).val)) (hc : BinaryFn (fun c => (col c).val)) (hm : modulus ∈ FP) :
    MatrixPolynomialEntryBits.Access (family F row col modulus) where
  dimension := BinaryFn.of_bits (mem_FP_of_eq ha.dimension (fun c => a.dimension_eq c))
  count := (BinaryFn.of_bits (mem_FP_of_eq ha.dimension (fun c => a.dimension_eq c))).add (BinaryFn.const 1)
  modulus := (BinaryFn.fromBits hm).add (BinaryFn.const 1)
  row := hr
  col := hc
  entry := a.entry ∘ entryQuery modulus
  coefficient := IntegralParameterInverseBits.value F ∘ coefficientQuery modulus
  entry_eq c i j := by
    simp only [Function.comp_apply, entryQuery, pairFst_pair, pairSnd_pair]
    change a.entry (pair (pair c (modulus c)) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((F.matrix c i j : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))
    exact IntegerMatrixTrailingBits.canonical_entry a c (modulus c) i j
  coefficient_eq c k := by
    simpa only [Function.comp_apply, coefficientQuery, entryQuery, pairFst_pair, pairSnd_pair, family] using
      inverse_packet F c (modulus c) k

noncomputable def value (F : IntegerFamily) (row col : (c : List Bool) → Fin (F.dimension c))
    (modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits ((((polynomial F c).eval₂ (Matrix.scalar (Fin (F.dimension c))) (F.matrix c)) (row c) (col c) : ℤ) :
    ZMod (Nat.fromBitsLE (modulus c) + 1))

theorem evaluator (F : IntegerFamily) (a : IntegerAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) (row col : (c : List Bool) → Fin (F.dimension c)) (modulus : List Bool → List Bool)
    (hr : BinaryFn (fun c => (row c).val)) (hc : BinaryFn (fun c => (col c).val)) (hm : modulus ∈ FP)
    {budget : List Bool → ℕ} (hb : BinaryFn budget)
    (hbudget : ∀ c k, ((F.matrix c).charpoly.coeff k).natAbs.size ≤ budget c) :
    SpaceFunction (value F row col modulus) := by
  have HE := E.precompose (entryQuery modulus) (entryQuery_FP modulus hm)
  have HC := (IntegralParameterInverseBits.evaluator a ha E hb hbudget).precompose
    (coefficientQuery modulus) (entryQuery_FP modulus hm)
  have HP := MatrixPolynomialEntryBits.polynomial_evaluator (family F row col modulus)
    (access F a ha row col modulus hr hc hm) HE HC
    (fun c => (polynomial F c).map (Int.castRingHom _))
    (fun c => Polynomial.natDegree_map_le.trans_lt (polynomial_degree F c))
    (by intro c k; rw [Polynomial.coeff_map]; rfl)
  refine HP.congr (funext fun c => ?_)
  exact congrArg residueBits (MatrixPolynomialEntryBits.map_polynomial_entry
    (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c) + 1))) (polynomial F c) (F.matrix c)
    (F.dimension c + 1) (polynomial_degree F c) (row c) (col c)).symm

theorem evaluator_of_entry_bounds (F : IntegerFamily) (a : IntegerAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) (row col : (c : List Bool) → Fin (F.dimension c)) (modulus : List Bool → List Bool)
    (hr : BinaryFn (fun c => (row c).val)) (hc : BinaryFn (fun c => (col c).val)) (hm : modulus ∈ FP)
    {height : List Bool → ℕ} (hh : BinaryFn height)
    (hentries : ∀ c i j, (F.matrix c i j).natAbs ≤ 2 ^ height c) :
    SpaceFunction (value F row col modulus) := by
  have hN : BinaryFn F.dimension := BinaryFn.of_bits (mem_FP_of_eq ha.dimension (fun c => a.dimension_eq c))
  exact evaluator F a ha E row col modulus hr hc hm (CharacteristicIntegerBounds.budget_binary hN hh)
    (fun c k => CharacteristicIntegerBounds.coefficient_bits (F.matrix c) (height c) (hentries c) k)

theorem value_aeval (F : IntegerFamily) (row col : (c : List Bool) → Fin (F.dimension c))
    (modulus : List Bool → List Bool) (c : List Bool) :
    value F row col modulus c =
      residueBits (((Polynomial.aeval (F.matrix c) (polynomial F c)) (row c) (col c) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  have HS : algebraMap ℤ (Matrix (Fin (F.dimension c)) (Fin (F.dimension c)) ℤ) = Matrix.scalar (Fin (F.dimension c)) :=
    Subsingleton.elim _ _
  simp only [value, Polynomial.aeval_def, HS]

end LeanCanny.Algebra.IntegralInverseMatrixBits
