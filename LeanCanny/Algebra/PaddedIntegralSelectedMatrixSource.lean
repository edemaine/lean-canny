/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralGeneratorSource
public import LeanCanny.Algebra.IntegralInverseMatrixSpace

/-! # Selected coefficient matrices from the original scalar-prefix source

The selected leading-coefficient matrix is constructed from the original
coefficient reader. Its determinant and characteristic budgets follow
from the original entry-height allowance. Internal residue scans retain
their own requested modulus when returning to the original source.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralSelectedMatrixSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Berkowitz FixedWidthPolynomial
open PaddedIntegralGeneratorSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Bounds (S : Source) where
  height : List Bool → ℕ
  selected : ∀ c i j, (S.coefficient c (S.degree c) i j).natAbs ≤ 2 ^ height c

theorem determinant_bits {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ H) : A.det.natAbs.size ≤ CharacteristicIntegerBounds.budget n H := by
  rw [Matrix.det_eq_sign_charpoly_coeff]
  simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul] using
    CharacteristicIntegerBounds.coefficient_bits A H hA 0

noncomputable def integerFamily (S : Source) (B : Bounds S) : IntegerFamily where
  dimension q := count (S.arity (base q)) (S.width (base q))
  matrix q := S.coefficient (base q) (S.degree (base q))
  budget q := CharacteristicIntegerBounds.budget (count (S.arity (base q)) (S.width (base q))) (B.height (base q))
  determinant_bits q := determinant_bits _ _ (B.selected (base q))

def query (S : Source) (r : List Bool) : List Bool :=
  pair (pair (base (base r)) (modulus r))
    (pair (BinaryNatCode.encode (S.degree (base (base r)))) (pairSnd r))

theorem query_FP (S : Source) (a : Access S) : query S ∈ FP := by
  have hs : (fun r => base (base r)) ∈ FP := mem_FP_comp (f := base) (g := base) base_FP base_FP
  have hd : BinaryFn (fun r => S.degree (base (base r))) := a.degree.comp hs
  exact mem_FP_pair (mem_FP_pair hs modulus_FP) (mem_FP_pair hd.bits_mem_FP pairSnd_mem_FP)

noncomputable def access (S : Source) (B : Bounds S) (a : Access S) : IntegerAccess (integerFamily S B) where
  dimension := countCode (fun q => S.arity (base q)) (fun q => S.width (base q))
  budget q := BinaryNatCode.encode ((integerFamily S B).budget q)
  entry := a.entry ∘ query S
  dimension_eq q := countCode_code _ _ q
  budget_eq _ := rfl
  entry_eq q i j := by
    simp only [Function.comp_apply, query, base, modulus, pairFst_pair, pairSnd_pair]
    change a.entry (pair (pair (base (pairFst q)) (pairSnd q))
      (pair (BinaryNatCode.encode (S.degree (base (pairFst q))))
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((S.coefficient (base (pairFst q)) (S.degree (base (pairFst q))) i j : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))
    exact a.entry_eq _ _ _ _ _

theorem dimension_binary (S : Source) (B : Bounds S) (a : Access S) : BinaryFn (integerFamily S B).dimension :=
  BinaryFn.of_bits (mem_FP_of_eq (countCode_mem_FP (a.arity.comp base_FP) (a.width.comp base_FP))
    (fun q => countCode_code _ _ q))

theorem controls (S : Source) (B : Bounds S) (a : Access S) (hh : BinaryFn B.height) :
    (access S B a).ControlsPolyTime := by
  have hN := dimension_binary S B a
  have hH : BinaryFn (fun q => B.height (base q)) := hh.comp base_FP
  exact ⟨countCode_mem_FP (a.arity.comp base_FP) (a.width.comp base_FP),
    (CharacteristicIntegerBounds.budget_binary hN hH).bits_mem_FP⟩

def index (S : Source) (B : Bounds S) (word : List Bool → List Bool) (q : List Bool) : Fin ((integerFamily S B).dimension q) :=
  ⟨Nat.fromBitsLE (word q) % count (S.arity (base q)) (S.width (base q)), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

theorem index_binary (S : Source) (B : Bounds S) (a : Access S) (word : List Bool → List Bool) (hw : word ∈ FP) :
    BinaryFn (fun q => (index S B word q).val) := (BinaryFn.fromBits hw).mod (dimension_binary S B a)

noncomputable def matrix (S : Source) (c : List Bool) :
    Matrix (Fin (count (S.arity c) (S.width c))) (Fin (count (S.arity c) (S.width c))) ℤ :=
  Polynomial.aeval (S.coefficient c (S.degree c))
    (IntegralParameterInverse.inverse (S.coefficient c (S.degree c)).charpoly)

noncomputable def value (S : Source) (B : Bounds S) (q : List Bool) : List Bool :=
  residueBits ((matrix S (base q) (index S B row q) (index S B col q) : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1))

theorem evaluator (S : Source) (B : Bounds S) (a : Access S) (hh : BinaryFn B.height) (E : SpaceFunction a.entry) :
    SpaceFunction (value S B) := by
  have H := IntegralInverseMatrixBits.evaluator_of_entry_bounds (integerFamily S B) (access S B a) (controls S B a hh)
    (E.precompose (query S) (query_FP S a)) (index S B row) (index S B col) modulus
    (index_binary S B a row row_FP) (index_binary S B a col col_FP) modulus_FP
    (hh.comp base_FP) (fun q => B.selected (base q))
  exact H.congr (funext fun q => IntegralInverseMatrixBits.value_aeval (integerFamily S B)
    (index S B row) (index S B col) modulus q)

def denominatorQuery (q : List Bool) : List Bool := pair q (modulus q)
theorem denominatorQuery_FP : denominatorQuery ∈ FP := mem_FP_pair id_mem_FP modulus_FP

noncomputable def denominatorValue (S : Source) (B : Bounds S) : List Bool → List Bool :=
  IntegralParameterInverseBits.denominatorValue (integerFamily S B) ∘ denominatorQuery

theorem denominator_evaluator (S : Source) (B : Bounds S) (a : Access S) (hh : BinaryFn B.height)
    (E : SpaceFunction a.entry) : SpaceFunction (denominatorValue S B) :=
  (IntegralParameterInverseBits.denominator_evaluator_of_entry_bounds (access S B a) (controls S B a hh)
    (E.precompose (query S) (query_FP S a)) (hh.comp base_FP) (fun q => B.selected (base q))).precompose
      denominatorQuery denominatorQuery_FP

attribute [local irreducible] matrix

theorem value_packet (S : Source) (B : Bounds S) (c mw : List Bool)
    (i j : Fin (count (S.arity c) (S.width c))) :
    value S B (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((matrix S c i j : ℤ) : ZMod (Nat.fromBitsLE mw + 1)) := by
  generalize hz : pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) = q
  have hb : base q = c := by rw [base, ← hz, pairFst_pair, pairFst_pair]
  have hm : modulus q = mw := by rw [modulus, ← hz, pairFst_pair, pairSnd_pair]
  have hr : (index S B row q).val = i.val := by
    rw [← hz]
    change Nat.fromBitsLE (row _) % count (S.arity (base _)) (S.width (base _)) = _
    simp only [row, base, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact Nat.mod_eq_of_lt i.isLt
  have hc : (index S B col q).val = j.val := by
    rw [← hz]
    change Nat.fromBitsLE (col _) % count (S.arity (base _)) (S.width (base _)) = _
    simp only [col, base, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact Nat.mod_eq_of_lt j.isLt
  subst c
  subst mw
  have HI : index S B row q = i := Fin.ext hr
  have HJ : index S B col q = j := Fin.ext hc
  have HP : ((index S B row q, index S B col q) :
    Fin ((integerFamily S B).dimension q) × Fin ((integerFamily S B).dimension q)) = (i, j) := Prod.ext HI HJ
  exact congrArg (fun rc : Fin ((integerFamily S B).dimension q) × Fin ((integerFamily S B).dimension q) =>
    residueBits ((matrix S (base q) rc.1 rc.2 : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1))) HP

end LeanCanny.Algebra.PaddedIntegralSelectedMatrixSource
