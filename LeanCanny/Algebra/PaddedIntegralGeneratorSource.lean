/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralGeneratorFinSpace
public import LeanCanny.Computation.PolyTimeBinaryArithmetic
public import LeanCanny.Algebra.FixedWidthPolynomialFP

/-! # Canonical generator queries retaining the original source record

A query contains the original scalar-prefix source, caller modulus, and
two binary basis ranks. Metadata and coefficient queries always return
to that same source. Invalid ranks are reduced modulo the positive
canonical rank; every valid rank keeps its exact meaning.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralGeneratorSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u

structure Source where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  carrier : List Bool → Type u
  ring : ∀ c, CommRing (carrier c)
  nontrivial : ∀ c, Nontrivial (carrier c)
  basis : ∀ c, @IntegralCoordinateBasis (carrier c) (ring c) (arity c) (2 ^ width c)
  polynomial : ∀ c, Polynomial (carrier c)
  degree : List Bool → ℕ

noncomputable def Source.coefficient (S : Source) (c : List Bool) (k : ℕ) :
    Matrix (Fin (count (S.arity c) (S.width c))) (Fin (count (S.arity c) (S.width c))) ℤ := by
  letI := S.ring c
  exact Algebra.leftMulMatrix (S.basis c).finBasis ((S.polynomial c).coeff k)

noncomputable def Source.matrix (S : Source) (c : List Bool) :
    Matrix (Fin (count (S.arity c + 1) (S.width c))) (Fin (count (S.arity c + 1) (S.width c))) ℤ := by
  letI := S.ring c
  letI := S.nontrivial c
  exact Algebra.leftMulMatrix
    (PaddedIntegralParameterExtension.coordinateBasis (S.basis c) (S.polynomial c) (S.degree c)).finBasis (AdjoinRoot.root _)

def base (q : List Bool) : List Bool := pairFst (pairFst q)
def modulus (q : List Bool) : List Bool := pairSnd (pairFst q)
def row (q : List Bool) : List Bool := pairFst (pairSnd q)
def col (q : List Bool) : List Bool := pairSnd (pairSnd q)

theorem base_FP : base ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem row_FP : row ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem col_FP : col ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

def rank (S : Source) (q : List Bool) : ℕ := count (S.arity (base q) + 1) (S.width (base q))
theorem rank_pos (S : Source) (q : List Bool) : 0 < rank S q :=
  pow_pos (Nat.two_pow_pos _) _

def index (S : Source) (word : List Bool → List Bool) (q : List Bool) : Fin (rank S q) :=
  ⟨Nat.fromBitsLE (word q) % rank S q, Nat.mod_lt _ (rank_pos S q)⟩

noncomputable def family (S : Source) : PaddedIntegralGeneratorFinBits.Family where
  arity q := S.arity (base q)
  width q := S.width (base q)
  carrier q := S.carrier (base q)
  ring q := S.ring (base q)
  nontrivial q := S.nontrivial (base q)
  basis q := S.basis (base q)
  polynomial q := S.polynomial (base q)
  degree q := S.degree (base q)
  modulus q := Nat.fromBitsLE (modulus q) + 1
  modulus_ne_zero _ := by omega
  row := index S row
  col := index S col

structure Access (S : Source) where
  arity : UnaryFn S.arity
  width : UnaryFn S.width
  degree : BinaryFn S.degree
  entry : List Bool → List Bool
  entry_eq : ∀ c mw k (i j : Fin (count (S.arity c) (S.width c))),
    entry (pair (pair c mw) (pair (BinaryNatCode.encode k)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((S.coefficient c k i j : ℤ) : ZMod (Nat.fromBitsLE mw + 1))

theorem rank_binary (S : Source) (a : Access S) : BinaryFn (rank S) := by
  have hM : UnaryFn (fun q => S.arity (base q) + 1) := (a.arity.comp base_FP).add (UnaryFn.const 1)
  have hB : UnaryFn (fun q => S.width (base q)) := a.width.comp base_FP
  apply BinaryFn.of_bits
  exact mem_FP_of_eq (countCode_mem_FP hM hB) (fun q => countCode_code _ _ q)

theorem index_binary (S : Source) (a : Access S) (word : List Bool → List Bool) (hw : word ∈ FP) :
    BinaryFn (fun q => (index S word q).val) := (BinaryFn.fromBits hw).mod (rank_binary S a)

def coefficientQuery (r : List Bool) : List Bool :=
  pair (pair (base (pairFst r)) (modulus (pairFst r))) (pairSnd r)

theorem coefficientQuery_FP : coefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (f := pairFst) (g := base) pairFst_mem_FP base_FP)
    (mem_FP_comp (f := pairFst) (g := modulus) pairFst_mem_FP modulus_FP)) pairSnd_mem_FP

noncomputable def access (S : Source) (a : Access S) : PaddedIntegralGeneratorFinBits.Access (family S) where
  arity := a.arity.comp base_FP
  width := a.width.comp base_FP
  degree := a.degree.comp base_FP
  modulus := (BinaryFn.fromBits modulus_FP).add (BinaryFn.const 1)
  row := index_binary S a row row_FP
  col := index_binary S a col col_FP
  entry := a.entry ∘ coefficientQuery
  entry_eq q k i j := by
    simp only [Function.comp_apply, coefficientQuery, pairFst_pair, pairSnd_pair]
    change a.entry (pair (pair (base q) (modulus q)) (pair (BinaryNatCode.encode k)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((S.coefficient (base q) k i j : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1))
    exact a.entry_eq _ _ _ _ _

noncomputable def value (S : Source) (q : List Bool) : List Bool :=
  residueBits ((S.matrix (base q) (index S row q) (index S col q) : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1))

theorem evaluator (S : Source) (a : Access S) (E : SpaceFunction a.entry) : SpaceFunction (value S) :=
  (PaddedIntegralGeneratorFinBits.evaluator (family S) (access S a) (E.precompose coefficientQuery coefficientQuery_FP)).congr
    (by funext q; rfl)

attribute [local irreducible] Source.matrix

theorem row_packet (S : Source) (c mw : List Bool) (i j : Fin (count (S.arity c + 1) (S.width c))) :
    (index S row (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))).val = i.val := by
  change Nat.fromBitsLE (row _) % rank S _ = _
  simp only [row, base, rank, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact Nat.mod_eq_of_lt i.isLt

theorem col_packet (S : Source) (c mw : List Bool) (i j : Fin (count (S.arity c + 1) (S.width c))) :
    (index S col (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))).val = j.val := by
  change Nat.fromBitsLE (col _) % rank S _ = _
  simp only [col, base, rank, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact Nat.mod_eq_of_lt j.isLt

theorem value_packet (S : Source) (c mw : List Bool) (i j : Fin (count (S.arity c + 1) (S.width c))) :
    value S (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((S.matrix c i j : ℤ) : ZMod (Nat.fromBitsLE mw + 1)) := by
  generalize hz : pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) = q
  have hb : base q = c := by rw [base, ← hz, pairFst_pair, pairFst_pair]
  have hm : modulus q = mw := by rw [modulus, ← hz, pairFst_pair, pairSnd_pair]
  have hr : (index S row q).val = i.val := by rw [← hz]; exact row_packet S c mw i j
  have hc : (index S col q).val = j.val := by rw [← hz]; exact col_packet S c mw i j
  subst c
  subst mw
  have HI : index S row q = i := Fin.ext hr
  have HJ : index S col q = j := Fin.ext hc
  have HP : ((index S row q, index S col q) : Fin (rank S q) × Fin (rank S q)) = (i, j) := Prod.ext HI HJ
  exact congrArg (fun rc : Fin (rank S q) × Fin (rank S q) =>
    residueBits ((S.matrix (base q) rc.1 rc.2 : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1))) HP

end LeanCanny.Algebra.PaddedIntegralGeneratorSource
