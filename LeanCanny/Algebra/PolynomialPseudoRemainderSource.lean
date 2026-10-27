/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialPseudoRemainderEntrySpace
public import LeanCanny.Algebra.CertifiedPolynomial
public import LeanCanny.Algebra.PseudoRemainderSpace
public import LeanCanny.Algebra.PolynomialMomentSpace

/-! # Original bivariate readers for polynomial reduction matrices

The outer reduction bound controls the input and matrix dimension. The head
may have higher symbolic degree; the reduction step uses only its declared
degree and lower coefficients. Parameter indices and moduli remain in every
streamed coefficient query.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialPseudoRemainderBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

structure Family where
  head : List Bool → (ℤ[X])[X]
  input : List Bool → (ℤ[X])[X]
  degree : List Bool → ℕ
  bound : List Bool → ℕ
  degree_pos : ∀ c, 0 < degree c
  degree_le : ∀ c, degree c ≤ bound c
  input_degree : ∀ c, (input c).natDegree ≤ bound c

structure Access (F : Family) where
  head : CertifiedPolynomial.BivariateReader F.head
  input : CertifiedPolynomial.BivariateReader F.input
  degree : BinaryFn F.degree
  bound : BinaryFn F.bound

noncomputable def Family.reduced (F : Family) (c : List Bool) : (ℤ[X])[X] :=
  (PseudoRemainder.step (F.head c) (F.degree c))^[2 * (F.bound c + 1)] (F.input c)

theorem Family.reduced_degree (F : Family) (c : List Bool) : (F.reduced c).natDegree ≤ F.bound c :=
  PseudoRemainder.iterate_natDegree_le_bound _ _ _ _ _ (F.degree_pos c) (F.degree_le c) (F.input_degree c)

noncomputable def mapCoefficients (p : (ℤ[X])[X]) (m : ℕ) : ((ZMod m)[X])[X] :=
  p.map (Polynomial.mapRingHom (Int.castRingHom (ZMod m)))

theorem mapCoefficients_coeff (p : (ℤ[X])[X]) (m u v : ℕ) :
    ((mapCoefficients p m).coeff v).coeff u = (((p.coeff v).coeff u : ℤ) : ZMod m) := by
  simp only [mapCoefficients, Polynomial.coeff_map, Polynomial.coe_mapRingHom, Int.coe_castRingHom]

def origin (z : List Bool) : List Bool := pairFst (pairFst z)
def modulus (z : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (pairFst z)) + 1
def parameter (z : List Bool) : ℕ := Nat.fromBitsLE (pairFst (pairSnd z))
def index (z : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (pairSnd z))
def selected (F : Family) (z : List Bool) : Fin (F.bound (origin z) + 1) :=
  ⟨index z % (F.bound (origin z) + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
theorem origin_FP : origin ∈ FP := by polytime [origin]

noncomputable def matrix (F : Family) (z : List Bool) :
    Matrix (Fin (F.bound (origin z) + 1)) (Fin (F.bound (origin z) + 1)) (ZMod (modulus z))[X] :=
  PseudoRemainder.matrix (mapCoefficients (F.head (origin z)) (modulus z))
    (F.degree (origin z)) (F.bound (origin z))

def sourceQuery (t : List Bool) : List Bool := pair (pairFst (pairFst (pairFst t)))
  (pair (pairSnd (pairFst t)) (pairSnd t))
theorem sourceQuery_FP : sourceQuery ∈ FP := by polytime [sourceQuery]

def source {F : Family} (A : Access F) : PseudoRemainderBits.Access where
  headDegree w := BinaryNatCode.encode (F.degree (origin (pairFst w)))
  modulus w := BinaryNat.succ (pairSnd (pairFst (pairFst w)))
  coefficient := A.head.coefficient ∘ sourceQuery

theorem source_degree_FP {F : Family} (A : Access F) : (source A).headDegree ∈ FP :=
  BinaryFn.bits_mem_FP (A.degree.comp (mem_FP_comp (f := pairFst) (g := origin) pairFst_mem_FP origin_FP))
theorem source_modulus_FP {F : Family} (A : Access F) : (source A).modulus ∈ FP := by
  polytime [source]

def entryQuery (e : List Bool) : List Bool :=
  pair (pair (pairFst e) (pairSnd (pairSnd (pairSnd e))))
    (pair (pairFst (pairSnd e)) (pairFst (pairSnd (pairSnd e))))
theorem entryQuery_FP : entryQuery ∈ FP := by polytime [entryQuery]

def entry {F : Family} (A : Access F) : List Bool → List Bool :=
  PseudoRemainderBits.entry (source A) ∘ entryQuery

theorem entry_evaluator {F : Family} (A : Access F) : SpaceFunction (entry A) :=
  (PseudoRemainderBits.entryEvaluator (source A) (source_degree_FP A) (source_modulus_FP A)
    (A.head.evaluator.precompose sourceQuery sourceQuery_FP)).precompose entryQuery entryQuery_FP

theorem entry_packet {F : Family} (A : Access F) (z : List Bool)
    (i j : Fin (F.bound (origin z) + 1)) (u : ℕ) :
    entry A (pair z (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u)))) =
      residueBits ((matrix F z i j).coeff u) := by
  let : NeZero (modulus z) := ⟨by simp [modulus]⟩
  simp only [entry, entryQuery, Function.comp_apply, pairFst_pair, pairSnd_pair]
  unfold matrix
  apply PseudoRemainderBits.entry_coefficient_correct (source A)
    (pair z (BinaryNatCode.encode u)) (modulus z) (F.degree (origin z)) (F.bound (origin z)) u
    (mapCoefficients (F.head (origin z)) (modulus z))
  · simp only [source, pairFst_pair]
  · simp only [source, pairFst_pair, BinaryNat.succ_eq_bits]
    rfl
  · intro k
    simp only [source, sourceQuery, Function.comp_apply, pairFst_pair, pairSnd_pair, mapCoefficients_coeff]
    exact A.head.coefficient_eq (pairFst z) u k

def columnQuery (e : List Bool) : List Bool :=
  pair (pairFst (pairFst e)) (pair (pairSnd (pairSnd e)) (pairFst (pairSnd e)))
theorem columnQuery_FP : columnQuery ∈ FP := by polytime [columnQuery]

def column {F : Family} (A : Access F) : List Bool → List Bool := A.input.coefficient ∘ columnQuery
theorem column_evaluator {F : Family} (A : Access F) : SpaceFunction (column A) :=
  A.input.evaluator.precompose columnQuery columnQuery_FP

theorem column_packet {F : Family} (A : Access F) (z : List Bool) (i : ℕ) (u : ℕ) :
    column A (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode u))) =
      residueBits (((mapCoefficients (F.input (origin z)) (modulus z)).coeff i).coeff u) := by
  simp only [column, columnQuery, Function.comp_apply, pairFst_pair, pairSnd_pair, mapCoefficients_coeff]
  exact A.input.coefficient_eq (pairFst z) u i

end LeanCanny.Algebra.PolynomialPseudoRemainderBits
