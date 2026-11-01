/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightCells
public import LeanCanny.Algebra.IntegralMixedHeightBankProduct
public import LeanCanny.Algebra.ModularProductSpace
/-! # Charged immutable-cell access and erased original scale products -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightCellAccessBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHeightCellsBits (cell Primitive)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cell modulus IntegralMixedHeightCellsBits.reader

def query (tag : ℕ) (p : List Bool) :=
  pair (pairFst (pairFst p)) (pair (BinaryNatCode.encode tag) (pairSnd p))

theorem query_FP (tag : ℕ) : query tag ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (mem_FP_pair (constFn_mem_FP _) pairSnd_mem_FP)

noncomputable def read (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (tag : ℕ) :=
  IntegralMixedHeightCellsBits.reader P D ∘ query tag

theorem read_space (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (hp : Primitive P D) (tag : ℕ) :
    SpaceFunction (read P D tag) := hp.precompose (query tag) (query_FP tag)

theorem read_packet (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (tag : ℕ) (z : List Bool) (i : ℕ) :
    read P D tag (pair z (BinaryNatCode.encode i)) = residueBits (cell P D (pairFst z) tag i : ZMod (modulus P (pairFst z))) := by
  simp only [read, Function.comp_apply, query, pairFst_pair, pairSnd_pair]
  exact IntegralMixedHeightCellsBits.reader_packet P D (pairFst z) tag i

def arity (P : Parameters) (z : List Bool) := P.ambient (RankedHistoryTask.root (pairFst z)) + 1

theorem arity_unary (P : Parameters) (a : Access P) : UnaryFn (arity P) :=
  ((a.ambient.comp RankedHistoryTask.root_FP).comp pairFst_mem_FP).add (UnaryFn.const 1)

noncomputable def scaleTerm (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (p : List Bool) :=
  if Nat.fromBitsLE (pairSnd p) = get P .slot8 (pairFst (pairFst p)) then
    ArithmeticBits.one (BinaryNatCode.encode (modulus P (pairFst (pairFst p)))) else read P D 2 p

theorem scaleTerm_space (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (hp : Primitive P D) :
    SpaceFunction (scaleTerm P D) := by
  have HQ := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HI : BinaryFn (fun p => get P .slot8 (pairFst (pairFst p))) := (get_binary P a .slot8).comp HQ
  have HM : BinaryFn (fun p => modulus P (pairFst (pairFst p))) := (modulus_binary P a).comp HQ
  have E := SpaceFunction.branch _ ((BinaryFn.fromBits pairSnd_mem_FP).eq HI).flag_mem_FP
    (SpaceFunction.ofFP _ (mem_FP_comp HM.bits_mem_FP ArithmeticBits.one_mem_FP)) (read_space P D hp 2)
  exact E.congr (funext fun z => by simp only [decide_eq_true_eq]; rfl)

noncomputable def scaleScalar (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (z : List Bool) (i : ℕ) :
    ZMod (modulus P (pairFst z)) := if i = get P .slot8 (pairFst z) then 1 else cell P D (pairFst z) 2 i

noncomputable def scaleProduct (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (z : List Bool) :=
  residueBits (∏ i ∈ Finset.range (arity P z), scaleScalar P D z i)

theorem scaleTerm_packet (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (z : List Bool) (i : ℕ) :
    scaleTerm P D (pair z (BinaryNatCode.encode i)) = residueBits (scaleScalar P D z i) := by
  simp only [scaleTerm, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HR := read_packet P D 2 z i
  simp only [BinaryNatCode.encode] at HR
  by_cases HI : i = get P .slot8 (pairFst z)
  · rw [ite_eq_left HI, scaleScalar, ite_eq_left HI]
    exact ArithmeticBits.one_residueBits _
  · rw [ite_eq_right HI, HR, scaleScalar, ite_eq_right HI]

theorem scaleProduct_space (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (hp : Primitive P D) :
    SpaceFunction (scaleProduct P D) := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have E := ModularProduct.evaluatorWithModulus (scaleTerm_space P a D hp)
    (fun z => BinaryNatCode.encode (arity P z)) (fun z => BinaryNatCode.encode (modulus P (pairFst z)))
    (BinaryFn.ofUnary (arity_unary P a)).bits_mem_FP HM.bits_mem_FP
    (fun z => modulus P (pairFst z)) (funext fun _ => Nat.fromBitsLE_bits _) (scaleScalar P D)
    (fun z => Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z))) (fun z i _ => scaleTerm_packet P D z i)
  exact E.congr (funext fun z => by simp only [scaleProduct, BinaryNatCode.encode, Nat.fromBitsLE_bits])

end LeanCanny.Algebra.IntegralMixedHeightCellAccessBits
