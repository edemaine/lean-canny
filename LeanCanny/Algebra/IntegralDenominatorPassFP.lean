/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ModularHistoryPassFP
public import LeanCanny.Algebra.ModularScalarFP

/-! # Forward modular evaluation of retained integer denominators

A critical root denominator depends only on its integer leading scalar and
on earlier denominators selected as coordinate scales. A bounded forward
pass computes their residues without requesting any algebraic matrix entry.
Selectors outside the retained history denote the unit scale.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralDenominatorPass
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

structure Family where
  count : List Bool → ℕ
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0
  arity : List Bool → ℕ → ℕ
  leading : List Bool → ℕ → ℤ
  degree : List Bool → ℕ → ℕ
  exponent : List Bool → ℕ → ℕ
  index : List Bool → ℕ → ℕ → ℕ

def cursor (p : List Bool) : ℕ := Nat.fromBitsLE (BoundedFold.counter p)

def scale {R : Type*} [One R] (v : List R) (j : ℕ) : R := (v[j]?).getD 1

def next (F : Family) (c : List Bool) (i : ℕ) (v : List (ZMod (F.modulus c))) : ZMod (F.modulus c) :=
  ((F.leading c i : ZMod (F.modulus c)) *
    (∏ j ∈ Finset.range (F.arity c i), scale v (F.index c i j)) ^ F.degree c i *
    (F.degree c i : ZMod (F.modulus c))) ^ F.exponent c i

def pass (F : Family) : ModularHistoryPass.Family where
  count := F.count
  modulus := F.modulus
  modulus_ne_zero := F.modulus_ne_zero
  next := next F

structure Access (F : Family) where
  count : UnaryFn F.count
  modulus : BinaryFn F.modulus
  arity : UnaryFn (fun p => F.arity (pairFst p) (cursor p))
  leading : (fun p => residueBits (F.leading (pairFst p) (cursor p) : ZMod (F.modulus (pairFst p)))) ∈ FP
  degree : BinaryFn (fun p => F.degree (pairFst p) (cursor p))
  exponent : BinaryFn (fun p => F.exponent (pairFst p) (cursor p))
  index : BinaryFn (fun z => F.index (pairFst (pairFst z)) (cursor (pairFst z)) (Nat.fromBitsLE (pairSnd z)))

def factor (F : Family) (c : List Bool) (i : ℕ) (table : List Bool) (coordinate : ℕ) : ZMod (F.modulus c) :=
  let j := F.index c i coordinate
  if j < i then (Nat.fromBitsLE (WordList.get table j) : ZMod (F.modulus c)) else 1

def rawScaleAt (F : Family) (p : List Bool) (coordinate : ℕ) : ZMod (F.modulus (pairFst p)) :=
  factor F (pairFst p) (cursor p) (BoundedFold.accumulator p) coordinate

def rawScale (F : Family) (z : List Bool) : ZMod (F.modulus (pairFst (pairFst z))) :=
  rawScaleAt F (pairFst z) (Nat.fromBitsLE (pairSnd z))

theorem rawScale_FP (F : Family) (a : Access F) : (fun z => residueBits (rawScale F z)) ∈ FP := by
  have HP : (fun z => pairFst (pairFst z)) ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HM : BinaryFn (fun z => F.modulus (pairFst (pairFst z))) := a.modulus.comp HP
  have HC : BinaryFn (fun z => cursor (pairFst z)) :=
    by
      have H : BinaryFn cursor := BinaryFn.fromBits BoundedFold.counter_mem_FP
      exact H.comp pairFst_mem_FP
  have HT : (fun z => BoundedFold.accumulator (pairFst z)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := BoundedFold.accumulator) pairFst_mem_FP BoundedFold.accumulator_mem_FP
  have HR := mem_FP_comp (mem_FP_pair HT a.index.bits_mem_FP) WordList.reader_FP
  have HN : BinaryFn (fun z => Nat.fromBitsLE (WordList.get (BoundedFold.accumulator (pairFst z))
      (F.index (pairFst (pairFst z)) (cursor (pairFst z)) (Nat.fromBitsLE (pairSnd z))))) :=
    BinaryFn.fromBits (mem_FP_of_eq HR (fun z => WordList.reader_packet _ _))
  have HE := ModularScalarFP.natCast HM _ HN
  have HO := ModularScalarFP.natCast HM (fun _ => 1) (BinaryFn.const 1)
  have H := (a.index.lt HC).ite_mem_FP HE HO
  exact mem_FP_of_eq H (fun z => by simp only [rawScale, rawScaleAt, factor]; split_ifs <;> simp only [Nat.cast_one])

def product (F : Family) (c : List Bool) (i : ℕ) (table : List Bool) : ZMod (F.modulus c) :=
  ∏ j ∈ Finset.range (F.arity c i), factor F c i table j

def rawProduct (F : Family) (p : List Bool) : ZMod (F.modulus (pairFst p)) :=
  product F (pairFst p) (cursor p) (BoundedFold.accumulator p)

theorem rawProduct_FP (F : Family) (a : Access F) : (fun p => residueBits (rawProduct F p)) ∈ FP := by
  have HM : BinaryFn (fun p => F.modulus (pairFst p)) := a.modulus.comp pairFst_mem_FP
  exact ModularProduct.evaluatorWithModulus_FP _ _ _ (rawScale_FP F a)
    HM.bits_mem_FP a.arity
    (fun p => F.modulus (pairFst p))
    (funext fun _ => Nat.fromBitsLE_bits _) _
    (fun p => Nat.pos_of_ne_zero (F.modulus_ne_zero (pairFst p))) (fun p j _ => by
      simp only [rawScale, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      exact congrArg (fun u => residueBits (rawScaleAt F u j)) (pairFst_pair p _))

def stepValue (F : Family) (c : List Bool) (i : ℕ) (table : List Bool) : ZMod (F.modulus c) :=
  ((F.leading c i : ZMod (F.modulus c)) * product F c i table ^ F.degree c i *
    (F.degree c i : ZMod (F.modulus c))) ^ F.exponent c i

def rawNext (F : Family) (p : List Bool) : ZMod (F.modulus (pairFst p)) :=
  stepValue F (pairFst p) (cursor p) (BoundedFold.accumulator p)

theorem rawNext_FP (F : Family) (a : Access F) : (fun p => residueBits (rawNext F p)) ∈ FP := by
  have HM : BinaryFn (fun p => F.modulus (pairFst p)) := a.modulus.comp pairFst_mem_FP
  have H0 := fun p => F.modulus_ne_zero (pairFst p)
  have HQ := ModularScalarFP.pow HM H0 _ a.degree (rawProduct F) (rawProduct_FP F a)
  have HA := ModularScalarFP.mul HM _ _ a.leading HQ
  have HD := ModularScalarFP.natCast HM _ a.degree
  have HB := ModularScalarFP.mul HM _ _ HA HD
  exact ModularScalarFP.pow HM H0 _ a.exponent _ HB

theorem factor_encoded (F : Family) (c : List Bool) (i : ℕ) (v : List (ZMod (F.modulus c)))
    (hv : v.length = i) (j : ℕ) :
    factor F c i (WordList.encode (v.map residueBits)) j = scale v (F.index c i j) := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  unfold factor scale
  by_cases h : F.index c i j < i
  · rw [ite_eq_left h, WordList.get_encode, List.getElem?_map,
      List.getElem?_eq_getElem (by omega)]
    simp only [Option.map_some, Option.getD_some, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.natCast_zmod_val]
  · rw [ite_eq_right h, List.getElem?_eq_none (by omega), Option.getD_none]

theorem stepValue_encoded (F : Family) (c : List Bool) (i : ℕ) (v : List (ZMod (F.modulus c)))
    (hv : v.length = i) : stepValue F c i (WordList.encode (v.map residueBits)) = next F c i v := by
  unfold stepValue next product
  congr 4
  apply Finset.prod_congr rfl
  intro j _hj
  exact factor_encoded F c i v hv j

def access (F : Family) (a : Access F) : ModularHistoryPass.Access (pass F) where
  count := a.count
  modulus := a.modulus
  step := fun p => residueBits (rawNext F p)
  step_FP := rawNext_FP F a
  step_eq := by
    intro c i v hv
    change residueBits (rawNext F (BoundedFold.packet c i (WordList.encode (v.map residueBits)))) =
      residueBits (next F c i v)
    simp only [rawNext, cursor, BoundedFold.counter_packet,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, BoundedFold.accumulator_packet]
    exact (congrArg (fun u => residueBits (stepValue F u i (WordList.encode (v.map residueBits))))
      (BoundedFold.context_packet c i _)).trans (congrArg residueBits (stepValue_encoded F c i v hv))

theorem table_FP (F : Family) (a : Access F) : ModularHistoryPass.run (pass F) (access F a) ∈ FP :=
  ModularHistoryPass.run_FP (pass F) (access F a)

theorem reader_FP (F : Family) (a : Access F) (j : List Bool → ℕ) (hj : BinaryFn j) :
    ModularHistoryPass.read (pass F) (access F a) j ∈ FP :=
  ModularHistoryPass.read_FP (pass F) (access F a) j hj

end LeanCanny.Algebra.IntegralDenominatorPass
