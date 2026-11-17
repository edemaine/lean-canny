/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.UnaryModularList
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import LeanCanny.CountingHierarchy.ModularArithmetic
public import CslibFrontier.Computability.Circuit.Rational.Runtime.Determinant
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv

/-! # Determinants of polynomial-size matrices at the entry evaluator's level -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM
open Cslib.Circuits

@[expose] def modularMatrixRows (n : ℕ) (entries : List ℕ) : List (List ℤ) :=
  tabulateTable n n (fun i j => ((entries[i * n + j]?.getD 0 : ℕ) : ℤ))

@[expose] noncomputable def modularMatrixDeterminant (p n : ℕ) (entry : ℕ → ℕ) : ℕ :=
  (Rational.detRows (modularMatrixRows n (unaryModularList (n * n) (max 1 p) entry)) % (p : ℤ)).toNat

theorem modularMatrixRows_polyTime {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {entries : α → List ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (he : ComputableInPolyTime entries enc (encList encNat)) :
    ComputableInPolyTime (fun w => modularMatrixRows (n w) (entries w)) enc encIntTable := by
  have hctx : ComputableInPolyTime (fun q : TableIndex α => q.1.1)
      (encPair (encPair enc encUnary) encUnary) enc := by fun_prop
  have hr : ComputableInPolyTime (fun q : TableIndex α => q.1.2)
      (encPair (encPair enc encUnary) encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hc : ComputableInPolyTime (fun q : TableIndex α => q.2)
      (encPair (encPair enc encUnary) encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hnb := (ComputableInPolyTime.unary_to_binary.comp hn).comp hctx
  have hindex := ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_mul' hr hnb) hc
  have hlookup : ComputableInPolyTime
      (fun q : TableIndex α => ((entries q.1.1)[q.1.2 * n q.1.1 + q.2]?.getD 0))
      (encPair (encPair enc encUnary) encUnary) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 (he.comp hctx) hindex
  exact computableInPolyTime_tabulateTable hn hn (ComputableInPolyTime.intBin_natCast.comp hlookup)

/-- Each entry is reduced before collection. The resulting short integer
table is passed to Frontier's certified polynomial-time determinant program. -/
theorem modularMatrixDeterminant_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    {p n : α → ℕ} {entry : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (he : entry ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => modularMatrixDeterminant (p w) (n w) (fun i => entry (w, i))) ∈
      CountingFunction a enc encNat := by
  have hq := ComputableInPolyTime.binary_max' (.const 1) hp
  have hlist := unaryModularList_mem (ComputableInPolyTime.unary_mul' hn hn) hq
    (fun _ => lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)) he
  have hrows := CountingFunction.map (CountingFunction.prod (CountingFunction.of_polyTime hn) hlist)
    (modularMatrixRows_polyTime (ComputableInPolyTime.fst encUnary (encList encNat))
      (ComputableInPolyTime.snd encUnary (encList encNat)))
  have hdet := CountingFunction.map hrows Rational.detRows_polytime
  have hres := CountingFunction.map (CountingFunction.prod hdet (CountingFunction.of_polyTime hp))
    ComputableInPolyTime.intBin_emodNat
  simpa only [modularMatrixDeterminant] using hres

lemma unaryModularList_get (n p : ℕ) (f : ℕ → ℕ) {i : ℕ} (hi : i < n) :
    (unaryModularList n p f)[i]?.getD 0 = f i % p := by
  simp [unaryModularList, hi]

/-- Only the residues of the entries are required, including for singular
matrices. The determinant program itself runs on ordinary short integers. -/
theorem modularMatrixDeterminant_cast {p n : ℕ} [Fact p.Prime]
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (entry : ℕ → ℕ)
    (he : ∀ i j : Fin n, (entry (i.val * n + j.val) : ZMod p) = A i j) :
    (modularMatrixDeterminant p n entry : ZMod p) = A.det := by
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j => ((entry (i.val * n + j.val) % p : ℕ) : ℤ)
  have hrows : Rational.detRows (modularMatrixRows n (unaryModularList (n * n) (max 1 p) entry)) = M.det := by
    apply Rational.detRows_eq_det_of_rowEntry M
    · simp only [modularMatrixRows, length_tabulateTable]
    · intro i j
      rw [modularMatrixRows, rowEntry_tabulateTable, ite_eq_left ⟨i.isLt, j.isLt⟩,
        unaryModularList_get, max_eq_right (Fact.out : p.Prime).one_le]
      exact lt_of_lt_of_le (by nlinarith [j.isLt] : i.val * n + j.val < (i.val + 1) * n)
        (Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt))
  rw [modularMatrixDeterminant, hrows]
  have hp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hval := congrArg Int.toNat (ZMod.val_intCast (n := p) M.det)
  simp only [Int.toNat_natCast] at hval
  rw [← hval, ZMod.natCast_zmod_val]
  change (Int.castRingHom (ZMod p)) M.det = A.det
  rw [RingHom.map_det]
  congr 1
  ext i j
  change (((entry (i.val * n + j.val) % p : ℕ) : ℤ) : ZMod p) = A i j
  rw [Int.cast_natCast, ZMod.natCast_mod]
  exact he i j

end LeanCanny.CountingHierarchy
