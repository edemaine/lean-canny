/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CoefficientEvaluation
public import Mathlib.Algebra.BigOperators.Fin
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Short addresses for finite-field grids

An address below `p^n` enumerates one point in the `n`-dimensional prime-field
grid. Decoding the address and forming Fourier weights are ordinary
polynomial-time computations when `n` is unary and all other numbers are binary.
Thus the whole grid can be handled by one counting sum.
-/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators

/-- The first `n` base-`p` digits, least significant coordinate first. -/
@[expose] def gridPoint (p n r : ℕ) : List ℕ :=
  (List.range n).map (fun i => r / p ^ i % p)

@[simp] theorem gridPoint_length (p n r : ℕ) : (gridPoint p n r).length = n := by
  simp [gridPoint]

theorem gridPoint_get {p n r i : ℕ} (hi : i < n) :
    (gridPoint p n r)[i]?.getD 0 = r / p ^ i % p := by
  simp [gridPoint, hi]

/-- Modular Fourier monomials are multiplied as a polynomially long list.
Every factor already has binary length bounded by the input modulus. -/
@[expose] def gridWeight (p n : ℕ) (β z : List ℕ) : ℕ :=
  ((List.range n).map (fun i => powMod p (z[i]?.getD 0) (p - 1 - β[i]?.getD 0))).prod

theorem gridPoint_polyTime {α : Type} {enc : α ↪ List Bool} {p n r : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hr : ComputableInPolyTime r enc encNat) :
    ComputableInPolyTime (fun w => gridPoint (p w) (n w) (r w)) enc (encList encNat) := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc encUnary)
  have hr' := hr.comp (ComputableInPolyTime.fst enc encUnary)
  have hpower := ComputableInPolyTime.binary_pow' hp'
    (ComputableInPolyTime.snd enc encUnary)
  have hdigit := ComputableInPolyTime.binary_mod.comp
    ((ComputableInPolyTime.binary_div' hr' hpower).prod hp')
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn) hdigit

theorem gridWeight_polyTime {α : Type} {enc : α ↪ List Bool}
    {p n : α → ℕ} {β z : α → List ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hβ : ComputableInPolyTime β enc (encList encNat))
    (hz : ComputableInPolyTime z enc (encList encNat)) :
    ComputableInPolyTime (fun w => gridWeight (p w) (n w) (β w) (z w)) enc encNat := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc encUnary)
  have hz' := hz.comp (ComputableInPolyTime.fst enc encUnary)
  have hβ' := hβ.comp (ComputableInPolyTime.fst enc encUnary)
  have hi := ComputableInPolyTime.snd enc encUnary
  have hx : ComputableInPolyTime
      (fun q : α × ℕ => (z q.1)[q.2]?.getD 0) (encPair enc encUnary) encNat := by
    fun_prop
  have he : ComputableInPolyTime
      (fun q : α × ℕ => p q.1 - 1 - (β q.1)[q.2]?.getD 0)
      (encPair enc encUnary) encNat := by
    fun_prop
  exact ComputableInPolyTime.binary_prod.comp
    (ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn)
      (computableInPolyTime_powMod hp' hx he))

theorem gridWeight_cast {p : ℕ} [Fact p.Prime] (n : ℕ) (β z : List ℕ) :
    (gridWeight p n β z : ZMod p) =
      ∏ i : Fin n, (z[i.val]?.getD 0 : ZMod p) ^ (p - 1 - β[i.val]?.getD 0) := by
  rw [gridWeight, Nat.cast_list_prod, List.map_map,
    ← List.prod_toFinset _ List.nodup_range, List.toFinset_range, Finset.prod_range]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Function.comp_apply, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero,
    ZMod.natCast_mod, Nat.cast_pow]

private noncomputable def gridFieldEquiv (p n : ℕ) [NeZero p] :
    (Fin n → Fin p) ≃ (Fin n → ZMod p) where
  toFun z i := (z i : ℕ)
  invFun z i := ⟨(z i).val, ZMod.val_lt _⟩
  left_inv z := funext fun i => Fin.ext (ZMod.val_natCast_of_lt (z i).isLt)
  right_inv z := funext fun i => ZMod.natCast_zmod_val (z i)

/-- A single natural-number range enumerates the entire grid exactly once.
The empty grid has its one empty point, including at zero variables. -/
theorem sum_gridPoint {p n : ℕ} [NeZero p] {M : Type*} [AddCommMonoid M]
    (F : (Fin n → ZMod p) → M) :
    (∑ r ∈ Finset.range (p ^ n),
      F (fun i => ((gridPoint p n r)[i.val]?.getD 0 : ZMod p))) = ∑ z, F z := by
  have hpoint (r : ℕ) (i : Fin n) :
      (gridPoint p n r)[i.val]?.getD 0 = r / p ^ i.val % p := gridPoint_get i.isLt
  simp_rw [hpoint]
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ z : Fin n → Fin p, F (fun i => (z i : ℕ)) := by
      exact (finFunctionFinEquiv : (Fin n → Fin p) ≃ Fin (p ^ n)).symm.sum_comp
        (fun z => F (fun i => (z i : ℕ)))
    _ = ∑ z, F z := (gridFieldEquiv p n).sum_comp F

end LeanCanny.CountingHierarchy
