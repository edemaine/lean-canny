/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalScriptOrigin

/-! # Creating companion entries as functions of the whole actual family

Packaging the basis and polynomial together permits exact source transport
through a selected script prefix, including all dependent carrier fields.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalCreatingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower UniformIntegralPrefix FixedWidthPolynomial
open IntegralCriticalScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def creatingPrefix (F : IntegralHistoryCriticalBits.Family) :=
  UniformIntegralPrefix.step (F.scalarPrefix []) (F.data []).birth_bound (Nat.two_pow_pos (F.width []))
    ((IntegralHistoryCriticalBits.source F).annihilator []) (IntegralScalarRootHistoryBounds.degree F [])

noncomputable def value (F : IntegralHistoryCriticalBits.Family) (row col modulus : ℕ) : List Bool :=
  let P := creatingPrefix F
  residueBits ((Algebra.leftMulMatrix P.basis.finBasis (AdjoinRoot.root _)
    ⟨row % count (F.birth [] + 1) (F.width []), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨col % count (F.birth [] + 1) (F.width []), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩ : ℤ) : ZMod modulus)

theorem value_mod (F : IntegralHistoryCriticalBits.Family) (row col modulus : ℕ) :
    value F (row % count (F.birth [] + 1) (F.width []))
      (col % count (F.birth [] + 1) (F.width [])) modulus = value F row col modulus := by
  unfold value
  simp only [Nat.mod_mod]

theorem birth_value {S B n W D C : ℕ} (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length)
    (r t : Fin (count ((older rules i).length + 1) B)) (modulus : ℕ) :
    value (birthFamily rules h hN i) r.val t.val modulus = residueBits
      ((Algebra.leftMulMatrix (birthStep rules h hN i).scalarPrefix.basis.finBasis
        (AdjoinRoot.root _) r t : ℤ) : ZMod modulus) := by
  unfold value
  change residueBits ((Algebra.leftMulMatrix (birthStep rules h hN i).scalarPrefix.basis.finBasis
    (AdjoinRoot.root _) ⟨r.val % count ((older rules i).length + 1) B, _⟩
      ⟨t.val % count ((older rules i).length + 1) B, _⟩ : ℤ) : ZMod modulus) = _
  simp only [Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]

theorem radix {S B n W D C : ℕ} (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length) :
    (origin rules hN h i).chain.radix = count i.val B := by
  exact (origin rules hN h i).toGeneratorOrigin.radix_eq

theorem retained_value {S B n W D C : ℕ} (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length)
    (r t : Fin (count rules.length B)) (modulus : ℕ) :
    residueBits ((Algebra.leftMulMatrix (run rules h hN).scalarPrefix.basis.finBasis
      ((run rules h hN).bank.numerator i) r t : ℤ) : ZMod modulus) =
      if r.val % count i.val B = t.val % count i.val B then
        value (birthFamily rules h hN i) (r.val / count i.val B) (t.val / count i.val B) modulus else [] := by
  rw [run_generators, (origin rules hN h i).matrix]
  rw [radix]
  split_ifs with he
  · rw [← birth_value rules h hN i ((origin rules hN h i).chain.oldIndex r)
      ((origin rules hN h i).chain.oldIndex t) modulus]
    simp only [Chain.oldIndex, radix]
  · simp [Int.cast_zero, residueBits, BinaryNatCode.encode]

theorem prefix_birth_value {S B n W D C : ℕ} (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (j : ℕ) (hj : j ≤ rules.length)
    (i : Fin (past rules j).length) (r t modulus : ℕ) :
    value (birthFamily (past rules j) (past_bound rules h j) hN i) r t modulus =
      value (birthFamily rules h hN (pastIndex rules j hj i)) r t modulus := by
  rw [birthFamily_past]

end LeanCanny.Algebra.IntegralCriticalCreatingBits
