/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalTotalCompanionSource

/-! # Native scalar companion access without coefficient evaluator premises

The coefficient function is semantic data. Its space or time cost is not
an input to the native local controller certificate.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] coefficient leading leadingInteger

noncomputable def coefficientAt (F : Scripts) (q : List Bool) (k r t : ℕ) : List Bool :=
  residueBits (coefficient F q k
    ⟨r % oldRank F q, Nat.mod_lt _ (oldRank_pos F q)⟩ ⟨t % oldRank F q, Nat.mod_lt _ (oldRank_pos F q)⟩)

attribute [local irreducible] coefficientAt

noncomputable def entry (F : Scripts) (p : List Bool) : List Bool :=
  coefficientAt F (pairFst p) (Nat.fromBitsLE (IntegralPowerProductBits.factorWord p))
    (Nat.fromBitsLE (IntegralPowerProductBits.rowWord p)) (Nat.fromBitsLE (IntegralPowerProductBits.colWord p))

theorem entry_packet (F : Scripts) (q : List Bool) (k : ℕ) (r t : Fin (oldRank F q)) :
    entry F (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      residueBits (coefficient F q k r t) := by
  unfold entry
  simp only [pairFst_pair, IntegralPowerProductBits.factorWord, IntegralPowerProductBits.rowWord,
    IntegralPowerProductBits.colWord, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold coefficientAt
  simp only [Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]

attribute [local irreducible] entry

noncomputable def access (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) :
    IntegralScalarGeneratorBits.Access (family F) where
  width := oldRank_binary F a
  scalarDegree := scalarDegree_binary F a
  selectedDegree := selectedDegree_binary F a n
  modulus := IntegralCriticalHistoryTask.modulus_binary _ a.toAccess
  oldRow := (row_binary F a).div (scalarDegree_binary F a)
  oldCol := (col_binary F a).div (scalarDegree_binary F a)
  row := (row_binary F a).mod (scalarDegree_binary F a)
  col := (col_binary F a).mod (scalarDegree_binary F a)
  entry := entry F
  entry_eq := entry_packet F
  leading q := residueBits (leading F q)
  leading_eq _ := rfl

end LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
