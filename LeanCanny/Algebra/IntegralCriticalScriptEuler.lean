/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalOriginalCoefficient
public import LeanCanny.Algebra.IntegralCriticalScriptSelectedFP
public import LeanCanny.Algebra.IntegralEulerLowerController
public import LeanCanny.Algebra.IntegralEulerObjectiveController
public import LeanCanny.Algebra.IntegralEulerSumController
public import LeanCanny.Algebra.IntegralCriticalCoordinateProductController

/-! # Actual Euler source access from creating-command metadata

The canonical query source fixes the actual old algebra and all Euler
polynomials. Original coefficients use the diagonal integer leaf. Height,
denominator, and leading readers below are explicit semantic functions;
no evaluator or space certificate for them is an input to this adapter.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScriptEulerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def source (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : IntegralEulerBits.Source :=
  (IntegralCriticalScriptQueryBits.generatorSource F q).toEuler

structure Controls (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : Prop where
  script : IntegralCriticalScriptGeneratorBits.Controls F
  sourceWidth : UnaryFn F.sourceWidth
  objective : BinaryFn (fun c => (IntegralCriticalScript.chosen (F.rules c) (F.selected c)).objective)
  target : BinaryFn q.target
  row : BinaryFn (fun c => (q.row c).val)
  col : BinaryFn (fun c => (q.col c).val)

theorem free_unary (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (h : Controls F q) : UnaryFn (source F q).free :=
  ((h.script.ambient.sub (IntegralCriticalScriptGeneratorBits.offset_unary F h.script)).add (UnaryFn.const 1))

theorem rank_binary (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (h : Controls F q) : BinaryFn (source F q).rank :=
  ((BinaryFn.const 2).powUnary h.script.width).powUnary (IntegralCriticalScriptGeneratorBits.arity_unary F h.script)

noncomputable def scalarCoefficientAt (F : IntegralCriticalScriptGeneratorBits.Queries) (c : List Bool) (k : ℕ) : List Bool :=
  residueBits (IntegralCriticalOriginalCoefficientBits.coefficient (IntegralCriticalScriptQueryBits.birthFamilies F) c k : ZMod (F.modulus c))

noncomputable def scalarCoefficient (F : IntegralCriticalScriptGeneratorBits.Queries) (p : List Bool) : List Bool :=
  scalarCoefficientAt F (pairFst p) (Nat.fromBitsLE (pairSnd p))

noncomputable def heightAt (S : IntegralClearedCoefficientBits.Source) (c : List Bool) (i r t : ℕ) : List Bool := by
  let := S.ring c
  have HP : 0 < S.rank c := (Nat.zero_le (S.row c).val).trans_lt (S.row c).isLt
  exact residueBits ((Algebra.leftMulMatrix (S.basis c) (S.height c i)
    ⟨r % S.rank c, Nat.mod_lt _ HP⟩ ⟨t % S.rank c, Nat.mod_lt _ HP⟩ : ℤ) : ZMod (S.modulus c))

noncomputable def heightReader (S : IntegralClearedCoefficientBits.Source) (p : List Bool) : List Bool :=
  heightAt S (pairFst p) (Nat.fromBitsLE (IntegralPowerProductBits.factorWord p))
    (Nat.fromBitsLE (IntegralPowerProductBits.rowWord p)) (Nat.fromBitsLE (IntegralPowerProductBits.colWord p))

theorem height_packet (S : IntegralClearedCoefficientBits.Source) (c : List Bool) (i : ℕ) (r t : Fin (S.rank c)) :
    heightReader S (pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      letI := S.ring c
      residueBits ((Algebra.leftMulMatrix (S.basis c) (S.height c i) r t : ℤ) : ZMod (S.modulus c)) := by
  let := S.ring c
  simp only [heightReader, IntegralPowerProductBits.factorWord, IntegralPowerProductBits.rowWord,
    IntegralPowerProductBits.colWord, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  simp only [heightAt, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]

noncomputable def access (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (h : Controls F q) : IntegralEulerBits.Access (source F q) where
  arity := h.script.ambient.add (UnaryFn.const 1)
  free := free_unary F q h
  offset := IntegralCriticalScriptGeneratorBits.offset_unary F h.script
  sourceWidth := h.sourceWidth
  targetWidth := PurePowerReductionBounds.width_unary (free_unary F q h) h.script.degree
  rank := rank_binary F q h
  allowance := h.script.degree
  target := h.target
  row := h.row
  col := h.col
  modulus := h.script.modulus
  coefficient := IntegralCriticalOriginalCoefficientBits.reader (scalarCoefficient F)
  height := heightReader (source F q).toGradient.toFrozen.toSource
  denominator c := residueBits ((source F q).denominator c : ZMod (F.modulus c))
  coefficient_eq c k r t :=
    IntegralCriticalOriginalCoefficientBits.reader_packet (IntegralCriticalScriptQueryBits.birthFamilies F) q.toQueries
      (scalarCoefficient F) (fun c k => by
        simp only [scalarCoefficient, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
        rfl) c k r t
  height_eq := height_packet _
  denominator_eq _ := rfl
  leading c := residueBits ((source F q).leading c : ZMod (F.modulus c))
  leading_eq _ := rfl
  degree := h.script.degree
  objective := h.objective.mod (BinaryFn.ofUnary (free_unary F q h))

theorem leading_FP (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (h : Controls F q)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatCompanionBits.metadata F)) :
    (access F q h).leading ∈ FP :=
  mem_FP_of_eq (IntegralCriticalScriptSelectedFP.leading_FP F h.script n) (fun _ => rfl)

/-- Normalization changes the spatial layout, while preserving every lower polynomial. -/
theorem lower_polynomial (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool)
    (i : Fin ((source F q).free c)) :
    letI := (source F q).ring c
    (source F q).lowerPolynomial c i =
      (IntegralHistoryCriticalBits.euler (IntegralCriticalScriptQueryBits.generatorFamily F q)).lowerPolynomial c i := rfl

end LeanCanny.Algebra.IntegralCriticalScriptEulerBits
