/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceLevels

/-! # A single native sampler family for shared-source coordinate histories -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (stage levelQuery)
set_option backward.isDefEq.respectTransparency false

def queryBase (q : List Bool) : List Bool := base (LeanCanny.pairFst (LeanCanny.pairFst q))
def queryHistory (q : List Bool) : List Bool := history (LeanCanny.pairFst (LeanCanny.pairFst q))

theorem queryBase_FP : queryBase ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP

theorem queryHistory_FP : queryHistory ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

def sourceLevelQuery (q : List Bool) : List Bool :=
  LeanCanny.pair (sourceStage (LeanCanny.pairFst q)) (BinaryNatCode.encode (Nat.fromBitsLE (LeanCanny.pairSnd q)))

theorem sourceLevelQuery_FP : sourceLevelQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP sourceStage_FP) (BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP

def currentLevelQuery (d : List Bool → ℕ) (q : List Bool) : List Bool :=
  levelQuery (queryBase q) (d (queryBase q)) (Nat.fromBitsLE (LeanCanny.pairSnd q))

theorem currentLevelQuery_FP {d : List Bool → ℕ} (hd : UnaryFn d) : currentLevelQuery d ∈ FP :=
  mem_FP_pair (mem_FP_pair queryBase_FP (BinaryFn.ofUnary (hd.comp queryBase_FP)).bits_mem_FP)
    (BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP

def generatedIndex (d old : List Bool → ℕ) (q : List Bool) : ℕ :=
  min (Nat.fromBitsLE (LeanCanny.pairSnd q) - seedCoordinate d old (queryBase q)) (queryHistory q).length

theorem generatedIndex_unary {d old : List Bool → ℕ} (hd : UnaryFn d) (ho : UnaryFn old) :
    UnaryFn (generatedIndex d old) := by
  have hb := (BinaryFn.fromBits pairSnd_mem_FP).sub (BinaryFn.ofUnary ((seedCoordinate_unary hd ho).comp queryBase_FP))
  apply (UnaryFn.fromBitsLE_min hb.bits_mem_FP (UnaryFn.length queryHistory_FP)).of_eq
  intro q
  simp only [generatedIndex, BinaryNatCode.encode, Nat.fromBitsLE_bits]

def levels (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ) (level : List Bool → List Bool)
    (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (LeanCanny.pairSnd (LeanCanny.pairFst q)) < d (queryBase q) then level (sourceLevelQuery q) else
    if seedCoordinate d old (queryBase q) ≤ Nat.fromBitsLE (LeanCanny.pairSnd q) ∧
      Nat.fromBitsLE (LeanCanny.pairSnd q) < seedCoordinate d old (queryBase q) +
        completed (d (queryBase q)) (queryHistory q) (Nat.fromBitsLE (LeanCanny.pairSnd (LeanCanny.pairFst q))) then
      generated (P.dim (queryBase q) + 4) (d (queryBase q)) (seedCoordinate d old (queryBase q))
        (queryHistory q) (generatedIndex d old q) else
      if queryHistory q = [] then level (currentLevelQuery d q) else
        FlatAffineFrozenLevelRecord.freeze (d (queryBase q)) (level (currentLevelQuery d q))

theorem levels_evaluator {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level) : SpaceFunction (levels P d old level) := by
  have hD := hd.comp queryBase_FP
  have hC := (seedCoordinate_unary hd ho).comp queryBase_FP
  have hK : BinaryFn (fun q => Nat.fromBitsLE (LeanCanny.pairSnd (LeanCanny.pairFst q))) :=
    (BinaryFn.fromBits pairSnd_mem_FP).comp pairFst_mem_FP
  have hJ := BinaryFn.fromBits pairSnd_mem_FP
  have hCount := completed_unary hD queryHistory_FP hK
  have hBefore := hK.lt (BinaryFn.ofUnary hD)
  have hBorn := ((BinaryFn.ofUnary hC).le hJ).and (hJ.lt (BinaryFn.ofUnary (hC.add hCount)))
  have hEmpty := Brackets.stringEq_fppred queryHistory_FP (constFn_mem_FP [])
  have E := hl.precompose _ (currentLevelQuery_FP hd)
  have D := SpaceFunction.branch _ hEmpty.flag_mem_FP E (FlatAffineFrozenLevelRecord.reader_evaluator hD E)
  have G := SpaceFunction.ofFP _ (generated_FP ((hP.dim.comp queryBase_FP).add (UnaryFn.const 4))
    hD hC queryHistory_FP (generatedIndex_unary hd ho))
  have B := SpaceFunction.branch _ hBorn.flag_mem_FP G D
  exact (SpaceFunction.branch _ hBefore.flag_mem_FP (hl.precompose _ sourceLevelQuery_FP) B).congr
    (funext fun q => by simp only [levels, Function.comp_apply, decide_eq_true_eq, FlatAffineFrozenLevelRecord.reader])

theorem levels_stage (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ) (level : List Bool → List Bool)
    (q : List Bool) (k j : ℕ) :
    levels P d old level (levelQuery q k j) =
      levelAt (P.dim (base q) + 4) (d (base q)) (seedCoordinate d old (base q)) (history q)
        (fun a b => level (levelQuery (base q) a b)) k j := by
  simp only [levels, levelAt, generatedIndex, queryBase, queryHistory, sourceLevelQuery, currentLevelQuery,
    sourceStage, levelQuery, stage, LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

def inputs (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ) (level : List Bool → List Bool) :
    FlatAffineFullSourceTower.Inputs :=
  CoordinateDoubleAffinePrefix.inputs (readers P) (depth d) (objective d old) (levels P d old level)

theorem access {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) : (inputs P d old level).Access :=
  CoordinateDoubleAffinePrefix.access (readers_polyTime hP) (depth_unary hd) (objective_unary hd ho)
    (levels_evaluator hP hd ho hl) (fun q => hA (base q))

theorem cone (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ) (level : List Bool → List Bool) :
    FlatAffinePowerPositive.ConeCertificate (inputs P d old level) :=
  CoordinateDoubleAffinePrefix.coneCertificate (readers P) (depth d) (objective d old) (levels P d old level)

end LeanCanny.Encoding.CoordinateDoubleAffineTrace
