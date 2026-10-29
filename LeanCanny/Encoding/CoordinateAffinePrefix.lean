/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateAffineTower
public import LeanCanny.Encoding.FlatAffineCompleteVertices

/-! # Complete native sampling for coordinate-prefix constraints

A prefix level record activates precisely the coordinates before the selected
objective. Its remaining fields retain the ancestral levels. Consequently the
coordinate tower has its cone certificate by construction, and complete vertex
validity is in native PSPACE from the original readers alone.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateAffinePrefix
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open FlatAffineFullSourceTower (stage)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def cut (P : BoundedFullWriter.Readers) (objective : List Bool → ℕ) (q : List Bool) : ℕ :=
  min (objective (pairFst q)) (P.dim (pairFst (pairFst q)) + 3)

def setFlags (P : BoundedFullWriter.Readers) (objective : List Bool → ℕ) (z : List Bool) : List Bool :=
  pair ([decide (Nat.fromBitsLE (pairSnd (pairFst z)) < cut P objective (pairFst z))] ++
    (FlatAffineFullSourceTower.flags (pairSnd z)).drop 1) (pairSnd (pairSnd z))

def levels (P : BoundedFullWriter.Readers) (objective : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) : List Bool :=
  setFlags P objective (pair q (level q))

theorem levels_evaluator {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {objective : List Bool → ℕ} {level : List Bool → List Bool}
    (ho : UnaryFn objective) (hl : SpaceFunction level) : SpaceFunction (levels P objective level) := by
  have hc : UnaryFn (cut P objective) := (ho.comp pairFst_mem_FP).min
    (((hP.dim.comp pairFst_mem_FP).comp pairFst_mem_FP).add (UnaryFn.const 3))
  have hi : BinaryFn (fun z => Nat.fromBitsLE (pairSnd (pairFst z))) :=
    (BinaryFn.fromBits pairSnd_mem_FP).comp pairFst_mem_FP
  have hf := (hi.lt ((BinaryFn.ofUnary hc).comp pairFst_mem_FP)).flag_mem_FP
  have ht := drop_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (UnaryFn.const 1)
  have hb := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hw : setFlags P objective ∈ FP := mem_FP_pair (appendFn_mem_FP hf ht) hb
  exact hl.withInput.postcompose _ hw

def inputs (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) : FlatAffineFullSourceTower.Inputs :=
  CoordinateAffineTower.inputs P depth objective (levels P objective level)

theorem access {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (TermView.term (P.source u)).arity ≤ P.dim u) :
    (inputs P depth objective level).Access :=
  CoordinateAffineTower.access hP hd ho (levels_evaluator hP ho hl) hA

lemma active_iff (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j : Fin (P.dim u + 4)) :
    j ∈ FlatAffineFullSourceTower.free (inputs P depth objective level) u k ↔
      j.val < (CoordinateAffineTower.selected P objective u k).val := by
  simp [FlatAffineFullSourceTower.free, inputs, CoordinateAffineTower.inputs, levels, setFlags,
    FlatAffineFullSourceTower.levelQuery, stage, FlatAffineFullSourceTower.active,
    FlatAffineFullSourceTower.flags, cut, CoordinateAffineTower.selected, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem coneCertificate (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) : FlatAffinePowerPositive.ConeCertificate (inputs P depth objective level) := by
  apply CoordinateAffineTower.coneCertificate
  intro u k h
  have H := (active_iff P depth objective level u k.val _).mp h
  exact (Nat.lt_irrefl _) H

noncomputable def language (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  FlatAffineCompleteVertices.language (inputs P depth objective level) (coneCertificate P depth objective level)

theorem mem_PSPACE {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (TermView.term (P.source u)).arity ≤ P.dim u) : language P depth objective level ∈ PSPACE :=
  FlatAffineCompleteVertices.mem_PSPACE (access hP hd ho hl hA) (coneCertificate P depth objective level)

end LeanCanny.Encoding.CoordinateAffinePrefix
