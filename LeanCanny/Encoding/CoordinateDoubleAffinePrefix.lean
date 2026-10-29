/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatScaledCoordinateCone
public import LeanCanny.Encoding.CoordinateDoubleAffineRecord
public import LeanCanny.Encoding.CoordinateAffinePrefix

/-! # Complete coordinate-prefix towers with doubled normals

Doubled coordinate constraints support exact ancestral midpoint equations
with integer coefficients. Their native cone certificate and complete
vertices do not depend on regularity of finite critical roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffinePrefix
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stage)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

def inputs (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) : Inputs where
  source := P
  depth := depth
  width _ := 2
  direction q := CoordinateDoubleAffineRecord.record (P.dim (pairFst q) + 4)
    (min (objective q) (P.dim (pairFst q) + 3))
  level := CoordinateAffinePrefix.levels P objective level

theorem access {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (TermView.term (P.source u)).arity ≤ P.dim u) :
    (inputs P depth objective level).Access := by
  refine ⟨hP, hd, UnaryFn.const 2, SpaceFunction.ofFP _ ?_, CoordinateAffinePrefix.levels_evaluator hP ho hl, hA⟩
  exact CoordinateDoubleAffineRecord.record_FP ((hP.dim.comp pairFst_mem_FP).add (UnaryFn.const 4))
    (BinaryFn.ofUnary (ho.min ((hP.dim.comp pairFst_mem_FP).add (UnaryFn.const 3))))

lemma objective (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (i : Fin (P.dim u + 4)) :
    FlatAffineFullSourceTower.direction (inputs P depth objective level) u k 0 i =
      2 * FermatCoordinateCone.normal (CoordinateAffineTower.selected P objective u k) i := by
  simp only [FlatAffineFullSourceTower.direction, inputs, stage, pairFst_pair, Fin.val_zero,
    zero_mul, zero_add, FermatCoordinateCone.normal]
  exact CoordinateDoubleAffineRecord.objective _ (CoordinateAffineTower.selected P objective u k) i

lemma normal (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j i : Fin (P.dim u + 4)) :
    FlatAffineFullSourceTower.direction (inputs P depth objective level) u k j.succ i =
      2 * FermatCoordinateCone.normal j i := by
  simp only [FlatAffineFullSourceTower.direction, inputs, stage, pairFst_pair, FermatCoordinateCone.normal]
  exact CoordinateDoubleAffineRecord.normal _ _ j i

lemma active_iff (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j : Fin (P.dim u + 4)) :
    j ∈ FlatAffineFullSourceTower.free (inputs P depth objective level) u k ↔
      j.val < (CoordinateAffineTower.selected P objective u k).val :=
  CoordinateAffinePrefix.active_iff P depth objective level u k j

private theorem integer_cone {n : ℕ} (a : ℤ) (ha : a ≠ 0) (D : ℕ) (hD : 1 < D)
    (s : Finset (Fin n)) (r : Fin n) (hr : r ∉ s) :
    FlatAffinePowerTower.ConeRootFree (C a * ∑ i : Fin n, X i ^ D) s
      (Fin.cases (fun i => 2 * FermatCoordinateCone.normal r i)
        (fun j i => 2 * FermatCoordinateCone.normal j i)) := by
  apply FlatAffinePowerTower.coneRootFree_of_critical
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have H := FermatScaledCoordinateCone.criticalRootFree (K := ℚ) (L := ℂ) (a : ℚ) ha' D hD
    2 (by norm_num) (fun _ => 2) (fun _ => by norm_num) s r hr
  convert H using 1 <;> simp [FermatAffineConeFlag.form, FermatCoordinateCone.normal, apply_ite]

theorem coneCertificate (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) : FlatAffinePowerPositive.ConeCertificate (inputs P depth objective level) := by
  intro u k
  have htable : FlatAffineFullSourceTower.direction (inputs P depth objective level) u k.val =
      Fin.cases (fun i => 2 * FermatCoordinateCone.normal (CoordinateAffineTower.selected P objective u k.val) i)
        (fun j i => 2 * FermatCoordinateCone.normal j i) := by
    funext j i
    refine Fin.cases ?_ (fun r => ?_) j
    · exact CoordinateDoubleAffinePrefix.objective P depth objective level u k.val i
    · exact normal P depth objective level u k.val r i
  rw [htable]
  apply integer_cone _ (IntegerRegularSource.leading_ne_zero _ _ _ one_ne_zero) _
    (BoundedRegularSource.powerDegree_gt_one (BoundedFullWriter.size P u))
  intro h
  exact (Nat.lt_irrefl _) ((active_iff P depth objective level u k.val _).mp h)

noncomputable def language (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  FlatAffineCompleteVertices.language (inputs P depth objective level) (coneCertificate P depth objective level)

theorem mem_PSPACE {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (TermView.term (P.source u)).arity ≤ P.dim u) : language P depth objective level ∈ PSPACE :=
  FlatAffineCompleteVertices.mem_PSPACE (access hP hd ho hl hA) (coneCertificate P depth objective level)

end LeanCanny.Encoding.CoordinateDoubleAffinePrefix
