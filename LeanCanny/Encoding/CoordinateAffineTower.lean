/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCoordinateCone
public import LeanCanny.Encoding.CoordinateAffineRecord
public import LeanCanny.Encoding.FlatAffinePowerInfinity

/-! # Native coordinate directions for complete affine towers

The objective reader selects a coordinate; all height normals are coordinate
vectors. An objective outside the active constraints supplies the actual
leading-cone certificate, independently of ancestral levels and affine
singularities. The record writer is polynomial time and has one-bit entries.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateAffineTower
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stage)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

def selected (P : BoundedFullWriter.Readers) (objective : List Bool → ℕ) (u : List Bool) (k : ℕ) :
    Fin (P.dim u + 4) := ⟨min (objective (stage u k)) (P.dim u + 3), by omega⟩

def inputs (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) : Inputs where
  source := P
  depth := depth
  width _ := 1
  direction q := CoordinateAffineRecord.record (P.dim (pairFst q) + 4)
    (min (objective q) (P.dim (pairFst q) + 3))
  level := level

theorem access {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (TermView.term (P.source u)).arity ≤ P.dim u) :
    (inputs P depth objective level).Access := by
  refine ⟨hP, hd, UnaryFn.const 1, SpaceFunction.ofFP _ ?_, hl, hA⟩
  exact CoordinateAffineRecord.record_FP ((hP.dim.comp pairFst_mem_FP).add (UnaryFn.const 4))
    (BinaryFn.ofUnary (ho.min ((hP.dim.comp pairFst_mem_FP).add (UnaryFn.const 3))))

lemma objective (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (i : Fin (P.dim u + 4)) :
    FlatAffineFullSourceTower.direction (inputs P depth objective level) u k 0 i =
      FermatCoordinateCone.normal (selected P objective u k) i := by
  simp only [FlatAffineFullSourceTower.direction, inputs, stage, pairFst_pair, Fin.val_zero,
    zero_mul, zero_add, FermatCoordinateCone.normal]
  exact CoordinateAffineRecord.objective _ (selected P objective u k) i

lemma normal (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j i : Fin (P.dim u + 4)) :
    FlatAffineFullSourceTower.direction (inputs P depth objective level) u k j.succ i =
      FermatCoordinateCone.normal j i := by
  simp only [FlatAffineFullSourceTower.direction, inputs, stage, pairFst_pair,
    FermatCoordinateCone.normal]
  exact CoordinateAffineRecord.normal _ _ j i

private theorem integer_cone {n : ℕ} (a : ℤ) (ha : a ≠ 0) (D : ℕ) (hD : 1 < D)
    (s : Finset (Fin n)) (r : Fin n) (hr : r ∉ s) :
    FlatAffinePowerTower.ConeRootFree (C a * ∑ i : Fin n, X i ^ D) s
      (Fin.cases (FermatCoordinateCone.normal r) FermatCoordinateCone.normal) := by
  apply FlatAffinePowerTower.coneRootFree_of_critical
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have H := FermatCoordinateCone.criticalRootFree (K := ℚ) (L := ℂ) (a : ℚ) ha' D hD s r hr
  convert H using 1 <;> simp [FermatAffineConeFlag.form, FermatCoordinateCone.normal]
  rfl

theorem coneCertificate (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool)
    (hfree : ∀ u (k : Fin (depth u)), selected P objective u k.val ∉
      FlatAffineFullSourceTower.free (inputs P depth objective level) u k.val) :
    FlatAffinePowerPositive.ConeCertificate (inputs P depth objective level) := by
  intro u k
  have htable : FlatAffineFullSourceTower.direction (inputs P depth objective level) u k.val =
      Fin.cases (FermatCoordinateCone.normal (selected P objective u k.val)) FermatCoordinateCone.normal := by
    funext j i
    refine Fin.cases ?_ (fun r => ?_) j
    · exact CoordinateAffineTower.objective P depth objective level u k.val i
    · exact normal P depth objective level u k.val r i
  rw [htable]
  apply integer_cone _ (IntegerRegularSource.leading_ne_zero _ _ _ one_ne_zero) _ ?_ _ _ (hfree u k)
  exact BoundedRegularSource.powerDegree_gt_one (BoundedFullWriter.size P u)

end LeanCanny.Encoding.CoordinateAffineTower
