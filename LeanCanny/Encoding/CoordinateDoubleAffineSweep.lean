/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineSliceRegularity
public import LeanCanny.Algebra.TriangularPolynomialPrefixCongruence

/-! # Native coordinate sweeps preserve all earlier stage records

At a nonterminal slice, advance only the newest objective by one coordinate.
The previous objective becomes an active height to sweep. Every earlier
objective, normal, flag, and ancestral level record remains the original
record, so the existing frozen parent equations are retained.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineSweep
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (stage levelQuery)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def objective (depth old : List Bool → ℕ) (q : List Bool) : ℕ :=
  if Nat.fromBitsLE (pairSnd q) = depth (pairFst q) then old q + 1 else old q

theorem objective_unary {depth old : List Bool → ℕ} (hd : UnaryFn depth) (ho : UnaryFn old) :
    UnaryFn (objective depth old) := by
  have H := (BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.ofUnary (hd.comp pairFst_mem_FP))
  exact H.computable.ite_decide (ho.add (UnaryFn.const 1)) ho

theorem objective_stage (depth old : List Bool → ℕ) (u : List Bool) (k : ℕ) :
    objective depth old (stage u k) = if k = depth u then old (stage u k) + 1 else old (stage u k) := by
  simp only [objective, stage, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem objective_before (depth old : List Bool → ℕ) (u : List Bool) (k : ℕ) (hk : k < depth u) :
    objective depth old (stage u k) = old (stage u k) := by
  rw [objective_stage, ite_eq_right (Nat.ne_of_lt hk)]

def inputs (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ) (level : List Bool → List Bool) :
    FlatAffineFullSourceTower.Inputs := CoordinateDoubleAffinePrefix.inputs P depth (objective depth old) level

theorem access {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) : (inputs P depth old level).Access :=
  CoordinateDoubleAffinePrefix.access hP hd (objective_unary hd ho) hl hA

theorem cone (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ) (level : List Bool → List Bool) :
    FlatAffinePowerPositive.ConeCertificate (FlatAffineCompleteRootStages.next (inputs P depth old level)) :=
  CoordinateDoubleAffineSliceRegularity.cone P depth (objective depth old) level

theorem direction_before (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (hk : k < depth u) :
    FlatAffineFullSourceTower.direction (inputs P depth old level) u k =
      FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P depth old level) u k := by
  funext r i
  change FlatAffineFullSourceTower.integer 2
      (CoordinateDoubleAffineRecord.record (P.dim (pairFst (stage u k)) + 4)
        (min (objective depth old (stage u k)) (P.dim (pairFst (stage u k)) + 3)))
      (r.val * (P.dim u + 4) + i.val) =
    FlatAffineFullSourceTower.integer 2
      (CoordinateDoubleAffineRecord.record (P.dim (pairFst (stage u k)) + 4)
        (min (old (stage u k)) (P.dim (pairFst (stage u k)) + 3)))
      (r.val * (P.dim u + 4) + i.val)
  rw [objective_before depth old u k hk]

theorem level_record_before (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k j : ℕ) (hk : k < depth u) :
    (inputs P depth old level).level (levelQuery u k j) =
      (CoordinateDoubleAffinePrefix.inputs P depth old level).level (levelQuery u k j) := by
  unfold inputs CoordinateDoubleAffinePrefix.inputs CoordinateAffinePrefix.levels
    CoordinateAffinePrefix.setFlags CoordinateAffinePrefix.cut
  simp only [levelQuery, pairFst_pair, pairSnd_pair, objective_before depth old u k hk]

theorem free_before (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (hk : k < depth u) :
    FlatAffineFullSourceTower.free (inputs P depth old level) u k =
      FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth old level) u k := by
  unfold FlatAffineFullSourceTower.free
  apply Finset.filter_congr
  intro j _
  rw [level_record_before P depth old level u k j.val hk]

theorem level_before (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (hk : k < depth u)
    (j : Fin (P.dim u + 4)) :
    FlatAffineFullSourceTower.level (inputs P depth old level) u k j =
      FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u k j := by
  let decode (r : List Bool) : FlatAffineCriticalTower.Level (P.dim u + 4) k ℤ :=
    let a := fun i : Fin (P.dim u + 4) => FlatAffineFullSourceTower.integer 2 (FlatAffineFullSourceTower.normal r) i.val
    if hk : 0 < k then
      let l : Fin k := ⟨min (Nat.fromBitsLE (FlatAffineFullSourceTower.left r)) (k - 1), by omega⟩
      let h : Fin k := ⟨min (Nat.fromBitsLE (FlatAffineFullSourceTower.right r)) (k - 1), by omega⟩
      if FlatAffineFullSourceTower.tag r = 1 then .height l a
      else if FlatAffineFullSourceTower.tag r = 2 then .midpoint l h a
      else .constant (FlatAffineFullSourceTower.integer 2 (FlatAffineFullSourceTower.constant r) 0)
    else .constant (FlatAffineFullSourceTower.integer 2 (FlatAffineFullSourceTower.constant r) 0)
  exact congrArg decode (level_record_before P depth old level u k j.val hk)

theorem family_row_before (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (hk : k < depth u) :
    (FlatAffineFullSourceTower.family (inputs P depth old level) u).row k =
      (FlatAffineFullSourceTower.family (CoordinateDoubleAffinePrefix.inputs P depth old level) u).row k := by
  have HF := free_before P depth old level u k hk
  have HD := direction_before P depth old level u k hk
  have HL := funext (level_before P depth old level u k hk)
  let build (s : Finset (Fin (P.dim u + 4))) (a : Fin (P.dim u + 4 + 1) → Fin (P.dim u + 4) → ℤ)
      (b : Fin (P.dim u + 4) → FlatAffineCriticalTower.Level (P.dim u + 4) k ℤ) :=
    fun i : Fin (FlatAffineCriticalTower.width (P.dim u + 4)) =>
      MvPolynomial.rename
        (Equiv.sumCongr (Equiv.refl (FlatAffineCriticalTower.Ancestors (P.dim u + 4) k))
          (FlatAffineCriticalTower.blockEquiv (P.dim u + 4)))
        (FlatAffineCriticalStage.row (BoundedFullCriticalSamples.polynomial P u) s a
          (fun j => (b j).polynomial) ((FlatAffineCriticalTower.blockEquiv (P.dim u + 4)).symm i))
  change build (FlatAffineFullSourceTower.free (inputs P depth old level) u k)
      (FlatAffineFullSourceTower.direction (inputs P depth old level) u k)
      (FlatAffineFullSourceTower.level (inputs P depth old level) u k) =
    build (FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth old level) u k)
      (FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P depth old level) u k)
      (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u k)
  rw [HF, HD, HL]

theorem parent_system (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    FlatAffineFullSourceTower.system (inputs P depth old level) u =
      FlatAffineFullSourceTower.system (CoordinateDoubleAffinePrefix.inputs P depth old level) u :=
  TriangularPolynomialIndexing.system_congr _ _ (depth u) (family_row_before P depth old level u)

theorem newest_selected (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ) (u : List Bool)
    (hn : old (stage u (depth u)) < P.dim u + 3) :
    (CoordinateAffineTower.selected P (objective depth old) u (depth u)).val = old (stage u (depth u)) + 1 := by
  change min (objective depth old (stage u (depth u))) (P.dim u + 3) = _
  rw [objective_stage, ite_eq_left rfl, Nat.min_eq_left (by omega)]

theorem sweep_active (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (hn : old (stage u (depth u)) < P.dim u + 3) :
    CoordinateAffineTower.selected P old u (depth u) ∈ FlatAffineFullSourceTower.free (inputs P depth old level) u (depth u) := by
  apply (CoordinateDoubleAffinePrefix.active_iff P depth (objective depth old) level u (depth u) _).mpr
  rw [newest_selected P depth old u hn]
  change min (old (stage u (depth u))) (P.dim u + 3) < _
  omega

theorem coarse_active (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (hn : old (stage u (depth u)) < P.dim u + 3) :
    (FlatAffineFullSourceTower.free (inputs P depth old level) u (depth u)).erase
        (CoordinateAffineTower.selected P old u (depth u)) =
      FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u) := by
  ext j
  rw [Finset.mem_erase]
  have HS := CoordinateDoubleAffinePrefix.active_iff P depth (objective depth old) level u (depth u) j
  have HO := CoordinateDoubleAffinePrefix.active_iff P depth old level u (depth u) j
  have HR : (CoordinateAffineTower.selected P old u (depth u)).val = old (stage u (depth u)) :=
    Nat.min_eq_left hn.le
  have HE : j ≠ CoordinateAffineTower.selected P old u (depth u) ↔ j.val ≠ old (stage u (depth u)) := by
    rw [← HR]
    exact not_congr Fin.ext_iff
  have HK : (j ≠ CoordinateAffineTower.selected P old u (depth u) ∧
      j.val < (CoordinateAffineTower.selected P (objective depth old) u (depth u)).val) ↔
      j.val < (CoordinateAffineTower.selected P old u (depth u)).val := by
    rw [HE, HR, newest_selected P depth old u hn]
    omega
  exact (and_congr Iff.rfl HS).trans (HK.trans HO.symm)

end LeanCanny.Encoding.CoordinateDoubleAffineSweep
