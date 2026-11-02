/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHistoryScript
public import LeanCanny.Algebra.IntegralMixedSourceReframe
/-! # Source-framed commands preserve the literal retained history

Every instruction stores its own spatial source and an existing mixed command
for that source. Interpretation reframes the actual older state before adding
the scalar birth. Earlier commands are never reinterpreted under a new source.
The ambient dimension, scalar width and horizon are shared throughout. No task
root or recursive arithmetic controller changes when the spatial source does.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory
open scoped Classical BigOperators

structure Instruction (n B : ℕ) where
  source : SpatialSource n
  source_cap : PurePowerReductionBounds.dimension (n+1) source.degree≤2^B
  command : IntegralMixedFullHistoryScript.Command source B

def source {n B : ℕ} (initial : SpatialSource n) : List (Instruction n B) → SpatialSource n
  | [] => initial
  | c::_ => c.source

def Index {n B : ℕ} (ι : Type) : List (Instruction n B) → Type
  | [] => ι
  | c::cs => IntegralMixedFullHistoryScript.NextIndex (Index ι cs) c.command

instance indexFintype {n B : ℕ} (ι : Type) [Fintype ι] : (cs : List (Instruction n B)) → Fintype (Index ι cs)
  | [] => inferInstanceAs (Fintype ι)
  | c::cs => by
    change Fintype (IntegralMixedFullHistoryScript.NextIndex (Index ι cs) c.command)
    letI := indexFintype ι cs
    exact IntegralMixedFullHistoryScript.nextFintype _ c.command

noncomputable def run {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) : (cs : List (Instruction n B)) → cs.length≤S+1 →
      State (source P cs) S B cs.length (Index ι cs)
  | [], _ => initial
  | c::cs, h => IntegralMixedFullHistoryScript.step
      (reframe (run initial cs (by simp only [List.length_cons] at h; omega)) c.source c.source_cap)
      (by simp only [List.length_cons] at h; omega) c.command

theorem reframe_canonical {n n' S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (H : Canonical x) (Q : SpatialSource n')
    (hcap : PurePowerReductionBounds.dimension (n'+1) Q.degree≤2^B) :
    Canonical (reframe x Q hcap) := H

theorem run_canonical {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (H : Canonical initial)
    (cs : List (Instruction n B)) (h : cs.length≤S+1) : Canonical (run initial cs h) := by
  induction cs with
  | nil => exact H
  | cons c cs ih =>
    exact IntegralMixedFullHistoryScript.step_canonical _
      (reframe_canonical _ (ih (by simp only [List.length_cons] at h; omega)) _ _) _ c.command

theorem run_prefix {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (c : Instruction n B) (cs : List (Instruction n B))
    (h : (c::cs).length≤S+1) :
    (run initial (c::cs) h).sampler.scalarPrefix=
      UniformIntegralPrefix.step
        (run initial cs (by simp only [List.length_cons] at h; omega)).sampler.scalarPrefix
        (by simp only [List.length_cons] at h; omega) (Nat.two_pow_pos B)
        (IntegralMixedFullHistoryScript.polynomial
          (reframe (run initial cs (by simp only [List.length_cons] at h; omega)) c.source c.source_cap)
          (by simp only [List.length_cons] at h; omega) c.command)
        (IntegralMixedFullHistoryScript.degree
          (reframe (run initial cs (by simp only [List.length_cons] at h; omega)) c.source c.source_cap)
          (by simp only [List.length_cons] at h; omega) c.command) :=
  IntegralMixedFullHistoryScript.step_prefix _ _ _

theorem run_denominator_zero {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (c : Instruction n B) (cs : List (Instruction n B))
    (h : (c::cs).length≤S+1) :
    (run initial (c::cs) h).bank.denominator 0=
      IntegralMixedFullHistoryScript.leading
        (reframe (run initial cs (by simp only [List.length_cons] at h; omega)) c.source c.source_cap)
        (by simp only [List.length_cons] at h; omega) c.command :=
  IntegralMixedFullHistoryScript.step_denominator_zero _ _ _

theorem run_denominator_succ {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (c : Instruction n B) (cs : List (Instruction n B))
    (h : (c::cs).length≤S+1) (i : Fin cs.length) :
    (run initial (c::cs) h).bank.denominator i.succ=
      (run initial cs (by simp only [List.length_cons] at h; omega)).bank.denominator i :=
  IntegralMixedFullHistoryScript.step_denominator_succ _ _ _ i

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
