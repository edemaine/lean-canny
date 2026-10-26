/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedOriginalQuery
public import LeanCanny.Geometry.BoundedMarkedCoordinates
public import LeanCanny.Connectivity.Problem

/-! # Native marked-piece tests for original singleton endpoints

Endpoint formulas keep their original coordinate names. The query recognizes
marked source points projecting to that endpoint, with arbitrary independent
piece witnesses. Its native space certificate charges both formula readers and
the actual generated source circuit.
-/

@[expose] public section
namespace LeanCanny.Connectivity
open ETR Geometry MvPolynomial Computation
open scoped Classical

theorem Denotes.holds_iff_restrict {n : ℕ} {p : Formula} {a : Fin n → ℝ}
    (hp : Denotes n p a) (x : ℕ → ℝ) : p.Holds x ↔ (fun i : Fin n => x i.val) = a := by
  have he : p.Holds x ↔ p.Holds (Formula.extend (fun i : Fin n => x i.val)) := by
    apply p.holds_congr
    intro i hi
    simp [Formula.extend, hi.trans_le hp.1]
  exact he.trans (hp.2 _)

namespace BoundedEndpointQuery
open Encoding Encoding.BoundedFullWriter Encoding.BoundedOriginalQuery

def witnessPiece {m : ℕ} (p : Formula) (z : Fin m → ℝ) : Prop :=
  ∃ x : ℕ → ℝ, (∀ i : Fin m, x i.val = z i) ∧ p.Holds x

theorem marked_projection_fiber_iff {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (a : Fin n → ℝ) :
    (∃ z : BoundedRegularSource.Marked q D b R, (BoundedRegularSource.markedProjection q D b R z).val = a) ↔
      a ∈ BoundedZeroSource.Bounded q R := by
  constructor
  · rintro ⟨z, rfl⟩
    exact (BoundedRegularSource.markedProjection q D b R z).property
  · intro ha
    exact ⟨BoundedRegularSource.markedLift q D b R ⟨a, ha⟩,
      congrArg Subtype.val (BoundedRegularSource.markedProjection_lift q D b R ⟨a, ha⟩)⟩

theorem marked_endpoint_correct (P : Readers) (c : List Bool) (endpoint piece : Formula)
    (a : Fin (P.dim c) → ℝ) (hp : Denotes (P.dim c) endpoint a) :
    (∃ x : ℕ → ℝ, MarkedPoint P c (fun i => x i.val) ∧ (Formula.and endpoint piece).Holds x) ↔
      ∃ z : BoundedRegularSource.Marked (original P c) (size P c) (size P c) (P.radius c),
        (BoundedRegularSource.markedProjection (original P c) (size P c) (size P c) (P.radius c) z).val = a ∧
          witnessPiece piece z.val.val := by
  constructor
  · rintro ⟨x, hm, hend, hpiece⟩
    let z : BoundedRegularSource.Marked (original P c) (size P c) (size P c) (P.radius c) :=
      ⟨⟨fun i => x i.val, hm.1⟩, hm.2⟩
    have he : (fun i : Fin (P.dim c) => x i.val) =
        (BoundedRegularSource.markedProjection (original P c) (size P c) (size P c) (P.radius c) z).val := by
      funext i
      exact (BoundedRegularSource.markedProjection_apply _ _ _ _ z i).symm
    exact ⟨z, he.symm.trans ((hp.holds_iff_restrict x).mp hend), x, fun _ => rfl, hpiece⟩
  · rintro ⟨z, hproj, x, hx, hpiece⟩
    have he : (fun i : Fin (P.dim c + 4) => x i.val) = z.val.val := funext hx
    refine ⟨x, ?_, ?_, hpiece⟩
    · rw [he]
      exact ⟨z.val.property, z.property⟩
    · apply (hp.holds_iff_restrict x).mpr
      refine Eq.trans ?_ hproj
      funext i
      exact (hx (i.castAdd 4)).trans (BoundedRegularSource.markedProjection_apply _ _ _ _ z i).symm

theorem and_encode_mem_FP {p q : List Bool → Formula}
    (hp : (fun c => (p c).encode) ∈ FP) (hq : (fun c => (q c).encode) ∈ FP) :
    (fun c => (Formula.and (p c) (q c)).encode) ∈ FP := by
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 4 hp hq)
  intro c
  simp only [Formula.encode, Formula.toData, Codec.taggedTwo_toBits]

theorem marked_endpoint_evaluator {P : Readers} {endpoint piece : List Bool → Formula}
    {a : (c : List Bool) → Fin (P.dim c) → ℝ} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hp : (fun c => (endpoint c).encode) ∈ FP) (hq : (fun c => (piece c).encode) ∈ FP)
    (hdenotes : ∀ c, Denotes (P.dim c) (endpoint c) (a c)) :
    SpaceFunction (fun c => [decide (∃ z : BoundedRegularSource.Marked (original P c) (size P c) (size P c) (P.radius c),
      (BoundedRegularSource.markedProjection (original P c) (size P c) (size P c) (P.radius c) z).val = a c ∧
        witnessPiece (piece c) z.val.val)]) := by
  apply (Encoding.BoundedOriginalQuery.marked_evaluator h ht (and_encode_mem_FP hp hq)).congr
  funext c
  rw [marked_endpoint_correct P c (endpoint c) (piece c) (a c) (hdenotes c)]

end BoundedEndpointQuery
end LeanCanny.Connectivity
