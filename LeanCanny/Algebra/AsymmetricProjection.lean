/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.VectorSeparation
public import LeanCanny.Algebra.AffineGridAvoidance

/-! # Simultaneous bounded directions for asymmetric coordinate recovery

For N vectors in n coordinates, choose a positive k <= N^4+1 and integer
projection coefficients <= (n+1)*N^4. The projection is injective on the vectors.
For every coordinate j, all pairs of shifted projections
(L(a)+k*a_j, L(b)-b_j) have distinct values under (A,B) ↦ A+k*B.
This is the separating-pair condition needed by univariate coordinate recovery.
-/

@[expose] public section

namespace LeanCanny.Algebra.AsymmetricProjection
open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [Field K]

def projection (c : ι → ℕ) (x : ι → K) : K := ∑ i, x i * (c i : K)

def plus (c : ι → ℕ) (k : ℕ) (j : ι) (x : ι → K) : K :=
  projection c x + (k : K) * x j

def minus (c : ι → ℕ) (j : ι) (x : ι → K) : K := projection c x - x j

def pairValue (c : ι → ℕ) (k : ℕ) (j : ι) (p : (ι → K) × (ι → K)) : K :=
  LeanCanny.Algebra.shear k (plus c k j p.1, minus c j p.2)

theorem projection_shear (c : ι → ℕ) (k : ℕ) (p : (ι → K) × (ι → K)) :
    projection c (VectorSeparation.shear k p) = projection c p.1 + (k : K) * projection c p.2 := by
  simp only [projection, VectorSeparation.shear, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem pairValue_eq (c : ι → ℕ) (k : ℕ) (j : ι) (p : (ι → K) × (ι → K)) :
    pairValue c k j p = (k : K) * (p.1 j - p.2 j) + projection c (VectorSeparation.shear k p) := by
  rw [projection_shear]
  unfold pairValue LeanCanny.Algebra.shear plus minus
  ring

theorem diagonal_pairValue (c : ι → ℕ) (k : ℕ) (j : ι) (x : ι → K) :
    pairValue c k j (x, x) = ((k : K) + 1) * projection c x := by
  unfold pairValue LeanCanny.Algebra.shear plus minus
  ring

theorem exists_bounded_direction [CharZero K] (s : Finset (ι → K)) :
    ∃ k : ℕ, ∃ c : ι → ℕ, 0 < k ∧ k ≤ s.card ^ 4 + 1 ∧
      (∀ i, c i ≤ (Fintype.card ι + 1) * s.card ^ 4) ∧
      Set.InjOn (projection (K := K) c) (s : Set (ι → K)) ∧
      ∀ j, Set.InjOn (pairValue (K := K) c k j)
        ((s ×ˢ s : Finset ((ι → K) × (ι → K))) : Set ((ι → K) × (ι → K))) := by
  classical
  obtain ⟨k, hk, hkb, hinj⟩ := VectorSeparation.exists_bounded_pair_encoding s
  let P := {x : ι → K // x ∈ s}
  let vectors : (P × P) → ι → K := fun p => VectorSeparation.shear k (p.1.val, p.2.val)
  let offset : Option ι → (P × P) → K := fun r p =>
    match r with
    | none => 0
    | some j => (k : K) * (p.1.val j - p.2.val j)
  have hv : Function.Injective vectors := by
    intro p q he
    have hp : (p.1.val, p.2.val) ∈ s ×ˢ s := Finset.mem_product.mpr ⟨p.1.property, p.2.property⟩
    have hq : (q.1.val, q.2.val) ∈ s ×ˢ s := Finset.mem_product.mpr ⟨q.1.property, q.2.property⟩
    have heq := hinj hp hq he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst heq)) (Subtype.ext (congrArg Prod.snd heq))
  obtain ⟨c, hc, hsep⟩ := AffineGridAvoidance.exists_bounded_separating_direction
    (fun _r : Option ι => vectors) offset (fun _ => hv)
  have hcard : Fintype.card (Option ι) * Fintype.card (P × P) ^ 2 =
      (Fintype.card ι + 1) * s.card ^ 4 := by
    simp only [Fintype.card_option, Fintype.card_prod, P, Fintype.card_coe]
    ring
  refine ⟨k, c, hk, hkb, fun i => (hc i).trans_eq hcard, ?_, ?_⟩
  · intro a ha b hb he
    let pa : P := ⟨a, ha⟩
    let pb : P := ⟨b, hb⟩
    have hvalues : offset none (pa, pa) + projection c (vectors (pa, pa)) =
        offset none (pb, pa) + projection c (vectors (pb, pa)) := by
      simp only [offset, vectors, projection_shear, he, zero_add, pa, pb]
    have hp := hsep none hvalues
    exact congrArg (fun p : P × P => p.1.val) hp
  · intro j p hp q hq he
    obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hp
    obtain ⟨hqa, hqb⟩ := Finset.mem_product.mp hq
    let pp : P × P := (⟨p.1, hpa⟩, ⟨p.2, hpb⟩)
    let qq : P × P := (⟨q.1, hqa⟩, ⟨q.2, hqb⟩)
    have hvalues : offset (some j) pp + projection c (vectors pp) =
        offset (some j) qq + projection c (vectors qq) := by
      simpa only [pairValue_eq] using he
    have heq := hsep (some j) hvalues
    exact Prod.ext (congrArg (fun r : P × P => r.1.val) heq)
      (congrArg (fun r : P × P => r.2.val) heq)

end LeanCanny.Algebra.AsymmetricProjection
