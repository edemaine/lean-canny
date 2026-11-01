/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalSliceFrame
public import LeanCanny.Algebra.IntegralScalarRootHeightBank
public import LeanCanny.Algebra.IntegralHistoryBounds

/-! # An actual exceptional scalar extends the retained ordinary parent

The initial history sampler contains the whole original parent square
system and an empty scalar prefix. Appending the actual exceptional
integer polynomial retains every parent coordinate and constructs an
interpreted integral scalar prefix. Its companion root divided by the
nonzero integer leading coefficient recovers the independent frame scalar.

The norm degree bounds this initial scalar birth only. It does not replace
the spatial source degree. Nonconstant older level values still refer to
physical parent coordinates; turning those into coefficient-algebra
elements is a further required construction before a general critical step.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalIntegralPrefix
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (row parentCone)
open IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
attribute [local irreducible] SquareSampleCompleteVertices.candidate

noncomputable def parentSampler (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (S N : ℕ) (u : List Bool) : Sampler S N 0 (Fin (FlatAffineFullSourcePositive.count F u)) where
  scalarPrefix := UniformIntegralPrefix.base S N
  scalar := Fin.elim0
  rows := FlatAffinePowerPositive.system F u
  degrees := FlatAffinePowerPositive.degree F u
  row_degree := FlatAffinePowerPositive.polynomial_degree F u
  degree_pos := FlatAffinePowerPositive.degree_pos F u
  noInfinity := FlatAffinePowerPositive.noInfinity F (parentCone F C) u
  interpret := by
    intro K instK z hz
    exact ⟨Algebra.ofId ℤ K, fun i => Fin.elim0 i⟩

noncomputable def polynomial (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) : Polynomial ℤ :=
  FlatAffineHeightSlabExceptional.polynomial (next F) (row F h) u

noncomputable def degree (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) : ℕ :=
  (polynomial F h u).natDegree

noncomputable def capWidth (F : Inputs) (u : List Bool) : ℕ :=
  (FlatAffineHeightSlabExceptional.degreeBound (next F) u).size

theorem capWidth_unary {F : Inputs} (hF : F.Access)
    (h : (u : List Bool) → Fin (arity F u)) : UnaryFn (capWidth F) := by
  have H := FlatAffineHeightSlabExceptional.degreeBound_binary
    (FlatAffineCompleteRootStages.access hF (hF.depth.add (UnaryFn.const 1))) (row F h)
  exact (UnaryFn.length H.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

theorem degree_cap (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) : degree F h u ≤ 2 ^ capWidth F u :=
  (FlatAffineHeightSlabExceptional.degree_bound (next F) C (row F h) u).trans
    (Nat.lt_size_self _).le

theorem polynomial_evaluator {F : Inputs} (hF : F.Access)
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial F h)) :=
  FlatAffineHeightSlabExceptional.evaluator (FlatAffineCompleteRootStages.access hF (hF.depth.add (UnaryFn.const 1)))
    (row F h) (FlatAffineLastHeightRow.row_unary hF h hh)

theorem degree_evaluator {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    SpaceFunction (fun u => BinaryNatCode.encode (degree F h u)) := by
  have A := FlatAffineExceptionalSliceFrame.scalarAccess hF C h hh
  exact IntegerPolynomialBits.degreeEvaluator _ A.coefficient _ _ A.degree A.mass
    (FlatAffineExceptionalSliceFrame.scalarSource F C h).degree_bound
    (FlatAffineExceptionalSliceFrame.scalarSource F C h).mass_bound

def leadingQuery (z : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst z)) (pairSnd z)) (pairSnd (pairFst z))
theorem leadingQuery_FP : leadingQuery ∈ FP := by polytime [leadingQuery]

noncomputable def leading (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) : List Bool :=
  PrimitivePairBits.coefficient (polynomial F h)
    (pair (pair (pairFst q) (BinaryNatCode.encode (degree F h (pairFst q)))) (pairSnd q))

/-- The companion's integer denominator is read from the actual exceptional
polynomial after a charged exact-degree computation. -/
theorem leading_evaluator {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    SpaceFunction (leading F h) := by
  have E := (((degree_evaluator hF C h hh).precompose pairFst pairFst_mem_FP).withInput.postcompose
    leadingQuery leadingQuery_FP).chain (polynomial_evaluator hF h hh)
  exact E.congr (funext fun q => by simp only [leading, leadingQuery, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def sampler (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S N : ℕ) (hN : 0 < N) (u : List Bool) :
    Sampler S N 1 (Fin (FlatAffineFullSourcePositive.count F u) ⊕ Unit) :=
  scalarStep (parentSampler F C S N u) (Nat.zero_le S) hN (polynomial F h u) (degree F h u)

theorem physical_arity (F : Inputs) (u : List Bool) :
    Fintype.card (Fin (FlatAffineFullSourcePositive.count F u) ⊕ Unit) =
      F.depth u * (2 * arity F u + 1) + 2 := by
  calc
    _ = FlatAffineFullSourcePositive.count F u + 1 := by simp
    _ = _ := by
      dsimp only [FlatAffineFullSourcePositive.count, FlatAffineFullSourceTower.count,
        FlatAffineFullSourceTower.stageWidth, FlatAffineCriticalTower.width]
      ring

theorem physical_arity_unary {F : Inputs} (hF : F.Access) :
    UnaryFn (fun u => Fintype.card (Fin (FlatAffineFullSourcePositive.count F u) ⊕ Unit)) :=
  ((FlatAffineFullSourcePositive.count_unary hF).add (UnaryFn.const 1)).of_eq (fun _ => by simp)

theorem old_degrees (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S N : ℕ) (hN : 0 < N) (u : List Bool)
    (i : Fin (FlatAffineFullSourcePositive.count F u)) :
    (sampler F C h S N hN u).degrees (Sum.inl i) ≤ FlatAffineFullSourceTower.degree F u :=
  FlatAffinePowerPositive.degree_le F u i

theorem new_degree (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S N : ℕ) (hN : 0 < N) (u : List Bool) :
    (sampler F C h S N hN u).degrees (Sum.inr ()) = N * birth S N 0 := rfl

theorem scalar_root (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u a : List Bool)
    (ha : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a) :
    (polynomial F h u).eval₂ (Int.castRingHom ℝ) (FlatAffineExceptionalSliceFrame.scalar F C h u a) = 0 := by
  have H := (IntegerPolynomialSampleInput.roots_iff (FlatAffineExceptionalSliceFrame.scalarSource F C h) u
    (FlatAffineHeightSlabExceptional.ne_zero (next F) C (row F h) u) _).mp
      (SquareSampleCompleteVertices.candidate
        (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a ha).property
  exact (congrArg (fun t => (polynomial F h u).eval₂ (Int.castRingHom ℝ) t = 0)
    (FlatAffineExceptionalSliceFrame.scalar_packet F C h u a ha)).mpr H

/-- The native independent frame has a root in the interpreted history,
retaining the entire powered parent tuple literally. -/
theorem exists_interpreted_root (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S N : ℕ) (hN : 0 < N)
    (u v a : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a)
    (hcap : degree F h u ≤ N) :
    ∃ y : (Fin (FlatAffineFullSourcePositive.count F u) ⊕ Unit) → ℝ,
      (∀ j, ((sampler F C h S N hN u).rows j).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y (Sum.inl i) = (SquareSampleCompleteVertices.candidate
        (FlatAffinePowerSampleInput.input F (parentCone F C)) u v hv).val i) ∧
      ∀ ψ : (sampler F C h S N hN u).scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ψ ((sampler F C h S N hN u).scalarPrefix.basis.generator i) =
          y ((sampler F C h S N hN u).scalar i) ^ weights S N 1 i) →
        ψ (AdjoinRoot.root _) / ((polynomial F h u).coeff (degree F h u) : ℝ) =
          FlatAffineExceptionalSliceFrame.scalar F C h u a := by
  have hp := FlatAffineHeightSlabExceptional.ne_zero (next F) C (row F h) u
  have ht := scalar_root F C h u a ha
  have hpos : 1 ≤ degree F h u :=
    Polynomial.natDegree_pos_of_eval₂_root hp (Int.castRingHom ℝ) ht
      (by intro z hz; exact Int.cast_eq_zero.mp hz)
  have hlead : (polynomial F h u).coeff (degree F h u) ≠ 0 := by
    change (polynomial F h u).coeff (polynomial F h u).natDegree ≠ 0
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  exact scalarStep_real_extend_recover_root_integer (parentSampler F C S N u) (Nat.zero_le S) hN
    (polynomial F h u) (degree F h u) hcap
    ((polynomial F h u).coeff (degree F h u))
    hlead rfl
    (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F C)) u v hv).val
    (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F C)) u v hv).property
    (Algebra.ofId ℤ ℝ) (fun i => Fin.elim0 i) _
    (Polynomial.natDegree_map_eq_of_injective (Int.cast_injective (α := ℝ)) _) hpos ht

end LeanCanny.Encoding.FlatAffineExceptionalIntegralPrefix
