/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralParameterFinMatrix
public import LeanCanny.Algebra.PaddedIntegralGeneratorSpace

/-! # Native entries of the actual canonical padded generator matrix

Binary division splits a queried canonical rank into the old basis rank
and its new least significant scalar digit. The original coefficient
matrix reader supplies all normalization entries; the new generator
matrix is constructed internally, including on invalid degree branches.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralGeneratorFinBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCoordinateBasis
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u

structure Family where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  carrier : List Bool → Type u
  ring : ∀ c, CommRing (carrier c)
  nontrivial : ∀ c, Nontrivial (carrier c)
  basis : ∀ c, @IntegralCoordinateBasis (carrier c) (ring c) (arity c) (2 ^ width c)
  polynomial : ∀ c, Polynomial (carrier c)
  degree : List Bool → ℕ
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0
  row : (c : List Bool) → Fin (count (arity c + 1) (width c))
  col : (c : List Bool) → Fin (count (arity c + 1) (width c))

noncomputable def Family.coefficient (F : Family) (c : List Bool) (k : ℕ) :
    Matrix (Fin (count (F.arity c) (F.width c))) (Fin (count (F.arity c) (F.width c))) (ZMod (F.modulus c)) := by
  letI := F.ring c
  exact (Algebra.leftMulMatrix (F.basis c).finBasis ((F.polynomial c).coeff k)).map (Int.castRingHom _)

noncomputable def Family.matrix (F : Family) (c : List Bool) :
    Matrix (Fin (count (F.arity c + 1) (F.width c))) (Fin (count (F.arity c + 1) (F.width c))) ℤ := by
  letI := F.ring c
  letI := F.nontrivial c
  exact Algebra.leftMulMatrix (PaddedIntegralParameterExtension.coordinateBasis (F.basis c) (F.polynomial c) (F.degree c)).finBasis
    (AdjoinRoot.root _)

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool :=
  residueBits ((F.matrix c (F.row c) (F.col c) : ℤ) : ZMod (F.modulus c))

noncomputable def rawFamily (F : Family) : PaddedIntegralGeneratorBits.Family where
  width c := count (F.arity c) (F.width c)
  scalarDegree c := 2 ^ F.width c
  selectedDegree := F.degree
  modulus := F.modulus
  oldRow c := ((pairIndex (F.arity c) (F.width c)).symm (F.row c)).1
  oldCol c := ((pairIndex (F.arity c) (F.width c)).symm (F.col c)).1
  row c := ((pairIndex (F.arity c) (F.width c)).symm (F.row c)).2
  col c := ((pairIndex (F.arity c) (F.width c)).symm (F.col c)).2
  coefficient := F.coefficient
  modulus_ne_zero := F.modulus_ne_zero

theorem value_eq (F : Family) : (rawFamily F).value = F.value := by
  funext c
  let := F.ring c
  let := F.nontrivial c
  have HE := PaddedIntegralGeneratorBits.value_packet (rawFamily F) c (F.basis c).finBasis (F.polynomial c) (fun _ => rfl)
  rw [HE]
  have HM := finBasis_step_matrix (F.basis c)
    (PaddedIntegralNormalization.polynomial (F.polynomial c) (F.degree c) (2 ^ F.width c))
    (PaddedIntegralNormalization.monic _ _ _) (PaddedIntegralNormalization.natDegree _ _ _)
    (AdjoinRoot.root _) ((rawFamily F).oldRow c) ((rawFamily F).oldCol c) ((rawFamily F).row c) ((rawFamily F).col c)
  have HR : pairIndex (F.arity c) (F.width c) ((rawFamily F).oldRow c, (rawFamily F).row c) = F.row c :=
    (pairIndex (F.arity c) (F.width c)).apply_symm_apply (F.row c)
  have HC : pairIndex (F.arity c) (F.width c) ((rawFamily F).oldCol c, (rawFamily F).col c) = F.col c :=
    (pairIndex (F.arity c) (F.width c)).apply_symm_apply (F.col c)
  rw [HR, HC] at HM
  exact congrArg (fun x : ℤ => residueBits (x : ZMod (F.modulus c))) HM.symm

structure Access (F : Family) where
  arity : UnaryFn F.arity
  width : UnaryFn F.width
  degree : BinaryFn F.degree
  modulus : BinaryFn F.modulus
  row : BinaryFn (fun c => (F.row c).val)
  col : BinaryFn (fun c => (F.col c).val)
  entry : List Bool → List Bool
  entry_eq : ∀ c k (i j : Fin (count (F.arity c) (F.width c))),
    entry (pair c (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (F.coefficient c k i j)

noncomputable def rawAccess (F : Family) (a : Access F) : PaddedIntegralGeneratorBits.Access (rawFamily F) where
  width := by
    refine BinaryFn.of_eq ((BinaryFn.const 2).powUnary (a.width.mul a.arity)) (fun c => ?_)
    change 2 ^ (F.width c * F.arity c) = (2 ^ F.width c) ^ F.arity c
    exact pow_mul _ _ _
  scalarDegree := (BinaryFn.const 2).powUnary a.width
  selectedDegree := a.degree
  modulus := a.modulus
  oldRow := BinaryFn.of_eq (a.row.div ((BinaryFn.const 2).powUnary a.width)) (fun _ => rfl)
  oldCol := BinaryFn.of_eq (a.col.div ((BinaryFn.const 2).powUnary a.width)) (fun _ => rfl)
  row := BinaryFn.of_eq (a.row.mod ((BinaryFn.const 2).powUnary a.width)) (fun _ => rfl)
  col := BinaryFn.of_eq (a.col.mod ((BinaryFn.const 2).powUnary a.width)) (fun _ => rfl)
  entry := a.entry
  entry_eq := a.entry_eq

theorem evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) : SpaceFunction F.value :=
  (PaddedIntegralGeneratorBits.evaluator (rawFamily F) (rawAccess F a) E).congr (value_eq F)

end LeanCanny.Algebra.PaddedIntegralGeneratorFinBits
