/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionMacaulay
public import LeanCanny.Encoding.BoundedProjectionFamily

/-! # Native Macaulay readers for arbitrary critical projection records -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionFamilyMacaulay
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Computation
open BoundedFullWriter MatrixPower RationalSubstitution.Indexed MvPolynomial Brackets FixedWidthPolynomial
open BoundedProjectionMacaulay (layout layout_polyTime degrees_eq width_fits width_pos dimension dimension_binary dimension_eq_pow sourceIndex sourceRank parameterDegree sourceIndex_mem_FP sourceRank_mem_FP parameterDegree_mem_FP selectedRow selectedRow_unary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def system (P : Readers) (record : List Bool → List Bool) (c : List Bool) :=
  BoundedProjectionRowsCoefficient.polynomial P (BoundedFullDirectionChoice.record P) record c

noncomputable def matrix (P : Readers) (record : List Bool → List Bool) (c : List Bool) :
    Matrix (Fin (dimension P c)) (Fin (dimension P c)) (Polynomial ℤ) :=
  Macaulay.matrix (system P record c) (MacaulayBits.Degrees (layout P) c) ((layout P).width c)

theorem lowest_eq (P : Readers) (record : List Bool → List Bool) (c : List Bool) :
    CharacteristicLowestBounds.lowest (matrix P record c) = BoundedProjectionFamily.polynomial P record c := by
  unfold matrix BoundedProjectionFamily.polynomial LinearProjectionEliminant.polynomial
    MacaulayLowestBounds.polynomial
  rw [degrees_eq]
  rfl

noncomputable def sourceCoefficient (P : Readers) (record : List Bool → List Bool) (modulus : List Bool → List Bool) : List Bool → List Bool :=
  BoundedProjectionRowsCoefficient.answer (P.comp pairFst)
    (BoundedFullDirectionChoice.record (P.comp pairFst)) (record ∘ pairFst)
    (selectedRow P) ((layout P).width ∘ pairFst) sourceRank parameterDegree (modulus ∘ pairFst)

theorem sourceCoefficient_evaluator {P : Readers} {record : List Bool → List Bool} {modulus : List Bool → List Bool}
    (h : P.PolyTime) (hr : SpaceFunction record) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (sourceCoefficient P record modulus) :=
  BoundedProjectionRowsCoefficient.record_evaluator (h.comp pairFst_mem_FP)
    (hr.precompose pairFst pairFst_mem_FP) (selectedRow_unary h)
    ((BoundedCriticalProjection.systemWidth_unary h).comp pairFst_mem_FP) sourceRank_mem_FP parameterDegree_mem_FP
    (mem_FP_comp pairFst_mem_FP hm) (fun q => ha (pairFst q)) (fun q => width_fits P (pairFst q))
    (fun q => width_pos P (pairFst q))

theorem sourceCoefficient_packet (P : Readers) (record : List Bool → List Bool) (modulus : List Bool → List Bool) (c : List Bool)
    (i : Fin ((layout P).arity c)) (r : ℕ) (k : List Bool) :
    sourceCoefficient P record modulus (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode r) k))) =
      residueBits (((((system P record c i).coeff
        (exponentVector ((layout P).arity c) (entry ((layout P).width c) r))).coeff (Nat.fromBitsLE k)) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  unfold sourceCoefficient BoundedProjectionRowsCoefficient.answer
  simp only [BoundedFullDirectionChoice.record_comp]
  simp only [sourceIndex, sourceRank, parameterDegree, selectedRow, Readers.comp, Function.comp_apply,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold BoundedProjectionRowsCoefficient.valueData
  have hi : i.val ≤ P.dim c + 4 := by have := i.isLt; change i.val < P.dim c + 5 at this; omega
  simp only [Nat.min_eq_left hi, Nat.fromBitsLE_bits]
  rfl

noncomputable def entry (P : Readers) (record : List Bool → List Bool) (modulus : List Bool → List Bool) : List Bool → List Bool :=
  MacaulayBits.entryWithIdentity (layout P) (sourceCoefficient P record modulus ∘ MacaulayPolynomial.sourceInput)
    (MacaulayPolynomial.constantEntry (BinaryNat.succ ∘ modulus)) ∘ PolynomialMoment.augmentedInput

theorem entry_evaluator {P : Readers} {record : List Bool → List Bool} {modulus : List Bool → List Bool}
    (h : P.PolyTime) (hr : SpaceFunction record) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (entry P record modulus) :=
  (MacaulayBits.entryWithIdentityEvaluator (layout_polyTime h)
    ((sourceCoefficient_evaluator h hr hm ha).precompose MacaulayPolynomial.sourceInput MacaulayPolynomial.sourceInput_mem_FP)
    (MacaulayPolynomial.constantEntry_mem_FP (mem_FP_comp hm BinaryNat.succ_mem_FP))).precompose
      PolynomialMoment.augmentedInput PolynomialMoment.augmentedInput_mem_FP

private theorem raw_entry_packet (P : Readers) (record : List Bool → List Bool) (modulus : List Bool → List Bool) (q : List Bool)
    (i j : Fin (dimension P (pairFst q))) :
    MacaulayBits.entryWithIdentity (layout P) (sourceCoefficient P record modulus ∘ MacaulayPolynomial.sourceInput)
      (MacaulayPolynomial.constantEntry (BinaryNat.succ ∘ modulus)) (MacaulayBits.packet q i.val j.val) =
        residueBits ((((matrix P record (pairFst q) i j).coeff (Nat.fromBitsLE (pairSnd q))) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1)) := by
  refine MacaulayBits.entryWithIdentity_packet (R := Polynomial ℤ) (layout P)
    (sourceCoefficient P record modulus ∘ MacaulayPolynomial.sourceInput)
    (MacaulayPolynomial.constantEntry (BinaryNat.succ ∘ modulus)) q (system P record (pairFst q))
    (fun p => residueBits ((p.coeff (Nat.fromBitsLE (pairSnd q)) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1)))
    (by simp [residueBits, BinaryNatCode.encode]) ?_ i j ?_
  · intro s r
    have hs : MacaulayPolynomial.sourceInput (MacaulayBits.packet q s.val r) =
        pair (pairFst q) (pair (BinaryNatCode.encode s.val) (pair (BinaryNatCode.encode r) (pairSnd q))) := by
      simp only [MacaulayPolynomial.sourceInput, MacaulayBits.context, MacaulayBits.row, MacaulayBits.col,
        MacaulayBits.packet, pairFst_pair, pairSnd_pair]
    rw [Function.comp_apply, hs]
    exact sourceCoefficient_packet P record modulus (pairFst q) s r (pairSnd q)
  · simp only [MacaulayPolynomial.constantEntry, MacaulayBits.context, MacaulayBits.sameIndex,
      MacaulayBits.row, MacaulayBits.col, MacaulayBits.packet, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Function.comp_apply]
    by_cases hij : i.val = j.val <;> by_cases hk : Nat.fromBitsLE (pairSnd q) = 0 <;>
      simp only [hij, hk, ite_true, ite_false, and_true, and_false,
        Polynomial.coeff_one, Polynomial.coeff_zero, Int.cast_zero, Int.cast_one]
    · rw [BinaryNat.succ_eq_bits]
      exact ArithmeticBits.one_residueBits _
    all_goals simp [residueBits, BinaryNatCode.encode]

theorem entry_packet (P : Readers) (record : List Bool → List Bool) (modulus : List Bool → List Bool) (c : List Bool)
    (i j : Fin (dimension P c)) (k : ℕ) :
    entry P record modulus (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k)))) =
      residueBits ((((matrix P record c i j).coeff k) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  simp only [entry, Function.comp_apply, PolynomialMoment.augmentedInput, pairFst_pair, pairSnd_pair]
  change MacaulayBits.entryWithIdentity (layout P) (sourceCoefficient P record modulus ∘ MacaulayPolynomial.sourceInput)
    (MacaulayPolynomial.constantEntry (BinaryNat.succ ∘ modulus))
      (MacaulayBits.packet (pair c (BinaryNatCode.encode k)) i.val j.val) = _
  generalize hz : pair c (BinaryNatCode.encode k) = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  have hk : Nat.fromBitsLE (pairSnd z) = k := by rw [← hz, pairSnd_pair]; exact Nat.fromBitsLE_bits k
  subst c
  subst k
  exact raw_entry_packet P record modulus z i j

theorem matrix_degree (P : Readers) (record : List Bool → List Bool) (c : List Bool) (i j : Fin (dimension P c)) :
    (matrix P record c i j).natDegree ≤ 1 :=
  Macaulay.polynomial_entry_degree_le (system P record c) (MacaulayBits.Degrees (layout P) c) ((layout P).width c) 1
    (LinearProjectionSystem.coefficient_degree _ _ _) i j

theorem system_mass (P : Readers) (record : List Bool → List Bool) (c : List Bool) (i : Fin ((layout P).arity c))
    (e : Fin ((layout P).arity c) →₀ ℕ) :
    coefficientMass ((system P record c i).coeff e) ≤ 2 ^ BoundedCriticalProjection.projectionBits P c := by
  exact (LinearProjectionSystem.coefficient_mass (BoundedFullCriticalSamples.equations P c) (fun _ => degree P c)
    (BoundedProjectionFamily.weights P record c) (BoundedCriticalProjection.equationBits P c)
    (BoundedCriticalSeparator.width P c)
    (fun j e => (MvMass.coeff_le _ _).trans (BoundedCriticalProjection.equations_mass P c j))
    (BoundedProjectionFamily.weight_bound P record c) i e).trans (BoundedCriticalProjection.projection_mass_bound P c)

theorem matrix_mass (P : Readers) (record : List Bool → List Bool) (c : List Bool) (i j : Fin (dimension P c)) :
    coefficientMass (matrix P record c i j) ≤ 2 ^ BoundedCriticalProjection.projectionBits P c :=
  Macaulay.matrix_entry_mass_le (system P record c) (MacaulayBits.Degrees (layout P) c) ((layout P).width c)
    (BoundedCriticalProjection.projectionBits P c) (system_mass P record c) i j

theorem matrix_comp (P : Readers) (record : List Bool → List Bool) (f : List Bool → List Bool) (c : List Bool) :
    matrix (P.comp f) (record ∘ f) c = matrix P record (f c) := by
  unfold matrix system BoundedProjectionRowsCoefficient.polynomial BoundedCriticalSampleQuery.equations
    BoundedFullDirectionQueries.direction BoundedCriticalSeparator.weight FixedWidthQuery.coordinate
  simp only [BoundedFullDirectionChoice.record_comp]
  rfl

/-- Uniform modulus packets permit the integer determinant backend to query
each entry under any positive modulus without a new coefficient oracle. -/
noncomputable def uniformEntry (P : Readers) (record : List Bool → List Bool) : List Bool → List Bool := entry (P.comp pairFst) (record ∘ pairFst) pairSnd

theorem uniformEntry_evaluator {P : Readers} {record : List Bool → List Bool} (h : P.PolyTime) (hr : SpaceFunction record)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (uniformEntry P record) :=
  entry_evaluator (h.comp pairFst_mem_FP)
    (hr.precompose pairFst pairFst_mem_FP) pairSnd_mem_FP (fun q => ha (pairFst q))

theorem uniformEntry_packet (P : Readers) (record : List Bool → List Bool) (c m : List Bool) (i j : Fin (dimension P c)) (k : ℕ) :
    uniformEntry P record (pair (pair c m) (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k)))) =
      residueBits ((((matrix P record c i j).coeff k) : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hz : pair c m = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  have hm : pairSnd z = m := by rw [← hz, pairSnd_pair]
  subst c
  subst m
  have he := entry_packet (P.comp pairFst) (record ∘ pairFst) pairSnd z i j k
  rw [matrix_comp] at he
  exact he

end LeanCanny.Encoding.BoundedProjectionFamilyMacaulay
