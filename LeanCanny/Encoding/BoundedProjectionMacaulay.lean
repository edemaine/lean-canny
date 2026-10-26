/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionRowsCoefficient
public import LeanCanny.Algebra.MacaulayPolynomialSpace

/-! # The actual projection system as an implicit integer Macaulay matrix -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionMacaulay
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Computation
open BoundedFullWriter MatrixPower RationalSubstitution.Indexed MvPolynomial Brackets FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def layout (P : Readers) : MacaulayBits.Layout where
  arity c := P.dim c + 5
  width := BoundedCriticalProjection.systemWidth P
  degree c i := if i = 0 then 1 else degree P c

theorem layout_polyTime {P : Readers} (h : P.PolyTime) : (layout P).PolyTime := by
  refine ⟨h.dim.add (UnaryFn.const 5), BoundedCriticalProjection.systemWidth_unary h, ?_⟩
  exact UnaryFn.ite (FPPred.eq UnaryFn.index (UnaryFn.const 0)) (UnaryFn.const 1)
    ((BoundedRegularModularTerm.degree_unary h).comp pairFst_mem_FP)

theorem degrees_eq (P : Readers) (c : List Bool) :
    MacaulayBits.Degrees (layout P) c = AffineCoordinateSystem.degrees (fun _ : Fin (P.dim c + 4) => degree P c) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [MacaulayBits.Degrees, layout, AffineCoordinateSystem.degrees]

theorem width_fits (P : Readers) (c : List Bool) : degree P c < 2 ^ (layout P).width c := by
  have hpos : 0 < degree P c := by
    have := BoundedRegularSource.powerDegree_gt_one (size P c)
    change 0 < BoundedZeroSource.powerDegree (size P c)
    omega
  have hm : degree P c - 1 ≤ (P.dim c + 4) * (degree P c - 1) := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right (degree P c - 1) (show 1 ≤ P.dim c + 4 by omega)
  apply (show degree P c ≤ (P.dim c + 4) * (degree P c - 1) + 1 by omega).trans_lt
  exact Nat.lt_size_self _

theorem width_pos (P : Readers) (c : List Bool) : 0 < (layout P).width c := by
  have hf := width_fits P c
  have hd := BoundedRegularSource.powerDegree_gt_one (size P c)
  by_contra hn
  have hz : (layout P).width c = 0 := by omega
  rw [hz, pow_zero] at hf
  change BoundedZeroSource.powerDegree (size P c) < 1 at hf
  omega

noncomputable def system (P : Readers) (c : List Bool) :=
  BoundedProjectionRowsCoefficient.polynomial P (BoundedFullDirectionChoice.record P) (BoundedCriticalSeparator.record P) c

noncomputable def dimension (P : Readers) (c : List Bool) : ℕ :=
  FixedWidthPolynomial.count ((layout P).arity c) ((layout P).width c)

noncomputable def matrix (P : Readers) (c : List Bool) :
    Matrix (Fin (dimension P c)) (Fin (dimension P c)) (Polynomial ℤ) :=
  Macaulay.matrix (system P c) (MacaulayBits.Degrees (layout P) c) ((layout P).width c)

theorem lowest_eq (P : Readers) (c : List Bool) :
    CharacteristicLowestBounds.lowest (matrix P c) = BoundedCriticalProjection.polynomial P c := by
  unfold matrix BoundedCriticalProjection.polynomial LinearProjectionEliminant.polynomial
    MacaulayLowestBounds.polynomial
  rw [degrees_eq]
  rfl

def sourceIndex (q : List Bool) : List Bool := pairFst (pairSnd q)
def sourceRank (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def parameterDegree (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd q))

theorem sourceIndex_mem_FP : sourceIndex ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem sourceRank_mem_FP : sourceRank ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem parameterDegree_mem_FP : parameterDegree ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

def selectedRow (P : Readers) (q : List Bool) : Fin ((P.comp pairFst).dim q + 5) :=
  ⟨min (Nat.fromBitsLE (sourceIndex q)) (P.dim (pairFst q) + 4), by
    change min (Nat.fromBitsLE (sourceIndex q)) (P.dim (pairFst q) + 4) < P.dim (pairFst q) + 5
    omega⟩

theorem selectedRow_unary {P : Readers} (h : P.PolyTime) : UnaryFn (fun q => (selectedRow P q).val) :=
  UnaryFn.fromBitsLE_min sourceIndex_mem_FP ((h.dim.comp pairFst_mem_FP).add (UnaryFn.const 4))

noncomputable def sourceCoefficient (P : Readers) (modulus : List Bool → List Bool) : List Bool → List Bool :=
  BoundedProjectionRowsCoefficient.answer (P.comp pairFst)
    (BoundedFullDirectionChoice.record (P.comp pairFst)) (BoundedCriticalSeparator.record (P.comp pairFst))
    (selectedRow P) ((layout P).width ∘ pairFst) sourceRank parameterDegree (modulus ∘ pairFst)

theorem sourceCoefficient_evaluator {P : Readers} {modulus : List Bool → List Bool}
    (h : P.PolyTime) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (sourceCoefficient P modulus) :=
  BoundedProjectionRowsCoefficient.selected_evaluator (h.comp pairFst_mem_FP) (selectedRow_unary h)
    ((BoundedCriticalProjection.systemWidth_unary h).comp pairFst_mem_FP) sourceRank_mem_FP parameterDegree_mem_FP
    (mem_FP_comp pairFst_mem_FP hm) (fun q => ha (pairFst q)) (fun q => width_fits P (pairFst q))
    (fun q => width_pos P (pairFst q))

theorem sourceCoefficient_packet (P : Readers) (modulus : List Bool → List Bool) (c : List Bool)
    (i : Fin ((layout P).arity c)) (r : ℕ) (k : List Bool) :
    sourceCoefficient P modulus (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode r) k))) =
      residueBits (((((system P c i).coeff
        (exponentVector ((layout P).arity c) (entry ((layout P).width c) r))).coeff (Nat.fromBitsLE k)) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  unfold sourceCoefficient BoundedProjectionRowsCoefficient.answer
  simp only [BoundedFullDirectionChoice.record_comp, BoundedCriticalSeparator.record_comp]
  simp only [sourceIndex, sourceRank, parameterDegree, selectedRow, Readers.comp, Function.comp_apply,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold BoundedProjectionRowsCoefficient.valueData
  have hi : i.val ≤ P.dim c + 4 := by have := i.isLt; change i.val < P.dim c + 5 at this; omega
  simp only [Nat.min_eq_left hi, Nat.fromBitsLE_bits]
  rfl

noncomputable def entry (P : Readers) (modulus : List Bool → List Bool) : List Bool → List Bool :=
  MacaulayBits.entryWithIdentity (layout P) (sourceCoefficient P modulus ∘ MacaulayPolynomial.sourceInput)
    (MacaulayPolynomial.constantEntry (BinaryNat.succ ∘ modulus)) ∘ PolynomialMoment.augmentedInput

theorem entry_evaluator {P : Readers} {modulus : List Bool → List Bool}
    (h : P.PolyTime) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (entry P modulus) :=
  (MacaulayBits.entryWithIdentityEvaluator (layout_polyTime h)
    ((sourceCoefficient_evaluator h hm ha).precompose MacaulayPolynomial.sourceInput MacaulayPolynomial.sourceInput_mem_FP)
    (MacaulayPolynomial.constantEntry_mem_FP (mem_FP_comp hm BinaryNat.succ_mem_FP))).precompose
      PolynomialMoment.augmentedInput PolynomialMoment.augmentedInput_mem_FP

private theorem raw_entry_packet (P : Readers) (modulus : List Bool → List Bool) (q : List Bool)
    (i j : Fin (dimension P (pairFst q))) :
    MacaulayBits.entryWithIdentity (layout P) (sourceCoefficient P modulus ∘ MacaulayPolynomial.sourceInput)
      (MacaulayPolynomial.constantEntry (BinaryNat.succ ∘ modulus)) (MacaulayBits.packet q i.val j.val) =
        residueBits ((((matrix P (pairFst q) i j).coeff (Nat.fromBitsLE (pairSnd q))) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1)) := by
  refine MacaulayBits.entryWithIdentity_packet (R := Polynomial ℤ) (layout P)
    (sourceCoefficient P modulus ∘ MacaulayPolynomial.sourceInput)
    (MacaulayPolynomial.constantEntry (BinaryNat.succ ∘ modulus)) q (system P (pairFst q))
    (fun p => residueBits ((p.coeff (Nat.fromBitsLE (pairSnd q)) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1)))
    (by simp [residueBits, BinaryNatCode.encode]) ?_ i j ?_
  · intro s r
    have hs : MacaulayPolynomial.sourceInput (MacaulayBits.packet q s.val r) =
        pair (pairFst q) (pair (BinaryNatCode.encode s.val) (pair (BinaryNatCode.encode r) (pairSnd q))) := by
      simp only [MacaulayPolynomial.sourceInput, MacaulayBits.context, MacaulayBits.row, MacaulayBits.col,
        MacaulayBits.packet, pairFst_pair, pairSnd_pair]
    rw [Function.comp_apply, hs]
    exact sourceCoefficient_packet P modulus (pairFst q) s r (pairSnd q)
  · simp only [MacaulayPolynomial.constantEntry, MacaulayBits.context, MacaulayBits.sameIndex,
      MacaulayBits.row, MacaulayBits.col, MacaulayBits.packet, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Function.comp_apply]
    by_cases hij : i.val = j.val <;> by_cases hk : Nat.fromBitsLE (pairSnd q) = 0 <;>
      simp only [hij, hk, ite_true, ite_false, and_true, and_false,
        Polynomial.coeff_one, Polynomial.coeff_zero, Int.cast_zero, Int.cast_one]
    · rw [BinaryNat.succ_eq_bits]
      exact ArithmeticBits.one_residueBits _
    all_goals simp [residueBits, BinaryNatCode.encode]

theorem entry_packet (P : Readers) (modulus : List Bool → List Bool) (c : List Bool)
    (i j : Fin (dimension P c)) (k : ℕ) :
    entry P modulus (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k)))) =
      residueBits ((((matrix P c i j).coeff k) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  simp only [entry, Function.comp_apply, PolynomialMoment.augmentedInput, pairFst_pair, pairSnd_pair]
  change MacaulayBits.entryWithIdentity (layout P) (sourceCoefficient P modulus ∘ MacaulayPolynomial.sourceInput)
    (MacaulayPolynomial.constantEntry (BinaryNat.succ ∘ modulus))
      (MacaulayBits.packet (pair c (BinaryNatCode.encode k)) i.val j.val) = _
  generalize hz : pair c (BinaryNatCode.encode k) = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  have hk : Nat.fromBitsLE (pairSnd z) = k := by rw [← hz, pairSnd_pair]; exact Nat.fromBitsLE_bits k
  subst c
  subst k
  exact raw_entry_packet P modulus z i j

theorem dimension_binary {P : Readers} (h : P.PolyTime) : BinaryFn (dimension P) := by
  apply BinaryFn.of_bits
  apply mem_FP_of_eq (MacaulayBits.dimensionCode_mem_FP (layout_polyTime h))
  intro c
  exact FixedWidthPolynomial.countCode_code (layout P).arity (layout P).width c

theorem matrix_degree (P : Readers) (c : List Bool) (i j : Fin (dimension P c)) :
    (matrix P c i j).natDegree ≤ 1 :=
  Macaulay.polynomial_entry_degree_le (system P c) (MacaulayBits.Degrees (layout P) c) ((layout P).width c) 1
    (LinearProjectionSystem.coefficient_degree _ _ _) i j

theorem dimension_eq_pow (P : Readers) (c : List Bool) :
    dimension P c = 2 ^ BoundedCriticalProjection.labelWidth P c := by
  simp only [dimension, layout, FixedWidthPolynomial.count, ← pow_mul,
    BoundedCriticalProjection.labelWidth, Nat.mul_comm]

theorem system_mass (P : Readers) (c : List Bool) (i : Fin ((layout P).arity c))
    (e : Fin ((layout P).arity c) →₀ ℕ) :
    coefficientMass ((system P c i).coeff e) ≤ 2 ^ BoundedCriticalProjection.projectionBits P c := by
  exact (LinearProjectionSystem.coefficient_mass (BoundedFullCriticalSamples.equations P c) (fun _ => degree P c)
    (BoundedCriticalProjection.weights P c) (BoundedCriticalProjection.equationBits P c)
    (BoundedCriticalSeparator.width P c)
    (fun j e => (MvMass.coeff_le _ _).trans (BoundedCriticalProjection.equations_mass P c j))
    (BoundedCriticalProjection.weight_bound P c) i e).trans (BoundedCriticalProjection.projection_mass_bound P c)

theorem matrix_mass (P : Readers) (c : List Bool) (i j : Fin (dimension P c)) :
    coefficientMass (matrix P c i j) ≤ 2 ^ BoundedCriticalProjection.projectionBits P c :=
  Macaulay.matrix_entry_mass_le (system P c) (MacaulayBits.Degrees (layout P) c) ((layout P).width c)
    (BoundedCriticalProjection.projectionBits P c) (system_mass P c) i j

theorem matrix_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    matrix (P.comp f) c = matrix P (f c) := by
  unfold matrix system BoundedProjectionRowsCoefficient.polynomial BoundedCriticalSampleQuery.equations
    BoundedFullDirectionQueries.direction BoundedCriticalSeparator.weight FixedWidthQuery.coordinate
  simp only [BoundedFullDirectionChoice.record_comp, BoundedCriticalSeparator.record_comp]
  rfl

/-- Uniform modulus packets permit the integer determinant backend to query
each entry under any positive modulus without a new coefficient oracle. -/
noncomputable def uniformEntry (P : Readers) : List Bool → List Bool := entry (P.comp pairFst) pairSnd

theorem uniformEntry_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (uniformEntry P) :=
  entry_evaluator (h.comp pairFst_mem_FP) pairSnd_mem_FP (fun q => ha (pairFst q))

theorem uniformEntry_packet (P : Readers) (c m : List Bool) (i j : Fin (dimension P c)) (k : ℕ) :
    uniformEntry P (pair (pair c m) (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k)))) =
      residueBits ((((matrix P c i j).coeff k) : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hz : pair c m = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  have hm : pairSnd z = m := by rw [← hz, pairSnd_pair]
  subst c
  subst m
  have he := entry_packet (P.comp pairFst) pairSnd z i j k
  rw [matrix_comp] at he
  exact he

end LeanCanny.Encoding.BoundedProjectionMacaulay
