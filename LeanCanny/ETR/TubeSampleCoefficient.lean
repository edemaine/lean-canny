/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelSignQueries
public import LeanCanny.ETR.TubeDenseQuery

/-! # Source coefficients in compiled sample coordinates

The projection and reciprocal coordinates precede the original point block.
A guard rejects nonzero exponents outside that point block. Remaining queries
drop the two leading blocks and reuse the full compact-polynomial reader.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeSampleCoefficient
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket MvPolynomial
open RationalSubstitution.Indexed MatrixPower
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable (packet : List Bool → List Bool) (W : List Bool → ℕ) (target : List Bool → List Bool)

noncomputable def A (c : List Bool) : ℕ := TubeParameter.spatialCount (pairFst (packet c))
noncomputable def n (c : List Bool) : ℕ := TubeIndexed.arity (pairFst (packet c))
noncomputable def exponent (c : List Bool) : Fin (A packet c) →₀ ℕ :=
  exponentVector (A packet c) (FixedWidthQuery.coordinate W target c)

def Pattern (c : List Bool) : Prop := ∀ i < A packet c,
  (2 ≤ i ∧ i < n packet c + 2) ∨ FixedWidthQuery.coordinate W target c i = 0

theorem sampleIndex_point_val (c : List Bool) (j : Fin (n packet c)) :
    (sampleIndex (packet c) (.inl j)).val = j.val + 2 := rfl

theorem embedding_injective (c : List Bool) :
    Function.Injective (fun j : Fin (n packet c) => sampleIndex (packet c) (.inl j)) := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [sampleIndex_point_val] at he
  omega

theorem support_iff_pattern (c : List Bool) :
    (↑(exponent packet W target c).support : Set (Fin (A packet c))) ⊆
      Set.range (fun j : Fin (n packet c) => sampleIndex (packet c) (.inl j)) ↔ Pattern packet W target c := by
  have he (i : Fin (A packet c)) : exponent packet W target c i = FixedWidthQuery.coordinate W target c i.val := by
    simp only [exponent, exponentVector, Finsupp.coe_equivFunOnFinite_symm]
  constructor
  · intro h i hi
    by_cases hz : FixedWidthQuery.coordinate W target c i = 0
    · exact Or.inr hz
    · have hm : (⟨i, hi⟩ : Fin (A packet c)) ∈ (exponent packet W target c).support := by
        rw [Finsupp.mem_support_iff, he]
        exact hz
      obtain ⟨j, hj⟩ := h hm
      have hv := congrArg Fin.val hj
      rw [sampleIndex_point_val] at hv
      change j.val + 2 = i at hv
      exact Or.inl ⟨by omega, by have hlt := j.isLt; omega⟩
  · intro h i hi
    have hz : FixedWidthQuery.coordinate W target c i.val ≠ 0 := by
      rw [← he, ← Finsupp.mem_support_iff]
      exact hi
    have hp := (h i.val i.isLt).resolve_right hz
    refine ⟨⟨i.val - 2, by omega⟩, Fin.ext ?_⟩
    rw [sampleIndex_point_val]
    change (i.val - 2) + 2 = i.val
    omega

def shifted (c : List Bool) : List Bool := (target c).drop (2 * W c)

theorem coordinate_shifted (c : List Bool) (i : ℕ) :
    FixedWidthQuery.coordinate W (shifted W target) c i = FixedWidthQuery.coordinate W target c (i + 2) := by
  unfold FixedWidthQuery.coordinate shifted
  rw [List.drop_drop]
  exact congrArg (fun k => Nat.fromBitsLE ((target c).drop k |>.take (W c))) (by ring)

noncomputable def coefficient (c : List Bool) : ℤ :=
  (samplePolynomial (packet c)).coeff (exponent packet W target c)

theorem coefficient_formula (c : List Bool) : coefficient packet W target c =
    if Pattern packet W target c then (CompactSource.polynomial (pairFst (packet c))).coeff
      (exponentVector (n packet c) (FixedWidthQuery.entry (n packet) W (shifted W target) c)) else 0 := by
  have he := EmbeddedCoefficient.coeff_rename (fun j : Fin (n packet c) => sampleIndex (packet c) (.inl j))
    (embedding_injective packet c) (CompactSource.polynomial (pairFst (packet c))) (exponent packet W target c)
  have hr : (exponent packet W target c).comapDomain
      (fun j : Fin (n packet c) => sampleIndex (packet c) (.inl j)) (embedding_injective packet c).injOn =
        exponentVector (n packet c) (FixedWidthQuery.entry (n packet) W (shifted W target) c) := by
    ext j
    change FixedWidthQuery.coordinate W target c (sampleIndex (packet c) (.inl j)).val =
      FixedWidthQuery.entry (n packet) W (shifted W target) c j.val
    rw [sampleIndex_point_val, FixedWidthQuery.entry, ite_eq_left j.isLt, coordinate_shifted]
  have hs := support_iff_pattern packet W target c
  exact he.trans ((congrArg (fun m => if
    (↑(exponent packet W target c).support : Set (Fin (A packet c))) ⊆
      Set.range (fun j : Fin (n packet c) => sampleIndex (packet c) (.inl j))
    then (CompactSource.polynomial (pairFst (packet c))).coeff m else 0) hr).trans
    (congrArg (fun P : Prop => if P then (CompactSource.polynomial (pairFst (packet c))).coeff
      (exponentVector (n packet c) (FixedWidthQuery.entry (n packet) W (shifted W target) c)) else 0) (propext hs)))

theorem A_unary (hp : packet ∈ FP) : UnaryFn (A packet) :=
  TubeParameter.spatialCount_unary.comp (mem_FP_comp hp pairFst_mem_FP)

theorem n_unary (hp : packet ∈ FP) : UnaryFn (n packet) :=
  TubeIndexed.arity_unary.comp (mem_FP_comp hp pairFst_mem_FP)

theorem pattern_fppred (hp : packet ∈ FP) (hW : UnaryFn W) (ht : target ∈ FP) :
    FPPred (Pattern packet W target) := by
  have hs := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht) (UnaryFn.index.mul hW.lift)) hW.lift
  have hz := BinaryNat.le_fppred hs (constFn_mem_FP [])
  have hin := (FPPred.le (UnaryFn.const 2) UnaryFn.index).and
    (FPPred.lt UnaryFn.index ((n_unary packet hp).lift.add (UnaryFn.const 2)))
  apply (FPPred.forall_lt (A_unary packet hp) (hin.or hz)).of_iff
  intro c
  have hnil : Nat.fromBitsLE ([] : List Bool) = 0 := rfl
  simp only [Pattern, pairFst_pair, pairSnd_pair, List.length_replicate,
    FixedWidthQuery.coordinate, Function.comp_apply, hnil, Nat.le_zero]

theorem shifted_mem_FP (hW : UnaryFn W) (ht : target ∈ FP) : shifted W target ∈ FP :=
  drop_mem_FP ht ((UnaryFn.const 2).mul hW)

def base : List Bool → List Bool := fun c => RationalSubstitutionBits.compiledTerm (pairFst (packet c))

theorem base_mem_FP (hp : packet ∈ FP) : base packet ∈ FP :=
  mem_FP_comp (mem_FP_comp hp pairFst_mem_FP) RationalSubstitutionBits.compiledTerm_mem_FP

def Allowed (c : List Bool) : Prop := Pattern packet W target c ∧
  FixedWidthQuery.Bounded (n packet) W (shifted W target) (TubeDense.degreeBudget (base packet) 1) c

theorem allowed_fppred (hp : packet ∈ FP) (hW : UnaryFn W) (ht : target ∈ FP) :
    FPPred (Allowed packet W target) :=
  (pattern_fppred packet W target hp hW ht).and
    (FixedWidthQuery.bounded_fppred (n_unary packet hp) hW
      (TubeDense.degreeBudget_unary (base_mem_FP packet hp) 1) (shifted_mem_FP W target hW ht))

theorem source_degree (c : List Bool) :
    (CompactSource.polynomial (pairFst (packet c))).totalDegree ≤ TubeDense.degreeBudget (base packet) 1 c := by
  have hd := TubeDense.polynomial_power_degree (base packet) 1 (by decide) c
  rw [pow_one] at hd
  dsimp +instances only [TubeDense.polynomial, base, CompactSource.polynomial, CompactSource.term] at hd ⊢
  exact hd

theorem child_correct (modulus : List Bool → List Bool) (c : List Bool)
    (hb : FixedWidthQuery.Bounded (n packet) W (shifted W target) (TubeDense.degreeBudget (base packet) 1) c) :
    CompactPowerCoefficient.value (base packet) (TubeDense.repacked (base packet) 1 W (shifted W target))
      modulus (fun _ => 1) c = residueBits
        (((CompactSource.polynomial (pairFst (packet c))).coeff
          (exponentVector (n packet c) (FixedWidthQuery.entry (n packet) W (shifted W target) c))) :
            ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  dsimp +instances only [n, TubeIndexed.arity, CompactSource.term, base, TubeDense.arity, TermArity.arity,
    CompactSource.polynomial] at *
  have he := TubeDense.child_correct (base packet) 1 (by decide) W (shifted W target) modulus c hb
  have he' := he.trans (congrArg (fun p : MvPolynomial (Fin (TubeDense.arity (base packet) c)) ℤ =>
    residueBits ((p.coeff (exponentVector (TubeDense.arity (base packet) c)
      (FixedWidthQuery.entry (TubeDense.arity (base packet)) W (shifted W target) c))) :
        ZMod (Nat.fromBitsLE (modulus c) + 1))) (pow_one (TubeDense.polynomial (base packet) c)))
  dsimp +instances only [n, TubeIndexed.arity, CompactSource.term, base, TubeDense.arity, TermArity.arity,
    CompactSource.polynomial, TubeDense.polynomial] at he' ⊢
  exact he'

theorem coefficient_zero_of_not_allowed (c : List Bool) (h : ¬ Allowed packet W target c) :
    coefficient packet W target c = 0 := by
  by_contra hn
  have hp : Pattern packet W target c := by
    by_contra hp
    exact hn (by rw [coefficient_formula, ite_eq_right hp])
  rw [coefficient_formula, ite_eq_left hp] at hn
  apply h
  refine ⟨hp, ?_⟩
  intro i hi
  have hm := MvPolynomial.monomial_le_degreeOf (⟨i, hi⟩ : Fin (n packet c)) (MvPolynomial.mem_support_iff.mpr hn)
  have hd := source_degree packet c
  have hb := hm.trans ((degreeOf_le_totalDegree _ _).trans hd)
  simpa only [exponentVector, Finsupp.coe_equivFunOnFinite_symm, FixedWidthQuery.entry, hi, ite_true] using hb

noncomputable def value (modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits (coefficient packet W target c : ZMod (Nat.fromBitsLE (modulus c) + 1))

theorem evaluator (modulus : List Bool → List Bool) (hp : packet ∈ FP)
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (value packet W target modulus) := by
  let child := CompactPowerCoefficient.value (base packet)
    (TubeDense.repacked (base packet) 1 W (shifted W target)) modulus (fun _ => 1)
  have hc : SpaceFunction child := CompactPowerCoefficient.evaluator (base packet) _ modulus (fun _ => 1)
    (base_mem_FP packet hp) (TubeDense.repacked_mem_FP (base_mem_FP packet hp) hW (shifted_mem_FP W target hW ht) 1)
    hm (UnaryFn.const 1)
  let E := SpaceFunction.branch (fun c => decide (Allowed packet W target c))
    (allowed_fppred packet W target hp hW ht).flag_mem_FP hc (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine E.congr (funext fun c => ?_)
  by_cases ha : Allowed packet W target c
  · have he := child_correct packet W target modulus c ha.2
    have hp' := coefficient_formula packet W target c
    rw [ite_eq_left ha.1] at hp'
    simp only [ha, decide_true, ↓reduceIte]
    change child c = residueBits (coefficient packet W target c : ZMod (Nat.fromBitsLE (modulus c) + 1))
    exact he.trans (congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus c) + 1))) hp'.symm)
  · have hz := coefficient_zero_of_not_allowed packet W target c ha
    simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte, value, hz, Int.cast_zero, residueBits, ZMod.val_zero]
    rfl

end LeanCanny.ETR.TubeSampleCoefficient
