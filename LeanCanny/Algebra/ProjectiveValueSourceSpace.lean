/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayFullBoxDeterminantSpace
public import LeanCanny.Algebra.ProjectiveValueGram
public import LeanCanny.Algebra.ModularResidueSpace

/-! # Native source rows for reciprocal polynomial-value determinants

Row zero is U * F - X₀^e; the other original homogeneous rows are lifted
unchanged. Binary degree metadata and native original-row coefficients suffice
for every coefficient of this nested family. The original reader's workspace
is retained. No determinant coefficient oracle is assumed.
-/

@[expose] public section
namespace LeanCanny.Algebra.ProjectiveValueSourceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MvPolynomial
open MacaulayFullBoxBits (Layout ctx idx shift uv ctx_FP idx_FP shift_FP uv_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def row (L : Layout) (hpos : ∀ c, 0 < L.arity c) (q : List Bool) : Fin (L.arity (ctx q)) :=
  ⟨min (Nat.fromBitsLE (idx q)) (L.arity (ctx q) - 1), by have := hpos (ctx q); omega⟩

lemma row_unary (L : Layout) (h : L.Controls) (hpos : ∀ c, 0 < L.arity c) :
    UnaryFn (fun q => (row L hpos q).val) :=
  UnaryFn.fromBitsLE_min idx_FP ((h.arity.comp ctx_FP).sub (UnaryFn.const 1))

noncomputable def exponent (L : Layout) (q : List Bool) : Fin (L.arity (ctx q)) →₀ ℕ :=
  RationalSubstitution.Indexed.exponentVector _ (FixedWidthPolynomial.entry (L.width (ctx q)) (Nat.fromBitsLE (shift q)))

def pure (L : Layout) (q : List Bool) : Prop :=
  ∀ i < L.arity (ctx q), MacaulayFullBoxBits.shiftAt L q i = if i = 0 then L.degree (ctx q) 0 else 0

instance (L : Layout) : DecidablePred (pure L) := fun _ => inferInstanceAs (Decidable (∀ i < _, _))

lemma pure_FP (L : Layout) (h : L.Controls) : FPPred (pure L) := by
  have hr := mem_FP_comp MacaulayBits.loopQuery_mem_FP (MacaulayFullBoxBits.shiftRead_FP h)
  have he := BinaryFn.fromBits hr
  have hd : BinaryFn (fun q => L.degree (ctx (pairFst q)) 0) := by
    apply BinaryFn.of_eq (h.degree.comp
      (mem_FP_pair (mem_FP_comp pairFst_mem_FP ctx_FP) (constFn_mem_FP [])))
    intro q
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, show Nat.fromBitsLE [] = 0 from rfl]
  have hz := FPPred.eq (UnaryFn.length pairSnd_mem_FP) (UnaryFn.const 0)
  have ht := BinaryFn.ite hz hd (BinaryFn.const 0)
  apply ((he.eq ht).forall_lt (h.arity.comp ctx_FP)).of_iff
  intro q
  simp only [MacaulayBits.loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate, MacaulayFullBoxBits.shiftRead, FixedWidthQuery.read_packet,
    MacaulayBits.fromBits_encode, pure, MacaulayFullBoxBits.shiftAt]

lemma pure_iff (L : Layout) (hpos : ∀ c, 0 < L.arity c) (q : List Bool) :
    pure L q ↔ exponent L q = Finsupp.single ⟨0, hpos (ctx q)⟩ (L.degree (ctx q) 0) := by
  have he (i : Fin (L.arity (ctx q))) :
      exponent L q i = MacaulayFullBoxBits.shiftAt L q i.val := by
    simp only [exponent, RationalSubstitution.Indexed.exponentVector, Finsupp.coe_equivFunOnFinite_symm,
      MacaulayFullBoxBits.shiftAt, FixedWidthQuery.entry, Function.comp_apply, i.isLt, ite_true,
      FixedWidthQuery.coordinate, FixedWidthPolynomial.entry_eq_digit, BinaryNat.value_take,
      FixedWidthPolynomial.drop_value]
  constructor
  · intro hp
    ext i
    rw [he, hp i.val i.isLt, Finsupp.single_apply]
    congr 1
    exact propext ⟨fun hi => Fin.ext hi.symm, fun hi => congrArg Fin.val hi.symm⟩
  · intro hp i hi
    have H := congrArg (fun v => v (⟨i, hi⟩ : Fin (L.arity (ctx q)))) hp
    rw [he, Finsupp.single_apply] at H
    simpa only [Fin.mk.injEq, eq_comm (a := 0)] using H

variable (L : Layout) (hpos : ∀ c, 0 < L.arity c)
  (G : (c : List Bool) → Fin (L.arity c) → MvPolynomial (Fin (L.arity c)) (Polynomial ℤ))

noncomputable def system (c : List Bool) (j : Fin (L.arity c)) :
    MvPolynomial (Fin (L.arity c)) (Polynomial (Polynomial ℤ)) :=
  if j.val = 0 then C Polynomial.X * (G c j).map Polynomial.C - X ⟨0, hpos c⟩ ^ L.degree c 0
  else (G c j).map Polynomial.C

noncomputable def source (modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits (((((G (ctx q) (row L hpos q)).coeff (exponent L q)).coeff
    (Nat.fromBitsLE (pairFst (uv q)))) : ℤ) : ZMod (Nat.fromBitsLE (modulus (ctx q)) + 1))

noncomputable def value (modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  MacaulayFullBoxBits.scalar modulus (ctx q) (Nat.fromBitsLE (pairFst (uv q)))
    (Nat.fromBitsLE (pairSnd (uv q))) ((system L hpos G (ctx q) (row L hpos q)).coeff (exponent L q))

noncomputable def selected (q : List Bool) : Prop :=
  ((row L hpos q).val = 0 ∧ Nat.fromBitsLE (pairSnd (uv q)) = 1) ∨
    ((row L hpos q).val ≠ 0 ∧ Nat.fromBitsLE (pairSnd (uv q)) = 0)

noncomputable def delta (q : List Bool) : Prop :=
  (row L hpos q).val = 0 ∧ Nat.fromBitsLE (pairSnd (uv q)) = 0 ∧
    Nat.fromBitsLE (pairFst (uv q)) = 0 ∧ pure L q

noncomputable instance : DecidablePred (selected L hpos) := Classical.decPred _
noncomputable instance : DecidablePred (delta L hpos) := Classical.decPred _

lemma selected_FP (h : L.Controls) : FPPred (selected L hpos) := by
  have hz := (BinaryFn.ofUnary (row_unary L h hpos)).eq (BinaryFn.const 0)
  have hv := BinaryFn.fromBits (mem_FP_comp uv_FP pairSnd_mem_FP)
  exact ((hz.and (hv.eq (BinaryFn.const 1))).or (hz.not.and (hv.eq (BinaryFn.const 0)))).of_iff (fun _ => Iff.rfl)

lemma delta_FP (h : L.Controls) : FPPred (delta L hpos) := by
  have hz := (BinaryFn.ofUnary (row_unary L h hpos)).eq (BinaryFn.const 0)
  have hv := BinaryFn.fromBits (mem_FP_comp uv_FP pairSnd_mem_FP)
  have hu := BinaryFn.fromBits (mem_FP_comp uv_FP pairFst_mem_FP)
  exact (hz.and ((hv.eq (BinaryFn.const 0)).and ((hu.eq (BinaryFn.const 0)).and (pure_FP L h)))).of_iff (fun _ => Iff.rfl)

lemma coefficient_lift (p : Polynomial ℤ) (u v : ℕ) :
    (((Polynomial.C p : Polynomial (Polynomial ℤ)).coeff v).coeff u) =
      if v = 0 then p.coeff u else 0 := by
  rw [Polynomial.coeff_C]
  split_ifs <;> simp

lemma coefficient_reciprocal (p : Polynomial ℤ) (u v : ℕ) :
    (((Polynomial.X * Polynomial.C p : Polynomial (Polynomial ℤ)).coeff v).coeff u) =
      if v = 1 then p.coeff u else 0 := by
  cases v with
  | zero => simp
  | succ v =>
    rw [Polynomial.coeff_X_mul, coefficient_lift]
    simp

lemma coefficient_eq (q : List Bool) :
    ((((system L hpos G (ctx q) (row L hpos q)).coeff (exponent L q)).coeff
      (Nat.fromBitsLE (pairSnd (uv q)))).coeff (Nat.fromBitsLE (pairFst (uv q)))) =
    (if selected L hpos q then ((G (ctx q) (row L hpos q)).coeff (exponent L q)).coeff
      (Nat.fromBitsLE (pairFst (uv q))) else 0) - if delta L hpos q then 1 else 0 := by
  by_cases hz : (row L hpos q).val = 0
  · rw [system, ite_eq_left hz, MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_map, Polynomial.coeff_sub, Polynomial.coeff_sub, coefficient_reciprocal,
      MvPolynomial.coeff_X_pow]
    by_cases hp : pure L q
    · have ht := (pure_iff L hpos q).mp hp
      rw [ite_eq_left ht.symm]
      by_cases hv : Nat.fromBitsLE (pairSnd (uv q)) = 0 <;>
        by_cases hv1 : Nat.fromBitsLE (pairSnd (uv q)) = 1 <;>
        by_cases hu : Nat.fromBitsLE (pairFst (uv q)) = 0 <;>
        simp_all [selected, delta, Polynomial.coeff_one]
    · have ht : Finsupp.single (⟨0, hpos (ctx q)⟩ : Fin (L.arity (ctx q))) (L.degree (ctx q) 0) ≠
          exponent L q := fun ht => hp ((pure_iff L hpos q).mpr ht.symm)
      rw [ite_eq_right ht, Polynomial.coeff_zero, Polynomial.coeff_zero, sub_zero]
      simp [selected, delta, hz, hp]
  · rw [system, ite_eq_right hz, MvPolynomial.coeff_map, coefficient_lift]
    simp [selected, delta, hz]

/-- Native coefficient access to all original homogeneous rows suffices for
the reciprocal test family. Each source call retains its original cost. -/
theorem evaluator (h : L.Controls) (modulus : List Bool → List Bool) (hm : modulus ∈ FP)
    (E : SpaceFunction (source L hpos G modulus)) : SpaceFunction (value L hpos G modulus) := by
  let a (q : List Bool) : ZMod (Nat.fromBitsLE (modulus (ctx q)) + 1) :=
    if selected L hpos q then ((((G (ctx q) (row L hpos q)).coeff (exponent L q)).coeff
      (Nat.fromBitsLE (pairFst (uv q)))) : ℤ) else 0
  let b (q : List Bool) : ZMod (Nat.fromBitsLE (modulus (ctx q)) + 1) := if delta L hpos q then 1 else 0
  have E0 : SpaceFunction (fun _ : List Bool => []) := SpaceFunction.ofFP _ (constFn_mem_FP [])
  have EA : SpaceFunction (fun q => residueBits (a q)) := by
    have EB := SpaceFunction.branch (fun q => decide (selected L hpos q)) (selected_FP L hpos h).flag_mem_FP E E0
    refine EB.congr (funext fun q => ?_)
    simp only [decide_eq_true_eq]
    by_cases hs : selected L hpos q <;> simp [a, source, hs, residueBits, BinaryNatCode.encode]
  have hm' := mem_FP_comp ctx_FP hm
  have E1 : SpaceFunction (fun q => residueBits (1 : ZMod (Nat.fromBitsLE (modulus (ctx q)) + 1))) := by
    apply SpaceFunction.ofFP
    refine mem_FP_of_eq (mem_FP_comp (mem_FP_comp hm' BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP) (fun q => ?_)
    simp only [Function.comp_apply]
    rw [BinaryNat.succ_eq_bits]
    exact ArithmeticBits.one_residueBits _
  have EB : SpaceFunction (fun q => residueBits (b q)) := by
    have EC := SpaceFunction.branch (fun q => decide (delta L hpos q)) (delta_FP L hpos h).flag_mem_FP E1 E0
    refine EC.congr (funext fun q => ?_)
    simp only [decide_eq_true_eq]
    by_cases hs : delta L hpos q <;> simp [b, hs, residueBits, BinaryNatCode.encode]
  have EN := ModularResidueSpace.negEvaluator (fun q => modulus (ctx q)) _ hm' EB
  have ER := ModularResidueSpace.addEvaluator (fun q => modulus (ctx q)) _ _ hm' EA EN
  refine ER.congr (funext fun q => ?_)
  simp only [value, MacaulayFullBoxBits.scalar, coefficient_eq]
  rw [Int.cast_sub]
  simp [a, b, sub_eq_add_neg]

lemma row_packet (c : List Bool) (i : Fin (L.arity c)) (r u v : ℕ) :
    (row L hpos (MacaulayFullBoxBits.entryPacket c i.val r u v)).val = i.val := by
  simp only [row, MacaulayFullBoxBits.ctx_entryPacket, MacaulayFullBoxBits.idx_entryPacket,
    MacaulayBits.fromBits_encode]
  exact Nat.min_eq_left (by have := i.isLt; omega)

lemma value_packet (modulus : List Bool → List Bool) (c : List Bool)
    (i : Fin (L.arity c)) (r u v : ℕ) :
    value L hpos G modulus (MacaulayFullBoxBits.entryPacket c i.val r u v) =
      MacaulayFullBoxBits.scalar modulus c u v ((system L hpos G c i).coeff
        (RationalSubstitution.Indexed.exponentVector (L.arity c) (FixedWidthPolynomial.entry (L.width c) r))) := by
  generalize hpkt : MacaulayFullBoxBits.entryPacket c i.val r u v = q
  have hc := MacaulayFullBoxBits.ctx_entryPacket c i.val r u v
  have hi := row_packet L hpos c i r u v
  have hs := MacaulayFullBoxBits.shift_entryPacket c i.val r u v
  have hu := MacaulayFullBoxBits.uv_entryPacket c i.val r u v
  rw [hpkt] at hc hi hs hu
  cases hc
  have hrow : row L hpos q = i := Fin.ext hi
  simp only [value, exponent, hrow, hs, hu, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]

lemma inner_degree (c : List Bool) (E : ℕ)
    (hG : ∀ i u, ((G c i).coeff u).natDegree ≤ E)
    (i : Fin (L.arity c)) (u : Fin (L.arity c) →₀ ℕ) (k : ℕ) :
    (((system L hpos G c i).coeff u).coeff k).natDegree ≤ E := by
  unfold system
  split_ifs
  · rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, Polynomial.coeff_sub]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · cases k with
      | zero => simp
      | succ k =>
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_C]
        split_ifs
        · exact hG i u
        · simp
    · rw [MvPolynomial.coeff_X_pow]
      split_ifs
      · simp only [Polynomial.coeff_one]
        split_ifs <;> simp
      · simp
  · rw [MvPolynomial.coeff_map, Polynomial.coeff_C]
    split_ifs
    · exact hG i u
    · simp

/-- The complete nested determinant is native from the original rows, even
when the Macaulay degree level is only available in binary. -/
theorem determinantEvaluator (h : L.Controls)
    (modulus inner outer bound : List Bool → List Bool)
    (hlevel : ∀ c, L.level c = Macaulay.level (fun i : Fin (L.arity c) => L.degree c i.val))
    (hbound : ∀ c i u, ((G c i).coeff u).natDegree ≤ Nat.fromBitsLE (bound c))
    (hm : modulus ∈ FP) (hi : inner ∈ FP) (ho : outer ∈ FP) (hb : bound ∈ FP)
    (E : SpaceFunction (source L hpos G modulus)) :
    SpaceFunction (MacaulayFullBoxBits.determinantValue L modulus inner outer (system L hpos G)) :=
  MacaulayFullBoxBits.determinantEvaluator L h modulus inner outer bound
    (value L hpos G modulus) (system L hpos G) hlevel
    (fun c => inner_degree L hpos G c _ (hbound c))
    (value_packet L hpos G modulus) (evaluator L hpos G h modulus hm E) hm hi ho hb

end LeanCanny.Algebra.ProjectiveValueSourceBits
