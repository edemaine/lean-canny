/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionLinearCoefficient
public import LeanCanny.Encoding.BoundedCriticalHomogeneousCoefficient

/-! # Native coefficients of the complete retained-projection system -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionRowsCoefficient
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Computation
open BoundedFullWriter MatrixPower RationalSubstitution.Indexed MvPolynomial Brackets FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (P : Readers) (direction separator : List Bool → List Bool) (c : List Bool) :=
  LinearProjectionSystem.rows (BoundedCriticalSampleQuery.equations P direction c) (fun _ => degree P c)
    (fun i => (BoundedCriticalSeparator.weight P separator c i.val : ℤ))

noncomputable def value (P : Readers) (direction separator : List Bool → List Bool)
    (row : (c : List Bool) → Fin (P.dim c + 5)) (W : List Bool → ℕ)
    (k modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits (((((polynomial P direction separator (pairFst q) (row (pairFst q))).coeff
    (exponentVector (P.dim (pairFst q) + 5) (entry (W (pairFst q)) (Nat.fromBitsLE (pairSnd q))))).coeff
      (Nat.fromBitsLE (k (pairFst q)))) : ℤ) : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1))

noncomputable def valueData (source : List Bool) (dim radius : ℕ) (direction separator : List Bool)
    (i W : ℕ) (k modulus target : List Bool) : List Bool :=
  let P : Readers := ⟨fun _ => source, fun _ => dim, fun _ => radius⟩
  residueBits (((((polynomial P (fun _ => direction) (fun _ => separator) []
    ⟨min i (dim + 4), by change min i (dim + 4) < dim + 5; omega⟩).coeff
      (exponentVector (dim + 5) (entry W (Nat.fromBitsLE target)))).coeff (Nat.fromBitsLE k)) : ℤ) :
        ZMod (Nat.fromBitsLE modulus + 1))

theorem value_data (P : Readers) (direction separator : List Bool → List Bool)
    (row : (c : List Bool) → Fin (P.dim c + 5)) (W : List Bool → ℕ)
    (k modulus : List Bool → List Bool) (q : List Bool) :
    value P direction separator row W k modulus q = valueData (P.source (pairFst q))
      (P.dim (pairFst q)) (P.radius (pairFst q)) (direction (pairFst q)) (separator (pairFst q))
      (row (pairFst q)).val (W (pairFst q)) (k (pairFst q)) (modulus (pairFst q)) (pairSnd q) := by
  unfold valueData
  simp only [Nat.min_eq_left (show (row (pairFst q)).val ≤ P.dim (pairFst q) + 4 by
    have := (row (pairFst q)).isLt; omega)]
  rfl

noncomputable def answer (P : Readers) (direction separator : List Bool → List Bool)
    (row : (c : List Bool) → Fin (P.dim c + 5)) (W : List Bool → ℕ)
    (target k modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  valueData (P.source c) (P.dim c) (P.radius c) (direction c) (separator c)
    (row c).val (W c) (k c) (modulus c) (target c)

def tailRow (P : Readers) (row : (c : List Bool) → Fin (P.dim c + 5)) (c : List Bool) : Fin (P.dim c + 4) :=
  ⟨min ((row c).val - 1) (P.dim c + 3), by omega⟩

theorem tailRow_succ (P : Readers) (row : (c : List Bool) → Fin (P.dim c + 5)) (c : List Bool)
    (hrow : (row c).val ≠ 0) : (tailRow P row c).succ = row c := by
  apply Fin.ext
  have := (row c).isLt
  change min ((row c).val - 1) (P.dim c + 3) + 1 = (row c).val
  omega

theorem homogeneous_eq (P : Readers) (direction separator : List Bool → List Bool)
    (row : (c : List Bool) → Fin (P.dim c + 5)) (c : List Bool) :
    BoundedCriticalHomogeneousCoefficient.polynomial P direction (tailRow P row) c =
      polynomial P direction separator c (tailRow P row c).succ := rfl

theorem evaluator {P : Readers} {direction separator : List Bool → List Bool}
    {row : (c : List Bool) → Fin (P.dim c + 5)} {W : List Bool → ℕ} {k modulus : List Bool → List Bool}
    (h : P.PolyTime) (hd : direction ∈ FP) (hs : separator ∈ FP) (hi : UnaryFn (fun c => (row c).val))
    (hW : UnaryFn W) (hk : k ∈ FP) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hfit : ∀ c, degree P c < 2 ^ W c) (hpos : ∀ c, 0 < W c) :
    SpaceFunction (value P direction separator row W k modulus) := by
  have htail : UnaryFn (fun c => (tailRow P row c).val) :=
    (hi.sub (UnaryFn.const 1)).min (h.dim.add (UnaryFn.const 3))
  have hL := BoundedProjectionLinearCoefficient.evaluator h hs hW hpos hk hm
  have hR := BoundedCriticalHomogeneousCoefficient.evaluator h hd htail hW hk hm ha hfit
  have hp := FPPred.eq (hi.comp pairFst_mem_FP) (UnaryFn.const 0)
  have he := SpaceFunction.branch _ hp.flag_mem_FP hL hR
  apply he.congr
  funext q
  simp only [decide_eq_true_eq]
  by_cases hz : (row (pairFst q)).val = 0
  · rw [ite_eq_left hz]
    have hrow : row (pairFst q) = 0 := Fin.ext hz
    unfold value
    rw [hrow]
    unfold BoundedProjectionLinearCoefficient.value LinearCoefficientBits.value LinearCoefficientBits.coefficient
    change residueBits (((((BoundedProjectionLinearCoefficient.polynomial P separator (pairFst q)).coeff
      (exponentVector (P.dim (pairFst q) + 5) (entry (W (pairFst q)) (Nat.fromBitsLE (pairSnd q))))).coeff
      (Nat.fromBitsLE (k (pairFst q)))) : ℤ) : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1)) = _
    rw [BoundedProjectionLinearCoefficient.polynomial_eq P separator (pairFst q)
      (BoundedCriticalSampleQuery.equations P direction (pairFst q)) (fun _ => degree P (pairFst q))]
    rfl
  · rw [ite_eq_right hz]
    unfold BoundedCriticalHomogeneousCoefficient.value value
    rw [homogeneous_eq P direction separator row, tailRow_succ P row (pairFst q) hz]

theorem answer_evaluator {P : Readers} {direction separator : List Bool → List Bool}
    {row : (c : List Bool) → Fin (P.dim c + 5)} {W : List Bool → ℕ} {target k modulus : List Bool → List Bool}
    (h : P.PolyTime) (hd : direction ∈ FP) (hs : separator ∈ FP) (hi : UnaryFn (fun c => (row c).val))
    (hW : UnaryFn W) (ht : target ∈ FP) (hk : k ∈ FP) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hfit : ∀ c, degree P c < 2 ^ W c) (hpos : ∀ c, 0 < W c) :
    SpaceFunction (answer P direction separator row W target k modulus) := by
  have he := (evaluator h hd hs hi hW hk hm ha hfit hpos).precompose
    (fun c => pair c (target c)) (mem_FP_pair id_mem_FP ht)
  apply he.congr
  funext c
  have hi' : (row (pairFst (pair c (target c)))).val = (row c).val :=
    congrArg (fun p => (row p).val) (pairFst_pair c (target c))
  simp only [value_data, answer, Function.comp_apply, pairFst_pair, pairSnd_pair, hi']

/-- Charge a native weight record together with the selected critical direction. -/
theorem record_evaluator {P : Readers} {record : List Bool → List Bool} {row : (c : List Bool) → Fin (P.dim c + 5)}
    {W : List Bool → ℕ} {target k modulus : List Bool → List Bool}
    (h : P.PolyTime) (hr : SpaceFunction record) (hi : UnaryFn (fun c => (row c).val)) (hW : UnaryFn W)
    (ht : target ∈ FP) (hk : k ∈ FP) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hfit : ∀ c, degree P c < 2 ^ W c) (hpos : ∀ c, 0 < W c) :
    SpaceFunction (answer P (BoundedFullDirectionChoice.record P) record
      row W target k modulus) := by
  have hc := answer_evaluator (row := fun p => row (pairFst p)) (h.comp pairFst_mem_FP)
    (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
    (hi.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP) (mem_FP_comp pairFst_mem_FP ht)
    (mem_FP_comp pairFst_mem_FP hk) (mem_FP_comp pairFst_mem_FP hm)
    (fun p => ha (pairFst p)) (fun p => hfit (pairFst p)) (fun p => hpos (pairFst p))
  have hp := ((BoundedFullDirectionChoice.evaluator h ha).pairOutputs hr).withInput
  have he : SpaceFunction _ := ⟨hc.computable.comp hp.computable⟩
  apply he.congr
  funext c
  have hi' : (row (pairFst (pair c (pair (BoundedFullDirectionChoice.record P c)
      (record c))))).val = (row c).val :=
    congrArg (fun p => (row p).val) (pairFst_pair c _)
  simp only [answer, Readers.comp, Function.comp_apply, pairFst_pair, pairSnd_pair, hi']

/-- Both actual record searches are included in the workspace bound. -/
theorem selected_evaluator {P : Readers} {row : (c : List Bool) → Fin (P.dim c + 5)}
    {W : List Bool → ℕ} {target k modulus : List Bool → List Bool}
    (h : P.PolyTime) (hi : UnaryFn (fun c => (row c).val)) (hW : UnaryFn W)
    (ht : target ∈ FP) (hk : k ∈ FP) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hfit : ∀ c, degree P c < 2 ^ W c) (hpos : ∀ c, 0 < W c) :
    SpaceFunction (answer P (BoundedFullDirectionChoice.record P) (BoundedCriticalSeparator.record P)
      row W target k modulus) :=
  record_evaluator h (BoundedCriticalSeparator.evaluator h ha) hi hW ht hk hm ha hfit hpos

end LeanCanny.Encoding.BoundedProjectionRowsCoefficient
