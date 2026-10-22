/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationNormalization

/-! # Literal bit-size bounds for equation normalization -/

@[expose] public section

namespace LeanCanny.ETR


namespace Term

@[simp] theorem dataSize_var (i : ℕ) : (var i).toData.size = 2 * i + 8 := by
  simp only [toData, Data.cons_size, Codec.unary_size, Data.size_empty]
  omega

@[simp] theorem dataSize_add (t u : Term) :
    (add t u).toData.size = t.toData.size + u.toData.size + 8 := by
  simp only [toData, Data.cons_size, Codec.unary_size, Data.size_empty]
  omega

@[simp] theorem dataSize_mul (t u : Term) :
    (mul t u).toData.size = t.toData.size + u.toData.size + 10 := by
  simp only [toData, Data.cons_size, Codec.unary_size, Data.size_empty]
  omega

@[simp] theorem dataSize_const_zero : (const 0).toData.size = 10 := by
  simp [toData, Codec.integer, Codec.natural, Nat.bits, Codec.unary,
    Data.cons_size, Data.size_empty]

@[simp] theorem dataSize_const_one : (const 1).toData.size = 14 := by
  simp [toData, Codec.integer, Codec.natural, Codec.bit, Nat.bits, Codec.unary,
    Data.cons_size, Data.size_empty]

@[simp] theorem dataSize_const_neg_one : (const (-1)).toData.size = 12 := by
  change (const (.negSucc 0)).toData.size = 12
  simp [toData, Codec.integer, Codec.natural, Nat.bits, Codec.unary,
    Data.cons_size, Data.size_empty]

@[simp] theorem dataSize_nonzeroEquation (t : Term) (i : ℕ) :
    (t.nonzeroEquation i).toData.size = t.toData.size + 2 * i + 38 := by
  simp only [nonzeroEquation, dataSize_add, dataSize_mul, dataSize_var, dataSize_const_neg_one]
  omega

@[simp] theorem dataSize_negativeEquation (t : Term) (i : ℕ) :
    (t.negativeEquation i).toData.size = t.toData.size + 4 * i + 58 := by
  simp only [negativeEquation, square, dataSize_add, dataSize_mul, dataSize_var,
    dataSize_const_one]
  omega

@[simp] theorem dataSize_nonnegativeEquation (t : Term) (i : ℕ) :
    (t.nonnegativeEquation i).toData.size = t.toData.size + 4 * i + 56 := by
  simp only [nonnegativeEquation, square, dataSize_add, dataSize_mul, dataSize_var,
    dataSize_const_neg_one]
  omega

@[simp] theorem dataSize_booleanEquation (i : ℕ) :
    (booleanEquation i).toData.size = 4 * i + 46 := by
  simp only [booleanEquation, dataSize_mul, dataSize_add, dataSize_var, dataSize_const_neg_one]
  omega

@[simp] theorem dataSize_oneMinus (i : ℕ) : (oneMinus i).toData.size = 2 * i + 52 := by
  simp only [oneMinus, dataSize_add, dataSize_mul, dataSize_var,
    dataSize_const_one, dataSize_const_neg_one]
  omega

end Term

namespace SignedFormula

/-- A syntactic budget that includes the original term bit lengths, before fresh variables
and selectors are allocated. It is bounded by the original formula's encoded length. -/
def budget : SignedFormula → ℕ
  | .truth | .falsum => 1
  | .eqZero t | .neZero t | .ltZero t | .nonneg t => t.toData.size + 1
  | .and p q | .or p q => p.budget + q.budget + 1

theorem budget_pos (p : SignedFormula) : 0 < p.budget := by
  cases p <;> simp [budget]

theorem equations_length_le (p : SignedFormula) (start : ℕ) :
    (p.equations start).terms.length ≤ p.budget := by
  induction p generalizing start with
  | and p q ihp ihq | or p q ihp ihq =>
      have hp := ihp start
      have hq := ihq (p.equations start).next
      simp only [equations, EquationSystem.conjunction, EquationSystem.disjunction,
        List.length_append, List.length_cons, List.length_map, budget]
      omega
  | _ => simp [equations, budget]

theorem equations_next_le (p : SignedFormula) (start : ℕ) :
    (p.equations start).next ≤ start + p.budget := by
  induction p generalizing start with
  | and p q ihp ihq | or p q ihp ihq =>
      have hp := ihp start
      have hq := ihq (p.equations start).next
      simp only [equations, EquationSystem.conjunction, EquationSystem.disjunction, budget]
      omega
  | _ => simp [equations, budget]

end SignedFormula

namespace Formula

theorem toSigned_budget_le (p : Formula) (positive : Bool) :
    (p.toSigned positive).budget ≤ p.toData.size := by
  induction p generalizing positive with
  | falsum | eqZero t | ltZero t =>
      cases positive <;> simp [toSigned, SignedFormula.budget, toData, Data.cons_size,
        Codec.unary_size, Data.size_empty] <;> omega
  | not p ih =>
      have h := ih (!positive)
      simp only [toSigned, toData, Data.cons_size, Codec.unary_size, Data.size_empty]
      omega
  | and p q ihp ihq | or p q ihp ihq =>
      have hp0 := ihp false
      have hp1 := ihp true
      have hq0 := ihq false
      have hq1 := ihq true
      cases positive <;> simp only [toSigned, Bool.false_eq_true, ite_false, ite_true,
        SignedFormula.budget, toData, Data.cons_size, Codec.unary_size, Data.size_empty] <;> omega

end Formula

namespace Term

/-- Total encoded bit length of terms, without an additional list wrapper. -/
def listDataSize (ts : List Term) : ℕ := (ts.map (fun t => t.toData.size)).sum

@[simp] theorem listDataSize_nil : listDataSize [] = 0 := rfl

@[simp] theorem listDataSize_cons (t : Term) (ts : List Term) :
    listDataSize (t :: ts) = t.toData.size + listDataSize ts := rfl

@[simp] theorem listDataSize_append (ts us : List Term) :
    listDataSize (ts ++ us) = listDataSize ts + listDataSize us := by
  simp [listDataSize]

@[simp] theorem listDataSize_map_mul (ts : List Term) (u : Term) :
    listDataSize (ts.map (Term.mul u)) = listDataSize ts + ts.length * (u.toData.size + 10) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map_cons, listDataSize_cons, dataSize_mul, List.length_cons, ih,
        Nat.add_mul, Nat.one_mul]
      omega

theorem dataSize_sumSquares (ts : List Term) :
    (sumSquares ts).toData.size = 2 * listDataSize ts + 18 * ts.length + 10 := by
  induction ts with
  | nil => simp [sumSquares]
  | cons t ts ih =>
      simp only [sumSquares, square, dataSize_add, dataSize_mul, listDataSize_cons,
        List.length_cons, ih]
      omega

end Term

namespace EquationSystem

def dataSize (s : EquationSystem) : ℕ := Term.listDataSize s.terms

@[simp] theorem dataSize_conjunction (a b : EquationSystem) :
    (a.conjunction b).dataSize = a.dataSize + b.dataSize := by
  simp [conjunction, dataSize]

theorem dataSize_disjunction (a b : EquationSystem) :
    (a.disjunction b).dataSize = a.dataSize + b.dataSize +
      a.terms.length * (2 * b.next + 18) + b.terms.length * (2 * b.next + 62) +
      (4 * b.next + 46) := by
  simp only [disjunction, dataSize, Term.listDataSize_cons, Term.listDataSize_append,
    Term.listDataSize_map_mul, Term.dataSize_booleanEquation, Term.dataSize_var,
    Term.dataSize_oneMinus]
  ring

end EquationSystem

namespace SignedFormula

private theorem atomic_cost_bound (size start cap : ℕ) (h : start ≤ cap) :
    size + 4 * start + 58 ≤ 100 * (cap + 1) * (size + 1) ^ 2 := by
  have hsq : size + 1 ≤ (size + 1) ^ 2 := by nlinarith
  calc
    size + 4 * start + 58 ≤ 100 * (cap + 1) * (size + 1) := by
      nlinarith [Nat.zero_le (size * cap)]
    _ ≤ 100 * (cap + 1) * (size + 1) ^ 2 := Nat.mul_le_mul_left _ hsq

/-- A uniform bound for all compiled terms. `cap` bounds allocated indices, and `budget`
bounds the number of equations and the sizes of the original atomic polynomials. -/
theorem equations_dataSize_le (p : SignedFormula) (start cap : ℕ)
    (hcap : (p.equations start).next ≤ cap) :
    (p.equations start).dataSize ≤ 100 * (cap + 1) * p.budget ^ 2 := by
  induction p generalizing start cap with
  | truth => simp [equations, EquationSystem.dataSize]
  | falsum =>
      simp only [equations, EquationSystem.dataSize, Term.listDataSize_cons,
        Term.listDataSize_nil, Term.dataSize_const_one, budget]
      omega
  | eqZero t | neZero t | ltZero t | nonneg t =>
      have hstart : start ≤ cap := (equations_next_ge _ start).trans hcap
      have hb := atomic_cost_bound t.toData.size start cap hstart
      simp only [equations, EquationSystem.dataSize, Term.listDataSize_cons,
        Term.listDataSize_nil, Term.dataSize_nonzeroEquation, Term.dataSize_negativeEquation,
        Term.dataSize_nonnegativeEquation, budget]
      omega
  | and p q ihp ihq =>
      have hqcap : (q.equations (p.equations start).next).next ≤ cap := hcap
      have hpcap : (p.equations start).next ≤ cap :=
        (equations_next_ge q _).trans hqcap
      have ha := ihp start cap hpcap
      have hb := ihq _ cap hqcap
      simp only [equations, EquationSystem.dataSize_conjunction, budget]
      calc
        _ ≤ 100 * (cap + 1) * p.budget ^ 2 + 100 * (cap + 1) * q.budget ^ 2 :=
          Nat.add_le_add ha hb
        _ = 100 * (cap + 1) * (p.budget ^ 2 + q.budget ^ 2) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (by nlinarith [Nat.zero_le (p.budget * q.budget)])
  | or p q ihp ihq =>
      have hqcap : (q.equations (p.equations start).next).next ≤ cap := by
        change (q.equations (p.equations start).next).next + 1 ≤ cap at hcap
        omega
      have hpcap : (p.equations start).next ≤ cap :=
        (equations_next_ge q _).trans hqcap
      have ha := ihp start cap hpcap
      have hb := ihq _ cap hqcap
      have hla := Nat.mul_le_mul (equations_length_le p start)
        (show 2 * (q.equations (p.equations start).next).next + 18 ≤ 100 * (cap + 1) by omega)
      have hlb := Nat.mul_le_mul (equations_length_le q (p.equations start).next)
        (show 2 * (q.equations (p.equations start).next).next + 62 ≤ 100 * (cap + 1) by omega)
      have hbool : 4 * (q.equations (p.equations start).next).next + 46 ≤
          100 * (cap + 1) := by omega
      simp only [equations, EquationSystem.dataSize_disjunction, budget]
      calc
        _ ≤ 100 * (cap + 1) * p.budget ^ 2 + 100 * (cap + 1) * q.budget ^ 2 +
            p.budget * (100 * (cap + 1)) + q.budget * (100 * (cap + 1)) +
            100 * (cap + 1) := by omega
        _ = 100 * (cap + 1) *
            (p.budget ^ 2 + q.budget ^ 2 + p.budget + q.budget + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (by nlinarith [Nat.zero_le (p.budget * q.budget)])

end SignedFormula

namespace Formula

theorem equationSystem_next_le (p : Formula) : p.equationSystem.next ≤ 2 * p.inputSize := by
  have hb := p.toSigned_budget_le true
  have hn := (p.toSigned true).equations_next_le p.arity
  have ha := p.arity_le_inputSize
  rw [p.inputSize_eq_dataSize] at ha ⊢
  exact hn.trans (by omega)

theorem singleEquation_arity_le (p : Formula) : p.singleEquation.arity ≤ 2 * p.inputSize :=
  p.singleEquation_scoped.trans p.equationSystem_next_le

/-- The compiler has polynomial *literal binary output length*, including every unary
fresh-variable index and every copied integer coefficient. This is a size bound, not yet
a polynomial-time implementation theorem in the machine model. -/
theorem singleEquation_inputSize_le (p : Formula) :
    p.singleEquation.inputSize ≤ 500 * (p.inputSize + 1) ^ 3 := by
  let n := p.inputSize
  have hb : (p.toSigned true).budget ≤ n := by
    simpa only [n, p.inputSize_eq_dataSize] using p.toSigned_budget_le true
  have hl : p.equationSystem.terms.length ≤ n :=
    ((p.toSigned true).equations_length_le p.arity).trans hb
  have hc := (p.toSigned true).equations_dataSize_le p.arity (2 * n) p.equationSystem_next_le
  have hs : (p.toSigned true).budget ^ 2 ≤ n ^ 2 := by nlinarith
  have hsize : p.equationSystem.dataSize ≤ 100 * (2 * n + 1) * n ^ 2 :=
    hc.trans (Nat.mul_le_mul_left _ hs)
  have hout : p.singleEquation.inputSize =
      2 * p.equationSystem.dataSize + 18 * p.equationSystem.terms.length + 16 := by
    simp only [inputSize_eq_dataSize, singleEquation, toData, Data.cons_size,
      Codec.unary_size, Data.size_empty, Term.dataSize_sumSquares, EquationSystem.dataSize]
    omega
  rw [hout]
  change _ ≤ 500 * (n + 1) ^ 3
  calc
    _ ≤ 2 * (100 * (2 * n + 1) * n ^ 2) + 18 * n + 16 := by omega
    _ ≤ 500 * (n + 1) ^ 3 := by nlinarith [Nat.zero_le (n ^ 3)]

end Formula
end LeanCanny.ETR
