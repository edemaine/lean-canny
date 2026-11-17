import LeanCanny.CountingHierarchy
import Lean.Util.CollectAxioms

/-! Checked clients and transitive axiom audit for the optional CH extension. -/

open LeanCanny.CountingHierarchy Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators

namespace CountingHierarchyChecks

example : LeanCanny.ETR.language ∈ CountingLevel 26 encBits := etr_mem_CountingLevel
example : LeanCanny.ExistsReal ⊆ CountingLevel 26 encBits := existsReal_subset_CountingLevel

example : ExistsForall.language ∈ CountingLevel 60 encBits := ExistsForall.mem_CountingLevel
example : ExistsForall.RealClass ⊆ CountingLevel 60 encBits :=
  ExistsForall.realClass_subset_CountingLevel

/-- This client uses the generic theorem with variable block sizes and no
nonnegativity promise or auxiliary characteristic/selection oracle. -/
example {n m : List Bool → ℕ}
    {P : (w : List Bool) → MvPolynomial (Fin (n w + m w)) ℤ}
    (C : Controlled P encBits 0)
    (hn : ComputableInPolyTime n encBits encUnary)
    (hm : ComputableInPolyTime m encBits encUnary) :
    {w | ∃ x : Fin (m w) → ℝ, ∀ z : Fin (n w) → ℝ,
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) (P w) ≠ 0} ∈
        CountingLevel 60 encBits := C.twoBlock_mem Decoder.bits hn hm

example (r : ℕ) : ExistsForall.encSentence (r, LeanCanny.ETR.Formula.falsum.encode) ∉
    ExistsForall.language := by
  rw [ExistsForall.encode_mem_language]
  exact ExistsForall.not_sentence_falsum r

/-- Empty blocks and malformed framing exercise the total language boundary. -/
example : ExistsForall.encSentence (0, (LeanCanny.ETR.Formula.not .falsum).encode) ∈
    ExistsForall.language := by
  rw [ExistsForall.encode_mem_language]
  exact ⟨fun i => Fin.elim0 i, fun _ _ => id⟩

example : [] ∉ ExistsForall.language := by
  intro h
  have hf : ¬ExistsForall.FrameCanonical [] := by
    change ¬(ExistsForall.reencode ([] : List Bool) = [])
    decide
  exact hf ((ExistsForall.language_iff_normalized []).mp h).1

/-- A shared circuit computes twice the fourth power of a universal input.
The semantic bridge keeps both uses of each intermediate wire shared. -/
example : ExistsForall.encSentence (1,
    (RealCircuit.guardedMatrix 2 [.mul 1 1, .mul 2 2, .add 3 3]
      (.not (.ltZero (.var 4)))).encode) ∈ ExistsForall.language := by
  rw [RealCircuit.encode_mem_language 1 2 _ _ (by decide)
    (by simp [RealCircuit.WellFormed, LeanCanny.ETR.ComplexCircuit.StraightLine.WellFormed,
      LeanCanny.ETR.ComplexCircuit.Operation.InputsBelow]) (by decide)]
  refine ⟨fun _ => 0, ?_⟩
  intro env _
  change ¬((env 1 * env 1) * (env 1 * env 1) + (env 1 * env 1) * (env 1 * env 1) < 0)
  exact not_lt.mpr (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))


private theorem binaryMod_polyTime {α : Type} {enc : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f enc encNat) (hg : ComputableInPolyTime g enc encNat) :
    ComputableInPolyTime (fun x => f x % g x) enc encNat :=
  (ComputableTidilyInPolyTime.binary_mod.comp (hf.tidy.prod hg.tidy)).computableInPolyTime

/-- The constant polynomial has an exponentially long coefficient on unary input.
Its evaluator uses modular powers; its bound has only polynomially many bits. -/
noncomputable def hugeConstant :
    Controlled (fun w : ℕ =>
      (MvPolynomial.C (2 : ℤ) : MvPolynomial (Fin 0) ℤ) ^ (2 ^ w)) encUnary 0 :=
  (Controlled.constant (n := fun _ : ℕ => 0) (ComputableInPolyTime.const 0)
    (fun _ => 2) (ComputableInPolyTime.const 2)).pow (fun w => 2 ^ w)
      ComputableInPolyTime.binary_two_pow

example : hugeConstant.evaluate (3, 17, []) = 1 := by decide

noncomputable def signedConstant :
    Controlled (fun z : ℤ => (MvPolynomial.C z : MvPolynomial (Fin 0) ℤ)) encIntBin 0 :=
  Controlled.constant (n := fun _ : ℤ => 0) (ComputableInPolyTime.const 0)
    id ComputableInPolyTime.id'

example : signedConstant.evaluate (-13, 5, []) = 2 := by decide
example : signedConstant.evaluate (0, 5, []) = 0 := by decide

/-- A nonconstant family exercises point-list access and the arithmetic closures. -/
noncomputable def coordinate :
    Controlled (fun _ : List Bool => (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℤ))
      encBits 0 :=
  Controlled.coordinate (n := fun _ : List Bool => 1) (ComputableInPolyTime.const 1)
    (fun _ => 0) (ComputableInPolyTime.const 0)

noncomputable def quadratic := (coordinate.mul coordinate).add
  (Controlled.constant (ComputableInPolyTime.const 1) (fun _ : List Bool => 1)
    (ComputableInPolyTime.const 1))

example : quadratic.evaluate ([], 5, [3]) = 0 := by decide
example : quadratic.evaluate ([], 5, []) = 1 := by decide
example : quadratic.evaluate ([], 5, [3, 99]) = 0 := by decide

/-- The addressed central binomial coefficient has exponentially many bits.
The input contains its short exponent, not that integer coefficient. -/
noncomputable def exponentialBinomial :=
  ((Controlled.coordinate (n := fun _ : ℕ => 1) (enc := encUnary) (a := 0)
    (ComputableInPolyTime.const 1) (fun _ => 0) (ComputableInPolyTime.const 0)).add
      (Controlled.constant (ComputableInPolyTime.const 1) (fun _ : ℕ => 1)
        (ComputableInPolyTime.const 1))).pow (fun w => 2 ^ w)
      ComputableInPolyTime.binary_two_pow

noncomputable def centralExponent (w : ℕ) : Fin 1 →₀ ℕ := Finsupp.single 0 (2 ^ w / 2)
def centralAddress (w : ℕ) : List ℕ := [2 ^ w / 2]

private theorem centralAddress_eq (w : ℕ) (i : Fin 1) :
    (centralAddress w)[i.val]?.getD 0 = centralExponent w i := by
  have hi : i = 0 := by apply Fin.ext; omega
  subst i
  simp [centralAddress, centralExponent]

private theorem centralAddress_polyTime :
    ComputableInPolyTime centralAddress encUnary (encList encNat) := by
  unfold centralAddress
  exact ComputableInPolyTime.cons'
    (ComputableInPolyTime.binary_div' ComputableInPolyTime.binary_two_pow (.const 2)) (.const [])

example : (exponentialBinomial.coefficientAccess centralExponent centralAddress
    centralAddress_eq).residue (3, 17) = 2 := by decide

example : (fun w : ℕ =>
    (((MvPolynomial.X (0 : Fin 1) + 1 : MvPolynomial (Fin 1) ℤ) ^ (2 ^ w)).coeff
      (centralExponent w)).sign) ∈ CountingFunction 8 encUnary encIntBin := by
  simpa [max_def] using
      exponentialBinomial.coefficientSign_mem Decoder.unary centralExponent
        centralAddress_polyTime centralAddress_eq

/-- A genuine client of the residue-sign theorem on an implicitly represented integer. -/
example : (fun w : ℕ =>
    (((MvPolynomial.C (2 : ℤ) : MvPolynomial (Fin 0) ℤ) ^ (2 ^ w)).coeff 0).sign) ∈
      CountingFunction 8 encUnary encIntBin :=
  hugeConstant.sign_mem Decoder.unary

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Coefficient extraction includes the constant slot and coefficients above the degree. -/
example : coefficientResidue 7 0 (fun z => (3 + 2 * z + 4 * z ^ 3) % 7) = 3 := by decide
example : coefficientResidue 7 3 (fun z => (3 + 2 * z + 4 * z ^ 3) % 7) = 4 := by decide
example : coefficientResidue 7 4 (fun z => (3 + 2 * z + 4 * z ^ 3) % 7) = 0 := by decide

/-- Degree p-2 is still within the strict multiplicative-period bound. -/
example : coefficientResidue 7 5 (fun z => z ^ 5 % 7) = 1 := by decide

/-- The degree restriction cannot be dropped: X^(p-1) aliases the constant slot. -/
example : coefficientResidue 7 0 (fun z => z ^ 6 % 7) = 1 := by decide

example : gridPoint 5 3 42 = [2, 3, 1] := by decide
example : gridPoint 5 0 42 = [] := by decide

def bivariateValue (z : List ℕ) : ℕ :=
  (3 + 2 * z[0]?.getD 0 + 4 * z[0]?.getD 0 * z[1]?.getD 0) % 5

example : multivariateCoefficientResidue 5 2 [1, 1] bivariateValue = 4 := by decide
example : multivariateCoefficientResidue 5 2 [] bivariateValue = 3 := by decide
example : multivariateCoefficientResidue 5 2 [0, 1] bivariateValue = 0 := by decide
example : multivariateCoefficientResidue 5 0 [] (fun _ => 13) = 3 := by decide

/-- The variable count varies in unary; there is still just one additional
counting level, rather than one coefficient-extraction level per variable. -/
example : (fun q : ℕ × ℕ => multivariateCoefficientResidue q.1 q.2 []
      (fun z => (z[0]?.getD 0 + 1) % q.1)) ∈
    CountingFunction 1 (encPair encNat encUnary) encNat := by
  have hv : (fun q : (ℕ × ℕ) × List ℕ => (q.2[0]?.getD 0 + 1) % q.1.1) ∈
      CountingFunction 0 (encPair (encPair encNat encUnary) (encList encNat)) encNat := by
    apply CountingFunction.of_polyTime
    have hc : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × List ℕ => q.2[0]?.getD 0)
        (encPair (encPair encNat encUnary) (encList encNat)) encNat := by
      simpa only [List.getD_eq_getElem?_getD] using
        ComputableInPolyTime.listGetD_binary 0 (ComputableInPolyTime.snd _ _) (.const 0)
    exact binaryMod_polyTime
      (ComputableInPolyTime.binary_add' hc (.const 1))
      ((ComputableInPolyTime.fst encNat encUnary).comp (ComputableInPolyTime.fst _ _))
  exact multivariateCoefficientResidue_mem (a := 0) (Decoder.pair Decoder.nat Decoder.unary)
    (p := fun q : ℕ × ℕ => q.1) (n := fun q => q.2) (β := fun _ => [])
    (value := fun q : (ℕ × ℕ) × List ℕ => (q.2[0]?.getD 0 + 1) % q.1.1)
    (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.snd _ _) (.const []) hv

/-- For the diagonal matrix with entries 2 and 3 over F_7, the negative
trace/k slots are 0, 2, 4. Its determinant polynomial is 1 + 2X + 6X².
These examples check the exponential computation against those actual coefficients. -/
def logarithmSlots (k : ℕ) : ℕ := if k = 1 then 2 else if k = 2 then 4 else 0

private theorem example_exponential :
    truncatedExponential 2 (fun i => (logarithmSlots i : ZMod 7)) =
      1 + Polynomial.C 2 * Polynomial.X + Polynomial.C 6 * Polynomial.X ^ 2 +
        Polynomial.X ^ 3 + Polynomial.X ^ 4 := by
  have hinv : (2 : ZMod 7)⁻¹ = 4 :=
    (eq_inv_of_mul_eq_one_left (by decide : (4 : ZMod 7) * 2 = 1)).symm
  have h20 : (20 : Polynomial (ZMod 7)) = 6 := by
    simpa only [Polynomial.C_ofNat] using
      congrArg Polynomial.C (by decide : (20 : ZMod 7) = 6)
  have h64 : (64 : Polynomial (ZMod 7)) = 1 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_1] using
      congrArg Polynomial.C (by decide : (64 : ZMod 7) = 1)
  norm_num [truncatedExponential, coefficientPolynomial, logarithmSlots,
    Finset.sum_range_succ, hinv, Polynomial.C_ofNat]
  ring_nf
  simp only [h20, h64, mul_one]

example : truncatedExponentialCoefficient 7 2 0 logarithmSlots = 1 := by
  rw [truncatedExponentialCoefficient_eq (by decide : 2 < 7)
    (by decide : 2 * 2 < 7 - 1) (by decide : 0 < 7 - 1)]
  rw [example_exponential]
  norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_one]; decide

example : truncatedExponentialCoefficient 7 2 1 logarithmSlots = 2 := by
  rw [truncatedExponentialCoefficient_eq (by decide : 2 < 7)
    (by decide : 2 * 2 < 7 - 1) (by decide : 1 < 7 - 1)]
  rw [example_exponential]
  norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_one]; decide

example : truncatedExponentialCoefficient 7 2 2 logarithmSlots = 6 := by
  rw [truncatedExponentialCoefficient_eq (by decide : 2 < 7)
    (by decide : 2 * 2 < 7 - 1) (by decide : 2 < 7 - 1)]
  rw [example_exponential]
  norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_one]; decide

example : (factorialResidue 7 0 : ZMod 7) = 1 := by
  rw [factorialResidue_cast]
  decide

example : (factorialResidue 7 6 : ZMod 7) = -1 := by
  rw [factorialResidue_cast]
  decide

example : traceLogarithmResidue 7 1 5 = 2 := by decide
example : traceLogarithmResidue 7 2 6 = 4 := by decide
example : traceLogarithmResidue 2 0 99 = 0 := by decide

private theorem diagonal_trace_exponential :
    truncatedExponential 2
      (fun k => (traceLogarithmResidue 7 k (2 ^ k + 3 ^ k) : ZMod 7)) =
      1 + Polynomial.C 2 * Polynomial.X + Polynomial.C 6 * Polynomial.X ^ 2 +
        Polynomial.X ^ 3 + Polynomial.X ^ 4 := by
  have hslots : coefficientPolynomial 2
      (fun k => (traceLogarithmResidue 7 k (2 ^ k + 3 ^ k) : ZMod 7)) =
      coefficientPolynomial 2 (fun k => (logarithmSlots k : ZMod 7)) := by
    unfold coefficientPolynomial
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hcases with rfl | rfl | rfl <;> rfl
  simpa only [truncatedExponential, hslots] using example_exponential

/-- Actual diagonal-matrix traces reconstruct all three characteristic slots,
in increasing degree order. The full exponential still has higher terms. -/
example : (traceExponentialCoefficient 7 2 0 (fun k => 2 ^ k + 3 ^ k),
    traceExponentialCoefficient 7 2 1 (fun k => 2 ^ k + 3 ^ k),
    traceExponentialCoefficient 7 2 2 (fun k => 2 ^ k + 3 ^ k)) = (6, 2, 1) := by
  have h (d : ℕ) (hd : d ≤ 2) : traceExponentialCoefficient 7 2 d
      (fun k => 2 ^ k + 3 ^ k) =
        ((1 + Polynomial.C 2 * Polynomial.X + Polynomial.C 6 * Polynomial.X ^ 2 +
          Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial (ZMod 7)).coeff (2 - d)).val := by
    rw [traceExponentialCoefficient, ite_eq_left hd,
      truncatedExponentialCoefficient_eq (by decide : 2 < 7)
        (by decide : 2 * 2 < 7 - 1) (by omega)]
    rw [diagonal_trace_exponential]
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide)]
  norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_one]
  decide

example : traceExponentialCoefficient 7 2 3 (fun k => 2 ^ k + 3 ^ k) = 0 := by
  simp [traceExponentialCoefficient]

/-- Powers give the trace of a one-dimensional diagonal matrix. Both the entry
and modulus vary over binary input; the exponent is a uniform indexed query. -/
example :
    (fun q : ℕ × ℕ => traceExponentialCoefficient q.1 1 0
      (fun k => powMod q.1 q.2 k)) ∈
        CountingFunction 5 (encPair encNat encNat) encNat := by
  have ht : (fun q : (ℕ × ℕ) × ℕ => powMod q.1.1 q.1.2 q.2) ∈
      CountingFunction 0 (encPair (encPair encNat encNat) encNat) encNat := by
    apply CountingFunction.of_polyTime
    exact computableInPolyTime_powMod (by fun_prop) (by fun_prop) (by fun_prop)
  exact traceExponentialCoefficient_mem (a := 0) (Decoder.pair Decoder.nat Decoder.nat)
    (p := fun q : ℕ × ℕ => q.1) (D := fun _ => 1) (d := fun _ => 0)
    (t := fun q : (ℕ × ℕ) × ℕ => powMod q.1.1 q.1.2 q.2)
    (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.const 1)
    (ComputableInPolyTime.const 0) ht

example :
    (fun w : List Bool => truncatedExponentialCoefficient (BitString.binaryValue w)
      (BitString.binaryValue w) 1 logarithmSlots) ∈ CountingFunction 5 encBits encNat := by
  have hc : (fun q : List Bool × ℕ => logarithmSlots q.2) ∈
      CountingFunction 0 (encPair encBits encNat) encNat := by
    apply CountingFunction.of_polyTime
    unfold logarithmSlots
    fun_prop
  exact truncatedExponentialCoefficient_mem (a := 0) Decoder.bits
    (p := BitString.binaryValue) (D := BitString.binaryValue) (k := fun _ => 1)
    (c := fun q : List Bool × ℕ => logarithmSlots q.2)
    (by fun_prop) (by fun_prop) (ComputableInPolyTime.const 1) hc

/-- A single uniform evaluator with variable binary modulus and index costs one level.
This is a resource certificate for an algorithm, not an assumed coefficient oracle. -/
example :
    (fun q : ℕ × ℕ => coefficientResidue q.1 q.2
      (fun z => (3 + 2 * z + 4 * z ^ 3) % q.1)) ∈
        CountingFunction 1 (encPair encNat encNat) encNat := by
  have hv :
      (fun x : (ℕ × ℕ) × ℕ => (3 + 2 * x.2 + 4 * x.2 ^ 3) % x.1.1) ∈
        CountingFunction 0 (encPair (encPair encNat encNat) encNat) encNat := by
    apply CountingFunction.of_polyTime
    have hx : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ => q.2)
        (encPair (encPair encNat encNat) encNat) encNat := .snd _ _
    exact binaryMod_polyTime
      (ComputableInPolyTime.binary_add'
        (ComputableInPolyTime.binary_add' (.const 3) (ComputableInPolyTime.binary_mul' (.const 2) hx))
        (ComputableInPolyTime.binary_mul' (.const 4) (ComputableInPolyTime.binary_pow' hx (.const 3))))
      ((ComputableInPolyTime.fst encNat encNat).comp (ComputableInPolyTime.fst _ _))
  exact coefficientResidue_mem (a := 0) (Decoder.pair Decoder.nat Decoder.nat)
    (p := fun q : ℕ × ℕ => q.1) (k := fun q => q.2)
    (value := fun x : (ℕ × ℕ) × ℕ => (3 + 2 * x.2 + 4 * x.2 ^ 3) % x.1.1)
    (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.snd _ _) hv

/-- A uniform quotient computation varies both modulus and characteristic
 coefficient index, and constructs its own traces at the certified eight-level cost. -/
example : (fun q : ℕ × ℕ => quotientCharacteristicValue q.1 1 2 1 q.2
      (fun _ => 1) (fun z => (2 * z[0]?.getD 0) % q.1) (fun _ _ => 0)) ∈
    CountingFunction 8 (encPair encNat encNat) encNat := by
  have hv : (fun _ : (ℕ × ℕ) × List ℕ => 1) ∈
      CountingFunction 0 (encPair (encPair encNat encNat) (encList encNat)) encNat :=
    CountingFunction.of_polyTime (ComputableInPolyTime.const 1)
  have hJ : (fun q : (ℕ × ℕ) × List ℕ => (2 * q.2[0]?.getD 0) % q.1.1) ∈
      CountingFunction 0 (encPair (encPair encNat encNat) (encList encNat)) encNat := by
    apply CountingFunction.of_polyTime
    have hx := ComputableInPolyTime.listGetD_binary (encA := encNat) 0
      (ComputableInPolyTime.snd (encPair encNat encNat) (encList encNat))
      (ComputableInPolyTime.const 0)
    have hp := (ComputableInPolyTime.fst encNat encNat).comp
      (ComputableInPolyTime.fst (encPair encNat encNat) (encList encNat))
    simpa only [List.getD_eq_getElem?_getD, Function.comp_def] using
      ComputableInPolyTime.binary_mod.comp
        ((ComputableInPolyTime.binary_mul' (.const 2) hx).prod hp)
  have hr : (fun _ : (ℕ × ℕ) × (ℕ × List ℕ) => 0) ∈
      CountingFunction 0
        (encPair (encPair encNat encNat) (encPair encNat (encList encNat))) encNat :=
    CountingFunction.of_polyTime (ComputableInPolyTime.const 0)
  simpa only using quotientCharacteristicValue_mem (a := 0) (Decoder.pair Decoder.nat Decoder.nat)
    (p := fun q : ℕ × ℕ => q.1) (n := fun _ => 1) (ell := fun _ => 2)
    (B := fun _ => 1) (m := fun q => q.2)
    (v := fun _ => 1) (J := fun q => (2 * q.2[0]?.getD 0) % q.1.1)
    (r := fun _ => 0)
    (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.const 1)
    (ComputableInPolyTime.const 2) (ComputableInPolyTime.const 1)
    (ComputableInPolyTime.snd _ _) hv hJ hr

/-- The modular algorithm computes actual characteristic coefficients for
 this concrete matrix, including every index above its dimension. -/
example (d : ℕ) : traceExponentialCoefficient 7 2 d (fun k => 2 ^ k + 3 ^ k) =
    ((Matrix.diagonal ![(2 : ZMod 7), 3]).charpoly.coeff d).val := by
  simpa only [Fintype.card_fin] using traceExponentialCoefficient_eq_charpoly
    (Matrix.diagonal ![(2 : ZMod 7), 3]) (by decide) (by decide) d
    (fun k => 2 ^ k + 3 ^ k) (by
      intro k _
      simp [Matrix.diagonal_pow, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
        Nat.cast_add, Nat.cast_pow])

/-- The trace theorem applies to the actual nonreduced quotient `Z[X]/(X^2)`.
No basis, simple-root condition, or trace oracle is supplied by the client. -/
example (v : MvPolynomial (Fin 1) ℤ) :
    Algebra.trace ℤ (PurePowerResidue.QuotientAlgebra 2 (fun _ : Fin 1 => 0))
      (PurePowerResidue.projection 2 (fun _ : Fin 1 => 0) v) =
        PurePowerResidue.residue 2 (fun _ : Fin 1 => 0)
          (v * PurePowerResidue.jacobian 2 (fun _ : Fin 1 => 0)) := by
  exact PurePowerResidue.trace_eq_residue 1 (by decide) _ (by simp) v

/-- The same theorem includes bad characteristics and several variables. -/
example (v : MvPolynomial (Fin 2) (ZMod 2)) :
    Algebra.trace (ZMod 2) (PurePowerResidue.QuotientAlgebra 2 (fun _ : Fin 2 => 0))
      (PurePowerResidue.projection 2 (fun _ : Fin 2 => 0) v) =
        PurePowerResidue.residue 2 (fun _ : Fin 2 => 0)
          (v * PurePowerResidue.jacobian 2 (fun _ : Fin 2 => 0)) := by
  exact PurePowerResidue.trace_eq_residue 1 (by decide) _ (by simp) v

/-- The full finite criterion rejects a polynomial with no real zeros,
 for every allowed short label and shift, using source-derived cutoffs. -/
example (L : List (Fin 5 × SignType)) (hL : L.length ≤ 3) (e : ℕ) (he : e ≤ 5) :
    0 ≤ finiteCriticalDeterminant 4 0
      (MvPolynomial.C (1 : ℤ) : MvPolynomial (Fin 1) ℤ) (by simp) L e := by
  by_contra hn
  have h := real_zero_iff_negative_finiteCriticalDeterminant 4 (by decide) (by decide) 0
    (MvPolynomial.C (1 : ℤ) : MvPolynomial (Fin 1) ℤ) (by simp)
    (by simp only [LeanCanny.Algebra.MvMass.C, Int.natAbs_one, pow_zero, le_refl])
    (by intro x; simp)
  obtain ⟨x, hx⟩ := h.mpr ⟨L, by change L.length ≤ 3; exact hL, e, he, lt_of_not_ge hn⟩
  simp only [map_one, one_ne_zero] at hx

example : rationalSignApproximation 0 1 1 = 1 := by
  norm_num [rationalSignApproximation, signProductValue, rationalSignProduct,
    Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]

example : rationalSignApproximation 0 1 (-1) = -1 := by
  rw [rationalSignApproximation_neg]
  norm_num [rationalSignApproximation, signProductValue, rationalSignProduct,
    Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]

/-- Empty products, positive bounds and modulus zero exercise loop semantics. -/
example : unaryModularProduct 0 7 (fun i => i + 1) = 1 := by
  rw [unaryModularProduct_eq]
  decide

example : unaryModularProduct 3 0 (fun i => i + 1) = 6 := by
  rw [unaryModularProduct_eq]
  decide

example : unaryModularSum 3 7 (fun i => 3 * i) = 2 := by
  rw [unaryModularSum_eq]
  decide

example : unaryModularList 3 7 (fun i => 3 * i) = [0, 3, 6] := by
  decide

/-- The small determinant evaluator runs on collected residues. -/
example : (modularMatrixDeterminant 7 2 (fun k => k + 1) : ZMod 7) = 5 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let A : Matrix (Fin 2) (Fin 2) (ZMod 7) := fun i j => ((i.val * 2 + j.val + 1 : ℕ) : ZMod 7)
  rw [modularMatrixDeterminant_cast A _ (by intro i j; rfl)]
  rw [Matrix.det_fin_two A]
  norm_num [A]
  decide

/-- A source with no zeros exercises the norm budget in arbitrary arity,
including arity zero, without expanding the enormous specialization integers. -/
example (n d : ℕ) (hd : 1 ≤ d) (L : List (Fin ((d + 1) ^ n) × SignType))
    (e : ℕ) (he : e ≤ (d + 1) ^ n) :
    (finiteCriticalDeterminant d 0
      (MvPolynomial.C (1 : ℤ) : MvPolynomial (Fin n) ℤ) (by simp) L e).natAbs ≤
        2 ^ criticalNormMassExponent n d 0 := by
  exact finiteCriticalDeterminant_natAbs_le d hd 0
    (MvPolynomial.C (1 : ℤ) : MvPolynomial (Fin n) ℤ) (by simp)
    (by simp only [LeanCanny.Algebra.MvMass.C, Int.natAbs_one, pow_zero, le_refl]) L e he

end CountingHierarchyChecks

open Lean in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`LeanCanny.CountingHierarchy).isPrefixOf name then
      checked := checked + 1
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "{name} depends on unexpected axiom {ax}"
  if checked = 0 then
    throwError "No counting-hierarchy declarations found"
  logInfo m!"Audited {checked} CH declarations: standard Lean axioms only."
