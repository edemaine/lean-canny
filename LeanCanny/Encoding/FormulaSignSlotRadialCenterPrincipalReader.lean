/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalFamily
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficientSource
public import LeanCanny.Algebra.BivariateDerivativeSpace
public import LeanCanny.Algebra.PolynomialPrincipalCoefficientSpace
/-! # Closed native readers for the actual same-center principal family -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalReader
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower FixedWidthPolynomial Polynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

local instance centerPrincipalReaderArityNeZero (c : List Bool) :
    NeZero (FormulaSignSlotRadialCenterPrincipalFamily.arity c) :=
  ⟨by unfold FormulaSignSlotRadialCenterPrincipalFamily.arity; omega⟩

def origin (z : List Bool) := pairFst (pairFst z)
def target (z : List Bool) := pairFst (pairSnd z)
def outer (z : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd z))
noncomputable def centers (z : List Bool) := d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original (origin z)))
noncomputable def oldWidth (z : List Bool) := (FormulaSignSlotRadialCenterPrincipalFamily.inputBound (origin z)).size
noncomputable def width (z : List Bool) := FormulaSignSlotRadialCenterPrincipalFamily.width (origin z)
noncomputable def radius (z : List Bool) := IntegerParameterCoefficientBits.parameter width target z
noncomputable def centerWord (z : List Bool) := IntegerParameterCoefficientBits.spatial width target z
noncomputable def source (z : List Bool) := pair (FormulaSignSlotRadialCenterPrincipalFamily.original (origin z))
  (WordList.encode [BinaryNatCode.encode (FormulaSignSlotRadialCenterPrincipalFamily.tau (origin z)), BinaryNatCode.encode (outer z), radius z])

theorem origin_FP : origin ∈ FP := by polytime [origin]
theorem target_FP : target ∈ FP := by polytime [target]
theorem outer_binary : BinaryFn outer := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
theorem centers_unary : UnaryFn centers := FormulaSignSlotSource.dimension_unary.comp
  (mem_FP_comp (mem_FP_comp origin_FP FormulaSignSlotRadialCenterPrincipalFamily.original_FP) pairFst_mem_FP)
theorem oldWidth_unary : UnaryFn oldWidth := by
  have H : BinaryFn (fun z => FormulaSignSlotRadialCenterPrincipalFamily.inputBound (origin z)) :=
    FormulaSignSlotRadialCenterPrincipalFamily.inputBound_binary.comp origin_FP
  exact (UnaryFn.length H.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
theorem width_unary : UnaryFn width := FormulaSignSlotRadialCenterPrincipalFamily.width_unary.comp origin_FP
theorem radius_FP : radius ∈ FP := IntegerParameterCoefficientBits.parameter_mem_FP width target width_unary target_FP
theorem centerWord_FP : centerWord ∈ FP := IntegerParameterCoefficientBits.spatial_mem_FP width target width_unary target_FP
theorem source_FP : source ∈ FP := by
  have H : BinaryFn (fun z => FormulaSignSlotRadialCenterPrincipalFamily.tau (origin z)) :=
    FormulaSignSlotRadialCenterPrincipalFamily.tau_binary.comp origin_FP
  unfold source WordList.encode
  exact mem_FP_pair (mem_FP_comp origin_FP FormulaSignSlotRadialCenterPrincipalFamily.original_FP)
    (mem_FP_pair H.bits_mem_FP
      (mem_FP_pair outer_binary.bits_mem_FP (mem_FP_pair radius_FP (constFn_mem_FP []))))

noncomputable def query (z : List Bool) := pair (pair (source z)
  (FixedWidthQuery.repack centers width centers oldWidth centerWord z)) (pairSnd (pairFst z))
theorem query_FP : query ∈ FP := mem_FP_pair (mem_FP_pair source_FP
  (FixedWidthQuery.repack_mem_FP centers_unary width_unary centers_unary oldWidth_unary centerWord_FP))
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def centerPolynomial (z : List Bool) : MvPolynomial (Fin (centers z)) ℤ :=
  FormulaSignSlotRadialCenterCoefficient.polynomial (FormulaSignSlotRadialCenterPrincipalFamily.original (origin z)) (FormulaSignSlotRadialCenterPrincipalFamily.tau (origin z))
    (outer z) (Nat.fromBitsLE (radius z))

private noncomputable def entry (c : List Bool) (s t r W : ℕ) (bits modulus : List Bool) :=
  residueBits (((FormulaSignSlotRadialCenterCoefficient.polynomial c s t r).coeff
    (nativeExponent (Equiv.refl (Fin (d (pairFst c)))) W
      (Nat.fromBitsLE bits)) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1))
private noncomputable def sourceOutput (z bits modulus : List Bool) :=
  residueBits (((FormulaSignSlotRadialCenterCoefficientSource.polynomial z).coeff
    (nativeExponent (Equiv.refl (Fin (FormulaSignSlotRadialCenterCoefficientSource.arity z)))
      (FormulaSignSlotRadialCenterCoefficientSource.degree z).size (Nat.fromBitsLE bits)) : ℤ) :
        ZMod (Nat.fromBitsLE modulus + 1))
private theorem source_output (z bits modulus : List Bool) : sourceOutput z bits modulus =
    entry (pairFst z) (FormulaSignSlotRadialCenterCoefficientSource.selected 0 z)
      (FormulaSignSlotRadialCenterCoefficientSource.selected 1 z)
      (FormulaSignSlotRadialCenterCoefficientSource.selected 2 z)
      (FormulaSignSlotRadialEliminantPacked.resultDegree (pairFst z)).size bits modulus := rfl
attribute [local irreducible] entry
private theorem source_entry (c indices bits modulus : List Bool) :
    FormulaSignSlotRadialCenterCoefficientSource.coefficient (pair (pair (pair c indices) bits) modulus) =
      entry c (Nat.fromBitsLE (WordList.get indices 0)) (Nat.fromBitsLE (WordList.get indices 1))
        (Nat.fromBitsLE (WordList.get indices 2))
        (FormulaSignSlotRadialEliminantPacked.resultDegree c).size bits modulus := by
  have H := FormulaSignSlotRadialCenterCoefficientSource.packet (pair c indices) bits modulus
  change _ = sourceOutput (pair c indices) bits modulus at H
  rw [source_output] at H
  simpa only [FormulaSignSlotRadialCenterCoefficientSource.selected, pairFst_pair, pairSnd_pair] using H
attribute [local irreducible] FormulaSignSlotRadialCenterCoefficient.polynomial
  FormulaSignSlotRadialCenterPrincipalFamily.polynomial FormulaSignSlotRadialCenterPrincipalFamily.width

private theorem read_query (z : List Bool) : FormulaSignSlotRadialCenterCoefficientSource.coefficient (query z) =
    FixedWidthRowBits.value centers oldWidth centerPolynomial
      (FixedWidthQuery.repack centers width centers oldWidth centerWord) (pairSnd ∘ pairFst) z := by
  rw [query, source, source_entry]
  simp only [WordList.get_encode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold entry FixedWidthRowBits.value centerPolynomial oldWidth centers
  rfl

noncomputable def coefficient (z : List Bool) :=
  FixedWidthRowBits.value centers width centerPolynomial centerWord (pairSnd ∘ pairFst) z

private theorem coefficient_entry (z : List Bool) : coefficient z =
    entry (FormulaSignSlotRadialCenterPrincipalFamily.original (origin z))
      (FormulaSignSlotRadialCenterPrincipalFamily.tau (origin z)) (outer z) (Nat.fromBitsLE (radius z))
      (width z) (centerWord z) (pairSnd (pairFst z)) := by
  unfold entry coefficient FixedWidthRowBits.value centerPolynomial centers
  rfl

theorem coefficient_evaluator : SpaceFunction coefficient := by
  have E := FormulaSignSlotRadialCenterCoefficientSource.evaluator.precompose query query_FP
  have EO : SpaceFunction (FixedWidthRowBits.value centers oldWidth centerPolynomial
      (FixedWidthQuery.repack centers width centers oldWidth centerWord) (pairSnd ∘ pairFst)) :=
    E.congr (funext read_query)
  exact FixedWidthRowReboxBits.evaluator centers oldWidth width centerWord centerPolynomial
    (pairSnd ∘ pairFst) centers_unary oldWidth_unary width_unary centerWord_FP
    (fun z => (FormulaSignSlotRadialCenterCoefficient.degree _ _ _ _).trans_lt (Nat.lt_size_self _)) EO

noncomputable def value (z : List Bool) := if outer z ≤ FormulaSignSlotRadialCenterPrincipalFamily.degree (origin z) then coefficient z else []
theorem evaluator : SpaceFunction value := by
  have E := SpaceFunction.branch (fun z => decide (outer z ≤ FormulaSignSlotRadialCenterPrincipalFamily.degree (origin z)))
    (outer_binary.le (FormulaSignSlotRadialCenterPrincipalFamily.degree_binary.comp origin_FP)).flag_mem_FP coefficient_evaluator
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun z => by simp only [value, decide_eq_true_eq])

theorem native_coefficient (c bits : List Bool) (v : ℕ) :
    ((FormulaSignSlotRadialCenterPrincipalFamily.polynomial c).coeff v).coeff
        (nativeExponent (Equiv.refl (Fin (FormulaSignSlotRadialCenterPrincipalFamily.arity c))) (FormulaSignSlotRadialCenterPrincipalFamily.width c) (Nat.fromBitsLE bits)) =
      if v ≤ FormulaSignSlotRadialCenterPrincipalFamily.degree c then
        (FormulaSignSlotRadialCenterCoefficient.polynomial (FormulaSignSlotRadialCenterPrincipalFamily.original c) (FormulaSignSlotRadialCenterPrincipalFamily.tau c) v
          (Nat.fromBitsLE (IntegerParameterCoefficientBits.parameter (fun _ => FormulaSignSlotRadialCenterPrincipalFamily.width c) (fun _ => bits) []))).coeff
            (nativeExponent (Equiv.refl (Fin (d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original c))))) (FormulaSignSlotRadialCenterPrincipalFamily.width c)
              (Nat.fromBitsLE (IntegerParameterCoefficientBits.spatial (fun _ => FormulaSignSlotRadialCenterPrincipalFamily.width c) (fun _ => bits) []))) else 0 := by
  have HP := IntegerParameterCoefficientBits.parameter_nativeExponent (fun _ => FormulaSignSlotRadialCenterPrincipalFamily.width c) (fun _ => bits)
    (d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original c))) []
  have HT := IntegerParameterCoefficientBits.tail_nativeExponent (fun _ => FormulaSignSlotRadialCenterPrincipalFamily.width c) (fun _ => bits)
    (d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original c))) []
  have HC := FormulaSignSlotRadialCenterPrincipalFamily.coefficient c v
    (nativeExponent (Equiv.refl (Fin (FormulaSignSlotRadialCenterPrincipalFamily.arity c))) (FormulaSignSlotRadialCenterPrincipalFamily.width c) (Nat.fromBitsLE bits) 0)
    (nativeExponent (Equiv.refl (Fin (FormulaSignSlotRadialCenterPrincipalFamily.arity c))) (FormulaSignSlotRadialCenterPrincipalFamily.width c) (Nat.fromBitsLE bits)).tail
  dsimp only [FormulaSignSlotRadialCenterPrincipalFamily.arity] at HC ⊢
  rw [Finsupp.cons_tail] at HC
  change (nativeExponent (Equiv.refl (Fin (d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original c)) + 1)))
    (FormulaSignSlotRadialCenterPrincipalFamily.width c) (Nat.fromBitsLE bits)).tail = _ at HT
  rw [HP, HT] at HC
  exact HC

theorem packet (q : List Bool) (u v : ℕ) :
    value (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) =
      residueBits (((((FormulaSignSlotRadialCenterPrincipalFamily.polynomial (pairFst q)).coeff v).coeff
        (nativeExponent (Equiv.refl _) (FormulaSignSlotRadialCenterPrincipalFamily.width (pairFst q)) u)) : ℤ) :
          ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have HC := native_coefficient (pairFst q) (BinaryNatCode.encode u) v
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits] at HC
  rw [HC]
  unfold value
  rw [coefficient_entry]
  simp only [origin, outer, width, radius, centerWord,
    IntegerParameterCoefficientBits.parameter, IntegerParameterCoefficientBits.spatial, target,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs
  · unfold entry
    rfl
  · rfl

noncomputable def reader : CertifiedPolynomial.BivariateReader
    (FixedWidthBivariateReader.polynomial FormulaSignSlotRadialCenterPrincipalFamily.arity FormulaSignSlotRadialCenterPrincipalFamily.width FormulaSignSlotRadialCenterPrincipalFamily.polynomial) :=
  FixedWidthBivariateReader.reader FormulaSignSlotRadialCenterPrincipalFamily.arity FormulaSignSlotRadialCenterPrincipalFamily.width FormulaSignSlotRadialCenterPrincipalFamily.polynomial value evaluator
    FormulaSignSlotRadialCenterPrincipalFamily.arity_unary FormulaSignSlotRadialCenterPrincipalFamily.width_unary FormulaSignSlotRadialCenterPrincipalFamily.inputBound FormulaSignSlotRadialCenterPrincipalFamily.polynomial_degree FormulaSignSlotRadialCenterPrincipalFamily.input_fit packet

noncomputable def family : PolynomialPrincipalCoefficientBits.Family where
  left := FixedWidthBivariateReader.polynomial FormulaSignSlotRadialCenterPrincipalFamily.arity FormulaSignSlotRadialCenterPrincipalFamily.width FormulaSignSlotRadialCenterPrincipalFamily.polynomial
  right c := (FixedWidthBivariateReader.polynomial FormulaSignSlotRadialCenterPrincipalFamily.arity FormulaSignSlotRadialCenterPrincipalFamily.width FormulaSignSlotRadialCenterPrincipalFamily.polynomial c).derivative
  leftDegree := FormulaSignSlotRadialCenterPrincipalFamily.degree
  rightDegree c := FormulaSignSlotRadialCenterPrincipalFamily.degree c - 1

noncomputable def access : PolynomialPrincipalCoefficientBits.Access family where
  left := reader
  right := CertifiedPolynomial.BivariateDerivative.reader reader
  leftDegree := FormulaSignSlotRadialCenterPrincipalFamily.degree_binary
  rightDegree := FormulaSignSlotRadialCenterPrincipalFamily.degree_binary.sub (BinaryFn.const 1)

theorem principal_evaluator : SpaceFunction (PolynomialPrincipalCoefficientBits.residueValue access) :=
  PolynomialPrincipalCoefficientBits.evaluator access

theorem principal_polynomial (c : List Bool) (j : ℕ) :
    PolynomialPrincipalCoefficientBits.polynomial family (pair c (BinaryNatCode.encode j)) =
      FixedWidthKronecker.encode (FormulaSignSlotRadialCenterPrincipalFamily.arity c)
        (FormulaSignSlotRadialCenterPrincipalFamily.width c) (FormulaSignSlotRadialCenterPrincipalFamily.principal c j) := by
  unfold PolynomialPrincipalCoefficientBits.polynomial
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  change PrincipalSubresultant.signedPsc
    ((FormulaSignSlotRadialCenterPrincipalFamily.polynomial c).map _)
    ((FormulaSignSlotRadialCenterPrincipalFamily.polynomial c).map _).derivative _ _ _ = _
  rw [Polynomial.derivative_map, PrincipalSubresultant.signedPsc_map_map]
  rfl

theorem principal_word_packet (c modulus target : List Bool) (j : ℕ) :
    PolynomialPrincipalCoefficientBits.residueValue access
      (pair (pair (pair c (BinaryNatCode.encode j)) target) modulus) =
        residueBits (((FixedWidthKronecker.encode (FormulaSignSlotRadialCenterPrincipalFamily.arity c)
          (FormulaSignSlotRadialCenterPrincipalFamily.width c)
          (FormulaSignSlotRadialCenterPrincipalFamily.principal c j)).coeff (Nat.fromBitsLE target) : ℤ) :
            ZMod (Nat.fromBitsLE modulus + 1)) := by
  let z := pair (pair (pair c (BinaryNatCode.encode j)) target) modulus
  have HI : (PolynomialPrincipalCoefficientBits.polynomial family (PolynomialPrincipalMinorBits.origin z)).coeff
      (PolynomialPrincipalCoefficientBits.parameter z) =
        (FixedWidthKronecker.encode (FormulaSignSlotRadialCenterPrincipalFamily.arity c)
          (FormulaSignSlotRadialCenterPrincipalFamily.width c)
          (FormulaSignSlotRadialCenterPrincipalFamily.principal c j)).coeff (Nat.fromBitsLE target) := by
    simp only [z, PolynomialPrincipalMinorBits.origin, PolynomialPrincipalCoefficientBits.parameter,
      pairFst_pair, pairSnd_pair]
    rw [principal_polynomial]
  have HM : PolynomialPrincipalMinorBits.modulus z = Nat.fromBitsLE modulus + 1 := by
    simp only [z, PolynomialPrincipalMinorBits.modulus, pairSnd_pair]
  exact (PolynomialPrincipalCoefficientBits.residueValue_eq access z).trans
    (congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m)) HI HM)

theorem principal_packet (c modulus : List Bool) (j k : ℕ) :
    PolynomialPrincipalCoefficientBits.residueValue access
      (pair (pair (pair c (BinaryNatCode.encode j)) (BinaryNatCode.encode k)) modulus) =
        residueBits (((FixedWidthKronecker.encode (FormulaSignSlotRadialCenterPrincipalFamily.arity c)
          (FormulaSignSlotRadialCenterPrincipalFamily.width c)
          (FormulaSignSlotRadialCenterPrincipalFamily.principal c j)).coeff k : ℤ) :
            ZMod (Nat.fromBitsLE modulus + 1)) := by
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using principal_word_packet c modulus (BinaryNatCode.encode k) j

theorem principal_box_packet (c modulus : List Bool) (j k : ℕ)
    (hk : k < count (FormulaSignSlotRadialCenterPrincipalFamily.arity c) (FormulaSignSlotRadialCenterPrincipalFamily.width c)) :
    PolynomialPrincipalCoefficientBits.residueValue access
      (pair (pair (pair c (BinaryNatCode.encode j)) (BinaryNatCode.encode k)) modulus) =
        residueBits ((((FormulaSignSlotRadialCenterPrincipalFamily.principal c j).coeff
          (nativeExponent (Equiv.refl _) (FormulaSignSlotRadialCenterPrincipalFamily.width c) k)) : ℤ) :
            ZMod (Nat.fromBitsLE modulus + 1)) := by
  rw [principal_packet]
  have H := FixedWidthKronecker.native_coefficient (Equiv.refl _)
    (FormulaSignSlotRadialCenterPrincipalFamily.width c)
    (FormulaSignSlotRadialCenterPrincipalFamily.principal c j).totalDegree
    (FormulaSignSlotRadialCenterPrincipalFamily.principal c j) le_rfl
    (FormulaSignSlotRadialCenterPrincipalFamily.principal_fit c j) k hk
  have HE : (FixedWidthKronecker.encode (FormulaSignSlotRadialCenterPrincipalFamily.arity c)
      (FormulaSignSlotRadialCenterPrincipalFamily.width c) (FormulaSignSlotRadialCenterPrincipalFamily.principal c j)).coeff k =
      (FormulaSignSlotRadialCenterPrincipalFamily.principal c j).coeff
        (nativeExponent (Equiv.refl _) (FormulaSignSlotRadialCenterPrincipalFamily.width c) k) := by
    simpa [FixedWidthKronecker.native] using H
  rw [HE]

end LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalReader
