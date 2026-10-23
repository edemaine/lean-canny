/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomialLayout
public import LeanCanny.Algebra.PartialDerivativeDegree
public import LeanCanny.Algebra.ModularNatMulFP
public import LeanCanny.Computation.SpaceFunctionBranch

/-! # Native partial-derivative coefficients from one source coefficient

A bounded exponent guard permits changing the query block width before one
selected coordinate is incremented. One original coefficient call and modular
multiplication by the incremented exponent evaluate the actual derivative.
-/

@[expose] public section

namespace LeanCanny.Algebra.FixedWidthDerivativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical

variable (A W V D selected : List Bool → ℕ) (target modulus : List Bool → List Bool)

noncomputable def exponent {σ : Type*} [Fintype σ] {N : ℕ} (f : σ ≃ Fin N) (c : List Bool) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => FixedWidthQuery.coordinate V target c (f i).val)

def bumped (c : List Bool) (i : ℕ) : ℕ :=
  FixedWidthQuery.entry A V target c i + if i = selected c then 1 else 0

def read (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd q) = selected (pairFst q) then
    BinaryNat.succ (FixedWidthQuery.read A V target q)
  else FixedWidthQuery.read A V target q

theorem read_mem_FP (hA : UnaryFn A) (hV : UnaryFn V) (hs : UnaryFn selected) (ht : target ∈ FP) :
    read A V selected target ∈ FP := by
  have hr := FixedWidthQuery.read_mem_FP hA hV ht
  have he : FPPred (fun q => Nat.fromBitsLE (pairSnd q) = selected (pairFst q)) :=
    by simpa only [Nat.fromBitsLE_bits] using BinaryNat.eq_fppred pairSnd_mem_FP (bits_mem_FP hs.lift)
  have hinc : (BinaryNat.succ ∘ FixedWidthQuery.read A V target) ∈ FP := mem_FP_comp hr BinaryNat.succ_mem_FP
  have h := he.ite_mem_FP hinc hr
  exact mem_FP_of_eq h (fun _ => rfl)

theorem read_packet (c : List Bool) (i : ℕ) :
    read A V selected target (pair c (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (bumped A V selected target c i) := by
  simp only [read, pairFst_pair, pairSnd_pair, show Nat.fromBitsLE (BinaryNatCode.encode i) = i from Nat.fromBitsLE_bits i,
    FixedWidthQuery.read_packet, bumped]
  split_ifs <;> simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.add_zero]

def packed (c : List Bool) : List Bool := FixedWidthNatVector.encode (A c) (W c) (bumped A V selected target c)

theorem packed_mem_FP (hA : UnaryFn A) (hW : UnaryFn W) (hV : UnaryFn V)
    (hs : UnaryFn selected) (ht : target ∈ FP) : packed A W V selected target ∈ FP :=
  FixedWidthNatVector.encode_of_coordinate hA hW
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary
    (FixedWidthNatVector.coordinate_of_reader (read_mem_FP A V selected target hA hV hs ht)
      (read_packet A V selected target))

def query (c : List Bool) : List Bool := pair c (BinaryNat.normalize (packed A W V selected target c))

theorem query_mem_FP (hA : UnaryFn A) (hW : UnaryFn W) (hV : UnaryFn V)
    (hs : UnaryFn selected) (ht : target ∈ FP) : query A W V selected target ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_comp (packed_mem_FP A W V selected target hA hW hV hs ht) BinaryNat.normalize_mem_FP)

def factor (c : List Bool) : List Bool :=
  BinaryNat.succ (FixedWidthQuery.read A V target (pair c (BinaryNatCode.encode (selected c))))

theorem factor_mem_FP (hA : UnaryFn A) (hV : UnaryFn V) (hs : UnaryFn selected) (ht : target ∈ FP) :
    factor A V selected target ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_pair id_mem_FP (bits_mem_FP hs))
    (FixedWidthQuery.read_mem_FP hA hV ht)) BinaryNat.succ_mem_FP

def finish (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (modulus (pairFst z)) (pair (pairSnd z) (factor A V selected target (pairFst z))))

theorem finish_mem_FP (hA : UnaryFn A) (hV : UnaryFn V) (hs : UnaryFn selected)
    (ht : target ∈ FP) (hm : modulus ∈ FP) : finish A V selected target modulus ∈ FP := by
  have hf : factor A V selected target ∈ FP := factor_mem_FP A V selected target hA hV hs ht
  have hq := mem_FP_pair (mem_FP_comp pairFst_mem_FP hm)
    (mem_FP_pair pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hf))
  have h := mem_FP_comp hq BinaryNat.mulMod_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

noncomputable def value (coefficient : List Bool → List Bool) (c : List Bool) : List Bool :=
  if FixedWidthQuery.Bounded A V target (fun c => D c - 1) c then
    finish A V selected target modulus (pair c (coefficient (query A W V selected target c))) else []

theorem evaluator {coefficient : List Bool → List Bool} (E : SpaceFunction coefficient)
    (hA : UnaryFn A) (hW : UnaryFn W) (hV : UnaryFn V) (hD : UnaryFn D)
    (hs : UnaryFn selected) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value A W V D selected target modulus coefficient) := by
  have EQ := ((E.precompose (query A W V selected target) (query_mem_FP A W V selected target hA hW hV hs ht)).withInput).postcompose
    (finish A V selected target modulus) (finish_mem_FP A V selected target modulus hA hV hs ht hm)
  have hb := FixedWidthQuery.bounded_fppred hA hV (hD.sub (UnaryFn.const 1)) ht
  have EB := SpaceFunction.branch (fun c => decide (FixedWidthQuery.Bounded A V target (fun c => D c - 1) c))
    hb.flag_mem_FP EQ (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  exact EB.congr (funext fun c => by simp only [value, Function.comp_apply, decide_eq_true_eq])

private theorem entry_fromBits (w : ℕ) (bits : List Bool) (i : ℕ) :
    entry w (Nat.fromBitsLE bits) i = Nat.fromBitsLE ((bits.drop (i * w)).take w) := by
  rw [entry_eq_digit, BinaryNat.value_take, drop_value]

theorem packet {σ : Type*} [Fintype σ] {N : ℕ} (f : σ ≃ Fin N)
    (coefficient : List Bool → List Bool) (c : List Bool) (p : MvPolynomial σ ℤ) (base : σ) (m : ℕ)
    (hA : A c = N) (hs : selected c = (f base).val) (hpos : 0 < D c)
    (hD : p.totalDegree ≤ D c) (hW : D c < 2 ^ W c) (hm : modulus c = BinaryNatCode.encode m)
    (hp : ∀ r, coefficient (pair c (BinaryNatCode.encode r)) =
      residueBits ((p.coeff (nativeExponent f (W c) r) : ℤ) : ZMod m)) :
    value A W V D selected target modulus coefficient c =
      residueBits ((((MvPolynomial.pderiv base p).coeff (exponent V target f c)) : ℤ) : ZMod m) := by
  let e := exponent V target f c
  by_cases hb : FixedWidthQuery.Bounded A V target (fun c => D c - 1) c
  · have hfit (i : Fin N) : bumped A V selected target c i.val < 2 ^ W c := by
      have h := hb i.val (by rw [hA]; exact i.isLt)
      change FixedWidthQuery.coordinate V target c i.val ≤ D c - 1 at h
      have he : FixedWidthQuery.entry A V target c i.val = FixedWidthQuery.coordinate V target c i.val :=
        ite_eq_left (by rw [hA]; exact i.isLt)
      rw [bumped, he]
      split_ifs <;> omega
    have heq : nativeExponent f (W c) (Nat.fromBitsLE (packed A W V selected target c)) =
        e + Finsupp.single base 1 := by
      ext z
      simp only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm, entry_fromBits, packed]
      rw [FixedWidthNatVector.decode_block _ _ _ _ (by rw [hA]; exact (f z).isLt) (hfit (f z))]
      have hz : ((f z).val = selected c) ↔ z = base := by
        rw [hs, Fin.val_inj]
        exact f.injective.eq_iff
      simp only [bumped, FixedWidthQuery.entry, show (f z).val < A c by rw [hA]; exact (f z).isLt,
        ite_true, hz, e, exponent, Finsupp.coe_equivFunOnFinite_symm, Finsupp.add_apply,
        Finsupp.single_apply, eq_comm]
    have hf : factor A V selected target c = BinaryNatCode.encode (e base + 1) := by
      rw [factor, FixedWidthQuery.read_packet]
      simp only [FixedWidthQuery.entry, hs, show (f base).val < A c by rw [hA]; exact (f base).isLt,
        ite_true, BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      rfl
    rw [value, ite_eq_left hb, finish, pairFst_pair, pairSnd_pair, query,
      BinaryNat.normalize_eq_bits]
    change BinaryNat.mulMod (pair (modulus c) (pair
      (coefficient (pair c (BinaryNatCode.encode (Nat.fromBitsLE (packed A W V selected target c)))))
      (factor A V selected target c))) = _
    rw [hp, heq, hf, hm, ArithmeticBits.mulMod_nat_residueBits, MvPolynomial.coeff_pderiv]
    simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one]
    rfl
  · have hz : (MvPolynomial.pderiv base p).coeff e = 0 := by
      by_contra hn
      obtain ⟨i, hi, he⟩ : ∃ i, i < A c ∧ D c - 1 < FixedWidthQuery.coordinate V target c i := by
        simpa only [FixedWidthQuery.Bounded, not_forall, Classical.not_imp, not_le, exists_prop] using hb
      let z := f.symm ⟨i, by rw [← hA]; exact hi⟩
      have hei : e z = FixedWidthQuery.coordinate V target c i := by
        simp only [e, exponent, Finsupp.coe_equivFunOnFinite_symm, z, Equiv.apply_symm_apply]
      have hmem := MvPolynomial.mem_support_iff.mpr hn
      have hle := (MvPolynomial.monomial_le_degreeOf z hmem).trans
        ((MvPolynomial.degreeOf_le_totalDegree _ z).trans
          ((PartialDerivativeDegree.degree_le p base).trans (Nat.sub_le_sub_right hD 1)))
      rw [hei] at hle
      omega
    rw [value, ite_eq_right hb, show exponent V target f c = e from rfl, hz]
    simp [residueBits, BinaryNatCode.encode]

end LeanCanny.Algebra.FixedWidthDerivativeBits
