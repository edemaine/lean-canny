/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MvTwoParameterCoefficient
public import LeanCanny.Algebra.FixedWidthParameterCons
public import LeanCanny.Algebra.FixedWidthKronecker
/-! # Exact two-parameter coefficient queries to a streamed Kronecker polynomial -/
@[expose] public section
namespace LeanCanny.Algebra.MvTwoParameterEncodedCoefficient
open LeanCanny.Encoding FixedWidthPolynomial
open scoped Classical

def word (A V W δ ε : List Bool→ℕ) (target : List Bool→List Bool) :=
  FixedWidthParameterConsBits.two W δ ε (FixedWidthQuery.repack A V A W target)

theorem word_FP (A V W δ ε : List Bool→ℕ) (target : List Bool→List Bool)
    (hA : UnaryFn A) (hV : UnaryFn V) (hW : UnaryFn W) (hδ : BinaryFn δ) (hε : BinaryFn ε) (ht : target∈FP) :
    word A V W δ ε target∈FP :=
  FixedWidthParameterConsBits.two_FP W δ ε _ hW hδ hε (FixedWidthQuery.repack_mem_FP hA hV hA hW ht)

theorem word_length (A V W δ ε : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool) :
    (word A V W δ ε target c).length=(A c+2)*W c :=by
  simp only [word,FixedWidthParameterConsBits.two,FixedWidthParameterConsBits.prepend,List.length_append,
    FixedWidthNatVector.length_encode,Nat.one_mul,FixedWidthQuery.repack_length]
  ring

theorem nativeExponent_word (A V W δ ε : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool)
    (hV : V c≤W c) (hδ : δ c<2^W c) (hε : ε c<2^W c) :
    nativeExponent (Equiv.refl (Fin (A c+2))) (W c) (Nat.fromBitsLE (word A V W δ ε target c))=
      ((nativeExponent (Equiv.refl (Fin (A c))) (V c) (Nat.fromBitsLE (target c))).cons (ε c)).cons (δ c) :=by
  unfold word FixedWidthParameterConsBits.two FixedWidthParameterConsBits.prepend
  rw [FixedWidthParameterConsBits.nativeExponent_two _ _ _ _ _ hδ hε]
  exact congrArg (fun t : Fin (A c)→₀ℕ=>(t.cons (ε c)).cons (δ c))
    (nativeExponent_repack (Equiv.refl (Fin (A c))) V W target c hV)

theorem coefficient (A V W δ ε : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool)
    (p : MvPolynomial (Fin (A c+2)) ℤ) (hp : p.totalDegree<2^W c)
    (hV : V c≤W c) (hδ : δ c<2^W c) (hε : ε c<2^W c) :
    (FixedWidthKronecker.encode (A c+2) (W c) p).coeff (Nat.fromBitsLE (word A V W δ ε target c))=
      (MvTwoParameterCoefficient.slice p (δ c) (ε c)).coeff
        (nativeExponent (Equiv.refl _) (V c) (Nat.fromBitsLE (target c))) :=by
  have HR : Nat.fromBitsLE (word A V W δ ε target c)<count (A c+2) (W c) :=by
    have H:=Nat.fromBitsLE_lt_pow_length (word A V W δ ε target c)
    rw [word_length] at H
    simpa only [count,←pow_mul,Nat.mul_comm (W c)] using H
  have HC:=FixedWidthKronecker.native_coefficient (Equiv.refl _) (W c) p.totalDegree p le_rfl hp _ HR
  have HE : (FixedWidthKronecker.encode (A c+2) (W c) p).coeff (Nat.fromBitsLE (word A V W δ ε target c))=
      p.coeff (nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE (word A V W δ ε target c))) :=by
    simpa [FixedWidthKronecker.native] using HC
  rw [HE,nativeExponent_word A V W δ ε target c hV hδ hε,MvTwoParameterCoefficient.coefficient]

noncomputable def castPolynomial {m n : ℕ} (h : m=n) (p : MvPolynomial (Fin m) ℤ) : MvPolynomial (Fin n) ℤ :=
  MvPolynomial.rename (Fin.cast h) p

theorem cast_encoded {m n : ℕ} (h : m=n) (p : MvPolynomial (Fin m) ℤ) (W : ℕ) :
    FixedWidthKronecker.encode n W (castPolynomial h p)=FixedWidthKronecker.encode m W p :=by
  cases h
  simp [castPolynomial]

theorem cast_degree {m n : ℕ} (h : m=n) (p : MvPolynomial (Fin m) ℤ) :
    (castPolynomial h p).totalDegree≤p.totalDegree :=MvPolynomial.totalDegree_rename_le _ _
theorem cast_mass {m n : ℕ} (h : m=n) (p : MvPolynomial (Fin m) ℤ) :
    MvMass.mass (castPolynomial h p)≤MvMass.mass p :=MvMass.rename_le _ _

end LeanCanny.Algebra.MvTwoParameterEncodedCoefficient
