/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullCutTerminalReader
public import LeanCanny.Algebra.CoefficientCanonicalScalarAppend
/-! # Fixed-degree full relative heads with actual creating scalar powers -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientFullCutHeadQueries
open Polynomial LeanCanny.Encoding LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] {m N : ℕ}

noncomputable def scalarHead (w : Fin m → ℕ) (p : Polynomial (MvPolynomial (Fin m) R)) (d : ℕ) :=
  (IntegralRelativeTruncation.truncate p d).map (CoordinatePowerSubstitution.substitute w).toRingHom

theorem scalarHead_coefficient (w : Fin m → ℕ) (p : Polynomial (MvPolynomial (Fin m) R)) (d k : ℕ) :
    (scalarHead w p d).coeff k = if k ≤ d then CoordinatePowerSubstitution.substitute w (p.coeff k) else 0 := by
  rw [scalarHead, Polynomial.coeff_map, IntegralRelativeTruncation.coefficient]
  split_ifs
  · rfl
  · exact map_zero _

theorem scalarHead_map (φ : R →+* S) (w : Fin m → ℕ) (p : Polynomial (MvPolynomial (Fin m) R)) (d : ℕ) :
    (scalarHead w p d).map (MvPolynomial.map φ) = scalarHead w (p.map (MvPolynomial.map φ)) d := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_map, scalarHead_coefficient, scalarHead_coefficient]
  split_ifs
  · rw [Polynomial.coeff_map, CoordinatePowerSubstitution.map_substitute]
  · exact map_zero _

def tailIndex (h : m ≤ N) (i : Fin m) : Fin (N+1) := ⟨N-m+1+i.val, by omega⟩

noncomputable def terminalHead (h : m ≤ N) (w : Fin m → ℕ)
    (p : Polynomial (MvPolynomial (Fin m) R)) (d : ℕ) : Polynomial (MvPolynomial (Fin (N+1)) R) :=
  (scalarHead w p d).map (MvPolynomial.rename (tailIndex h)).toRingHom

theorem terminalHead_map (φ : R →+* S) (h : m ≤ N) (w : Fin m → ℕ)
    (p : Polynomial (MvPolynomial (Fin m) R)) (d : ℕ) :
    (terminalHead h w p d).map (MvPolynomial.map φ) = terminalHead h w (p.map (MvPolynomial.map φ)) d := by
  apply Polynomial.ext
  intro k
  simp only [terminalHead, Polynomial.coeff_map]
  change MvPolynomial.map φ (MvPolynomial.rename (tailIndex h) ((scalarHead w p d).coeff k)) =
    MvPolynomial.rename (tailIndex h) ((scalarHead w (p.map (MvPolynomial.map φ)) d).coeff k)
  rw [MvPolynomial.map_rename]
  have HE := congrArg (fun p => p.coeff k) (scalarHead_map φ w p d)
  rw [Polynomial.coeff_map] at HE
  exact congrArg (MvPolynomial.rename (tailIndex h)) HE

variable (P : IntegralCriticalHistoryTask.Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
  (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (parent terminal : List Bool → List Bool) (d : List Bool → ℕ)
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family P D H
noncomputable def nativeWeights (q : List Bool) :=
  let key := IntegralMixedVirtualTaskBits.saved P (parent q)
  UniformIntegralPowerSchedule.weights (P.cap (pairFst key)+1) (2^(G).width key) ((G).birth key)
noncomputable def nativePolynomial (q : List Bool) :=
  let key := IntegralMixedVirtualTaskBits.saved P (parent q)
  ((G).state key).sampler.scalarPrefix.basis.polynomial
    (IntegralMixedRelativeCuts.factor ((G).state key) ((G).birth_bound key) ((G).rule key) ((G).kind key))

theorem scalarHead_native (q : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P (parent q)) :
    scalarHead (nativeWeights P D H parent q) (nativePolynomial P D H parent q) (IntegralMixedFramedFullCutHead.degree P parent d q) =
      IntegralMixedFramedFullCutHead.head P D H parent d q := by
  apply Polynomial.ext
  intro k
  have HH := IntegralMixedFramedFullCutHead.head_coefficient P D H parent d q k
  dsimp only [IntegralMixedFramedFullCutHead.arity, IntegralMixedFramedFullCutHead.saved] at HH
  rw [scalarHead_coefficient, HH]
  dsimp only [nativePolynomial, nativeWeights]
  simp only [ha, true_and, IntegralCoordinateBasis.polynomial_coefficient]
  rfl

theorem terminalHead_native (q : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P (parent q))
    (hc : IntegralMixedFramedFullCutTerminalHead.Valid P D H parent terminal q) :
    terminalHead hc (nativeWeights P D H parent q) (nativePolynomial P D H parent q) (IntegralMixedFramedFullCutHead.degree P parent d q) =
      IntegralMixedFramedFullCutTerminalHead.polynomial P D H parent terminal d q := by
  unfold terminalHead
  have HS := scalarHead_native P D H parent d q ha
  rw [HS,
    IntegralMixedFramedFullCutTerminalHead.polynomial, dite_eq_left hc]
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_map, IntegralMixedFramedFullCutTerminalHead.castHead, Polynomial.coeff_map,
    FixedWidthBivariateSuffixBits.coefficient]
  change MvPolynomial.rename (tailIndex hc) ((IntegralMixedFramedFullCutHead.head P D H parent d q).coeff k) =
    MvPolynomial.rename (Fin.cast (IntegralMixedFramedFullCutTerminalHead.arity_eq P D H parent terminal q hc))
      (MvPolynomial.rename (FixedWidthSuffixLiftBits.shift
        (IntegralMixedFramedFullCutTerminalHead.newer P D H parent terminal q))
        ((IntegralMixedFramedFullCutHead.head P D H parent d q).coeff k))
  rw [MvPolynomial.rename_rename]
  apply congrArg (fun f => MvPolynomial.rename f _)
  funext i
  apply Fin.ext
  rfl

end LeanCanny.Algebra.CoefficientFullCutHeadQueries
