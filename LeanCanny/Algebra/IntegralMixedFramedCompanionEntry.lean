/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionQueryReadback
/-! # Actual creating matrix entries under source-key transport

Source packets wrap both natural basis indices modulo the positive padded
rank. This module preserves that convention under the creating-query writer.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength)
open scoped Classical
attribute [local irreducible] PaddedIntegralGeneratorSource.Source.matrix

def cyclicEntry {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) (hN : 0<N) (r c : ℕ) : ℤ :=
  A ⟨r%N,Nat.mod_lt _ hN⟩ ⟨c%N,Nat.mod_lt _ hN⟩

theorem cyclicEntry_congr {N M : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (B : Matrix (Fin M) (Fin M) ℤ) (hN : 0<N) (hM : 0<M)
    (hNM : N=M) (hAB : HEq A B) (r c : ℕ) : cyclicEntry A hN r c=cyclicEntry B hM r c := by
  cases hNM
  cases hAB
  rfl

theorem cyclicEntry_mod {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) (hN : 0<N) (r c : ℕ) :
    cyclicEntry A hN (r%N) (c%N)=cyclicEntry A hN r c := by
  unfold cyclicEntry
  simp only [Nat.mod_mod]

noncomputable def entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (r c : ℕ) : ℤ :=
  cyclicEntry ((source P D H).matrix key) (pow_pos (Nat.two_pow_pos _) _) r c

theorem source_arity (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (source P D H).arity key=prefixLength P key :=
  IntegralMixedFramedHistoryFamilyBits.family_birth P D H key

theorem source_width (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (source P D H).width key=P.width (pairFst key) := rfl

theorem entry_congr (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (x y : List Bool) (hr : pairFst x=pairFst y) (hb : prefixLength P x=prefixLength P y) (r c : ℕ) :
    entry P D H x r c=entry P D H y r c := by
  apply cyclicEntry_congr _ _ _ _ _ (source_matrix_congr P D H x y hr hb)
  rw [source_arity,source_arity,source_width,source_width,hr,hb]

theorem entry_mod (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (r c : ℕ) :
    entry P D H key (r%count (prefixLength P key+1) (P.width (pairFst key)))
      (c%count (prefixLength P key+1) (P.width (pairFst key)))=entry P D H key r c := by
  have HE := cyclicEntry_mod ((source P D H).matrix key) (pow_pos (Nat.two_pow_pos _) _) r c
  simpa only [entry,source_arity,source_width] using HE

theorem source_value_entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    PaddedIntegralGeneratorSource.value (source P D H) q=
      residueBits (entry P D H (PaddedIntegralGeneratorSource.base q)
        (Nat.fromBitsLE (PaddedIntegralGeneratorSource.row q)) (Nat.fromBitsLE (PaddedIntegralGeneratorSource.col q)) :
        ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)) := rfl

theorem value_entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    value P D H q=residueBits (entry P D H (IntegralMixedVirtualTaskBits.saved P q)
      (get P .row q) (get P .col q) : ZMod (modulus P q)) := rfl

end LeanCanny.Algebra.IntegralMixedFramedCompanionBits
