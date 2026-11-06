/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiInterval
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiOrdinal
/-! # Exact interval truth from the finite actual-source feature signs -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralPolynomialWindowTarski
open LeanCanny.Algebra LeanCanny.Computation Polynomial MvPolynomial PrincipalSubresultant Set
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem zero_iff_of_sign {x y : ℝ} (H : SignType.sign x = SignType.sign y) : x = 0 ↔ y = 0 := by
  simpa only [sign_eq_zero_iff] using Iff.of_eq (congrArg (fun a : SignType => a = 0) H)
private theorem feature_eval (C : ChargedPolynomialCatalogue.Input) (c : List Bool) (i : ℕ)
    (z : List Bool) (hz : C.row (pair c (BinaryNatCode.encode i)) = z)
    (v : Fin (C.arity c) → ℝ) (w : Fin (C.source.arity z) → ℝ)
    (hw : HEq w (fun j => v (Fin.cast (C.dimension c i) j))) :
    (ChargedPolynomialCatalogue.feature C c i).eval₂ (Int.castRingHom ℝ) v =
      (C.source.polynomial z).eval₂ (Int.castRingHom ℝ) w := by
  cases hz
  have HE : w = (fun j => v (Fin.cast (C.dimension c i) j)) := eq_of_heq hw
  subst w
  exact MvPolynomial.eval₂_rename _ _ _ _

private theorem eval_heq {n m : ℕ} (hn : n = m) (p : MvPolynomial (Fin n) ℤ)
    (q : MvPolynomial (Fin m) ℤ) (hp : HEq p q) (v : Fin n → ℝ) (w : Fin m → ℝ)
    (hv : HEq v w) : p.eval₂ (Int.castRingHom ℝ) v = q.eval₂ (Int.castRingHom ℝ) w := by
  cases hn
  have hp' : p = q := eq_of_heq hp
  have hv' : v = w := eq_of_heq hv
  rw [hp', hv']

private theorem cast_values_heq {n m : ℕ} (h : n = m) (v : Fin m → ℝ) :
    HEq (intervalCastValues h v) v := by cases h; rfl
private theorem cast_vectors_heq {n m k : ℕ} (hn : n = k) (hm : m = k) (v : Fin k → ℝ) :
    HEq (intervalCastValues hn v) (intervalCastValues hm v) := by cases hn; cases hm; rfl

variable (S : Source) (N : List Bool → ℕ) (hd : ∀ c, S.arity c = N c + 1)
noncomputable def sourceTuple (c : List Bool) (b : ℝ) (a : Fin (N c) → ℝ) : Fin (S.arity c) → ℝ :=
  fun i => (Fin.cons b a : Fin (N c + 1) → ℝ) (Fin.cast (hd c) i)

noncomputable def CatalogueSigns (c : List Bool) (b : ℝ) (a : Fin (N c) → ℝ)
    (b' : ℝ) (a' : Fin (N c) → ℝ) : Prop :=
  ∀ i : Fin (IntegralPolynomialWindowTarskiCatalogue.count S c),
    SignType.sign (((IntegralPolynomialWindowTarskiCatalogue.family S N hd).feature c i.val).eval₂
      (Int.castRingHom ℝ) (sourceTuple S N hd c b a)) =
    SignType.sign (((IntegralPolynomialWindowTarskiCatalogue.family S N hd).feature c i.val).eval₂
      (Int.castRingHom ℝ) (sourceTuple S N hd c b' a'))

noncomputable def entryPolynomial (q : List Bool) (r j : ℕ) : MvPolynomial (Fin (arity N q)) ℤ :=
  if r = 0 then FixedWidthTarskiPrincipalBits.polynomial (family S N hd) q j
  else if r = 1 then (head S N hd q).coeff j else (seed S N hd q).coeff j
private theorem packet_arity (q : List Bool) (r j : ℕ) :
    rowArity N (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j))) = arity N q := by
  simp only [rowArity, control, pairFst_pair, pairSnd_pair]
private theorem packet_polynomial (q : List Bool) (r j : ℕ) :
    HEq (polynomial S N hd (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j))))
      (entryPolynomial S N hd q r j) := by
  change HEq (entryPolynomial S N hd
    (control (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j))))
    (role (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j))))
    (index (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j))))) _
  have HC : control (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j))) = q := by
    simp only [control, pairFst_pair, pairSnd_pair]
  have HR : role (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j))) = r := by
    simp only [role, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HJ : index (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j))) = j := by
    simp only [index, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [HC, HR, HJ]

attribute [local irreducible] head seed family FixedWidthTarskiPrincipalBits.polynomial

theorem encoded_feature_eval (c : List Bool) (r m j s d : ℕ) (hr : r < 3) (hm : m < 2)
    (hj : j < IntegralPolynomialWindowTarskiCatalogue.limit S c)
    (hs : s < IntegralPolynomialWindowTarskiCatalogue.limit S c)
    (hD : d < IntegralPolynomialWindowTarskiCatalogue.limit S c)
    (b : ℝ) (a : Fin (N c) → ℝ) :
    ((IntegralPolynomialWindowTarskiCatalogue.family S N hd).feature c
      (IntegralPolynomialWindowTarskiCatalogue.encode S c r m j s d)).eval₂ (Int.castRingHom ℝ)
        (sourceTuple S N hd c b a) =
      (entryPolynomial S N hd (intervalControl c d s (decide (m = 1))) r j).eval₂
          (Int.castRingHom ℝ) (values N c d s (decide (m = 1)) b a) := by
  let q := intervalControl c d s (decide (m = 1))
  let z := pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j))
  let w := intervalCastValues (packet_arity N q r j) (values N c d s (decide (m = 1)) b a)
  calc
    _ = (polynomial S N hd z).eval₂ (Int.castRingHom ℝ) w := by
      apply feature_eval (IntegralPolynomialWindowTarskiCatalogue.input S N hd) c
        (IntegralPolynomialWindowTarskiCatalogue.encode S c r m j s d) z
          (IntegralPolynomialWindowTarskiCatalogue.row_encode S c r m j s d hr hm hj hs hD)
      let hW : rowArity N z = N c + 1 :=
        (packet_arity N q r j).trans (interval_control_dimension N c d s (decide (m = 1)))
      let hV := ((IntegralPolynomialWindowTarskiCatalogue.input S N hd).dimension c
        (IntegralPolynomialWindowTarskiCatalogue.encode S c r m j s d)).trans (hd c)
      change HEq (intervalCastValues hW (Fin.cons b a)) (intervalCastValues hV (Fin.cons b a))
      exact cast_vectors_heq hW hV _
    _ = _ := eval_heq (packet_arity N q r j) _ _ (packet_polynomial S N hd q r j) _ _
      (cast_values_heq _ _)

theorem entry_sign (c : List Bool) (b : ℝ) (a : Fin (N c) → ℝ)
    (b' : ℝ) (a' : Fin (N c) → ℝ) (H : CatalogueSigns S N hd c b a b' a')
    (d s j r : ℕ) (m : Bool) (hd0 : d < IntegralPolynomialWindowTarskiCatalogue.limit S c)
    (hs : s < IntegralPolynomialWindowTarskiCatalogue.limit S c)
    (hj : j < IntegralPolynomialWindowTarskiCatalogue.limit S c) (hr : r < 3) :
    SignType.sign ((entryPolynomial S N hd (intervalControl c d s m) r j).eval₂ (Int.castRingHom ℝ)
      (values N c d s m b a)) =
    SignType.sign ((entryPolynomial S N hd (intervalControl c d s m) r j).eval₂ (Int.castRingHom ℝ)
      (values N c d s m b' a')) := by
  let mn : ℕ := if m then 1 else 0
  have hm : mn < 2 := by cases m <;> decide
  have HH := H ⟨IntegralPolynomialWindowTarskiCatalogue.encode S c r mn j s d,
    IntegralPolynomialWindowTarskiCatalogue.encode_lt S c r mn j s d hr hm hj hs hd0⟩
  change SignType.sign (((IntegralPolynomialWindowTarskiCatalogue.family S N hd).feature c
    (IntegralPolynomialWindowTarskiCatalogue.encode S c r mn j s d)).eval₂ _ _) = _ at HH
  rw [encoded_feature_eval S N hd c r mn j s d hr hm hj hs hd0,
    encoded_feature_eval S N hd c r mn j s d hr hm hj hs hd0] at HH
  cases m <;> exact HH

theorem head_coefficient_sign (c : List Bool) (b : ℝ) (a : Fin (N c) → ℝ)
    (b' : ℝ) (a' : Fin (N c) → ℝ) (H : CatalogueSigns S N hd c b a b' a')
    (d s j : ℕ) (m : Bool) (hd0 : d < IntegralPolynomialWindowTarskiCatalogue.limit S c)
    (hs : s < IntegralPolynomialWindowTarskiCatalogue.limit S c)
    (hj : j < IntegralPolynomialWindowTarskiCatalogue.limit S c) :
    SignType.sign ((realHead S N hd (intervalControl c d s m) (values N c d s m b a)).coeff j) =
    SignType.sign ((realHead S N hd (intervalControl c d s m) (values N c d s m b' a')).coeff j) := by
  rw [head_value, head_value]
  simpa [entryPolynomial] using
    entry_sign S N hd c b a b' a' H d s j 1 m hd0 hs hj (by decide)

theorem seed_coefficient_sign (c : List Bool) (b : ℝ) (a : Fin (N c) → ℝ)
    (b' : ℝ) (a' : Fin (N c) → ℝ) (H : CatalogueSigns S N hd c b a b' a')
    (d s j : ℕ) (m : Bool) (hd0 : d < IntegralPolynomialWindowTarskiCatalogue.limit S c)
    (hs : s < IntegralPolynomialWindowTarskiCatalogue.limit S c)
    (hj : j < IntegralPolynomialWindowTarskiCatalogue.limit S c) :
    SignType.sign ((realSeed S N hd (intervalControl c d s m) (values N c d s m b a)).coeff j) =
    SignType.sign ((realSeed S N hd (intervalControl c d s m) (values N c d s m b' a')).coeff j) := by
  rw [seed_value, seed_value]
  simpa [entryPolynomial] using
    entry_sign S N hd c b a b' a' H d s j 2 m hd0 hs hj (by decide)

theorem base_coefficient_zero_iff (c : List Bool) (b : ℝ) (a : Fin (N c) → ℝ)
    (b' : ℝ) (a' : Fin (N c) → ℝ) (H : CatalogueSigns S N hd c b a b' a')
    (j : ℕ) (hj : j ≤ S.degree c) :
    (baseHead S N hd c a).coeff j = 0 ↔ (baseHead S N hd c a').coeff j = 0 := by
  have HH := head_coefficient_sign S N hd c b a b' a' H 0 0 j false
    (by unfold IntegralPolynomialWindowTarskiCatalogue.limit; omega)
    (by unfold IntegralPolynomialWindowTarskiCatalogue.limit; omega)
    (by unfold IntegralPolynomialWindowTarskiCatalogue.limit; omega)
  rw [canonical_head, canonical_head] at HH
  exact zero_iff_of_sign HH

theorem selected_iff_of_signs (c : List Bool) (b : ℝ) (a : Fin (N c) → ℝ)
    (b' : ℝ) (a' : Fin (N c) → ℝ) (H : CatalogueSigns S N hd c b a b' a')
    (d s : ℕ) (m : Bool) (hd0 : d < IntegralPolynomialWindowTarskiCatalogue.limit S c)
    (hs : s < IntegralPolynomialWindowTarskiCatalogue.limit S c) :
    Selected S N hd (intervalControl c d s m) (values N c d s m b a) ↔
      Selected S N hd (intervalControl c d s m) (values N c d s m b' a') := by
  have HD : degree S (intervalControl c d s m) ≤ S.degree c + 1 := by
    rw [interval_control_degree]; omega
  have HS : seedDegree S (intervalControl c d s m) ≤ S.degree c := by
    rw [interval_control_seed]; omega
  have HI : inputBound S (intervalControl c d s m) = S.degree c := by
    unfold inputBound; rw [interval_control_original]
  have Hhead (j : ℕ) (hj : j < IntegralPolynomialWindowTarskiCatalogue.limit S c) :=
    zero_iff_of_sign (head_coefficient_sign S N hd c b a b' a' H d s j m hd0 hs hj)
  have Hseed (j : ℕ) (hj : j < IntegralPolynomialWindowTarskiCatalogue.limit S c) :=
    zero_iff_of_sign (seed_coefficient_sign S N hd c b a b' a' H d s j m hd0 hs hj)
  unfold Selected HeadSelected SeedSelected
  apply and_congr
  · apply and_congr
    · exact (Hhead _ (by unfold IntegralPolynomialWindowTarskiCatalogue.limit; omega)).not
    · exact forall_congr' fun i => imp_congr_right fun _ => imp_congr_right fun hi =>
        Hhead i (by unfold IntegralPolynomialWindowTarskiCatalogue.limit; omega)
  · apply or_congr
    · exact and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi =>
        Hseed i (by unfold IntegralPolynomialWindowTarskiCatalogue.limit; omega)
    · apply and_congr
      · exact (Hseed _ (by unfold IntegralPolynomialWindowTarskiCatalogue.limit; omega)).not
      · exact forall_congr' fun i => imp_congr_right fun _ => imp_congr_right fun hi =>
          Hseed i (by unfold IntegralPolynomialWindowTarskiCatalogue.limit; omega)

theorem statistic_eq_of_signs (c : List Bool) (b : ℝ) (a : Fin (N c) → ℝ)
    (b' : ℝ) (a' : Fin (N c) → ℝ) (H : CatalogueSigns S N hd c b a b' a')
    (d s : ℕ) (m : Bool) (hd0 : d < IntegralPolynomialWindowTarskiCatalogue.limit S c)
    (hs : s < IntegralPolynomialWindowTarskiCatalogue.limit S c) :
    statistic S N hd (intervalControl c d s m) (values N c d s m b a) =
      statistic S N hd (intervalControl c d s m) (values N c d s m b' a') := by
  unfold statistic
  apply permanencesMinusVariations_congr
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  have HJ : j < IntegralPolynomialWindowTarskiCatalogue.limit S c := by
    have HH := List.mem_range.mp (List.mem_reverse.mp hj)
    rw [interval_control_degree] at HH
    unfold IntegralPolynomialWindowTarskiCatalogue.limit
    omega
  simpa [entryPolynomial] using
    entry_sign S N hd c b a b' a' H d s j 0 m hd0 hs HJ (by decide)

theorem empty_iff_of_signs (c : List Bool) (b : ℝ) (a : Fin (N c) → ℝ)
    (b' : ℝ) (a' : Fin (N c) → ℝ) (H : CatalogueSigns S N hd c b a b' a') :
    Empty S N hd c b a ↔ Empty S N hd c b' a' := by
  have transfer (b b' : ℝ) (a a' : Fin (N c) → ℝ) (H : CatalogueSigns S N hd c b a b' a') :
      Empty S N hd c b a → Empty S N hd c b' a' := by
    rintro (HC | ⟨d1,hd1,s1,hs1,d2,hd2,s2,hs2,H1,H2,HT⟩)
    · left
      constructor
      · exact (base_coefficient_zero_iff S N hd c b a b' a' H 0 (by omega)).not.mp HC.1
      · intro i hi hD
        exact (base_coefficient_zero_iff S N hd c b a b' a' H i hD).mp (HC.2 i hi hD)
    · right
      refine ⟨d1,hd1,s1,hs1,d2,hd2,s2,hs2,
        (selected_iff_of_signs S N hd c b a b' a' H d1 s1 false hd1 hs1).mp H1,
        (selected_iff_of_signs S N hd c b a b' a' H d2 s2 true hd2 hs2).mp H2,?_⟩
      rw [←statistic_eq_of_signs S N hd c b a b' a' H d2 s2 true hd2 hs2,
        ←statistic_eq_of_signs S N hd c b a b' a' H d1 s1 false hd1 hs1]
      exact HT
  exact ⟨transfer b b' a a' H, transfer b' b a' a (fun i => (H i).symm)⟩

theorem zero_iff_of_signs (c : List Bool) (b : ℝ) (a : Fin (N c) → ℝ)
    (b' : ℝ) (a' : Fin (N c) → ℝ) (H : CatalogueSigns S N hd c b a b' a') :
    Zero S N hd c a ↔ Zero S N hd c a' :=
  forall_congr' fun i => imp_congr_right fun hi => base_coefficient_zero_iff S N hd c b a b' a' H i hi

theorem interval_iff_of_signs (c : List Bool) (b : ℝ) (a : Fin (N c) → ℝ)
    (b' : ℝ) (a' : Fin (N c) → ℝ) (H : CatalogueSigns S N hd c b a b' a')
    (hb : 0 < b) (hb' : 0 < b') :
    (∀ r, (baseHead S N hd c a).eval r = 0 → r ∉ Ioo 0 b) ↔
      ∀ r, (baseHead S N hd c a').eval r = 0 → r ∉ Ioo 0 b' :=
  (empty_iff S N hd c b a hb).symm.trans
    ((empty_iff_of_signs S N hd c b a b' a' H).trans (empty_iff S N hd c b' a' hb'))

end LeanCanny.Encoding.IntegralPolynomialWindowTarski
