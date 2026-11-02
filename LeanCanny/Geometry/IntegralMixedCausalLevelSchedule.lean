/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCausalLevelCapacity
/-! # A binary causal schedule with separate reframe and birth charges

The base and seed can be fixed from the original input. A capacity charge
uses only the preceding bank bound; a subsequent birth charge assumes its
explicit linear bank-growth inequality. This does not supply a sampling
trajectory or silently derive a source-framed height recurrence.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedCausalLevelSchedule
open LeanCanny.Algebra IntegralMixedRetainedRealBound
open IntegralMixedCausalLevelCapacity Filter
open scoped Topology

def capacityFactor (n D R : ℕ) : ℕ := n.size+height R 0*FixedLeadingTiltedSource.degree D+2

theorem height_linear (R G : ℕ) : height R G ≤ height R 0*(G+1) := by
  have HR : R ≤ height R 0 := by unfold height CharacteristicIntegerBounds.budget; omega
  have HE : height R G=R*G+height R 0 := by unfold height CharacteristicIntegerBounds.budget; ring
  rw [HE]
  nlinarith

theorem height_mono {R R' G : ℕ} (hR : R≤R') : height R G ≤ height R' G := by
  have HS := Nat.size_le_size hR
  unfold height CharacteristicIntegerBounds.budget
  gcongr

theorem capacityFactor_mono {n D R R' : ℕ} (hR : R≤R') : capacityFactor n D R ≤ capacityFactor n D R' := by
  unfold capacityFactor
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (height_mono (G:=0) hR)) _) _

theorem exponent_linear (n D R G : ℕ) : exponent n D R G ≤ capacityFactor n D R*(G+1) := by
  have HH := Nat.mul_le_mul_right (FixedLeadingTiltedSource.degree D) (height_linear R G)
  unfold exponent capacityFactor
  nlinarith

theorem capacityFactor_binary {n D R : List Bool → ℕ} (hn : UnaryFn n) (hD : BinaryFn D) (hR : BinaryFn R) :
    BinaryFn (fun q => capacityFactor (n q) (D q) (R q)) :=
  (((BinaryFn.ofUnary hn).size).add ((height_binary hR (BinaryFn.const 0)).mul
    (((BinaryFn.const 4).mul hD).add (BinaryFn.const 2)))).add (BinaryFn.const 2)

def schedule (b C j : ℕ) : ℕ := b^j*(C+1)

theorem schedule_binary {b C j : List Bool → ℕ} (hb : BinaryFn b) (hC : BinaryFn C) (hj : UnaryFn j) :
    BinaryFn (fun q => schedule (b q) (C q) (j q)) :=
  (hb.powUnary hj).mul (hC.add (BinaryFn.const 1))

theorem schedule_positive {b : ℕ} (hb : 1≤b) (C j : ℕ) : 1≤schedule b C j := by
  have HP : 1≤b^j := Nat.one_le_pow j b hb
  unfold schedule
  nlinarith

theorem schedule_seed {b C : ℕ} (hb : 1≤b) (j : ℕ) : C+1≤schedule b C j := by
  have HP := Nat.one_le_pow j b hb
  unfold schedule
  nlinarith

theorem capacity_tick {n D R R' G b C j : ℕ} (hR : R≤R')
    (hG : G≤schedule b C j) (hb : 2*capacityFactor n D R'≤b) :
    exponent n D R G≤schedule b C (j+1) := by
  have HF : 2≤capacityFactor n D R' := by unfold capacityFactor; omega
  have HB : 1≤b := by omega
  have HP := schedule_positive HB C j
  have HFactor := capacityFactor_mono (n:=n) (D:=D) hR
  calc
    _ ≤ capacityFactor n D R*(G+1) := exponent_linear n D R G
    _ ≤ capacityFactor n D R'*(schedule b C j+1) := Nat.mul_le_mul HFactor (by omega)
    _ ≤ 2*capacityFactor n D R'*schedule b C j := by nlinarith
    _ ≤ b*schedule b C j := Nat.mul_le_mul_right _ hb
    _ = _ := by unfold schedule; rw [pow_succ]; ring

/-- The birth is charged after the new source exponent has been selected. -/
theorem birth_tick {G E G' K b C j : ℕ} (hb : 1≤b) (hK : 3*K≤b)
    (hG : G≤schedule b C j) (hE : E≤schedule b C j)
    (hbirth : G'≤K*(G+E+C+1)) : G'≤schedule b C (j+1) := by
  have HC := schedule_seed (C:=C) hb j
  calc
    G' ≤ K*(G+E+C+1) := hbirth
    _ ≤ 3*K*schedule b C j := by nlinarith
    _ ≤ b*schedule b C j := Nat.mul_le_mul_right _ hK
    _ = _ := by unfold schedule; rw [pow_succ]; ring

/-- A positive old budget avoids an additive unit in the capacity recurrence. -/
def hfactor (R : ℕ) : ℕ := R+height R 0

def cfactor (n D R : ℕ) : ℕ := n.size+hfactor R*FixedLeadingTiltedSource.degree D+2

theorem height_linear_of_pos (R G : ℕ) (hG : 1≤G) : height R G≤hfactor R*G := by
  have HE : height R G=R*G+height R 0 := by unfold height CharacteristicIntegerBounds.budget; ring
  rw [HE]
  unfold hfactor
  nlinarith

theorem exponent_linear_of_pos (n D R G : ℕ) (hG : 1≤G) : exponent n D R G≤cfactor n D R*G := by
  have HH := Nat.mul_le_mul_right (FixedLeadingTiltedSource.degree D) (height_linear_of_pos R G hG)
  unfold exponent cfactor
  nlinarith

theorem cfactor_mono {n D R R' : ℕ} (hR : R≤R') : cfactor n D R≤cfactor n D R' := by
  have HH := Nat.add_le_add hR (height_mono (G:=0) hR)
  unfold cfactor hfactor
  gcongr

theorem cfactor_binary {n D R : List Bool → ℕ} (hn : UnaryFn n) (hD : BinaryFn D) (hR : BinaryFn R) :
    BinaryFn (fun q => cfactor (n q) (D q) (R q)) :=
  (((BinaryFn.ofUnary hn).size).add ((hR.add (height_binary hR (BinaryFn.const 0))).mul
    (((BinaryFn.const 4).mul hD).add (BinaryFn.const 2)))).add (BinaryFn.const 2)

theorem source_charge {T E F G : ℕ} (hG : 1≤G) (hT : T≤G) (hE : E≤F*G) :
    T+E+1≤(F+2)*G := by nlinarith

/-- The actual next-bank inequality remains explicit; the source was charged
before that birth. No recurrence for a new interpreter is assumed implicitly. -/
theorem framed_schedule_step {G G' F b0 C j : ℕ}
    (hG : G≤schedule (b0*(F+2)) C j) (hbirth : G'≤b0*((F+2)*G)) :
    G'≤schedule (b0*(F+2)) C (j+1) := by
  calc
    _ ≤ b0*((F+2)*G) := hbirth
    _ ≤ b0*((F+2)*schedule (b0*(F+2)) C j) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hG)
    _ = _ := by unfold schedule; rw [pow_succ]; ring

theorem scheduled_frozen_margin {n p S B m R b C j : ℕ} {P : IntegralMixedHistory.SpatialSource p} {ι : Type}
    (x : IntegralMixedHistory.State P S B m ι) (hb : 1≤b)
    (HG : x.bank.Bounds (schedule b C j)) (hR : FixedWidthPolynomial.count m B≤R)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (k D : ℕ) (select : Fin k → Fin m)
    (a : Fin n → ℝ)
    (Hparam : ∀ i : Fin n, ∀ hi : i.val<k,
      a i=φ (x.bank.numerator (select ⟨i.val,hi⟩))/(x.bank.denominator (select ⟨i.val,hi⟩):ℝ)) :
    |FixedLeadingDilationValueBound.frozenValue k D a| <
      ((2^(cfactor n D R*schedule b C j):ℤ):ℝ)-1 := by
  have HE := exponent_linear_of_pos n D (FixedWidthPolynomial.count m B) (schedule b C j) (schedule_positive hb C j)
  have HF := cfactor_mono (n:=n) (D:=D) hR
  have HExp := HE.trans (Nat.mul_le_mul_right (schedule b C j) HF)
  have HA : (coefficient n D (FixedWidthPolynomial.count m B) (schedule b C j):ℝ) ≤
      ((2^(cfactor n D R*schedule b C j):ℤ):ℝ) := by
    unfold coefficient
    exact_mod_cast Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) HExp
  exact (IntegralMixedCausalLevelCapacity.frozen_margin x HG φ k D select a Hparam).trans_le (sub_le_sub_right HA 1)

theorem scheduled_eventually_value_bound {I : Type*} {n p S B m R b C j : ℕ}
    {P : IntegralMixedHistory.SpatialSource p} {ι : Type}
    (l : Filter I) (x : IntegralMixedHistory.State P S B m ι) (hb : 1≤b)
    (HG : x.bank.Bounds (schedule b C j)) (hR : FixedWidthPolynomial.count m B≤R)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (k D : ℕ) (select : Fin k → Fin m)
    (u : Fin n) (t : LeanCanny.ETR.Term) (ht : t.degreeBound≤D) (ha : t.arity≤n)
    (hu : k≤u.val) (hD : 0<D) (eta : I → ℝ) (original : I → Fin n → ℝ) (a : Fin n → ℝ)
    (heta : Tendsto eta l (𝓝 0)) (hx : Tendsto original l (𝓝 a))
    (Hparam : ∀ i : Fin n, ∀ hi : i.val<k,
      a i=φ (x.bank.numerator (select ⟨i.val,hi⟩))/(x.bank.denominator (select ⟨i.val,hi⟩):ℝ)) :
    ∀ᶠ i in l, |(FixedLeadingTiltedSource.polynomial k D u t ht).eval₂ (Int.castRingHom ℝ)
      (FixedLeadingTiltedGradient.point k (eta i/(IntegralMixedHistory.commonDenominator x:ℝ)) (original i))| ≤
      ((2^(cfactor n D R*schedule b C j):ℤ):ℝ)-1 := by
  have HV := (FixedLeadingDilationValueBound.value_tendsto l k D u t ht ha hu hD eta
    (IntegralMixedHistory.commonDenominator x:ℝ) original a heta hx).abs
  exact ((tendsto_order.mp HV).2 _
    (scheduled_frozen_margin x hb HG hR φ k D select a Hparam)).mono (fun _ h => h.le)

end LeanCanny.Geometry.IntegralMixedCausalLevelSchedule
