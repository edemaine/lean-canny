/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHistory
/-! # Physical critical sources over arbitrary actual mixed prefixes

A critical rule acts on the literal retained scalar algebra. No formal
nilpotent or frozen sweep coordinate is added. In particular offset zero
is permitted. Changing the selected coefficient and matrix query retains
the same actual prefix, basis, and original integer spatial polynomial.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalCriticalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family where
  ambient : List Bool → ℕ
  cap : List Bool → ℕ
  width : List Bool → ℕ
  birth : List Bool → ℕ
  physical : List Bool → Type
  spatial : (q : List Bool) → SpatialSource (ambient q)
  state : (q : List Bool) → State (spatial q) (cap q) (width q) (birth q) (physical q)
  birth_bound : ∀ q, birth q ≤ cap q
  rule : (q : List Bool) → CriticalRule (ambient q)

structure Indices (F : Family) where
  coordinate : (q : List Bool) → Fin (F.ambient q - (F.rule q).offset.val + 1)
  coefficientIndex : List Bool → ℕ
  target : List Bool → ℕ
  row : (q : List Bool) → Fin (FixedWidthPolynomial.count (F.birth q) (F.width q))
  col : (q : List Bool) → Fin (FixedWidthPolynomial.count (F.birth q) (F.width q))
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ q, modulus q ≠ 0

noncomputable def history (F : Family) (I : Indices F) : IntegralHistoryCriticalBits.Family where
  cap := F.cap
  width := F.width
  birth := F.birth
  ambient := F.ambient
  free q := F.ambient q - (F.rule q).offset.val
  scalarPrefix q := (F.state q).sampler.scalarPrefix
  data q := data (F.state q) (F.birth_bound q) (F.rule q)
  offset q := (F.rule q).offset.val
  fit q := by have H := (F.rule q).offset.isLt; omega
  sourceWidth q := (F.spatial q).degree.size
  degree_lt q := Nat.lt_size_self _
  objective q := ⟨(F.rule q).objective % (F.ambient q - (F.rule q).offset.val + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  coordinate := I.coordinate
  coefficientIndex := I.coefficientIndex
  target := I.target
  row := I.row
  col := I.col
  modulus := I.modulus
  modulus_ne_zero := I.modulus_ne_zero

noncomputable def euler (F : Family) (I : Indices F) := IntegralHistoryCriticalBits.euler (history F I)
noncomputable def source (F : Family) (I : Indices F) := IntegralHistoryCriticalBits.source (history F I)

abbrev Coefficient (F : Family) (q : List Bool) := (F.state q).sampler.scalarPrefix.carrier

noncomputable def denominator (F : Family) (q : List Bool) : ℤ :=
  CoordinateFrozenCriticalElimination.denominator (data (F.state q) (F.birth_bound q) (F.rule q)).scales
noncomputable def height (F : Family) (q : List Bool) (j : ℕ) : Coefficient F q :=
  CoordinateFrozenCriticalElimination.numerators (data (F.state q) (F.birth_bound q) (F.rule q)).scales
    (data (F.state q) (F.birth_bound q) (F.rule q)).heights j

theorem carrier (F : Family) (I : Indices F) (q : List Bool) : (source F I).carrier q = Coefficient F q := rfl

theorem basis (F : Family) (I : Indices F) (q : List Bool) :
    (source F I).basis q = (F.state q).sampler.scalarPrefix.basis.finBasis := rfl

theorem rank (F : Family) (I : Indices F) (q : List Bool) :
    (source F I).rank q = FixedWidthPolynomial.count (F.birth q) (F.width q) := rfl

theorem denominator_eq (F : Family) (I : Indices F) (q : List Bool) :
    (source F I).denominator q = denominator F q := rfl

theorem leading_eq (F : Family) (I : Indices F) (q : List Bool) :
    (source F I).leading q = (F.spatial q).leading := rfl

theorem height_eq (F : Family) (I : Indices F) (q : List Bool) (j : ℕ) :
    (source F I).height q j = height F q j := rfl

theorem annihilator_eq (F : Family) (I : Indices F) (q : List Bool) :
    (source F I).annihilator q = CoordinateFrozenCriticalElimination.polynomial (F.spatial q).degree
      (data (F.state q) (F.birth_bound q) (F.rule q)).scales
      (data (F.state q) (F.birth_bound q) (F.rule q)).heights (F.rule q).offset.val
      ((history F I).fit q) ((F.spatial q).low.map (Int.castRingHom (Coefficient F q)))
      ((F.spatial q).leading : Coefficient F q) ((history F I).objective q) (I.coordinate q) :=
  IntegralHistoryCriticalBits.annihilator_eq (history F I) q

noncomputable def value (F : Family) (I : Indices F) (q : List Bool) : List Bool := by
  letI := (source F I).ring q
  exact residueBits ((Algebra.leftMulMatrix (F.state q).sampler.scalarPrefix.basis.finBasis
    (((source F I).annihilator q).coeff (I.coefficientIndex q)) (I.row q) (I.col q) : ℤ) : ZMod (I.modulus q))

theorem value_eq (F : Family) (I : Indices F) (q : List Bool) : (source F I).value q = value F I q := rfl

theorem original_coefficient_matrix (F : Family) (I : Indices F) (q : List Bool)
    (e : Fin (F.ambient q + 1) →₀ ℕ)
    (r t : Fin (FixedWidthPolynomial.count (F.birth q) (F.width q))) :
    letI := (source F I).ring q
    Algebra.leftMulMatrix ((source F I).basis q) (((source F I).polynomial q).coeff e) r t =
      if r = t then (F.spatial q).low.coeff e else 0 := by
  let := (source F I).ring q
  change Algebra.leftMulMatrix ((source F I).basis q)
    ((((F.spatial q).low.map (Int.castRingHom (Coefficient F q))).coeff e)) r t = _
  rw [MvPolynomial.coeff_map]
  change Algebra.leftMulMatrix ((source F I).basis q)
    ((((F.spatial q).low.coeff e : ℤ) : (source F I).carrier q)) r t = _
  simp only [map_intCast, Matrix.intCast_apply, Int.cast_id]

theorem critical_polynomial (F : Family) (I : Indices F) (q : List Bool)
    (hc : (I.coordinate q).val = (F.rule q).coordinate % (F.ambient q - (F.rule q).offset.val + 1)) :
    (source F I).annihilator q = criticalPolynomial (F.state q) (F.birth_bound q) (F.rule q) := by
  rw [annihilator_eq, criticalPolynomial, IntegralHistoryCriticalBits.annihilator_eq]
  congr 1
  exact Fin.ext hc

theorem top_value (F : Family) (I : Indices F) (q : List Bool)
    (hc : (I.coordinate q).val = (F.rule q).coordinate % (F.ambient q - (F.rule q).offset.val + 1))
    (hk : I.coefficientIndex q = criticalDegree (F.state q) (F.birth_bound q) (F.rule q)) :
    (source F I).value q = residueBits
      ((if I.row q = I.col q then criticalLeading (F.state q) (F.birth_bound q) (F.rule q) else 0 : ℤ) : ZMod (I.modulus q)) := by
  let := (source F I).ring q
  let := (F.state q).sampler.scalarPrefix.ring
  have HC := congrArg (fun p : Polynomial (Coefficient F q) => p.coeff (I.coefficientIndex q))
    (critical_polynomial F I q hc)
  have HD : (((source F I).annihilator q).coeff (I.coefficientIndex q) : Coefficient F q) =
      (criticalLeading (F.state q) (F.birth_bound q) (F.rule q) : Coefficient F q) := by
    exact HC.trans (by simpa only [hk] using criticalLeading_coefficient (F.state q) (F.birth_bound q) (F.rule q))
  rw [value_eq]
  unfold value
  change residueBits ((Algebra.leftMulMatrix (F.state q).sampler.scalarPrefix.basis.finBasis
    (((source F I).annihilator q).coeff (I.coefficientIndex q)) (I.row q) (I.col q) : ℤ) : ZMod (I.modulus q)) = _
  rw [HD]
  simp only [map_intCast, Matrix.intCast_apply, Int.cast_id]
end LeanCanny.Algebra.IntegralMixedPhysicalCriticalBits
