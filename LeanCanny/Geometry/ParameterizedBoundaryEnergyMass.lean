/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.ParameterizedBoundaryGramValues
public import LeanCanny.Geometry.SystemCoordinateBounds
public import LeanCanny.Computation.PolyTimeBinaryNat
/-! # Dyadic growth of the actual boundary critical-value energy

Only the original source mass and degree allowances are inputs. The same
integer-parameter energy specializes to the literal critical-value system;
its mass exponent grows linearly with the dyadic parameter exponent.
-/
@[expose] public section
namespace LeanCanny.Geometry.ParameterizedBoundaryEnergyMass
open LeanCanny LeanCanny.Algebra MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def lagrangianOffset (n b : ℕ) : ℕ := n.size + 2*b + 2
def energyOffset (n D b : ℕ) : ℕ := (n+2).size + 2*(lagrangianOffset n b + (2*D+3).size + 1)

private theorem spatial_map (q : MvPolynomial (Fin n) ℤ) (e : ℤ) :
    (ParameterizedBoundaryCriticalValues.spatial q).map (Polynomial.evalRingHom e) = rename some q := by
  rw [ParameterizedBoundaryCriticalValues.spatial,MvPolynomial.map_map]
  have HC : (Polynomial.evalRingHom e).comp Polynomial.C = RingHom.id ℤ := by ext; simp
  rw [HC,MvPolynomial.map_id]

theorem lagrangian_map (q : MvPolynomial (Fin n) ℤ) (e : ℤ) :
    (ParameterizedBoundaryGramValues.lagrangian q).map (Polynomial.evalRingHom e) =
      rename CoerciveCriticalHomogenization.layout
        ((∑ i : Fin n, (X (some i) : MvPolynomial (Option (Fin n)) ℤ)^2) +
          X none * ((rename some q)^2 - C e)) := by
  simp [ParameterizedBoundaryGramValues.lagrangian,ParameterizedBoundaryCriticalValues.lagrangian,
    map_rename,spatial_map]

private theorem equations_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : MvPolynomial (Fin (n+1)) A) (j : Fin (n+2)) :
    (CriticalValueSystem.equations p j).map φ = CriticalValueSystem.equations (p.map φ) j := by
  refine Fin.cases ?_ (fun i => ?_) j <;>
    simp only [CriticalValueSystem.equations,Fin.cons_zero,Fin.cons_succ,map_sub,map_X,map_rename,pderiv_map]

theorem energy_map (q : MvPolynomial (Fin n) ℤ) (e : ℤ) :
    (ParameterizedBoundaryGramValues.energy q).map (Polynomial.evalRingHom e) =
      SystemCoordinateBounds.energy (CriticalValueSystem.equations
        ((ParameterizedBoundaryGramValues.lagrangian q).map (Polynomial.evalRingHom e))) := by
  simp only [ParameterizedBoundaryGramValues.energy,map_sum,map_pow,equations_map,SystemCoordinateBounds.energy]

theorem lagrangian_mass (q : MvPolynomial (Fin n) ℤ) (b : ℕ) (hq : MvMass.mass q ≤ 2^b) (r : ℕ) :
    MvMass.mass ((ParameterizedBoundaryGramValues.lagrangian q).map (Polynomial.evalRingHom ((2 : ℤ)^r))) ≤
      2^(r+lagrangianOffset n b) := by
  have HNorm : MvMass.mass (∑ i : Fin n, (X (some i) : MvPolynomial (Option (Fin n)) ℤ)^2) ≤ n := by
    apply (MvMass.sum_le _ _).trans
    calc
      _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (fun i _ => by
        simpa only [MvMass.X,one_pow] using MvMass.pow_le (X (some i) : MvPolynomial (Option (Fin n)) ℤ) 2)
      _ = n := by simp
  have HQ : MvMass.mass (rename some q) ≤ 2^b := (MvMass.rename_le _ _).trans hq
  have HSq : MvMass.mass ((rename some q)^2) ≤ 2^(2*b) := by
    exact ((MvMass.pow_le _ _).trans (Nat.pow_le_pow_left HQ 2)).trans_eq (by rw [←pow_mul]; congr 1; omega)
  have HC : MvMass.mass (C ((2 : ℤ)^r) : MvPolynomial (Option (Fin n)) ℤ) = 2^r := by
    rw [MvMass.C,Int.natAbs_pow]
    norm_num
  have HSub : MvMass.mass ((rename some q)^2 - C ((2 : ℤ)^r)) ≤ 2^(2*b)+2^r :=
    (MvMass.sub_le _ _).trans (Nat.add_le_add HSq HC.le)
  have HProd : MvMass.mass (X none * ((rename some q)^2 - C ((2 : ℤ)^r))) ≤ 2^(2*b)+2^r := by
    apply (MvMass.mul_le _ _).trans
    simpa only [MvMass.X,one_mul] using HSub
  have HL : MvMass.mass ((ParameterizedBoundaryGramValues.lagrangian q).map
      (Polynomial.evalRingHom ((2 : ℤ)^r))) ≤ n + 2^(2*b) + 2^r := by
    rw [lagrangian_map]
    apply (MvMass.rename_le _ _).trans
    exact ((MvMass.add_le _ _).trans (Nat.add_le_add HNorm HProd)).trans_eq (by omega)
  let E := r+n.size+2*b
  have HN : n ≤ 2^E := (Nat.lt_size_self n).le.trans (Nat.pow_le_pow_right (by decide) (by dsimp [E]; omega))
  have HB : 2^(2*b) ≤ 2^E := Nat.pow_le_pow_right (by decide) (by dsimp [E]; omega)
  have HR : 2^r ≤ 2^E := Nat.pow_le_pow_right (by decide) (by dsimp [E]; omega)
  apply HL.trans
  have HE : r+lagrangianOffset n b = E+2 := by dsimp [E,lagrangianOffset]; omega
  rw [HE,pow_add]
  norm_num
  omega

theorem energy_mass (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^b) (r : ℕ) :
    MvMass.mass ((ParameterizedBoundaryGramValues.energy q).map (Polynomial.evalRingHom ((2 : ℤ)^r))) ≤
      2^(2*r+energyOffset n D b) := by
  let p := (ParameterizedBoundaryGramValues.lagrangian q).map (Polynomial.evalRingHom ((2 : ℤ)^r))
  have HP : p.totalDegree ≤ 2*D+3 :=
    (PolynomialMapDegree.degree_le _ _).trans (ParameterizedBoundaryGramValues.lagrangian_degree q D hD)
  have HM : MvMass.mass p ≤ 2^(r+lagrangianOffset n b) := lagrangian_mass q b hq r
  have HR := CriticalValueSystem.mass_bound p (2*D+3) (r+lagrangianOffset n b) HP HM
  have H := SystemCoordinateBounds.energy_mass (CriticalValueSystem.equations p)
    (r+lagrangianOffset n b+(2*D+3).size+1) HR
  rw [←energy_map] at H
  have HSize : (n+1+1).size = (n+2).size := rfl
  rw [HSize] at H
  convert H using 1
  congr 1
  unfold energyOffset
  omega

theorem energyOffset_binary {N D B : List Bool → ℕ} (hN : BinaryFn N) (hD : BinaryFn D) (hB : BinaryFn B) :
    BinaryFn (fun u => energyOffset (N u) (D u) (B u)) := by
  have HL := (hN.size.add ((BinaryFn.const 2).mul hB)).add (BinaryFn.const 2)
  have HD := (((BinaryFn.const 2).mul hD).add (BinaryFn.const 3)).size
  exact ((hN.add (BinaryFn.const 2)).size).add
    ((BinaryFn.const 2).mul ((HL.add HD).add (BinaryFn.const 1)))

end LeanCanny.Geometry.ParameterizedBoundaryEnergyMass
