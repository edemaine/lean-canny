/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralHistoryCriticalStep
/-! # Full sampler scalar rows are literal renamed scalar-prefix rows

Physical critical blocks add their own equations while preserving this
identity. The scalar prefix is not substituted for the complete system.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralHistorySampler
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S N m n : ℕ} {ι : Type}

def ScalarRows (F : Sampler S N m ι) : Prop :=
  ∀ i,F.rows (F.scalar i)=rename F.scalar (F.scalarPrefix.rows i)

theorem ofPrefix_scalarRows (P : UniformIntegralPrefix.Prefix S N m) : ScalarRows (ofPrefix P) := by
  intro i
  change P.rows i=rename id (P.rows i)
  simp only [rename_id,AlgHom.id_apply]

theorem scalarStep_scalarRows [Fintype ι] (F : Sampler S N m ι) (hF : ScalarRows F)
    (hm : m≤S) (hN : 0<N) (p : Polynomial F.scalarPrefix.carrier) (d : ℕ) :
    ScalarRows (scalarStep F hm hN p d) := by
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · change rename (CanonicalIntegralScalarAppend.layout F.scalar) _=
      rename (Fin.cons (Sum.inr ()) (fun j=>Sum.inl (F.scalar j)))
        (rename (UniformIntegralPrefixRows.layout m) _)
    rw [rename_rename]
    have HL : CanonicalIntegralScalarAppend.layout F.scalar=
        (Fin.cons (Sum.inr ()) (fun j=>Sum.inl (F.scalar j)) : Fin (m+1)→ι⊕Unit) ∘
          UniformIntegralPrefixRows.layout m := by
      funext j
      cases j with
      | inl j=>rfl
      | inr u=>cases u; rfl
    exact congrArg (fun f=>rename f _) HL
  · change rename Sum.inl (F.rows (F.scalar j))=
      rename (Fin.cons (Sum.inr ()) (fun j=>Sum.inl (F.scalar j)))
        (rename Fin.succ (F.scalarPrefix.rows j))
    rw [hF j,rename_rename,rename_rename]
    rfl

theorem criticalStep_scalarRows [Fintype ι] (F : Sampler S N m ι) (hF : ScalarRows F)
    (data : CriticalData F.scalarPrefix n) : ScalarRows (criticalStep F data) := by
  intro i
  change rename Sum.inl (F.rows (F.scalar i))=rename (Sum.inl∘F.scalar) (F.scalarPrefix.rows i)
  rw [hF i,rename_rename]

theorem reindex_scalarRows {κ : Type} [Fintype ι] [Fintype κ]
    (F : Sampler S N m ι) (hF : ScalarRows F) (e : ι≃κ) : ScalarRows (reindex F e) := by
  intro i
  change rename e (F.rows (e.symm (e (F.scalar i))))=rename (e∘F.scalar) (F.scalarPrefix.rows i)
  rw [Equiv.symm_apply_apply,hF i,rename_rename]
end LeanCanny.Algebra.IntegralHistorySampler
