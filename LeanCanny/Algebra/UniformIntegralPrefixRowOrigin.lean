/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformIntegralPrefixLift

/-! # Literal old equations persist through scalar-prefix extensions

The newest-first variable embedding is fixed by the two prefix arities.
Every old row is exactly its original polynomial renamed through that
embedding, without expansion or reinterpretation at a later source.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPrefix
open MvPolynomial UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S B m n : ℕ} {P : Prefix S (2^B) m} {Q : Prefix S (2^B) n}

theorem Chain.rows (C : Chain S B P Q) (i : Fin m) :
    Q.rows (UniformIntegralPowerSchedule.embed C.le i)=
      rename (UniformIntegralPowerSchedule.embed C.le) (P.rows i) := by
  induction C with
  | refl P =>
    have HE : UniformIntegralPowerSchedule.embed (Chain.refl P).le=id := by
      funext i
      apply Fin.ext
      simp only [UniformIntegralPowerSchedule.embed,Nat.sub_self,Nat.zero_add,id_eq]
    rw [HE,rename_id]
    rfl
  | @step n P Q C hn p d ih =>
    have HE : UniformIntegralPowerSchedule.embed (C.step hn p d).le=
        Fin.succ ∘ UniformIntegralPowerSchedule.embed C.le := by
      funext i
      apply Fin.ext
      simp only [UniformIntegralPowerSchedule.embed,Function.comp_apply,Fin.val_succ]
      have H:=C.le
      omega
    rw [HE]
    change rename Fin.succ (Q.rows (UniformIntegralPowerSchedule.embed C.le i))=_
    rw [ih,rename_rename]

end LeanCanny.Algebra.UniformIntegralPrefix
