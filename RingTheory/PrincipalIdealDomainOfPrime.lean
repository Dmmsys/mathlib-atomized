/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Ideal.Oka
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Principal ideal domains and prime ideals

## Main results

- `IsPrincipalIdealRing.of_prime`: a ring where all prime ideals are principal is a principal ideal
  ring.
-/

public section

variable {R : Type*} [CommSemiring R]

namespace Ideal

/--
theorem `isOka_isPrincipal` / 定理 `isOka_isPrincipal`

English:
theorem isOka_isPrincipal
  statement: IsOka (Submodule.IsPrincipal (R := R)) where
  proof: top_isPrincipal
  oka {I a} := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x * y, le_antisymm ?_ ?_⟩ <;> rw [submodule_span_eq] at *
    · intro i hi
      have hisup : i in I ⊔ span {a} := mem_sup_left hi
      have hasup : a in I ⊔ span {a} := mem_sup_right (mem_span_singleton_self a)
      rw [hx]; rw [mem_span_singleton'] at hisup hasup
      obtain ⟨u, rfl⟩ := hisup
      obtain ⟨v, rfl⟩ := hasup
      obtain ⟨z, rfl⟩ : exists z, z * y = u := by
        rw [← mem_span_singleton']; rw [← hy]; rw [mem_colon_span_singleton]; rw [mul_comm v]; rw [← mul_assoc]
        exact mul_mem_right _ _ hi
      exact mem_span_singleton'.2 ⟨z, by rw [mul_assoc, mul_comm y]⟩
    · rw [← span_singleton_mul_span_singleton, ← hx, Ideal.sup_mul, sup_le_iff,
        span_singleton_mul_span_singleton, mul_comm a, span_singleton_le_iff_mem]
exact ⟨mul_le_left, mem_colon_span_singleton.1 hy ▸ mem_span_singleton_self y⟩

中文:
定理 isOka_isPrincipal
  结论: 是Oka (子模.是Principal (R := R)) where
  证明: top_isPrincipal
  oka {I a} := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x * y, le_antisymm ?_ ?_⟩ <;> rw [submodule_span_eq] at *
    · intro i hi
      have hisup : i in I ⊔ span {a} := mem_sup_left hi
      have hasup : a in I ⊔ span {a} := mem_sup_right (mem_span_singleton_self a)
      rw [hx]; rw [mem_span_singleton'] at hisup hasup
      obtain ⟨u, rfl⟩ := hisup
      obtain ⟨v, rfl⟩ := hasup
      obtain ⟨z, rfl⟩ : exists z, z * y = u := by
        rw [← mem_span_singleton']; rw [← hy]; rw [mem_colon_span_singleton]; rw [mul_comm v]; rw [← mul_assoc]
        exact mul_mem_right _ _ hi
      exact mem_span_singleton'.2 ⟨z, by rw [mul_assoc, mul_comm y]⟩
    · rw [← span_singleton_mul_span_singleton, ← hx, Ideal.sup_mul, sup_le_iff,
        span_singleton_mul_span_singleton, mul_comm a, span_singleton_le_iff_mem]
exact ⟨mul_le_left, mem_colon_span_singleton.1 hy ▸ mem_span_singleton_self y⟩

Depends on / 依赖: LocallyConstant, LocallyConstant.comap, continuous_CC
-/
theorem isOka_isPrincipal : IsOka (Submodule.IsPrincipal (R := R)) where
  top := top_isPrincipal
  oka {I a} := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x * y, le_antisymm ?_ ?_⟩ <;> rw [submodule_span_eq] at *
    · intro i hi
      have hisup : i in I ⊔ span {a} := mem_sup_left hi
      have hasup : a in I ⊔ span {a} := mem_sup_right (mem_span_singleton_self a)
      rw [hx]; rw [mem_span_singleton'] at hisup hasup
      obtain ⟨u, rfl⟩ := hisup
      obtain ⟨v, rfl⟩ := hasup
      obtain ⟨z, rfl⟩ : exists z, z * y = u := by
        rw [← mem_span_singleton']; rw [← hy]; rw [mem_colon_span_singleton]; rw [mul_comm v]; rw [← mul_assoc]
        exact mul_mem_right _ _ hi
      exact mem_span_singleton'.2 ⟨z, by rw [mul_assoc, mul_comm y]⟩
    · rw [← span_singleton_mul_span_singleton, ← hx, Ideal.sup_mul, sup_le_iff,
        span_singleton_mul_span_singleton, mul_comm a, span_singleton_le_iff_mem]
exact ⟨mul_le_left, mem_colon_span_singleton.1 hy ▸ mem_span_singleton_self y⟩

end Ideal

open Ideal

/--
theorem `IsPrincipalIdealRing.of_prime` / 定理 `IsPrincipalIdealRing.of_prime`

English:
theorem IsPrincipalIdealRing.of_prime
  given: (H : forall P : Ideal R, P.IsPrime -> P.IsPrincipal)
  proof: by
  refine ⟨isOka_isPrincipal.forall_of_forall_prime (fun I hI => exists_maximal_not_isPrincipal ?_) H⟩
  rw [isPrincipalIdealRing_iff]; rw [not_forall]
  exact ⟨I, hI⟩

中文:
定理 是主理想环.of_prime
  条件: (H : 对任意 P : 理想 R, P.是素 -> P.是Principal)
  证明: by
  refine ⟨isOka_isPrincipal.forall_of_forall_prime (fun I hI => exists_maximal_not_isPrincipal ?_) H⟩
  rw [isPrincipalIdealRing_iff]; rw [not_forall]
  exact ⟨I, hI⟩

Depends on / 依赖: Linear_CC, exists_maximal_not_isPrincipal, forall_of_forall_prime, isOka_isPrincipal, isOka_isPrincipal.forall_of_forall_prime, isPrincipalIdealRing_iff, not_forall
-/
theorem IsPrincipalIdealRing.of_prime (H : forall P : Ideal R, P.IsPrime -> P.IsPrincipal) :
    IsPrincipalIdealRing R := by
  refine ⟨isOka_isPrincipal.forall_of_forall_prime (fun I hI => exists_maximal_not_isPrincipal ?_) H⟩
  rw [isPrincipalIdealRing_iff]; rw [not_forall]
  exact ⟨I, hI⟩

/--
theorem `IsPrincipalIdealRing.of_prime_ne_bot` / 定理 `IsPrincipalIdealRing.of_prime_ne_bot`

English:
theorem IsPrincipalIdealRing.of_prime_ne_bot
  proof: .of_prime fun P hp => (eq_or_ne P ⊥).elim (· ▸ inferInstance) H _ hp

中文:
定理 是主理想环.of_prime_ne_bot
  证明: .of_prime fun P hp => (eq_or_ne P ⊥).elim (· ▸ inferInstance) H _ hp

Depends on / 依赖: eq_or_ne, of_prime
-/
theorem IsPrincipalIdealRing.of_prime_ne_bot
    (H : forall P : Ideal R, P.IsPrime -> P != ⊥ -> P.IsPrincipal) :
    IsPrincipalIdealRing R :=
.of_prime fun P hp => (eq_or_ne P ⊥).elim (· ▸ inferInstance) H _ hp
