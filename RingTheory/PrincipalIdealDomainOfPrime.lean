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

/-- `Submodule.IsPrincipal` is an Oka predicate. -/
/-
**Ideal.isOka_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isOka_isPrincipal : IsOka (Submodule.IsPrincipal (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `Ideal.mem_sup_left`：mem_sup_left {S T : Ideal R} : forall {x : R}, x in 
S -> x in S ⊔ T
· 使用定理 `Ideal.mem_sup_right`：mem_sup_right {S T : Ideal R} : forall {x : R}, x i
n T -> x in S ⊔ T
· 使用定理 `Ideal.mem_span_singleton_self`：mem_span_singleton_self (x : α) : x in sp
an ({x} : Set α)
· 使用定理 `Ideal.mem_span_singleton'`：mem_span_singleton' {x y : α} : x in span ({y
} : Set α) ↔ exists a, a * y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_colon_span_singleton`：∀ {R : Type u_1} [inst : CommSemiring R]
 {I : Ideal R} {x r : R}, r ∈ Submodule.colon I ↑(Ideal.span {x}) ↔ r * x ∈ I
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_mul_span_singleton`：span_singleton_mul_span_singlet
on (r s : R) [(span {r}).IsTwoSided] : span {r} * span {s} = (span {r * s} : Ide
al R)
· 使用定理 `Ideal.sup_mul`：sup_mul : (I ⊔ J) * K = I * K ⊔ J * K
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `Ideal.mul_le_left`：mul_le_left [I.IsTwoSided] : I * J <= I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
`Submodule.IsPrincipal` is an Oka predicate.
-/
theorem isOka_isPrincipal : IsOka (Submodule.IsPrincipal (R := R)) where
  top := top_isPrincipal
  oka {I a} := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x * y, le_antisymm ?_ ?_⟩ <;> rw [submodule_span_eq] at *
    · intro i hi
      have hisup : i ∈ I ⊔ span {a} := mem_sup_left hi
      have hasup : a ∈ I ⊔ span {a} := mem_sup_right (mem_span_singleton_self a)
      rw [hx, mem_span_singleton'] at hisup hasup
      obtain ⟨u, rfl⟩ := hisup
      obtain ⟨v, rfl⟩ := hasup
      obtain ⟨z, rfl⟩ : ∃ z, z * y = u := by
        rw [← mem_span_singleton', ← hy, mem_colon_span_singleton, mul_comm v, ← mul_assoc]
        exact mul_mem_right _ _ hi
      exact mem_span_singleton'.2 ⟨z, by rw [mul_assoc, mul_comm y]⟩
    · rw [← span_singleton_mul_span_singleton, ← hx, Ideal.sup_mul, sup_le_iff,
        span_singleton_mul_span_singleton, mul_comm a, span_singleton_le_iff_mem]
      exact ⟨mul_le_left, mem_colon_span_singleton.1 <| hy ▸ mem_span_singleton_self y⟩

end Ideal

open Ideal

/-- If all prime ideals in a commutative ring are principal, so are all other ideals. -/
/-
**IsPrincipalIdealRing.of_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrincipalIdealRing.of_prime (H : forall P : Ideal R, P.IsPrime -> P.IsPr
incipal) : IsPrincipalIdealRing R
参数：H : forall P : Ideal R, P.IsPrime -> P.IsPrincipal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsOka.forall_of_forall_prime`：forall_of_forall_prime (hmax : foral
l I, ¬P I -> exists I, Maximal (¬P ·) I) (hprime : forall I, I.IsPrime -> P I) (
I : Ideal R) : P I
· 使用定理 `Ideal.isOka_isPrincipal`：isOka_isPrincipal : IsOka (Submodule.IsPrincipa
l (R
· 使用定理 `Ideal.exists_maximal_not_isPrincipal`：exists_maximal_not_isPrincipal (hR
 : ¬IsPrincipalIdealRing R) : exists I : Ideal R, Maximal (¬·.IsPrincipal) I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPrincipalIdealRing_iff`：∀ (R : Type u) [inst : Semiring R], IsPrincipa
lIdealRing R ↔ ∀ (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x

--- 原说明 ---
If all prime ideals in a commutative ring are principal, so are all other ideals
.
-/
theorem IsPrincipalIdealRing.of_prime (H : ∀ P : Ideal R, P.IsPrime → P.IsPrincipal) :
    IsPrincipalIdealRing R := by
  refine ⟨isOka_isPrincipal.forall_of_forall_prime (fun I hI ↦ exists_maximal_not_isPrincipal ?_) H⟩
  rw [isPrincipalIdealRing_iff, not_forall]
  exact ⟨I, hI⟩

/-- If all prime ideals in a commutative ring that are not `(0)` are principal,
so are all other ideals. -/
/-
**IsPrincipalIdealRing.of_prime_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrincipalIdealRing.of_prime_ne_bot (H : forall P : Ideal R, P.IsPrime ->
 P != ⊥ -> P.IsPrincipal) : IsPrincipalIdealRing R
参数：H : forall P : Ideal R, P.IsPrime -> P != ⊥ -> P.IsPrincipal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.of_prime`：IsPrincipalIdealRing.of_prime (H : forall
 P : Ideal R, P.IsPrime -> P.IsPrincipal) : IsPrincipalIdealRing R
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If all prime ideals in a commutative ring that are not `(0)` are principal,
so are all other ideals.
-/
theorem IsPrincipalIdealRing.of_prime_ne_bot
    (H : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ → P.IsPrincipal) :
    IsPrincipalIdealRing R :=
  .of_prime fun P hp ↦ (eq_or_ne P ⊥).elim (· ▸ inferInstance) <| H _ hp
