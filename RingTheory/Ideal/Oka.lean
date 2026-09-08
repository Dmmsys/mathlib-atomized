/-
Copyright (c) 2025 Anthony Fernandes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Fernandes, Marc Robin
-/
module

public import Mathlib.RingTheory.Ideal.Colon

/-!
# Oka predicates

This file introduces the notion of Oka predicates and standard results about them.

## Main results

- `Ideal.IsOka.isPrime_of_maximal_not`: if an ideal is maximal for not satisfying an Oka predicate,
  then it is prime.
- `Ideal.IsOka.forall_of_forall_prime`: if all prime ideals of a ring satisfy an Oka predicate,
  then all its ideals also satisfy the predicate.

## References

- [stacks-project]: The Stacks project, [tag 05K7](https://stacks.math.columbia.edu/tag/05K7)
- [lam_reyes_2009]: *Oka and Ako ideal families in commutative rings*, 2009
-/

public section

namespace Ideal

variable {R : Type*} [CommSemiring R]

/-- A predicate `P : Ideal R → Prop` over the ideals of a ring `R` is said to be Oka if R satisfies
it (`P ⊤`) and whenever we have `I : Ideal R`, `P (I.colon (span {a})` and `P (I ⊔ span {a})` for
some `a : R` then `P I`. -/
@[stacks 05K9]
/-
**Ideal.IsOka** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ideal`。
形式化陈述：{R : Type u_1} → [inst : CommSemiring R] → (Ideal R → Prop) → Prop
参数：Ideal R → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate `P : Ideal R → Prop` over the ideals of a ring `R` is said to be Oka
 if R satisfies
it (`P ⊤`) and whenever we have `I : Ideal R`, `P (I.colon (span {a})` and `P (I
 ⊔ span {a})` for
some `a : R` then `P I`.
-/
structure IsOka (P : Ideal R → Prop) : Prop where
  top : P ⊤
  oka {I : Ideal R} {a : R} : P (I ⊔ span {a}) → P (I.colon (span {a})) → P I

namespace IsOka

variable {P : Ideal R → Prop} (hP : IsOka P)
include hP

/-- If an ideal is maximal for not satisfying an Oka predicate then it is prime. -/
@[stacks 05KE]
/-
**Ideal.IsOka.isPrime_of_maximal_not** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsOka`。
形式化陈述：isPrime_of_maximal_not {I : Ideal R} (hI : Maximal (¬P ·) I) : I.IsPrime w
here ne_top' hI'
参数：hI : Maximal (¬P ·) I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `Ideal.IsOka.top`：∀ {R : Type u_1} [inst : CommSemiring R] {P : Ideal R →
 Prop}, Ideal.IsOka P → P ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Maximal.not_prop_of_gt`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst 
: Preorder α], Maximal P x → x < y → ¬P y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.lt_sup_iff_notMem`：lt_sup_iff_notMem {I : Submodule R M} {a : 
M} : I < I ⊔ R ∙ a ↔ a ∉ I
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ideal.le_colon`：∀ {R : Type u_1} [inst : Semiring R] {I : Ideal R} {S : 
Set R} [I.IsTwoSided], I ≤ Submodule.colon I S
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.mem_colon_span_singleton`：∀ {R : Type u_1} [inst : CommSemiring R]
 {I : Ideal R} {x r : R}, r ∈ Submodule.colon I ↑(Ideal.span {x}) ↔ r * x ∈ I
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Ideal.IsOka.oka`：∀ {R : Type u_1} [inst : CommSemiring R] {P : Ideal R →
 Prop},   Ideal.IsOka P → ∀ {I : Ideal R} {a : R}, P (I ⊔ Ideal.span {a}) → P (S
ubmod…

--- 原说明 ---
If an ideal is maximal for not satisfying an Oka predicate then it is prime.
-/
theorem isPrime_of_maximal_not {I : Ideal R} (hI : Maximal (¬P ·) I) : I.IsPrime where
  ne_top' hI' := hI.prop (hI' ▸ hP.top)
  mem_or_mem' := by
    by_contra! ⟨a, b, hab, ha, hb⟩
    have h₁ : P (I ⊔ span {a}) := of_not_not <| hI.not_prop_of_gt (Submodule.lt_sup_iff_notMem.2 ha)
    have h₂ : P (I.colon (span {a})) := of_not_not <| hI.not_prop_of_gt <| lt_of_le_of_ne le_colon
      (fun H ↦ hb <| H ▸ mem_colon_span_singleton.2 (mul_comm a b ▸ hab))
    exact hI.prop (hP.oka h₁ h₂)

/-- If a ring `R` verify:
1. All prime ideals of `R` satisfy an Oka predicate `P`.
2. One ideal not satisfying `P` implies that there is an ideal maximal for not satisfying `P`.

Then all the ideals of `R` satisfy `P`. -/
/-
**Ideal.IsOka.forall_of_forall_prime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsOka`。
形式化陈述：forall_of_forall_prime (hmax : forall I, ¬P I -> exists I, Maximal (¬P ·) 
I) (hprime : forall I, I.IsPrime -> P I) (I : Ideal R) : P I
参数：hmax : forall I, ¬P I -> exists I, Maximal (¬P ·) I；hprime : forall I, I.IsPr
ime -> P I；I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `Ideal.IsOka.isPrime_of_maximal_not`：isPrime_of_maximal_not {I : Ideal R}
 (hI : Maximal (¬P ·) I) : I.IsPrime where ne_top' hI'

--- 原说明 ---
If a ring `R` verify:
1. All prime ideals of `R` satisfy an Oka predicate `P`.
2. One ideal not satisfying `P` implies that there is an ideal maximal for not s
atisfying `P`.

Then all the ideals of `R` satisfy `P`.
-/
theorem forall_of_forall_prime (hmax : ∀ I, ¬P I → ∃ I, Maximal (¬P ·) I)
    (hprime : ∀ I, I.IsPrime → P I) (I : Ideal R) : P I := by
  by_contra hI
  obtain ⟨I, hI⟩ := hmax I hI
  exact hI.prop <| hprime I (hP.isPrime_of_maximal_not hI)

/-- A variant of `forall_of_forall_prime` with a different spelling of the condition `hmax`. -/
/-
**Ideal.IsOka.forall_of_forall_prime'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsOka`。
形式化陈述：forall_of_forall_prime' (hchain : forall C subseteq {I | ¬P I}, IsChain (·
 <= ·) C -> forall _ in C, P (sSup C) -> exists I in C, P I) (hprime : forall I,
 I.IsPrime -> P I) : forall I, P I
参数：hchain : forall C subseteq {I | ¬P I}, IsChain (· <= ·) C -> forall _ in C, P
 (sSup C) -> exists I in C, P I；hprime : forall I, I.IsPrime -> P I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsOka.forall_of_forall_prime`：forall_of_forall_prime (hmax : foral
l I, ¬P I -> exists I, Maximal (¬P ·) I) (hprime : forall I, I.IsPrime -> P I) (
I : Ideal R) : P I
· 使用定理 `zorn_le_nonempty₀`：zorn_le_nonempty₀ (s : Set α) (ih : forall c subseteq
 s, IsChain (· <= ·) c -> forall y in c, exists ub in s, forall z in c, z <= ub)
 (x : α…
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s

--- 原说明 ---
A variant of `forall_of_forall_prime` with a different spelling of the condition
 `hmax`.
-/
theorem forall_of_forall_prime'
    (hchain : ∀ C ⊆ {I | ¬P I}, IsChain (· ≤ ·) C → ∀ _ ∈ C, P (sSup C) → ∃ I ∈ C, P I)
    (hprime : ∀ I, I.IsPrime → P I) : ∀ I, P I := by
  refine forall_of_forall_prime hP (fun I hI ↦ ?_) hprime
  obtain ⟨M, _, hM⟩ : ∃ M, I ≤ M ∧ Maximal (¬P ·) M := by
    refine zorn_le_nonempty₀ {I | ¬P I} (fun C hC₁ hC₂ J hJ ↦ ⟨sSup C, ?_, fun _ ↦ le_sSup⟩) I hI
    intro H
    obtain ⟨_, h₁, h₂⟩ := hchain C hC₁ hC₂ J hJ H
    exact hC₁ h₁ h₂
  exact ⟨M, hM⟩

end IsOka

end Ideal

