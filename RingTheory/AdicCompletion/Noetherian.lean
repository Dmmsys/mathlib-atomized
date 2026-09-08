/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Hausdorff-ness for Noetherian rings
-/

public section

open IsLocalRing Module

variable {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R M]

/-
**IsHausdorff.of_le_jacobson** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsHausdorff.of_le_jacobson (h : I <= Ideal.jacobson ⊥) : IsHausdorff I M
参数：h : I <= Ideal.jacobson ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`：Ideal.iInf_pow_smul_eq_bot_of
_le_jacobson [IsNoetherianRing R] [Module.Finite R M] (h : I <= Ideal.jacobson ⊥
) : (⨅ i : Nat, I ^ i • ⊤ : Sub…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma IsHausdorff.of_le_jacobson (h : I ≤ Ideal.jacobson ⊥) : IsHausdorff I M :=
  ⟨fun x hx ↦ (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I h).le (by simpa [SModEq.zero] using hx)⟩
/-
**IsHausdorff.of_isLocalRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHausdorff.of_isLocalRing [IsLocalRing R] (h : I != ⊤) : IsHausdorff I M
参数：h : I != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsHausdorff.of_le_jacobson`：IsHausdorff.of_le_jacobson (h : I <= Ideal.j
acobson ⊥) : IsHausdorff I M
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `IsLocalRing.maximalIdeal_le_jacobson`：maximalIdeal_le_jacobson (I : Idea
l R) : IsLocalRing.maximalIdeal R <= I.jacobson
-/
theorem IsHausdorff.of_isLocalRing [IsLocalRing R] (h : I ≠ ⊤) : IsHausdorff I M :=
  of_le_jacobson I M ((le_maximalIdeal h).trans (maximalIdeal_le_jacobson _))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsLocalRing R] : IsHausdorff (maximalIdeal R) M :=
  .of_le_jacobson _ _ (maximalIdeal_le_jacobson _)
/-
**IsHausdorff.of_isTorsionFree** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsHausdorff.of_isTorsionFree [IsDomain R] [IsTorsionFree R M] (h : I != ⊤)
 : IsHausdorff I M
参数：h : I != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree`：Ideal.iInf_pow_smul_eq_bot_
of_isTorsionFree [IsDomain R] [IsNoetherianRing R] [Module.IsTorsionFree R M] [M
odule.Finite R M] (h : I != ⊤) : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma IsHausdorff.of_isTorsionFree [IsDomain R] [IsTorsionFree R M] (h : I ≠ ⊤) : IsHausdorff I M :=
  ⟨fun x hx ↦ (I.iInf_pow_smul_eq_bot_of_isTorsionFree h).le (by simpa [SModEq.zero] using hx)⟩
/-
**IsHausdorff.of_isDomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHausdorff.of_isDomain [IsDomain R] (h : I != ⊤) : IsHausdorff I R
参数：h : I != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsHausdorff.of_isTorsionFree`：IsHausdorff.of_isTorsionFree [IsDomain R] 
[IsTorsionFree R M] (h : I != ⊤) : IsHausdorff I M
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem IsHausdorff.of_isDomain [IsDomain R] (h : I ≠ ⊤) : IsHausdorff I R :=
  .of_isTorsionFree I R h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {A : Type*} [CommRing A] [IsArtinianRing A] [IsLocalRing A] :
    IsAdicComplete (IsLocalRing.maximalIdeal A) A where
  prec' f hf := by
    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp ‹_›
    use f n; intro m
    by_cases h : m ≤ n
    · exact hf h
    specialize hf (show n ≤ m by lia)
    rw [hn, zero_smul, Ideal.zero_eq_bot, SModEq.bot] at hf
    rw [hf]
