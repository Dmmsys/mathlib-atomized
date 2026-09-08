/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of `IsScalarTower`

We prove that given `IsScalarTower F K A`, if `A` is finite as a module over `F` then
`A` is finite over `K`, and
(as long as `A` is Noetherian over `F` and torsion-free over `K`) `K` is finite over `F`.

In particular these conditions hold when `A`, `F`, and `K` are fields.

The formulas for the dimensions are given elsewhere by `Module.finrank_mul_finrank`.

## Tags

tower law

-/

public section


universe u v w u₁ v₁ w₁

open Cardinal Submodule

variable (F : Type u) (K : Type v) (A : Type w)

namespace Module.Finite

variable [Ring F] [Ring K] [Module F K]
  [AddCommGroup A] [Module K A] [Module.IsTorsionFree K A]
  [Module F A] [IsNoetherian F A] [IsScalarTower F K A] in
/-- In a tower of field extensions `A / K / F`, if `A / F` is finite, so is `K / F`.

(In fact, it suffices that `A` is a nontrivial ring.)

Note this cannot be an instance as Lean cannot infer `A`.
-/
/-
**Module.Finite.left** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：left [IsDomain K] [Nontrivial A] : Module.Finite F K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Module.Finite.of_injective`：∀ {R : Type u_1} {S : Type u_2} {M : Type u_
3} {N : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommM
onoid M] [inst_3…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α

--- 原说明 ---
In a tower of field extensions `A / K / F`, if `A / F` is finite, so is `K / F`.

(In fact, it suffices that `A` is a nontrivial ring.)

Note this cannot be an instance as Lean cannot infer `A`.
-/
theorem left [IsDomain K] [Nontrivial A] : Module.Finite F K :=
  let ⟨x, hx⟩ := exists_ne (0 : A)
  Module.Finite.of_injective
    (LinearMap.ringLmapEquivSelf K ℕ A |>.symm x |>.restrictScalars F) (smul_left_injective K hx)

variable [Semiring F] [Semiring K] [Module F K]
  [AddCommMonoid A] [Module K A] [Module F A] [IsScalarTower F K A] in
@[stacks 09G5]
/-
**Module.Finite.right** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：right [hf : Module.Finite F A] : Module.Finite K A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars S : Submodule R M -> Submodule S M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.restrictScalars_top`：restrictScalars_top : restrictScalars S (
⊤ : Submodule R M) = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
theorem right [hf : Module.Finite F A] : Module.Finite K A :=
  let ⟨⟨b, hb⟩⟩ := hf
  ⟨⟨b, Submodule.restrictScalars_injective F _ _ <| by
    rw [Submodule.restrictScalars_top, eq_top_iff, ← hb, Submodule.span_le]
    exact Submodule.subset_span⟩⟩

end Module.Finite

alias FiniteDimensional.left := Module.Finite.left
alias FiniteDimensional.right := Module.Finite.right

