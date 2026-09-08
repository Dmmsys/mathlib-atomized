/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Modules as direct limits of finitely generated submodules

We show that every module is the direct limit of its finitely generated submodules.

## Main definitions

* `Module.fgSystem`: the directed system of finitely generated submodules of a module.

* `Module.fgSystem.equiv`: the isomorphism between a module and the direct limit of its
  finitely generated submodules.
-/

@[expose] public section

namespace Module

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/-- The directed system of finitely generated submodules of a module. -/
/-
**Module.fgSystem** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：fgSystem (N₁ N₂ : {N : Submodule R M // N.FG}) (le : N₁ <= N₂) : N₁ ->ₗ[R]
 N₂
参数：N₁ N₂ : {N : Submodule R M // N.FG}；le : N₁ <= N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The directed system of finitely generated submodules of a module.
-/
def fgSystem (N₁ N₂ : {N : Submodule R M // N.FG}) (le : N₁ ≤ N₂) : N₁ →ₗ[R] N₂ :=
  Submodule.inclusion le

open Module.DirectLimit

namespace fgSystem

/-
**Module.fgSystem.** 是 Mathlib 中的一个实例，位于命名空间 `Module.fgSystem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDirectedOrder {N : Submodule R M // N.FG} where
  directed N₁ N₂ :=
    ⟨⟨_, N₁.2.sup N₂.2⟩, Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩
/-
**Module.fgSystem.** 是 Mathlib 中的一个实例，位于命名空间 `Module.fgSystem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DirectedSystem _ (fgSystem R M · · · ·) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

variable [DecidableEq (Submodule R M)]

open Submodule in
/-- Every module is the direct limit of its finitely generated submodules. -/
/-
**Module.fgSystem.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.fgSystem`。
形式化陈述：equiv : DirectLimit _ (fgSystem R M) ≃ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every module is the direct limit of its finitely generated submodules.
-/
noncomputable def equiv : DirectLimit _ (fgSystem R M) ≃ₗ[R] M :=
  .ofBijective (lift _ _ _ _ (fun _ ↦ Submodule.subtype _) fun _ _ _ _ ↦ rfl)
    ⟨lift_injective _ _ fun _ ↦ Subtype.val_injective, fun x ↦
      ⟨of _ _ _ _ ⟨_, fg_span_singleton x⟩ ⟨x, subset_span <| by rfl⟩, lift_of ..⟩⟩

variable {R M}

set_option backward.isDefEq.respectTransparency.types false in
/-
**Module.fgSystem.equiv_comp_of** 是 Mathlib 中的一个引理，位于命名空间 `Module.fgSystem`。
形式化陈述：equiv_comp_of (N : {N : Submodule R M // N.FG}) : (equiv R M).toLinearMap 
∘ₗ of _ _ _ _ N = N.1.subtype
参数：N : {N : Submodule R M // N.FG}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.DirectLimit.lift_of`：∀ {R : Type u_1} [inst : Semiring R] {ι : Ty
pe u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMo
noid (G i)] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv_comp_of (N : {N : Submodule R M // N.FG}) :
    (equiv R M).toLinearMap ∘ₗ of _ _ _ _ N = N.1.subtype := by
  ext; simp [equiv]

end fgSystem

end Module

