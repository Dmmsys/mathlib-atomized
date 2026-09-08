/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/
module
public import Mathlib.Algebra.Lie.Ideal

/-! ### Products of Lie algebras

This file defines the Lie algebra structure the Product of two Lie algebras

## Main definitions

- products in the domain:
  - `LieHom.fst` The first projection of a product is a Lie algebra map.
  - `LieHom.snd` The second projection of a product is a Lie algebra map.
  - `LieHom.prod_ext` Split equality of Lie algebra homomorphisms from a product into Lie algebra
  homomorphism over each component,
- products in the codomain:
  - `LieHom.inl` The left injection into a product is a Lie algebra map.
  - `LieHom.inr` The right injection into a product is a Lie algebra map.
  - `LieHom.prod` The prod of two Lie algebra homomorphisms is a Lie algebra homomorphism.
- products in both domain and codomain:
  - `LieHom.prodMap` the `Prod.map` of two Lie algebra homomorphisms is a Lie algebra homomorphism.

## Todo: Extend to further functionality from LinearMap.prod e.g.
- Lie Equivalences related to products
- Lie Submodule statements

-/

@[expose] public section

variable {R L₁ L₂ L L₃ L₄ L₅ L₆ : Type*}
  [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
  [LieRing L] [LieAlgebra R L] [LieRing L₃] [LieAlgebra R L₃] [LieRing L₄] [LieAlgebra R L₄]
  [LieRing L₅] [LieAlgebra R L₅] [LieRing L₆] [LieAlgebra R L₆]

namespace LieAlgebra.Prod

/-
**LieAlgebra.Prod.instLieRing** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.Prod`。
形式化陈述：instLieRing : LieRing (L₁ × L₂) where bracket x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLieRing : LieRing (L₁ × L₂) where
  bracket x y := ⟨⁅x.1, y.1⁆, ⁅x.2, y.2⁆⟩
  add_lie := by simp
  lie_add := by simp
  lie_self := by simp
  leibniz_lie := by simp

@[simp]
/-
**LieAlgebra.Prod.bracket_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Prod`。
形式化陈述：bracket_apply (x y : L₁ × L₂) : ⁅x, y⁆ = ⟨⁅x.1, y.1⁆, ⁅x.2, y.2⁆⟩
参数：x y : L₁ × L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bracket_apply (x y : L₁ × L₂) : ⁅x, y⁆ = ⟨⁅x.1, y.1⁆, ⁅x.2, y.2⁆⟩ := rfl
/-
**LieAlgebra.Prod.instLieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.Prod`。
形式化陈述：instLieAlgebra : LieAlgebra R (L₁ × L₂) where lie_smul _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLieAlgebra : LieAlgebra R (L₁ × L₂) where
  lie_smul _ _ _ := by simp

end LieAlgebra.Prod

namespace LieHom

section
variable (R L₁ L₂)

/-- The first projection of a product is a Lie algebra map. -/
/-
**LieHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：fst : L₁ × L₂ ->ₗ⁅R⁆ L₁ where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection of a product is a Lie algebra map.
-/
def fst : L₁ × L₂ →ₗ⁅R⁆ L₁ where
  toLinearMap := LinearMap.fst R L₁ L₂
  map_lie' := by simp

/-- The second projection of a product is a Lie algebra map. -/
/-
**LieHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：snd : L₁ × L₂ ->ₗ⁅R⁆ L₂ where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection of a product is a Lie algebra map.
-/
def snd : L₁ × L₂ →ₗ⁅R⁆ L₂ where
  toLinearMap := LinearMap.snd R L₁ L₂
  map_lie' := by simp

/-- The left injection into a product is a Lie algebra map. -/
/-
**LieHom.inl** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：inl : L₁ ->ₗ⁅R⁆ L₁ × L₂ where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left injection into a product is a Lie algebra map.
-/
def inl : L₁ →ₗ⁅R⁆ L₁ × L₂ where
  toLinearMap := LinearMap.inl R L₁ L₂
  map_lie' := by simp

/-- The right injection into a product is a Lie algebra map. -/
/-
**LieHom.inr** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：inr : L₂ ->ₗ⁅R⁆ L₁ × L₂ where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right injection into a product is a Lie algebra map.
-/
def inr : L₂ →ₗ⁅R⁆ L₁ × L₂ where
  toLinearMap := LinearMap.inr R L₁ L₂
  map_lie' := by simp

end

/-
**LieHom.fst_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：∀ {R : Type u_1} {L₁ : Type u_2} {L₂ : Type u_3} [inst : CommRing R] [inst
_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : LieRing L₂] [inst_4 : Li
eAlgebra R L₂] (x : L₁ × L₂), (LieHom.fst R L₁ L₂) x = x.1
参数：x : L₁ × L₂；LieHom.fst R L₁ L₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_apply (x : L₁ × L₂) : fst R L₁ L₂ x = x.1 := rfl
/-
**LieHom.snd_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：∀ {R : Type u_1} {L₁ : Type u_2} {L₂ : Type u_3} [inst : CommRing R] [inst
_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : LieRing L₂] [inst_4 : Li
eAlgebra R L₂] (x : L₁ × L₂), (LieHom.snd R L₁ L₂) x = x.2
参数：x : L₁ × L₂；LieHom.snd R L₁ L₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_apply (x : L₁ × L₂) : snd R L₁ L₂ x = x.2 := rfl
/-
**LieHom.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：∀ {R : Type u_1} {L₁ : Type u_2} {L₂ : Type u_3} [inst : CommRing R] [inst
_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : LieRing L₂] [inst_4 : Li
eAlgebra R L₂], ⇑(LieHom.fst R L₁ L₂) = Prod.fst
参数：LieHom.fst R L₁ L₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_fst : ⇑(fst R L₁ L₂) = Prod.fst := rfl
/-
**LieHom.coe_snd** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：∀ {R : Type u_1} {L₁ : Type u_2} {L₂ : Type u_3} [inst : CommRing R] [inst
_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : LieRing L₂] [inst_4 : Li
eAlgebra R L₂], ⇑(LieHom.snd R L₁ L₂) = Prod.snd
参数：LieHom.snd R L₁ L₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_snd : ⇑(snd R L₁ L₂) = Prod.snd := rfl
/-
**LieHom.fst_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：fst_surjective : Function.Surjective (fst R L₁ L₂)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_surjective : Function.Surjective (fst R L₁ L₂) := fun x => ⟨(x, 0), rfl⟩
/-
**LieHom.snd_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：snd_surjective : Function.Surjective (snd R L₁ L₂)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_surjective : Function.Surjective (snd R L₁ L₂) := fun x => ⟨(0, x), rfl⟩

/-- The prod of two Lie algebra homomorphisms is a Lie algebra homomorphism. -/
@[simps!]
/-
**LieHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：prod (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂) : L ->ₗ⁅R⁆ L₁ × L₂ where toLinear
Map
参数：f : L ->ₗ⁅R⁆ L₁；g : L ->ₗ⁅R⁆ L₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prod of two Lie algebra homomorphisms is a Lie algebra homomorphism.
-/
def prod (f : L →ₗ⁅R⁆ L₁) (g : L →ₗ⁅R⁆ L₂) : L →ₗ⁅R⁆ L₁ × L₂ where
  toLinearMap := LinearMap.prod f g
  map_lie' := by simp
/-
**LieHom.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：coe_prod (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂) : ⇑(f.prod g) = Function.prod
 f g
参数：f : L ->ₗ⁅R⁆ L₁；g : L ->ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (f : L →ₗ⁅R⁆ L₁) (g : L →ₗ⁅R⁆ L₂) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[simp]
/-
**LieHom.fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：fst_prod (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂) : (fst R L₁ L₂).comp (prod f 
g) = f
参数：f : L ->ₗ⁅R⁆ L₁；g : L ->ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_prod (f : L →ₗ⁅R⁆ L₁) (g : L →ₗ⁅R⁆ L₂) : (fst R L₁ L₂).comp (prod f g) = f := rfl

@[simp]
/-
**LieHom.snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：snd_prod (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂) : (snd R L₁ L₂).comp (prod f 
g) = g
参数：f : L ->ₗ⁅R⁆ L₁；g : L ->ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_prod (f : L →ₗ⁅R⁆ L₁) (g : L →ₗ⁅R⁆ L₂) : (snd R L₁ L₂).comp (prod f g) = g := rfl

@[simp]
/-
**LieHom.pair_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：pair_fst_snd : prod (fst R L₁ L₂) (snd R L₁ L₂) = LieHom.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pair_fst_snd : prod (fst R L₁ L₂) (snd R L₁ L₂) = LieHom.id := rfl
/-
**LieHom.prod_comp** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：prod_comp (f : L₁ ->ₗ⁅R⁆ L₂) (g : L₁ ->ₗ⁅R⁆ L) (h : L ->ₗ⁅R⁆ L₁) : (f.prod
 g).comp h = (f.comp h).prod (g.comp h)
参数：f : L₁ ->ₗ⁅R⁆ L₂；g : L₁ ->ₗ⁅R⁆ L；h : L ->ₗ⁅R⁆ L₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_comp (f : L₁ →ₗ⁅R⁆ L₂) (g : L₁ →ₗ⁅R⁆ L)
    (h : L →ₗ⁅R⁆ L₁) : (f.prod g).comp h = (f.comp h).prod (g.comp h) :=
  rfl
/-
**LieHom.inl_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：inl_apply (x : L₁) : inl R L₁ L₂ x = (x, 0)
参数：x : L₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_apply (x : L₁) : inl R L₁ L₂ x = (x, 0) := rfl
/-
**LieHom.inr_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：inr_apply (x : L₂) : inr R L₁ L₂ x = (0, x)
参数：x : L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inr_apply (x : L₂) : inr R L₁ L₂ x = (0, x) := rfl
/-
**LieHom.coe_inl** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：∀ {R : Type u_1} {L₁ : Type u_2} {L₂ : Type u_3} [inst : CommRing R] [inst
_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : LieRing L₂] [inst_4 : Li
eAlgebra R L₂], ⇑(LieHom.inl R L₁ L₂) = fun x => (x, 0)
参数：LieHom.inl R L₁ L₂；x, 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_inl : (inl R L₁ L₂ : L₁ → L₁ × L₂) = fun x => (x, 0) := rfl
/-
**LieHom.coe_inr** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：∀ {R : Type u_1} {L₁ : Type u_2} {L₂ : Type u_3} [inst : CommRing R] [inst
_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : LieRing L₂] [inst_4 : Li
eAlgebra R L₂], ⇑(LieHom.inr R L₁ L₂) = Prod.mk 0
参数：LieHom.inr R L₁ L₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_inr : (inr R L₁ L₂ : L₂ → L₁ × L₂) = Prod.mk 0 := rfl
/-
**LieHom.inl_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：inl_injective : Function.Injective (inl R L₁ L₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem inl_injective : Function.Injective (inl R L₁ L₂) := fun _ => by simp
/-
**LieHom.inr_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：inr_injective : Function.Injective (inr R L₁ L₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem inr_injective : Function.Injective (inr R L₁ L₂) := fun _ => by simp

section
variable (R L₁ L₂)

/-
**LieHom.range_inl** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：range_inl : range (inl R L₁ L₂) = ker (snd R L₁ L₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.toSubmodule_inj`：toSubmodule_inj (L₁' L₂' : LieSubalgebra 
R L) : (L₁' : Submodule R L) = (L₂' : Submodule R L) ↔ L₁' = L₂'
· 使用定理 `LieHom.range_toSubmodule`：range_toSubmodule : (f.range : Submodule R L')
 = LinearMap.range (f : L ->ₗ[R] L')
· 使用定理 `LieIdeal.toLieSubalgebra_toSubmodule`：LieIdeal.toLieSubalgebra_toSubmodu
le (I : LieIdeal R L) : ((I : LieSubalgebra R L) : Submodule R L) = LieSubmodule
.toSubmodule I
· 使用定理 `LieHom.ker_toSubmodule`：ker_toSubmodule : LieSubmodule.toSubmodule (ker 
f) = LinearMap.ker (f : L ->ₗ[R] L')
· 使用定理 `LinearMap.range_inl`：range_inl : range (inl R M M₂) = ker (snd R M M₂)
-/
theorem range_inl : range (inl R L₁ L₂) = ker (snd R L₁ L₂) := by
  rw [← LieSubalgebra.toSubmodule_inj, range_toSubmodule, LieIdeal.toLieSubalgebra_toSubmodule,
    ker_toSubmodule]
  exact LinearMap.range_inl R L₁ L₂
/-
**LieHom.ker_snd** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：ker_snd : ker (snd R L₁ L₂) = range (inl R L₁ L₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.range_inl`：range_inl : range (inl R L₁ L₂) = ker (snd R L₁ L₂)
-/
theorem ker_snd : ker (snd R L₁ L₂) = range (inl R L₁ L₂) :=
  Eq.symm <| range_inl R L₁ L₂
/-
**LieHom.range_inr** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：range_inr : range (inr R L₁ L₂) = ker (fst R L₁ L₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.toSubmodule_inj`：toSubmodule_inj (L₁' L₂' : LieSubalgebra 
R L) : (L₁' : Submodule R L) = (L₂' : Submodule R L) ↔ L₁' = L₂'
· 使用定理 `LieHom.range_toSubmodule`：range_toSubmodule : (f.range : Submodule R L')
 = LinearMap.range (f : L ->ₗ[R] L')
· 使用定理 `LieIdeal.toLieSubalgebra_toSubmodule`：LieIdeal.toLieSubalgebra_toSubmodu
le (I : LieIdeal R L) : ((I : LieSubalgebra R L) : Submodule R L) = LieSubmodule
.toSubmodule I
· 使用定理 `LieHom.ker_toSubmodule`：ker_toSubmodule : LieSubmodule.toSubmodule (ker 
f) = LinearMap.ker (f : L ->ₗ[R] L')
· 使用定理 `LinearMap.range_inr`：range_inr : range (inr R M M₂) = ker (fst R M M₂)
-/
theorem range_inr : range (inr R L₁ L₂) = ker (fst R L₁ L₂) := by
  rw [← LieSubalgebra.toSubmodule_inj, range_toSubmodule, LieIdeal.toLieSubalgebra_toSubmodule,
    ker_toSubmodule]
  exact LinearMap.range_inr R L₁ L₂
/-
**LieHom.ker_fst** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：ker_fst : ker (fst R L₁ L₂) = range (inr R L₁ L₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.range_inr`：range_inr : range (inr R L₁ L₂) = ker (fst R L₁ L₂)
-/
theorem ker_fst : ker (fst R L₁ L₂) = range (inr R L₁ L₂) :=
  Eq.symm <| range_inr R L₁ L₂
/-
**LieHom.fst_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：∀ (R : Type u_1) (L₁ : Type u_2) (L₂ : Type u_3) [inst : CommRing R] [inst
_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : LieRing L₂] [inst_4 : Li
eAlgebra R L₂], (LieHom.fst R L₁ L₂).comp (LieHom.inl R L₁ L₂) = LieHom.id
参数：R : Type u_1；L₁ : Type u_2；L₂ : Type u_3；LieHom.fst R L₁ L₂；LieHom.inl R L₁ L
₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_comp_inl : (fst R L₁ L₂).comp (inl R L₁ L₂) = id := rfl
/-
**LieHom.snd_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：∀ (R : Type u_1) (L₁ : Type u_2) (L₂ : Type u_3) [inst : CommRing R] [inst
_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : LieRing L₂] [inst_4 : Li
eAlgebra R L₂], (LieHom.snd R L₁ L₂).comp (LieHom.inl R L₁ L₂) = 0
参数：R : Type u_1；L₁ : Type u_2；L₂ : Type u_3；LieHom.snd R L₁ L₂；LieHom.inl R L₁ L
₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_comp_inl : (snd R L₁ L₂).comp (inl R L₁ L₂) = 0 := rfl
/-
**LieHom.fst_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：∀ (R : Type u_1) (L₁ : Type u_2) (L₂ : Type u_3) [inst : CommRing R] [inst
_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : LieRing L₂] [inst_4 : Li
eAlgebra R L₂], (LieHom.fst R L₁ L₂).comp (LieHom.inr R L₁ L₂) = 0
参数：R : Type u_1；L₁ : Type u_2；L₂ : Type u_3；LieHom.fst R L₁ L₂；LieHom.inr R L₁ L
₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_comp_inr : (fst R L₁ L₂).comp (inr R L₁ L₂) = 0 := rfl
/-
**LieHom.snd_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：∀ (R : Type u_1) (L₁ : Type u_2) (L₂ : Type u_3) [inst : CommRing R] [inst
_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : LieRing L₂] [inst_4 : Li
eAlgebra R L₂], (LieHom.snd R L₁ L₂).comp (LieHom.inr R L₁ L₂) = LieHom.id
参数：R : Type u_1；L₁ : Type u_2；L₂ : Type u_3；LieHom.snd R L₁ L₂；LieHom.inr R L₁ L
₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_comp_inr : (snd R L₁ L₂).comp (inr R L₁ L₂) = id := rfl
/-
**LieHom.inl_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：inl_eq_prod : inl R L₁ L₂ = prod LieHom.id 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_eq_prod : inl R L₁ L₂ = prod LieHom.id 0 :=
  rfl
/-
**LieHom.inr_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：inr_eq_prod : inr R L₁ L₂ = prod 0 LieHom.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inr_eq_prod : inr R L₁ L₂ = prod 0 LieHom.id :=
  rfl
/-
**LieHom.prod_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：prod_ext_iff {f g : L₁ × L₂ ->ₗ⁅R⁆ L} : f = g ↔ f.comp (inl _ _ _) = g.com
p (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.prod_ext_iff`：prod_ext_iff {f g : M × M₂ ->ₗ[R] M₃} : f = g ↔ 
f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _
)
-/
theorem prod_ext_iff {f g : L₁ × L₂ →ₗ⁅R⁆ L} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) := by
  simp_rw [LieHom.ext_iff]
  have h := LinearMap.prod_ext_iff (f := f.toLinearMap) (g := g.toLinearMap)
  simp_rw [LinearMap.ext_iff] at h
  exact h

/--
Split equality of Lie algebra homomorphisms from a product into Lie algebra homomorphism over
each component, to allow `ext` to apply lemmas specific to `L₁ →ₗ L` and `L₂ →ₗ L`.

See note [partially-applied ext lemmas]. -/
@[ext 1100]
/-
**LieHom.prod_ext** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：prod_ext {f g : L₁ × L₂ ->ₗ⁅R⁆ L} (hl : f.comp (inl _ _ _) = g.comp (inl _
 _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g
参数：hl : f.comp (inl _ _ _) = g.comp (inl _ _ _)；hr : f.comp (inr _ _ _) = g.comp
 (inr _ _ _)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieHom.prod_ext_iff`：prod_ext_iff {f g : L₁ × L₂ ->ₗ⁅R⁆ L} : f = g ↔ f.c
omp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _)

--- 原说明 ---
Split equality of Lie algebra homomorphisms from a product into Lie algebra homo
morphism over
each component, to allow `ext` to apply lemmas specific to `L₁ →ₗ L` and `L₂ →ₗ 
L`.

See note [partially-applied ext lemmas].
-/
theorem prod_ext {f g : L₁ × L₂ →ₗ⁅R⁆ L} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g := by
  refine (prod_ext_iff R L₁ L₂).mpr ⟨hl,hr⟩

end

/-- `Prod.map` of two Lie algebra homomorphisms. -/
/-
**LieHom.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：prodMap (f : L₁ ->ₗ⁅R⁆ L₃) (g : L₂ ->ₗ⁅R⁆ L₄) : L₁ × L₂ ->ₗ⁅R⁆ L₃ × L₄
参数：f : L₁ ->ₗ⁅R⁆ L₃；g : L₂ ->ₗ⁅R⁆ L₄。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.map` of two Lie algebra homomorphisms.
-/
def prodMap (f : L₁ →ₗ⁅R⁆ L₃) (g : L₂ →ₗ⁅R⁆ L₄) : L₁ × L₂ →ₗ⁅R⁆ L₃ × L₄ :=
  (f.comp (fst R L₁ L₂)).prod (g.comp (snd R L₁ L₂))
/-
**LieHom.coe_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：coe_prodMap (f : L₁ ->ₗ⁅R⁆ L₃) (g : L₂ ->ₗ⁅R⁆ L₄) : ⇑(prodMap f g) = Prod.
map f g
参数：f : L₁ ->ₗ⁅R⁆ L₃；g : L₂ ->ₗ⁅R⁆ L₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodMap (f : L₁ →ₗ⁅R⁆ L₃) (g : L₂ →ₗ⁅R⁆ L₄) : ⇑(prodMap f g) = Prod.map f g :=
  rfl

@[simp]
/-
**LieHom.prodMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：prodMap_apply (f : L₁ ->ₗ⁅R⁆ L₃) (g : L₂ ->ₗ⁅R⁆ L₄) (x) : f.prodMap g x = 
(f x.1, g x.2)
参数：f : L₁ ->ₗ⁅R⁆ L₃；g : L₂ ->ₗ⁅R⁆ L₄；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_apply (f : L₁ →ₗ⁅R⁆ L₃) (g : L₂ →ₗ⁅R⁆ L₄) (x) : f.prodMap g x = (f x.1, g x.2) :=
  rfl

@[simp]
/-
**LieHom.prodMap_id** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：prodMap_id : (id : L ->ₗ⁅R⁆ L).prodMap (id : L₁ ->ₗ⁅R⁆ L₁) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_id : (id : L →ₗ⁅R⁆ L).prodMap (id : L₁ →ₗ⁅R⁆ L₁) = id :=
  rfl

@[simp]
/-
**LieHom.prodMap_one** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：prodMap_one : (1 : L ->ₗ⁅R⁆ L).prodMap (1 : L₁ ->ₗ⁅R⁆ L₁) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_one : (1 : L →ₗ⁅R⁆ L).prodMap (1 : L₁ →ₗ⁅R⁆ L₁) = 1 :=
  rfl
/-
**LieHom.prodMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：prodMap_comp (f₁₂ : L₁ ->ₗ⁅R⁆ L₂) (f₂₃ : L₂ ->ₗ⁅R⁆ L₃) (g₁₂ : L₄ ->ₗ⁅R⁆ L₅
) (g₂₃ : L₅ ->ₗ⁅R⁆ L₆) : (f₂₃.prodMap g₂₃).comp (f₁₂.prodMap g₁₂) = (f₂₃.comp f₁
₂).prodMap (g₂₃.comp g₁₂)
参数：f₁₂ : L₁ ->ₗ⁅R⁆ L₂；f₂₃ : L₂ ->ₗ⁅R⁆ L₃；g₁₂ : L₄ ->ₗ⁅R⁆ L₅；g₂₃ : L₅ ->ₗ⁅R⁆ L₆。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_comp (f₁₂ : L₁ →ₗ⁅R⁆ L₂) (f₂₃ : L₂ →ₗ⁅R⁆ L₃) (g₁₂ : L₄ →ₗ⁅R⁆ L₅)
    (g₂₃ : L₅ →ₗ⁅R⁆ L₆) :
    (f₂₃.prodMap g₂₃).comp (f₁₂.prodMap g₁₂) = (f₂₃.comp f₁₂).prodMap (g₂₃.comp g₁₂) :=
  rfl

@[simp]
/-
**LieHom.prodMap_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：prodMap_zero : (0 : L₁ ->ₗ⁅R⁆ L₃).prodMap (0 : L₂ ->ₗ⁅R⁆ L₄) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_zero : (0 : L₁ →ₗ⁅R⁆ L₃).prodMap (0 : L₂ →ₗ⁅R⁆ L₄) = 0 :=
  rfl

end LieHom

variable (R L₁ L₂) in
/-- The map `(x, y) ↦ (y, x)` as a Lie equivalence. -/
/-
**LieEquiv.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `LieEquiv`。
形式化陈述：(R : Type u_1) →   (L₁ : Type u_2) →     (L₂ : Type u_3) →       [inst : C
ommRing R] →         [inst_1 : LieRing L₁] →           [inst_2 : LieAlgebra R L₁
] → [inst_3 : LieRing L₂] → [inst_4 : LieAlgebra R L₂] → (L₁ × L₂) ≃ₗ⁅R⁆ L₂ × L₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `(x, y) ↦ (y, x)` as a Lie equivalence.
-/
@[simps!] def LieEquiv.prodComm : (L₁ × L₂) ≃ₗ⁅R⁆ L₂ × L₁ where
  __ := LinearEquiv.prodComm R L₁ L₂
  map_lie' := by simp

end

