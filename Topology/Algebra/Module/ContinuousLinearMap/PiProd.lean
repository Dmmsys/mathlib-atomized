/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Continuous linear maps on products and Pi types

In this file, we collect various constructions relating continuous linear maps with (binary or
arbitrary) products.

## Main definitions

Binary products (viewed as categorical products):

* `ContinuousLinearMap.fst R M₁ M₂ : M₁ × M₂ →L[R] M₁` and
  `ContinuousLinearMap.snd R M₁ M₂ : M₁ × M₂ →L[R] M₂` are the two projections, given
  respectively by `fst (x, y) = x` and `snd (x, y) = y`. These are the continuous versions
  of `LinearMap.fst` and `LinearMap.snd`.
* `ContinuousLinearMap.prod f₁ f₂` is the continuous linear map `M →L[R] N₁ × N₂` given by two
  continuous linear maps `f₁ : M →L[R] N₁` and `f₂ : M →L[R] N₂`. This is the continuous version
  of `LinearMap.prod`.
* `ContinuousLinearMap.prodEquiv` shows that the above is a bijection: every continuous linear
  map to a product is obtained this way. In other words, this is the universal property of the
  product.
* `ContinuousLinearMap.prodMap f₁ f₂` is the continuous linear map `M₁ × M₂ →L[R] N₁ × N₂` given by
  two continuous linear maps `f₁ : M₁ →L[R] N₁` and `f₂ : M₂ →L[R] N₂`. This is the continuous
  version of `LinearMap.prodMap`.

Binary products (viewed as categorical coproducts):

* `ContinuousLinearMap.inl R M₁ M₂ : M₁ →L[R] M₁ × M₂` and
  `ContinuousLinearMap.inr R M₁ M₂ : M₂ →L[R] M₁ × M₂` are the two inclusions, given
  respectively by `inl x = (x, 0)` and `inr x = (0, x)`. These are the continuous versions
  of `LinearMap.inl` and `LinearMap.inr`.
* `ContinuousLinearMap.coprod f₁ f₂` is the continuous linear map ` M₁ × M₂ →L[R] N` given by
  two continuous linear maps `f₁ : M₁ →L[R] N` and `f₂ : M₂ →L[R] N`. This is the continuous
  version of `LinearMap.coprod`.
* `ContinuousLinearMap.coprodEquiv` shows that the above is a bijection: every continuous linear
  map from a (binary) product is obtained this way. In other words, this is the universal property
  of the coproduct.

Indexed products:

* `ContinuousLinearMap.pi f` is the continuous linear map `M →L[R] (Π i, N i)` given by a family
  `f₁ : Π i, M →L[R] N i` of continuous linear maps. This is the continuous version
  of `LinearMap.pi`.
* `ContinuousLinearMap.piMap f` is the continuous linear map `(Π i, M i) →L[R] (Π i, N i)` given by
  a family `f : Π i, M i →L[R] N i` of continuous linear maps. This is the continuous
  version of `LinearMap.piMap`.
* `ContinuousLinearMap.proj j : (Π i, M i) →L[R] M j` is the projection given by
  `proj i f = f i`. This is the continuous version of `LinearMap.proj`.
-/

@[expose] public section

assert_not_exists TrivialStar

open LinearMap (ker range)
open Topology Filter Pointwise

universe u v w u'

namespace ContinuousLinearMap

section Semiring

/-!
### Properties that hold for non-necessarily commutative semirings.
-/

variable
  {R : Type*} [Semiring R]
  {M₁ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R M₄]

set_option backward.defeqAttrib.useBackward true in
/-- The Cartesian product of two bounded linear maps, as a bounded linear map. -/
/-
**ContinuousLinearMap.prod** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：{R : Type u_1} →   [inst : Semiring R] →     {M₁ : Type u_2} →       [inst
_1 : TopologicalSpace M₁] →         [inst_2 : AddCommMonoid M₁] →           [ins
t_3 : _root_.Module R M₁] →             {M₂ : Type u_3} →               [inst_4 
: TopologicalSpace M₂] →                 [inst_5 : AddCommMonoid M₂] →          
         [inst_6 : _root_.Module R M₂] →                     {M₃ : Type u_4} →  
                     [inst_7 : TopologicalSpace M₃] →                         [i
nst_8 : AddCommMonoid M₃] →                           [inst_9 : _root_.Module R 
M₃] → (M₁ →L[R] M₂) → (M₁ →L[R] M₃) → M₁ →L[R] M₂ × M₃
参数：M₁ →L[R] M₂；M₁ →L[R] M₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartesian product of two bounded linear maps, as a bounded linear map.
-/
protected def prod (f₁ : M₁ →L[R] M₂) (f₂ : M₁ →L[R] M₃) :
    M₁ →L[R] M₂ × M₃ where
  toLinearMap := .prod f₁ f₂

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_prod (f₁ : M₁ ->L[R] M₂) (f₂ : M₁ ->L[R] M₃) : (f₁.prod f₂ : M₁ ->ₗ[R]
 M₂ × M₃) = LinearMap.prod f₁ f₂
参数：f₁ : M₁ ->L[R] M₂；f₂ : M₁ ->L[R] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (f₁ : M₁ →L[R] M₂) (f₂ : M₁ →L[R] M₃) :
    (f₁.prod f₂ : M₁ →ₗ[R] M₂ × M₃) = LinearMap.prod f₁ f₂ :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：prod_apply (f₁ : M₁ ->L[R] M₂) (f₂ : M₁ ->L[R] M₃) (x : M₁) : f₁.prod f₂ x
 = (f₁ x, f₂ x)
参数：f₁ : M₁ ->L[R] M₂；f₂ : M₁ ->L[R] M₃；x : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_apply (f₁ : M₁ →L[R] M₂) (f₂ : M₁ →L[R] M₃) (x : M₁) :
    f₁.prod f₂ x = (f₁ x, f₂ x) :=
  rfl

section

variable (R M₁ M₂)

/-- The left injection into a product is a continuous linear map. -/
/-
**ContinuousLinearMap.inl** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：inl : M₁ ->L[R] M₁ × M₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left injection into a product is a continuous linear map.
-/
def inl : M₁ →L[R] M₁ × M₂ :=
  (ContinuousLinearMap.id R M₁).prod 0

/-- The right injection into a product is a continuous linear map. -/
/-
**ContinuousLinearMap.inr** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：inr : M₂ ->L[R] M₁ × M₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right injection into a product is a continuous linear map.
-/
def inr : M₂ →L[R] M₁ × M₂ :=
  (0 : M₂ →L[R] M₁).prod (.id R M₂)

end

@[simp]
/-
**ContinuousLinearMap.inl_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：inl_apply (x : M₁) : inl R M₁ M₂ x = (x, 0)
参数：x : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_apply (x : M₁) : inl R M₁ M₂ x = (x, 0) :=
  rfl

@[simp]
/-
**ContinuousLinearMap.inr_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：inr_apply (x : M₂) : inr R M₁ M₂ x = (0, x)
参数：x : M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inr_apply (x : M₂) : inr R M₁ M₂ x = (0, x) :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_inl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_inl : (inl R M₁ M₂ : M₁ ->ₗ[R] M₁ × M₂) = LinearMap.inl R M₁ M₂
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inl : (inl R M₁ M₂ : M₁ →ₗ[R] M₁ × M₂) = LinearMap.inl R M₁ M₂ :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_inr** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_inr : (inr R M₁ M₂ : M₂ ->ₗ[R] M₁ × M₂) = LinearMap.inr R M₁ M₂
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inr : (inr R M₁ M₂ : M₂ →ₗ[R] M₁ × M₂) = LinearMap.inr R M₁ M₂ :=
  rfl
/-
**ContinuousLinearMap.comp_inl_add_comp_inr** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：comp_inl_add_comp_inr (L : M₁ × M₂ ->L[R] M₃) (v : M₁ × M₂) : L.comp (.inl
 R M₁ M₂) v.1 + L.comp (.inr R M₁ M₂) v.2 = L v
参数：L : M₁ × M₂ ->L[R] M₃；v : M₁ × M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_inl_add_comp_inr (L : M₁ × M₂ →L[R] M₃) (v : M₁ × M₂) :
    L.comp (.inl R M₁ M₂) v.1 + L.comp (.inr R M₁ M₂) v.2 = L v := by simp [← map_add]
/-
**ContinuousLinearMap.ker_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：ker_prod (f : M₁ ->L[R] M₂) (g : M₁ ->L[R] M₃) : ker (f.prod g : M₁ ->ₗ[R]
 M₂ × M₃) = ker (f : M₁ ->ₗ[R] M₂) ⊓ ker (g : M₁ ->ₗ[R] M₃)
参数：f : M₁ ->L[R] M₂；g : M₁ ->L[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_prod`：ker_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : ker (
prod f g) = ker f ⊓ ker g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ker_prod (f : M₁ →L[R] M₂) (g : M₁ →L[R] M₃) :
    ker (f.prod g : M₁ →ₗ[R] M₂ × M₃) = ker (f : M₁ →ₗ[R] M₂) ⊓ ker (g : M₁ →ₗ[R] M₃) := by
  simp

variable (R M₁ M₂)

/-- `Prod.fst` as a `ContinuousLinearMap`. -/
/-
**ContinuousLinearMap.fst** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：fst : M₁ × M₂ ->L[R] M₁ where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.fst` as a `ContinuousLinearMap`.
-/
def fst : M₁ × M₂ →L[R] M₁ where
  toLinearMap := LinearMap.fst R M₁ M₂

/-- `Prod.snd` as a `ContinuousLinearMap`. -/
/-
**ContinuousLinearMap.snd** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：snd : M₁ × M₂ ->L[R] M₂ where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.snd` as a `ContinuousLinearMap`.
-/
def snd : M₁ × M₂ →L[R] M₂ where
  toLinearMap := LinearMap.snd R M₁ M₂

variable {R M₁ M₂}

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_fst : ↑(fst R M₁ M₂) = LinearMap.fst R M₁ M₂
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fst : ↑(fst R M₁ M₂) = LinearMap.fst R M₁ M₂ :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_fst'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_fst' : ⇑(fst R M₁ M₂) = Prod.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fst' : ⇑(fst R M₁ M₂) = Prod.fst :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_snd** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_snd : ↑(snd R M₁ M₂) = LinearMap.snd R M₁ M₂
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_snd : ↑(snd R M₁ M₂) = LinearMap.snd R M₁ M₂ :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_snd'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_snd' : ⇑(snd R M₁ M₂) = Prod.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_snd' : ⇑(snd R M₁ M₂) = Prod.snd :=
  rfl

@[simp]
/-
**ContinuousLinearMap.fst_prod_snd** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：fst_prod_snd : (fst R M₁ M₂).prod (snd R M₁ M₂) = .id R (M₁ × M₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
-/
theorem fst_prod_snd : (fst R M₁ M₂).prod (snd R M₁ M₂) = .id R (M₁ × M₂) :=
  ext fun ⟨_x, _y⟩ => rfl

@[simp]
/-
**ContinuousLinearMap.fst_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：fst_comp_prod (f : M₁ ->L[R] M₂) (g : M₁ ->L[R] M₃) : (fst R M₂ M₃).comp (
f.prod g) = f
参数：f : M₁ ->L[R] M₂；g : M₁ ->L[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
-/
theorem fst_comp_prod (f : M₁ →L[R] M₂) (g : M₁ →L[R] M₃) :
    (fst R M₂ M₃).comp (f.prod g) = f :=
  ext fun _x => rfl

@[simp]
/-
**ContinuousLinearMap.snd_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：snd_comp_prod (f : M₁ ->L[R] M₂) (g : M₁ ->L[R] M₃) : (snd R M₂ M₃).comp (
f.prod g) = g
参数：f : M₁ ->L[R] M₂；g : M₁ ->L[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
-/
theorem snd_comp_prod (f : M₁ →L[R] M₂) (g : M₁ →L[R] M₃) :
    (snd R M₂ M₃).comp (f.prod g) = g :=
  ext fun _x => rfl
/-
**ContinuousLinearMap.fst_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M₁ : Type u_2} [inst_1 : Topological
Space M₁] [inst_2 : AddCommMonoid M₁]   [inst_3 : _root_.Module R M₁] {M₂ : Type
 u_3} [inst_4 : TopologicalSpace M₂] [inst_5 : AddCommMonoid M₂]   [inst_6 : _ro
ot_.Module R M₂],   ContinuousLinearMap.fst R M₁ M₂ ∘SL ContinuousLinearMap.inl 
R M₁ M₂ = ContinuousLinearMap.id R M₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_comp_inl : fst R M₁ M₂ ∘L inl R M₁ M₂ = .id R M₁ := rfl
/-
**ContinuousLinearMap.fst_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M₁ : Type u_2} [inst_1 : Topological
Space M₁] [inst_2 : AddCommMonoid M₁]   [inst_3 : _root_.Module R M₁] {M₂ : Type
 u_3} [inst_4 : TopologicalSpace M₂] [inst_5 : AddCommMonoid M₂]   [inst_6 : _ro
ot_.Module R M₂], ContinuousLinearMap.fst R M₁ M₂ ∘SL ContinuousLinearMap.inr R 
M₁ M₂ = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_comp_inr : fst R M₁ M₂ ∘L inr R M₁ M₂ = 0 := rfl
/-
**ContinuousLinearMap.snd_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M₁ : Type u_2} [inst_1 : Topological
Space M₁] [inst_2 : AddCommMonoid M₁]   [inst_3 : _root_.Module R M₁] {M₂ : Type
 u_3} [inst_4 : TopologicalSpace M₂] [inst_5 : AddCommMonoid M₂]   [inst_6 : _ro
ot_.Module R M₂], ContinuousLinearMap.snd R M₁ M₂ ∘SL ContinuousLinearMap.inl R 
M₁ M₂ = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_comp_inl : snd R M₁ M₂ ∘L inl R M₁ M₂ = 0 := rfl
/-
**ContinuousLinearMap.snd_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M₁ : Type u_2} [inst_1 : Topological
Space M₁] [inst_2 : AddCommMonoid M₁]   [inst_3 : _root_.Module R M₁] {M₂ : Type
 u_3} [inst_4 : TopologicalSpace M₂] [inst_5 : AddCommMonoid M₂]   [inst_6 : _ro
ot_.Module R M₂],   ContinuousLinearMap.snd R M₁ M₂ ∘SL ContinuousLinearMap.inr 
R M₁ M₂ = ContinuousLinearMap.id R M₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_comp_inr : snd R M₁ M₂ ∘L inr R M₁ M₂ = .id R M₂ := rfl

/-- `Prod.map` of two continuous linear maps. -/
/-
**ContinuousLinearMap.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：prodMap (f₁ : M₁ ->L[R] M₂) (f₂ : M₃ ->L[R] M₄) : M₁ × M₃ ->L[R] M₂ × M₄
参数：f₁ : M₁ ->L[R] M₂；f₂ : M₃ ->L[R] M₄。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.map` of two continuous linear maps.
-/
def prodMap (f₁ : M₁ →L[R] M₂) (f₂ : M₃ →L[R] M₄) :
    M₁ × M₃ →L[R] M₂ × M₄ :=
  (f₁.comp (fst R M₁ M₃)).prod (f₂.comp (snd R M₁ M₃))

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：coe_prodMap (f₁ : M₁ ->L[R] M₂) (f₂ : M₃ ->L[R] M₄) : ↑(f₁.prodMap f₂) = (
f₁ : M₁ ->ₗ[R] M₂).prodMap (f₂ : M₃ ->ₗ[R] M₄)
参数：f₁ : M₁ ->L[R] M₂；f₂ : M₃ ->L[R] M₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodMap (f₁ : M₁ →L[R] M₂)
    (f₂ : M₃ →L[R] M₄) : ↑(f₁.prodMap f₂) = (f₁ : M₁ →ₗ[R] M₂).prodMap (f₂ : M₃ →ₗ[R] M₄) :=
  rfl

@[simp, norm_cast]
/-
**ContinuousLinearMap.coe_prodMap'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：coe_prodMap' (f₁ : M₁ ->L[R] M₂) (f₂ : M₃ ->L[R] M₄) : ⇑(f₁.prodMap f₂) = 
Prod.map f₁ f₂
参数：f₁ : M₁ ->L[R] M₂；f₂ : M₃ ->L[R] M₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodMap' (f₁ : M₁ →L[R] M₂)
    (f₂ : M₃ →L[R] M₄) : ⇑(f₁.prodMap f₂) = Prod.map f₁ f₂ :=
  rfl

end Semiring

section Pi

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂] {ι : Type*} {φ : ι → Type*}
  [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

/-- `pi` construction for continuous linear functions. From a family of continuous linear functions
it produces a continuous linear function into a family of topological modules. -/
/-
**ContinuousLinearMap.pi** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：pi (f : forall i, M ->L[R] φ i) : M ->L[R] forall i, φ i where toLinearMap
参数：f : forall i, M ->L[R] φ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pi` construction for continuous linear functions. From a family of continuous l
inear functions
it produces a continuous linear function into a family of topological modules.
-/
def pi (f : ∀ i, M →L[R] φ i) : M →L[R] ∀ i, φ i where
  toLinearMap := .pi fun i => f i

@[simp]
/-
**ContinuousLinearMap.coe_pi'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_pi' (f : forall i, M ->L[R] φ i) : ⇑(pi f) = fun c i => f i c
参数：f : forall i, M ->L[R] φ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pi' (f : ∀ i, M →L[R] φ i) : ⇑(pi f) = fun c i => f i c :=
  rfl

@[simp]
/-
**ContinuousLinearMap.coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_pi (f : forall i, M ->L[R] φ i) : (pi f : M ->ₗ[R] forall i, φ i) = Li
nearMap.pi fun i => f i
参数：f : forall i, M ->L[R] φ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pi (f : ∀ i, M →L[R] φ i) : (pi f : M →ₗ[R] ∀ i, φ i) = LinearMap.pi fun i => f i :=
  rfl
/-
**ContinuousLinearMap.pi_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：pi_apply (f : forall i, M ->L[R] φ i) (c : M) (i : ι) : pi f c i = f i c
参数：f : forall i, M ->L[R] φ i；c : M；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_apply (f : ∀ i, M →L[R] φ i) (c : M) (i : ι) : pi f c i = f i c :=
  rfl
/-
**ContinuousLinearMap.pi_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：pi_eq_zero (f : forall i, M ->L[R] φ i) : pi f = 0 ↔ forall i, f i = 0
参数：f : forall i, M ->L[R] φ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem pi_eq_zero (f : ∀ i, M →L[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 := by
  simp only [ContinuousLinearMap.ext_iff, pi_apply, funext_iff]
  exact forall_comm
/-
**ContinuousLinearMap.pi_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：pi_zero : pi (fun _ => 0 : forall i, M ->L[R] φ i) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
-/
theorem pi_zero : pi (fun _ => 0 : ∀ i, M →L[R] φ i) = 0 :=
  ext fun _ => rfl
/-
**ContinuousLinearMap.pi_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：pi_comp (f : forall i, M ->L[R] φ i) (g : M₂ ->L[R] M) : (pi f).comp g = p
i fun i => (f i).comp g
参数：f : forall i, M ->L[R] φ i；g : M₂ ->L[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_comp (f : ∀ i, M →L[R] φ i) (g : M₂ →L[R] M) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl

/-- The projections from a family of topological modules are continuous linear maps. -/
/-
**ContinuousLinearMap.proj** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：proj (i : ι) : (forall i, φ i) ->L[R] φ i where toLinearMap
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projections from a family of topological modules are continuous linear maps.
-/
def proj (i : ι) : (∀ i, φ i) →L[R] φ i where
  toLinearMap := .proj i

@[simp]
/-
**ContinuousLinearMap.proj_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：proj_apply (i : ι) (b : forall i, φ i) : (proj i : (forall i, φ i) ->L[R] 
φ i) b = b i
参数：i : ι；b : forall i, φ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem proj_apply (i : ι) (b : ∀ i, φ i) : (proj i : (∀ i, φ i) →L[R] φ i) b = b i :=
  rfl

@[simp]
/-
**ContinuousLinearMap.proj_pi** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：proj_pi (f : forall i, M₂ ->L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i
参数：f : forall i, M₂ ->L[R] φ i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem proj_pi (f : ∀ i, M₂ →L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i := rfl

@[simp]
/-
**ContinuousLinearMap.coe_proj** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_proj (i : ι) : (proj i).toLinearMap = (LinearMap.proj i : ((i : ι) -> 
φ i) ->ₗ[R] _)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_proj (i : ι) : (proj i).toLinearMap = (LinearMap.proj i : ((i : ι) → φ i) →ₗ[R] _) :=
  rfl

@[simp]
/-
**ContinuousLinearMap.pi_proj** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：pi_proj : pi proj = .id R (forall i, φ i)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_proj : pi proj = .id R (∀ i, φ i) := rfl

@[simp]
/-
**ContinuousLinearMap.pi_proj_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：pi_proj_comp (f : M₂ ->L[R] forall i, φ i) : pi (proj · ∘L f) = f
参数：f : M₂ ->L[R] forall i, φ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_proj_comp (f : M₂ →L[R] ∀ i, φ i) : pi (proj · ∘L f) = f := rfl
/-
**ContinuousLinearMap.iInf_ker_proj** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：iInf_ker_proj : (⨅ i, ker (proj i : (forall i, φ i) ->L[R] φ i).toLinearMa
p : Submodule R (forall i, φ i)) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.iInf_ker_proj`：iInf_ker_proj : (⨅ i, ker (proj i : ((i : ι) ->
 φ i) ->ₗ[R] φ i) : Submodule R ((i : ι) -> φ i)) = ⊥
-/
theorem iInf_ker_proj :
    (⨅ i, ker (proj i : (∀ i, φ i) →L[R] φ i).toLinearMap : Submodule R (∀ i, φ i)) = ⊥ :=
  LinearMap.iInf_ker_proj

section PiMap
variable {ψ : ι → Type*} [∀ i, TopologicalSpace (ψ i)] [∀ i, AddCommMonoid (ψ i)]
  [∀ i, Module R (ψ i)]

/-- Construct a continuous linear map between two (dependent) function spaces
by applying index-dependent linear maps to the coordinates.
A bundled version of `Pi.map`.

If the index type is finite, then this map can be seen as a “block diagonal” map
between indexed products of modules. -/
/-
**ContinuousLinearMap.piMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：piMap (f : forall i, φ i ->L[R] ψ i) : (forall i, φ i) ->L[R] (forall i, ψ
 i)
参数：f : forall i, φ i ->L[R] ψ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a continuous linear map between two (dependent) function spaces
by applying index-dependent linear maps to the coordinates.
A bundled version of `Pi.map`.

If the index type is finite, then this map can be seen as a “block diagonal” map
between indexed products of modules.
-/
def piMap (f : ∀ i, φ i →L[R] ψ i) : (∀ i, φ i) →L[R] (∀ i, ψ i) :=
  .pi fun i ↦ f i ∘L .proj i

@[simp]
/-
**ContinuousLinearMap.coe_piMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_piMap (f : forall i, φ i ->L[R] ψ i) : (piMap f : (forall i, φ i) ->ₗ[
R] (forall i, ψ i)) = .piMap fun i => f i
参数：f : forall i, φ i ->L[R] ψ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_piMap (f : ∀ i, φ i →L[R] ψ i) :
    (piMap f : (∀ i, φ i) →ₗ[R] (∀ i, ψ i)) = .piMap fun i ↦ f i :=
  rfl

@[simp]
/-
**ContinuousLinearMap.coe_piMap'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：coe_piMap' (f : forall i, φ i ->L[R] ψ i) : ⇑(piMap f) = Pi.map fun i => f
 i
参数：f : forall i, φ i ->L[R] ψ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_piMap' (f : ∀ i, φ i →L[R] ψ i) : ⇑(piMap f) = Pi.map fun i ↦ f i :=
  rfl

end PiMap

variable (R φ)

/-- Given a function `f : α → ι`, it induces a continuous linear function by right composition on
product types. For `f = Subtype.val`, this corresponds to forgetting some set of variables. -/
/-
**ContinuousLinearMap._root_.Pi.compRightL** 是 Mathlib 中的一个定义，位于命名空间 `Continuous
LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : α → ι`, it induces a continuous linear function by right c
omposition on
product types. For `f = Subtype.val`, this corresponds to forgetting some set of
 variables.
-/
def _root_.Pi.compRightL {α : Type*} (f : α → ι) : ((i : ι) → φ i) →L[R] ((i : α) → φ (f i)) where
  toFun := fun v i ↦ v (f i)
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp
/-
**ContinuousLinearMap._root_.Pi.compRightL_apply** 是 Mathlib 中的一个引理，位于命名空间 `Cont
inuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.Pi.compRightL_apply {α : Type*} (f : α → ι) (v : (i : ι) → φ i) (i : α) :
    Pi.compRightL R φ f v i = v (f i) := rfl

/-- `Pi.single` as a bundled continuous linear map. -/
@[simps! -fullyApplied]
/-
**ContinuousLinearMap.single** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：single [DecidableEq ι] (i : ι) : φ i ->L[R] (forall i, φ i) where toLinear
Map
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Pi.single` as a bundled continuous linear map.
-/
def single [DecidableEq ι] (i : ι) : φ i →L[R] (∀ i, φ i) where
  toLinearMap := .single R φ i
/-
**ContinuousLinearMap.sum_comp_single** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：sum_comp_single [Fintype ι] [DecidableEq ι] (L : (Π i, φ i) ->L[R] M) (v :
 Π i, φ i) : ∑ i, L.comp (.single R φ i) (v i) = L v
参数：L : (Π i, φ i) ->L[R] M；v : Π i, φ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.single_apply`：∀ (R : Type u_1) [inst : Semiring R] {
ι : Type u_4} (φ : ι → Type u_5) [inst_1 : (i : ι) → TopologicalSpace (φ i)]   [
inst_2 : (i : ι) → Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用引理 `LinearMap.sum_single_apply`：sum_single_apply [Fintype ι] [DecidableEq ι]
 (v : Π i, φ i) : ∑ i, Pi.single i (v i) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_comp_single [Fintype ι] [DecidableEq ι] (L : (Π i, φ i) →L[R] M) (v : Π i, φ i) :
    ∑ i, L.comp (.single R φ i) (v i) = L v := by
  simp [← map_sum, LinearMap.sum_single_apply]

end Pi

section Ring

variable {R : Type*} [Ring R]
  {M : Type*} [TopologicalSpace M] [AddCommGroup M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃] [Module R M₃]

/-
**ContinuousLinearMap.range_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：range_prod_eq {f : M ->L[R] M₂} {g : M ->L[R] M₃} (h : f.ker ⊔ g.ker = ⊤) 
: (f.prod g).range = f.range.prod g.range
参数：h : f.ker ⊔ g.ker = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.range_prod_eq`：range_prod_eq {f : M ->ₗ[R] M₂} {g : M ->ₗ[R] M
₃} (h : ker f ⊔ ker g = ⊤) : range (prod f g) = (range f).prod (range g)
-/
theorem range_prod_eq {f : M →L[R] M₂} {g : M →L[R] M₃} (h : f.ker ⊔ g.ker = ⊤) :
    (f.prod g).range = f.range.prod g.range :=
  LinearMap.range_prod_eq h
/-
**ContinuousLinearMap.ker_prod_ker_le_ker_coprod** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousLinearMap`。
形式化陈述：ker_prod_ker_le_ker_coprod (f : M ->L[R] M₃) (g : M₂ ->L[R] M₃) : f.ker.pr
od g.ker <= (f.coprod g).ker
参数：f : M ->L[R] M₃；g : M₂ ->L[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_prod_ker_le_ker_coprod`：ker_prod_ker_le_ker_coprod {M₂ : T
ype*} [AddCommMonoid M₂] [Module R M₂] {M₃ : Type*} [AddCommMonoid M₃] [Module R
 M₃] (f : M ->ₗ[R] M₃) (g …
-/
theorem ker_prod_ker_le_ker_coprod (f : M →L[R] M₃) (g : M₂ →L[R] M₃) :
    f.ker.prod g.ker ≤ (f.coprod g).ker :=
  LinearMap.ker_prod_ker_le_ker_coprod f.toLinearMap g.toLinearMap

end Ring

section SMul

variable
  {R : Type*} [Semiring R]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R M₃]

/-- `ContinuousLinearMap.prod` as an `Equiv`. -/
@[simps apply]
/-
**ContinuousLinearMap.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：prodEquiv : (M ->L[R] M₂) × (M ->L[R] M₃) ≃ (M ->L[R] M₂ × M₃) where toFun
 f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.prod` as an `Equiv`.
-/
def prodEquiv : (M →L[R] M₂) × (M →L[R] M₃) ≃ (M →L[R] M₂ × M₃) where
  toFun f := f.1.prod f.2
  invFun f := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩
/-
**ContinuousLinearMap.prod_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：prod_ext_iff {f g : M × M₂ ->L[R] M₃} : f = g ↔ f.comp (inl _ _ _) = g.com
p (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prod_ext_iff {f g : M × M₂ →L[R] M₃} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) := by
  simp only [← coe_inj, LinearMap.prod_ext_iff]
  rfl

@[ext]
/-
**ContinuousLinearMap.prod_ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：prod_ext {f g : M × M₂ ->L[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _
 _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g
参数：hl : f.comp (inl _ _ _) = g.comp (inl _ _ _)；hr : f.comp (inr _ _ _) = g.comp
 (inr _ _ _)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearMap.prod_ext_iff`：prod_ext_iff {f g : M × M₂ ->L[R] M₃} 
: f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp 
(inr _ _ _)
-/
theorem prod_ext {f g : M × M₂ →L[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
  prod_ext_iff.2 ⟨hl, hr⟩

variable (S : Type*) [Semiring S]
  [Module S M₂] [ContinuousAdd M₂] [SMulCommClass R S M₂] [ContinuousConstSMul S M₂]
  [Module S M₃] [ContinuousAdd M₃] [SMulCommClass R S M₃] [ContinuousConstSMul S M₃]

/-- `ContinuousLinearMap.prod` as a `LinearEquiv`.

See `ContinuousLinearMap.prodL` for the `ContinuousLinearEquiv` version. -/
@[simps apply]
/-
**ContinuousLinearMap.prod** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：{R : Type u_1} →   [inst : Semiring R] →     {M₁ : Type u_2} →       [inst
_1 : TopologicalSpace M₁] →         [inst_2 : AddCommMonoid M₁] →           [ins
t_3 : _root_.Module R M₁] →             {M₂ : Type u_3} →               [inst_4 
: TopologicalSpace M₂] →                 [inst_5 : AddCommMonoid M₂] →          
         [inst_6 : _root_.Module R M₂] →                     {M₃ : Type u_4} →  
                     [inst_7 : TopologicalSpace M₃] →                         [i
nst_8 : AddCommMonoid M₃] →                           [inst_9 : _root_.Module R 
M₃] → (M₁ →L[R] M₂) → (M₁ →L[R] M₃) → M₁ →L[R] M₂ × M₃
参数：M₁ →L[R] M₂；M₁ →L[R] M₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.prod` as a `LinearEquiv`.

See `ContinuousLinearMap.prodL` for the `ContinuousLinearEquiv` version.
-/
def prodₗ : ((M →L[R] M₂) × (M →L[R] M₃)) ≃ₗ[S] M →L[R] M₂ × M₃ :=
  { prodEquiv with
    map_add' := fun _f _g => rfl
    map_smul' := fun _c _f => rfl }

end SMul

section coprod

variable {R S M N M₁ M₂ : Type*}
  [Semiring R] [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace M₁] [TopologicalSpace M₂]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M] [ContinuousAdd M] [AddCommMonoid N] [Module R N]
  [ContinuousAdd N] [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- The continuous linear map given by `(x, y) ↦ f₁ x + f₂ y`. -/
@[simps! coe apply]
/-
**ContinuousLinearMap.coprod** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：coprod (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M) : M₁ × M₂ ->L[R] M where toLi
nearMap
参数：f₁ : M₁ ->L[R] M；f₂ : M₂ ->L[R] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous linear map given by `(x, y) ↦ f₁ x + f₂ y`.
-/
def coprod (f₁ : M₁ →L[R] M) (f₂ : M₂ →L[R] M) : M₁ × M₂ →L[R] M where
  toLinearMap := .coprod f₁ f₂
/-
**ContinuousLinearMap.coprod_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {M₁ : Type u_5} {M₂ : Type u_6} [inst : Se
miring R] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSpace M₁] [inst_3
 : TopologicalSpace M₂] [inst_4 : AddCommMonoid M] [inst_5 : _root_.Module R M] 
  [inst_6 : ContinuousAdd M] [inst_7 : AddCommMonoid M₁] [inst_8 : _root_.Module
 R M₁] [inst_9 : AddCommMonoid M₂]   [inst_10 : _root_.Module R M₂] (f₁ g₁ : M₁ 
→L[R] M) (f₂ g₂ : M₂ →L[R] M),   (f₁ + g₁).coprod (f₂ + g₂) = f₁.coprod f₂ + g₁.
coprod g₂
参数：f₁ g₁ : M₁ →L[R] M；f₂ g₂ : M₂ →L[R] M；f₁ + g₁；f₂ + g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.prod_ext`：prod_ext {f g : M × M₂ ->L[R] M₃} (hl : f.
comp (inl _ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ 
_ _)) : f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.coprod_apply`：∀ {R : Type u_1} {M : Type u_3} {M₁ : 
Type u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : TopologicalSpace M]   [i
nst_2 : TopologicalSpa…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.add_comp`：add_comp [ContinuousAdd M₃] (g₁ g₂ : M₂ ->
SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) : (g₁ + g₂) ∘SL f = g₁ ∘SL f + g₂ ∘SL f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
@[simp] lemma coprod_add (f₁ g₁ : M₁ →L[R] M) (f₂ g₂ : M₂ →L[R] M) :
    (f₁ + g₁).coprod (f₂ + g₂) = f₁.coprod f₂ + g₁.coprod g₂ := by ext <;> simp
/-
**ContinuousLinearMap.range_coprod** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：range_coprod (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M) : (f₁.coprod f₂).range 
= f₁.range ⊔ f₂.range
参数：f₁ : M₁ ->L[R] M；f₂ : M₂ ->L[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.range_coprod`：range_coprod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃
) : range (f.coprod g) = range f ⊔ range g
-/
lemma range_coprod (f₁ : M₁ →L[R] M) (f₂ : M₂ →L[R] M) :
    (f₁.coprod f₂).range = f₁.range ⊔ f₂.range := LinearMap.range_coprod ..
/-
**ContinuousLinearMap.comp_fst_add_comp_snd** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：comp_fst_add_comp_snd (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M) : f₁.comp (.fs
t _ _ _) + f₂.comp (.snd _ _ _) = f₁.coprod f₂
参数：f₁ : M₁ ->L[R] M；f₂ : M₂ ->L[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_fst_add_comp_snd (f₁ : M₁ →L[R] M) (f₂ : M₂ →L[R] M) :
    f₁.comp (.fst _ _ _) + f₂.comp (.snd _ _ _) = f₁.coprod f₂ := rfl
/-
**ContinuousLinearMap.comp_coprod** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：comp_coprod (f : M ->L[R] N) (g₁ : M₁ ->L[R] M) (g₂ : M₂ ->L[R] M) : f.com
p (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp g₂)
参数：f : M ->L[R] N；g₁ : M₁ ->L[R] M；g₂ : M₂ ->L[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
· 使用定理 `LinearMap.comp_coprod`：comp_coprod (f : M₃ ->ₗ[R] M₄) (g₁ : M ->ₗ[R] M₃)
 (g₂ : M₂ ->ₗ[R] M₃) : f.comp (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp g₂)
-/
lemma comp_coprod (f : M →L[R] N) (g₁ : M₁ →L[R] M) (g₂ : M₂ →L[R] M) :
    f.comp (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp g₂) :=
  coe_injective <| LinearMap.comp_coprod ..
/-
**ContinuousLinearMap.coprod_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {M₁ : Type u_5} {M₂ : Type u_6} [inst : Se
miring R] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSpace M₁] [inst_3
 : TopologicalSpace M₂] [inst_4 : AddCommMonoid M] [inst_5 : _root_.Module R M] 
  [inst_6 : ContinuousAdd M] [inst_7 : AddCommMonoid M₁] [inst_8 : _root_.Module
 R M₁] [inst_9 : AddCommMonoid M₂]   [inst_10 : _root_.Module R M₂] (f₁ : M₁ →L[
R] M) (f₂ : M₂ →L[R] M),   f₁.coprod f₂ ∘SL ContinuousLinearMap.inl R M₁ M₂ = f₁
参数：f₁ : M₁ →L[R] M；f₂ : M₂ →L[R] M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
· 使用定理 `LinearMap.coprod_inl`：coprod_inl (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) : 
(coprod f g).comp (inl R M M₂) = f
-/
@[simp] lemma coprod_comp_inl (f₁ : M₁ →L[R] M) (f₂ : M₂ →L[R] M) :
    (f₁.coprod f₂).comp (.inl _ _ _) = f₁ := coe_injective <| LinearMap.coprod_inl ..
/-
**ContinuousLinearMap.coprod_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {M₁ : Type u_5} {M₂ : Type u_6} [inst : Se
miring R] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSpace M₁] [inst_3
 : TopologicalSpace M₂] [inst_4 : AddCommMonoid M] [inst_5 : _root_.Module R M] 
  [inst_6 : ContinuousAdd M] [inst_7 : AddCommMonoid M₁] [inst_8 : _root_.Module
 R M₁] [inst_9 : AddCommMonoid M₂]   [inst_10 : _root_.Module R M₂] (f₁ : M₁ →L[
R] M) (f₂ : M₂ →L[R] M),   f₁.coprod f₂ ∘SL ContinuousLinearMap.inr R M₁ M₂ = f₂
参数：f₁ : M₁ →L[R] M；f₂ : M₂ →L[R] M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
· 使用定理 `LinearMap.coprod_inr`：coprod_inr (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) : 
(coprod f g).comp (inr R M M₂) = g
-/
@[simp] lemma coprod_comp_inr (f₁ : M₁ →L[R] M) (f₂ : M₂ →L[R] M) :
    (f₁.coprod f₂).comp (.inr _ _ _) = f₂ := coe_injective <| LinearMap.coprod_inr ..

@[simp]
/-
**ContinuousLinearMap.coprod_inl_inr** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：coprod_inl_inr : ContinuousLinearMap.coprod (.inl R M N) (.inr R M N) = .i
d R (M × N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `LinearMap.coprod_inl_inr`：coprod_inl_inr : coprod (inl R M M₂) (inr R M 
M₂) = LinearMap.id
-/
lemma coprod_inl_inr : ContinuousLinearMap.coprod (.inl R M N) (.inr R M N) = .id R (M × N) :=
  coe_injective <| LinearMap.coprod_inl_inr

@[simp]
/-
**ContinuousLinearMap.coprod_comp_inl_inr** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：coprod_comp_inl_inr [ContinuousAdd M₁] [ContinuousAdd M₂] (f : M × M₁ ->L[
R] M₂) : (f ∘L .inl R M M₁).coprod (f ∘L .inr R M M₁) = f
参数：f : M × M₁ ->L[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousLinearMap.comp_coprod`：comp_coprod (f : M ->L[R] N) (g₁ : M₁ -
>L[R] M) (g₂ : M₂ ->L[R] M) : f.comp (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp
 g₂)
· 使用引理 `ContinuousLinearMap.coprod_inl_inr`：coprod_inl_inr : ContinuousLinearMap
.coprod (.inl R M N) (.inr R M N) = .id R (M × N)
· 使用定理 `ContinuousLinearMap.comp_id`：comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R
₁ M₁ = f
-/
lemma coprod_comp_inl_inr [ContinuousAdd M₁] [ContinuousAdd M₂] (f : M × M₁ →L[R] M₂) :
    (f ∘L .inl R M M₁).coprod (f ∘L .inr R M M₁) = f := by
  rw [← ContinuousLinearMap.comp_coprod, coprod_inl_inr, comp_id]

/-- Taking the product of two maps with the same codomain is equivalent to taking the product of
their domains.
See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.

See `ContinuousLinearMap.coprodEquivL` for the `ContinuousLinearEquiv` version.
-/
@[simps]
/-
**ContinuousLinearMap.coprodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：coprodEquiv [ContinuousAdd M₁] [ContinuousAdd M₂] [Semiring S] [Module S M
] [ContinuousConstSMul S M] [SMulCommClass R S M] : ((M₁ ->L[R] M) × (M₂ ->L[R] 
M)) ≃ₗ[S] M₁ × M₂ ->L[R] M where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the product of two maps with the same codomain is equivalent to taking th
e product of
their domains.
See note [bundled maps over different rings] for why separate `R` and `S` semiri
ngs are used.

See `ContinuousLinearMap.coprodEquivL` for the `ContinuousLinearEquiv` version.
-/
def coprodEquiv [ContinuousAdd M₁] [ContinuousAdd M₂] [Semiring S] [Module S M]
    [ContinuousConstSMul S M] [SMulCommClass R S M] :
    ((M₁ →L[R] M) × (M₂ →L[R] M)) ≃ₗ[S] M₁ × M₂ →L[R] M where
  toFun f := f.1.coprod f.2
  invFun f := (f.comp (.inl ..), f.comp (.inr ..))
  left_inv f := by simp
  right_inv f := by simp [← comp_coprod f (.inl R M₁ M₂)]
  map_add' a b := coprod_add ..
  map_smul' r a := by
    dsimp
    ext <;> simp [smul_apply]

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [Module R M] [ContinuousAdd M] [AddCommMonoid M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂]

/-
**ContinuousLinearMap.ker_coprod_of_disjoint_range** 是 Mathlib 中的一个引理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：ker_coprod_of_disjoint_range {f₁ : M₁ ->L[R] M} {f₂ : M₂ ->L[R] M} (hf : D
isjoint f₁.range f₂.range) : (f₁.coprod f₂).ker = f₁.ker.prod f₂.ker
参数：hf : Disjoint f₁.range f₂.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_coprod_of_disjoint_range`：ker_coprod_of_disjoint_range {M₂
 : Type*} [AddCommGroup M₂] [Module R M₂] {M₃ : Type*} [AddCommGroup M₃] [Module
 R M₃] (f : M ->ₗ[R] M₃) (g …
-/
lemma ker_coprod_of_disjoint_range {f₁ : M₁ →L[R] M} {f₂ : M₂ →L[R] M}
    (hf : Disjoint f₁.range f₂.range) :
    (f₁.coprod f₂).ker = f₁.ker.prod f₂.ker :=
  LinearMap.ker_coprod_of_disjoint_range f₁.toLinearMap f₂.toLinearMap hf

end AddCommGroup

end coprod

end ContinuousLinearMap

