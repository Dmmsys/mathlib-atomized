/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.GroupWithZero.Basic

/-!
# Monoid with zero and group with zero homomorphisms

This file defines homomorphisms of monoids with zero.

We also define coercion to a function, and usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.


## Notation

* `→*₀`: `MonoidWithZeroHom`, the type of bundled `MonoidWithZero` homs. Also use for
  `GroupWithZero` homs.

## Implementation notes

Implicit `{}` brackets are often used instead of type class `[]` brackets.  This is done when the
instances can be inferred because they are implicit arguments to the type `MonoidHom`.  When they
can be inferred from the type it is faster to use this method than to use type class inference.

## Tags

monoid homomorphism
-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

open Function

namespace NeZero
variable {F α β : Type*} [Zero α] [Zero β] [FunLike F α β] [ZeroHomClass F α β] {a : α}

/-
**NeZero.of_map** 是 Mathlib 中的一个引理，位于命名空间 `NeZero`。
形式化陈述：of_map (f : F) [neZero : NeZero (f a)] : NeZero a
参数：f : F；f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZeroHomClass.map_zero`：∀ {F : Type u_10} {M : outParam (Type u_11)} {N :
 outParam (Type u_12)} {inst : Zero M} {inst_1 : Zero N}   {inst_2 : FunLike F M
 N} [self :…
-/
lemma of_map (f : F) [neZero : NeZero (f a)] : NeZero a :=
  ⟨fun h ↦ ne (f a) <| by rw [h]; exact ZeroHomClass.map_zero f⟩
/-
**NeZero.of_injective** 是 Mathlib 中的一个引理，位于命名空间 `NeZero`。
形式化陈述：of_injective {f : F} (hf : Injective f) [NeZero a] : NeZero (f a)
参数：hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZeroHomClass.map_zero`：∀ {F : Type u_10} {M : outParam (Type u_11)} {N :
 outParam (Type u_12)} {inst : Zero M} {inst_1 : Zero N}   {inst_2 : FunLike F M
 N} [self :…
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
-/
lemma of_injective {f : F} (hf : Injective f) [NeZero a] : NeZero (f a) :=
  ⟨by rw [← ZeroHomClass.map_zero f]; exact hf.ne NeZero.out⟩

end NeZero

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

/-- `MonoidWithZeroHomClass F α β` states that `F` is a type of
`MonoidWithZero`-preserving homomorphisms.

You should also extend this typeclass when you extend `MonoidWithZeroHom`. -/
/-
**MonoidWithZeroHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (α : outParam (Type u_8)) →     (β : outParam (Type u_9
)) → [MulZeroOneClass α] → [MulZeroOneClass β] → [FunLike F α β] → Prop
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoidWithZeroHomClass F α β` states that `F` is a type of
`MonoidWithZero`-preserving homomorphisms.

You should also extend this typeclass when you extend `MonoidWithZeroHom`.
-/
class MonoidWithZeroHomClass (F : Type*) (α β : outParam Type*) [MulZeroOneClass α]
    [MulZeroOneClass β] [FunLike F α β] : Prop
  extends MonoidHomClass F α β, ZeroHomClass F α β

/-- `α →*₀ β` is the type of functions `α → β` that preserve
the `MonoidWithZero` structure.

`MonoidWithZeroHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : α →*₀ β)`,
you should parametrize over `(F : Type*) [MonoidWithZeroHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `MonoidWithZeroHomClass`. -/
/-
**MonoidWithZeroHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_7) → (β : Type u_8) → [MulZeroOneClass α] → [MulZeroOneClass β
] → Type (max u_7 u_8)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α →*₀ β` is the type of functions `α → β` that preserve
the `MonoidWithZero` structure.

`MonoidWithZeroHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : α →*₀ β)`,
you should parametrize over `(F : Type*) [MonoidWithZeroHomClass F α β] (f : F)`
.

When you extend this structure, make sure to extend `MonoidWithZeroHomClass`.
-/
structure MonoidWithZeroHom (α β : Type*) [MulZeroOneClass α] [MulZeroOneClass β]
  extends ZeroHom α β, MonoidHom α β

/-- `α →*₀ β` denotes the type of zero-preserving monoid homomorphisms from `α` to `β`. -/
infixr:25 " →*₀ " => MonoidWithZeroHom

/-- Turn an element of a type `F` satisfying `MonoidWithZeroHomClass F α β` into an actual
`MonoidWithZeroHom`. -/
/-
**MonoidWithZeroHom.ofClass** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidWithZeroHom.ofClass [FunLike F α β] [MonoidWithZeroHomClass F α β] (
f : F) : α ->*₀ β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…

--- 原说明 ---
Turn an element of a type `F` satisfying `MonoidWithZeroHomClass F α β` into an 
actual
`MonoidWithZeroHom`.
-/
def MonoidWithZeroHom.ofClass [FunLike F α β] [MonoidWithZeroHomClass F α β]
    (f : F) : α →*₀ β := { (f : α →* β), (f : ZeroHom α β) with }

namespace MonoidWithZeroHom

attribute [nolint docBlame] toMonoidHom
attribute [nolint docBlame] toZeroHom

/-
**MonoidWithZeroHom.funLike** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：funLike : FunLike (α ->*₀ β) α β where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (α →*₀ β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
/-
**MonoidWithZeroHom.monoidWithZeroHomClass** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWith
ZeroHom`。
形式化陈述：monoidWithZeroHomClass : MonoidWithZeroHomClass (α ->*₀ β) α β where map_m
ul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.map_mul'`：∀ {α : Type u_7} {β : Type u_8} [inst : MulZ
eroOneClass α] [inst_1 : MulZeroOneClass β] (self : α →*₀ β) (x y : α),   (↑self
).toFun (x * y) …
· 使用定理 `MonoidWithZeroHom.map_one'`：∀ {α : Type u_7} {β : Type u_8} [inst : MulZ
eroOneClass α] [inst_1 : MulZeroOneClass β] (self : α →*₀ β),   (↑self).toFun 1 
= 1
· 使用定理 `ZeroHom.map_zero'`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M] [in
st_1 : Zero N] (self : ZeroHom M N), self.toFun 0 = 0
-/
instance monoidWithZeroHomClass : MonoidWithZeroHomClass (α →*₀ β) α β where
  map_mul := MonoidWithZeroHom.map_mul'
  map_one := MonoidWithZeroHom.map_one'
  map_zero f := f.map_zero'
/-
**MonoidWithZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWithZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] : Subsingleton (α →*₀ β) := .of_oneHomClass

variable [FunLike F α β]
/-
**MonoidWithZeroHom.coe_ofClass** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : MulZeroOneClass α] 
[inst_1 : MulZeroOneClass β]   [inst_2 : FunLike F α β] [inst_3 : MonoidWithZero
HomClass F α β] (f : F), ⇑(MonoidWithZeroHom.ofClass f) = ⇑f
参数：f : F；MonoidWithZeroHom.ofClass f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_ofClass [MonoidWithZeroHomClass F α β] (f : F) :
    (MonoidWithZeroHom.ofClass f : α → β) = f := rfl

-- Completely uninteresting lemmas about coercion to function, that all homs need
section Coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/

attribute [coe] toMonoidHom

/-- `MonoidWithZeroHom` down-cast to a `MonoidHom`, forgetting the 0-preserving property. -/
/-
**MonoidWithZeroHom.coeToMonoidHom** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWithZeroHom`
。
形式化陈述：coeToMonoidHom : Coe (α ->*₀ β) (α ->* β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoidWithZeroHom` down-cast to a `MonoidHom`, forgetting the 0-preserving prop
erty.
-/
instance coeToMonoidHom : Coe (α →*₀ β) (α →* β) :=
  ⟨toMonoidHom⟩

attribute [coe] toZeroHom

/-- `MonoidWithZeroHom` down-cast to a `ZeroHom`, forgetting the monoidal property. -/
/-
**MonoidWithZeroHom.coeToZeroHom** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：coeToZeroHom : Coe (α ->*₀ β) (ZeroHom α β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoidWithZeroHom` down-cast to a `ZeroHom`, forgetting the monoidal property.
-/
instance coeToZeroHom : Coe (α →*₀ β) (ZeroHom α β) := ⟨toZeroHom⟩

-- This must come after the coe_toFun definitions
initialize_simps_projections MonoidWithZeroHom (toFun → apply)
/-
**MonoidWithZeroHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOneClass α] [inst_1 : MulZe
roOneClass β] (f : ZeroHom α β)   (h1 : f.toFun 1 = 1) (hmul : ∀ (x y : α), f.to
Fun (x * y) = f.toFun x * f.toFun y),   ⇑{ toZeroHom := f, map_one' := h1, map_m
ul' := hmul } = ⇑f
参数：f : ZeroHom α β；h1 : f.toFun 1 = 1；hmul : ∀ (x y : α), f.toFun (x * y) = f.to
Fun x * f.toFun y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mk (f h1 hmul) : (mk f h1 hmul : α → β) = (f : α → β) := rfl
/-
**MonoidWithZeroHom.toZeroHom_coe** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOneClass α] [inst_1 : MulZe
roOneClass β] (f : α →*₀ β), ⇑↑f = ⇑f
参数：f : α →*₀ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toZeroHom_coe (f : α →*₀ β) : (f.toZeroHom : α → β) = f := rfl
/-
**MonoidWithZeroHom.toMonoidHom_coe** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom
`。
形式化陈述：toMonoidHom_coe (f : α ->*₀ β) : f.toMonoidHom.toFun = f
参数：f : α ->*₀ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toMonoidHom_coe (f : α →*₀ β) : f.toMonoidHom.toFun = f := rfl
/-
**MonoidWithZeroHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOneClass α] [inst_1 : MulZe
roOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x) → f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
@[ext] lemma ext ⦃f g : α →*₀ β⦄ (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h
/-
**MonoidWithZeroHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOneClass α] [inst_1 : MulZe
roOneClass β] (f : α →*₀ β)   (h1 : (↑f).toFun 1 = 1) (hmul : ∀ (x y : α), (↑f).
toFun (x * y) = (↑f).toFun x * (↑f).toFun y),   { toZeroHom := ↑f, map_one' := h
1, map_mul' := hmul } = f
参数：f : α →*₀ β；h1 : (↑f).toFun 1 = 1；hmul : ∀ (x y : α), (↑f).toFun (x * y) = (↑
f).toFun x * (↑f).toFun y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `MonoidWithZeroHom.ext`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOn
eClass α] [inst_1 : MulZeroOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x)
 → f = g
-/
@[simp] lemma mk_coe (f : α →*₀ β) (h1 hmul) : mk f h1 hmul = f := ext fun _ ↦ rfl

end Coes

/-- Copy of a `MonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
/-
**MonoidWithZeroHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : MulZeroOneClass α] → [inst
_1 : MulZeroOneClass β] → (f : α →*₀ β) → (f' : α → β) → f' = ⇑f → α →* β
参数：f : α →*₀ β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `MonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities.
-/
protected def copy (f : α →*₀ β) (f' : α → β) (h : f' = f) : α →* β :=
  { f.toZeroHom.copy f' h, f.toMonoidHom.copy f' h with }

@[simp]
/-
**MonoidWithZeroHom.coe_copy** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：coe_copy (f : α ->*₀ β) (f' : α -> β) (h) : (f.copy f' h) = f'
参数：f : α ->*₀ β；f' : α -> β；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_copy (f : α →*₀ β) (f' : α → β) (h) : (f.copy f' h) = f' := rfl
/-
**MonoidWithZeroHom.copy_eq** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：copy_eq (f : α ->*₀ β) (f' : α -> β) (h) : f.copy f' h = f
参数：f : α ->*₀ β；f' : α -> β；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
lemma copy_eq (f : α →*₀ β) (f' : α → β) (h) : f.copy f' h = f := DFunLike.ext' h
/-
**MonoidWithZeroHom.map_one** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOneClass α] [inst_1 : MulZe
roOneClass β] (f : α →*₀ β), f 1 = 1
参数：f : α →*₀ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.map_one'`：∀ {α : Type u_7} {β : Type u_8} [inst : MulZ
eroOneClass α] [inst_1 : MulZeroOneClass β] (self : α →*₀ β),   (↑self).toFun 1 
= 1
-/
protected lemma map_one (f : α →*₀ β) : f 1 = 1 := f.map_one'
/-
**MonoidWithZeroHom.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOneClass α] [inst_1 : MulZe
roOneClass β] (f : α →*₀ β), f 0 = 0
参数：f : α →*₀ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroHom.map_zero'`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M] [in
st_1 : Zero N] (self : ZeroHom M N), self.toFun 0 = 0
-/
protected lemma map_zero (f : α →*₀ β) : f 0 = 0 := f.map_zero'
/-
**MonoidWithZeroHom.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOneClass α] [inst_1 : MulZe
roOneClass β] (f : α →*₀ β) (a b : α),   f (a * b) = f a * f b
参数：f : α →*₀ β；a b : α；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.map_mul'`：∀ {α : Type u_7} {β : Type u_8} [inst : MulZ
eroOneClass α] [inst_1 : MulZeroOneClass β] (self : α →*₀ β) (x y : α),   (↑self
).toFun (x * y) …
-/
protected lemma map_mul (f : α →*₀ β) (a b : α) : f (a * b) = f a * f b := f.map_mul' a b

@[simp]
/-
**MonoidWithZeroHom.map_ite_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHo
m`。
形式化陈述：map_ite_zero_one {F : Type*} [FunLike F α β] [MonoidWithZeroHomClass F α β
] (f : F) (p : Prop) [Decidable p] : f (ite p 0 1) = ite p 0 1
参数：f : F；p : Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem map_ite_zero_one {F : Type*} [FunLike F α β] [MonoidWithZeroHomClass F α β] (f : F)
    (p : Prop) [Decidable p] :
    f (ite p 0 1) = ite p 0 1 := by
  split_ifs with h <;> simp

@[simp]
/-
**MonoidWithZeroHom.map_ite_one_zero** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHo
m`。
形式化陈述：map_ite_one_zero {F : Type*} [FunLike F α β] [MonoidWithZeroHomClass F α β
] (f : F) (p : Prop) [Decidable p] : f (ite p 1 0) = ite p 1 0
参数：f : F；p : Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
-/
theorem map_ite_one_zero {F : Type*} [FunLike F α β] [MonoidWithZeroHomClass F α β] (f : F)
    (p : Prop) [Decidable p] :
    f (ite p 1 0) = ite p 1 0 := by
  split_ifs with h <;> simp

/-- The identity map from a `MonoidWithZero` to itself. -/
@[simps]
/-
**MonoidWithZeroHom.id** 是 Mathlib 中的一个定义，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：id (α : Type*) [MulZeroOneClass α] : α ->*₀ α where toFun x
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map from a `MonoidWithZero` to itself.
-/
def id (α : Type*) [MulZeroOneClass α] : α →*₀ α where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Composition of `MonoidWithZeroHom`s as a `MonoidWithZeroHom`. -/
/-
**MonoidWithZeroHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：comp (hnp : β ->*₀ γ) (hmn : α ->*₀ β) : α ->*₀ γ where toFun
参数：hnp : β ->*₀ γ；hmn : α ->*₀ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `MonoidWithZeroHom`s as a `MonoidWithZeroHom`.
-/
def comp (hnp : β →*₀ γ) (hmn : α →*₀ β) : α →*₀ γ where
  toFun := hnp ∘ hmn
  map_zero' := by rw [comp_apply, map_zero, map_zero]
  map_one' := by simp
  map_mul' := by simp
/-
**MonoidWithZeroHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : MulZeroOneClass α] 
[inst_1 : MulZeroOneClass β]   [inst_2 : MulZeroOneClass γ] (g : β →*₀ γ) (f : α
 →*₀ β), ⇑(g.comp f) = ⇑g ∘ ⇑f
参数：g : β →*₀ γ；f : α →*₀ β；g.comp f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_comp (g : β →*₀ γ) (f : α →*₀ β) : ↑(g.comp f) = g ∘ f := rfl
/-
**MonoidWithZeroHom.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：comp_apply (g : β ->*₀ γ) (f : α ->*₀ β) (x : α) : g.comp f x = g (f x)
参数：g : β ->*₀ γ；f : α ->*₀ β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_apply (g : β →*₀ γ) (f : α →*₀ β) (x : α) : g.comp f x = g (f x) := rfl
/-
**MonoidWithZeroHom.comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：comp_assoc (f : α ->*₀ β) (g : β ->*₀ γ) (h : γ ->*₀ δ) : (h.comp g).comp 
f = h.comp (g.comp f)
参数：f : α ->*₀ β；g : β ->*₀ γ；h : γ ->*₀ δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_assoc (f : α →*₀ β) (g : β →*₀ γ) (h : γ →*₀ δ) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl
/-
**MonoidWithZeroHom.cancel_right** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：cancel_right {g₁ g₂ : β ->*₀ γ} {f : α ->*₀ β} (hf : Surjective f) : g₁.co
mp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.ext`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOn
eClass α] [inst_1 : MulZeroOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x)
 → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
lemma cancel_right {g₁ g₂ : β →*₀ γ} {f : α →*₀ β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h ↦ ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h ↦ h ▸ rfl⟩
/-
**MonoidWithZeroHom.cancel_left** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：cancel_left {g : β ->*₀ γ} {f₁ f₂ : α ->*₀ β} (hg : Injective g) : g.comp 
f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.ext`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOn
eClass α] [inst_1 : MulZeroOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x)
 → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonoidWithZeroHom.comp_apply`：comp_apply (g : β ->*₀ γ) (f : α ->*₀ β) (
x : α) : g.comp f x = g (f x)
-/
lemma cancel_left {g : β →*₀ γ} {f₁ f₂ : α →*₀ β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h ↦ ext fun x ↦ hg <| by rw [← comp_apply, h,
    comp_apply], fun h ↦ h ▸ rfl⟩
/-
**MonoidWithZeroHom.toMonoidHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZ
eroHom`。
形式化陈述：toMonoidHom_injective : Injective (toMonoidHom : (α ->*₀ β) -> α ->* β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
lemma toMonoidHom_injective : Injective (toMonoidHom : (α →*₀ β) → α →* β) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective
/-
**MonoidWithZeroHom.toZeroHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZer
oHom`。
形式化陈述：toZeroHom_injective : Injective (toZeroHom : (α ->*₀ β) -> ZeroHom α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
lemma toZeroHom_injective : Injective (toZeroHom : (α →*₀ β) → ZeroHom α β) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective
/-
**MonoidWithZeroHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOneClass α] [inst_1 : MulZe
roOneClass β] (f : α →*₀ β),   f.comp (MonoidWithZeroHom.id α) = f
参数：f : α →*₀ β；MonoidWithZeroHom.id α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.ext`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOn
eClass α] [inst_1 : MulZeroOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x)
 → f = g
-/
@[simp] lemma comp_id (f : α →*₀ β) : f.comp (id α) = f := ext fun _ ↦ rfl
/-
**MonoidWithZeroHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOneClass α] [inst_1 : MulZe
roOneClass β] (f : α →*₀ β),   (MonoidWithZeroHom.id β).comp f = f
参数：f : α →*₀ β；MonoidWithZeroHom.id β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.ext`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOn
eClass α] [inst_1 : MulZeroOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x)
 → f = g
-/
@[simp] lemma id_comp (f : α →*₀ β) : (id β).comp f = f := ext fun _ ↦ rfl

-- Unlike the other homs, `MonoidWithZeroHom` does not have a `1` or `0`
/-
**MonoidWithZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWithZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (α →*₀ α) := ⟨id α⟩

/-- Given two monoid with zero morphisms `f`, `g` to a commutative monoid with zero, `f * g` is the
monoid with zero morphism sending `x` to `f x * g x`. -/
/-
**MonoidWithZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWithZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two monoid with zero morphisms `f`, `g` to a commutative monoid with zero,
 `f * g` is the
monoid with zero morphism sending `x` to `f x * g x`.
-/
instance {β} [CommMonoidWithZero β] : Mul (α →*₀ β) where
  mul f g :=
    { (f * g : α →* β) with
      map_zero' := by dsimp; rw [map_zero, zero_mul] }

/-- The trivial homomorphism between monoids with zero, sending 0 to 0 and all other elements to 1.
-/
/-
**MonoidWithZeroHom.one** 是 Mathlib 中的一个定义，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：(M₀ : Type u_7) →   (N₀ : Type u_8) →     [inst : MulZeroOneClass M₀] →   
    [inst_1 : MulZeroOneClass N₀] →         [DecidablePred fun x => x = 0] → [No
ntrivial M₀] → [NoZeroDivisors M₀] → One (M₀ →*₀ N₀)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial homomorphism between monoids with zero, sending 0 to 0 and all other
 elements to 1.
-/
protected instance one (M₀ N₀ : Type*) [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] :
    One (M₀ →*₀ N₀) where
  one.toFun x := if x = 0 then 0 else 1
  one.map_zero' := by simp
  one.map_one' := by simp
  one.map_mul' x y := by split_ifs <;> simp_all
/-
**MonoidWithZeroHom.one_apply_def** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：one_apply_def {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀] [D
ecidablePred fun x : M₀ => x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] (x : M₀) :
 (1 : M₀ ->*₀ N₀) x = if x = 0 then 0 else 1
参数：x : M₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_apply_def {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] (x : M₀) :
    (1 : M₀ →*₀ N₀) x = if x = 0 then 0 else 1 :=
  rfl

@[simp]
/-
**MonoidWithZeroHom.one_apply_zero** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`
。
形式化陈述：one_apply_zero {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀] [
DecidablePred fun x : M₀ => x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] : (1 : M₀
 ->*₀ N₀) 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma one_apply_zero {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] :
    (1 : M₀ →*₀ N₀) 0 = 0 :=
  if_pos rfl
/-
**MonoidWithZeroHom.one_apply_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZe
roHom`。
形式化陈述：one_apply_of_ne_zero {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass
 N₀] [DecidablePred fun x : M₀ => x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] {x 
: M₀} (hx : x != 0) : (1 : M₀ ->*₀ N₀) x = 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma one_apply_of_ne_zero {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] {x : M₀} (hx : x ≠ 0) :
    (1 : M₀ →*₀ N₀) x = 1 :=
  if_neg hx

@[simp]
/-
**MonoidWithZeroHom.one_apply_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZ
eroHom`。
形式化陈述：one_apply_eq_zero_iff {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClas
s N₀] [DecidablePred fun x : M₀ => x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] [N
ontrivial N₀] {x : M₀} : (1 : M₀ ->*₀ N₀) x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MonoidWithZeroHom.one_apply_zero`：one_apply_zero {M₀ N₀ : Type*} [MulZer
oOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 0] [Nontrivi
al M₀] [NoZeroDivisors…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonoidWithZeroHom.one_apply_of_ne_zero`：one_apply_of_ne_zero {M₀ N₀ : Ty
pe*} [MulZeroOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 
0] [Nontrivial M₀] [NoZeroDi…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma one_apply_eq_zero_iff {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] [Nontrivial N₀]
    {x : M₀} :
    (1 : M₀ →*₀ N₀) x = 0 ↔ x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx <;> simp_all [one_apply_of_ne_zero]

@[simp]
/-
**MonoidWithZeroHom.one_apply_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZe
roHom`。
形式化陈述：one_apply_eq_one_iff {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass
 N₀] [DecidablePred fun x : M₀ => x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] [No
ntrivial N₀] {x : M₀} : (1 : M₀ ->*₀ N₀) x = 1 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MonoidWithZeroHom.one_apply_zero`：one_apply_zero {M₀ N₀ : Type*} [MulZer
oOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 0] [Nontrivi
al M₀] [NoZeroDivisors…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonoidWithZeroHom.one_apply_of_ne_zero`：one_apply_of_ne_zero {M₀ N₀ : Ty
pe*} [MulZeroOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 
0] [Nontrivial M₀] [NoZeroDi…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma one_apply_eq_one_iff {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] [Nontrivial N₀]
    {x : M₀} :
    (1 : M₀ →*₀ N₀) x = 1 ↔ x ≠ 0 := by
  rcases eq_or_ne x 0 with rfl | hx <;> simp_all [one_apply_of_ne_zero]

end MonoidWithZeroHom

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] {n : ℕ} (hn : n ≠ 0)

/-- We define `x ↦ x^n` (for positive `n : ℕ`) as a `MonoidWithZeroHom` -/
/-
**powMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：powMonoidWithZeroHom : M₀ ->*₀ M₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define `x ↦ x^n` (for positive `n : ℕ`) as a `MonoidWithZeroHom`
-/
def powMonoidWithZeroHom : M₀ →*₀ M₀ :=
  { powMonoidHom n with map_zero' := zero_pow hn }
/-
**coe_powMonoidWithZeroHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M₀ : Type u_6} [inst : CommMonoidWithZero M₀] {n : ℕ} (hn : n ≠ 0), ⇑(p
owMonoidWithZeroHom hn) = fun x => x ^ n
参数：hn : n ≠ 0；powMonoidWithZeroHom hn。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_powMonoidWithZeroHom : (powMonoidWithZeroHom hn : M₀ → M₀) = fun x ↦ x ^ n := rfl
/-
**powMonoidWithZeroHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M₀ : Type u_6} [inst : CommMonoidWithZero M₀] {n : ℕ} (hn : n ≠ 0) (a :
 M₀), (powMonoidWithZeroHom hn) a = a ^ n
参数：hn : n ≠ 0；a : M₀；powMonoidWithZeroHom hn。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma powMonoidWithZeroHom_apply (a : M₀) : powMonoidWithZeroHom hn a = a ^ n := rfl

end CommMonoidWithZero

