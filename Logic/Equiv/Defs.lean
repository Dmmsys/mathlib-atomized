/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Quot
public import Mathlib.Data.Subtype
public import Mathlib.Logic.Unique
public import Mathlib.Tactic.Simps.Basic
public import Mathlib.Tactic.Substs

import Mathlib.Tactic.Attr.Register

/-!
# Equivalence between types

In this file we define two types:

* `Equiv α β` a.k.a. `α ≃ β`: a bijective map `α → β` bundled with its inverse map; we use this (and
  not equality!) to express that various `Type`s or `Sort`s are equivalent.

* `Equiv.Perm α`: the group of permutations `α ≃ α`. More lemmas about `Equiv.Perm` can be found in
  `Mathlib/GroupTheory/Perm/`.

Then we define

* canonical isomorphisms between various types: e.g.,

  - `Equiv.refl α` is the identity map interpreted as `α ≃ α`;

* operations on equivalences: e.g.,

  - `Equiv.symm e : β ≃ α` is the inverse of `e : α ≃ β`;

  - `Equiv.trans e₁ e₂ : α ≃ γ` is the composition of `e₁ : α ≃ β` and `e₂ : β ≃ γ` (note the order
    of the arguments!);

* definitions that transfer some instances along an equivalence. By convention, we transfer
  instances from right to left.

  - `Equiv.inhabited` takes `e : α ≃ β` and `[Inhabited β]` and returns `Inhabited α`;
  - `Equiv.unique` takes `e : α ≃ β` and `[Unique β]` and returns `Unique α`;
  - `Equiv.decidableEq` takes `e : α ≃ β` and `[DecidableEq β]` and returns `DecidableEq α`.

  More definitions of this kind can be found in other files.
  E.g., `Mathlib/Algebra/Group/TransferInstance.lean` does it for `Group`,
  `Mathlib/Algebra/Module/TransferInstance.lean` does it for `Module`, and similar files exist for
  other algebraic type classes.

Many more such isomorphisms and operations are defined in `Mathlib/Logic/Equiv/Basic.lean`.

## Tags

equivalence, congruence, bijective map
-/

@[expose] public section

open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
/-
**Equiv** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：Equiv (α β : Sort*) where /-- The forward map of an equivalence.  Do NOT u
se directly. Use the coercion instead. -/ protected toFun : α -> β /-- The backw
ard map of an equivalence.  Do NOT use `e.invFun` directly. Use the coercion of 
`e.symm` instead. -/ protected invFun : β -> α protected left_inv : LeftInverse 
invFun toFun
参数：α β : Sort*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α ≃ β` is the type of functions from `α → β` with a two-sided inverse.
-/
structure Equiv (α β : Sort*) where
  /-- The forward map of an equivalence.

  Do NOT use directly. Use the coercion instead. -/
  protected toFun : α → β
  /-- The backward map of an equivalence.

  Do NOT use `e.invFun` directly. Use the coercion of `e.symm` instead. -/
  protected invFun : β → α
  protected left_inv : LeftInverse invFun toFun := by intro; first | rfl | ext <;> rfl
  protected right_inv : RightInverse invFun toFun := by intro; first | rfl | ext <;> rfl

@[inherit_doc]
infixl:25 " ≃ " => Equiv

/-- Turn an element of a type `F` satisfying `EquivLike F α β` into an actual
`Equiv`. This is declared as the default coercion from `F` to `α ≃ β`. -/
@[coe]
/-
**EquivLike.toEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：EquivLike.toEquiv {F} [EquivLike F α β] (f : F) : α ≃ β where toFun
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.left_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : outP
aram (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.LeftInverse (Equiv
Like.inv…
· 使用定理 `EquivLike.right_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : out
Param (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.RightInverse (Equ
ivLike.in…

--- 原说明 ---
Turn an element of a type `F` satisfying `EquivLike F α β` into an actual
`Equiv`. This is declared as the default coercion from `F` to `α ≃ β`.
-/
def EquivLike.toEquiv {F} [EquivLike F α β] (f : F) : α ≃ β where
  toFun := f
  invFun := EquivLike.inv f
  left_inv := EquivLike.left_inv f
  right_inv := EquivLike.right_inv f

/-- Any type satisfying `EquivLike` can be cast into `Equiv` via `EquivLike.toEquiv`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type satisfying `EquivLike` can be cast into `Equiv` via `EquivLike.toEquiv`
.
-/
instance {F} [EquivLike F α β] : CoeTC F (α ≃ β) :=
  ⟨EquivLike.toEquiv⟩

/-- `Perm α` is the type of bijections from `α` to itself. -/
/-
**Equiv.Perm** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Equiv.Perm (α : Sort*)
参数：α : Sort*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Perm α` is the type of bijections from `α` to itself.
-/
abbrev Equiv.Perm (α : Sort*) :=
  Equiv α α

namespace Equiv

/-
**Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (α ≃ β) α β where
  coe := Equiv.toFun
  inv := Equiv.invFun
  left_inv := Equiv.left_inv
  right_inv := Equiv.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by cases e₁; cases e₂; congr

@[simp, norm_cast]
/-
**Equiv._root_.EquivLike.coe_coe** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.EquivLike.coe_coe {F} [EquivLike F α β] (e : F) :
    ((e : α ≃ β) : α → β) = e := rfl
/-
**Equiv.coe_fn_mk** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) (l : Function.LeftInve
rse g f) (r : Function.RightInverse g f),   ⇑{ toFun := f, invFun := g, left_inv
 := l, right_inv := r } = f
参数：f : α → β；g : β → α；l : Function.LeftInverse g f；r : Function.RightInverse g 
f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] theorem coe_fn_mk (f : α → β) (g l r) : (Equiv.mk f g l r : α → β) = f :=
  rfl

/-- The map `(r ≃ s) → (r → s)` is injective. -/
/-
**Equiv.coe_fn_injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_fn_injective : @Function.Injective (α ≃ β) (α -> β) (fun e => e)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe

--- 原说明 ---
The map `(r ≃ s) → (r → s)` is injective.
-/
theorem coe_fn_injective : @Function.Injective (α ≃ β) (α → β) (fun e => e) :=
  DFunLike.coe_injective
/-
**Equiv.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {e₁ e₂ : α ≃ β}, ⇑e₁ = ⇑e₂ ↔ e₁ = e₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
-/
protected theorem coe_inj {e₁ e₂ : α ≃ β} : (e₁ : α → β) = e₂ ↔ e₁ = e₂ :=
  @DFunLike.coe_fn_eq _ _ _ _ e₁ e₂
/-
**Equiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `Stream'.WSeq`。
形式化陈述：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) : s ~ʷ t
参数：h : forall n, get? s n ~ get? t n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
@[ext, grind ext] theorem ext {f g : Equiv α β} (H : ∀ x, f x = g x) : f = g := DFunLike.ext f g H
/-
**Equiv.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {f : α ≃ β} {x x' : α}, x = x' → f x = f x'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg {f : Equiv α β} {x x' : α} : x = x' → f x = f x' :=
  DFunLike.congr_arg f
/-
**Equiv.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {f g : α ≃ β}, f = g → ∀ (x : α), f x = g x
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {f g : Equiv α β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x
/-
**Equiv.Perm.ext** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ x) → σ = τ
参数：∀ (x : α), σ x = τ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
-/
@[ext] theorem Perm.ext {σ τ : Equiv.Perm α} (H : ∀ x, σ x = τ x) : σ = τ := Equiv.ext H
/-
**Equiv.Perm.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Sort u} {f : Equiv.Perm α} {x x' : α}, x = x' → f x = f x'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.congr_arg`：∀ {α : Sort u} {β : Sort v} {f : α ≃ β} {x x' : α}, x =
 x' → f x = f x'
-/
protected theorem Perm.congr_arg {f : Equiv.Perm α} {x x' : α} : x = x' → f x = f x' :=
  Equiv.congr_arg
/-
**Equiv.Perm.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Sort u} {f g : Equiv.Perm α}, f = g → ∀ (x : α), f x = g x
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.congr_fun`：∀ {α : Sort u} {β : Sort v} {f g : α ≃ β}, f = g → ∀ (x
 : α), f x = g x
-/
protected theorem Perm.congr_fun {f g : Equiv.Perm α} (h : f = g) (x : α) : f x = g x :=
  Equiv.congr_fun h x

/-- Any type is equivalent to itself. -/
/-
**Equiv.refl** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：Equiv.refl (s : Computation α) : s ~ s
参数：s : Computation α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type is equivalent to itself.
-/
@[refl] protected def refl (α : Sort*) : α ≃ α := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
/-
**Equiv.inhabited'** 是 Mathlib 中的一个实例，位于命名空间 `Equiv`。
形式化陈述：inhabited' : Inhabited (α ≃ α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Any type is equivalent to itself.
-/
instance inhabited' : Inhabited (α ≃ α) := ⟨Equiv.refl α⟩

/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm, implicit_reducible]
/-
**Equiv.symm** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun

--- 原说明 ---
Inverse of an equivalence `e : α ≃ β`.
-/
protected def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

/-- See Note [custom simps projection] -/
/-
**Equiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Parser.Command`。
形式化陈述：Equiv.Simps.symm_apply (e : α ≃ β) : β → α
参数：e : α ≃ β。
该定义给出了一个带前提的构造。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (e : α ≃ β) : β → α := e.symm

initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)

/-- Restatement of `Equiv.left_inv` in terms of `Function.LeftInverse`. -/
/-
**Equiv.left_inv'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：left_inv' (e : α ≃ β) : Function.LeftInverse e.symm e
参数：e : α ≃ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun

--- 原说明 ---
Restatement of `Equiv.left_inv` in terms of `Function.LeftInverse`.
-/
theorem left_inv' (e : α ≃ β) : Function.LeftInverse e.symm e := e.left_inv
/-- Restatement of `Equiv.right_inv` in terms of `Function.RightInverse`. -/
/-
**Equiv.right_inv'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：right_inv' (e : α ≃ β) : Function.RightInverse e.symm e
参数：e : α ≃ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
Restatement of `Equiv.right_inv` in terms of `Function.RightInverse`.
-/
theorem right_inv' (e : α ≃ β) : Function.RightInverse e.symm e := e.right_inv
/-
**Equiv.symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) (hl : Function.LeftInv
erse g f) (hr : Function.RightInverse g f),   { toFun := f, invFun := g, left_in
v := hl, right_inv := hr }.symm =     { toFun := g, invFun := f, left_inv := hr,
 right_inv := hl }
参数：f : α → β；g : β → α；hl : Function.LeftInverse g f；hr : Function.RightInverse 
g f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma symm_mk (f : α → β) (g hl hr) : (mk f g hl hr).symm = mk g f hr hl := rfl

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[trans]
/-
**Equiv.trans** 是 Mathlib 中的一个定理，位于命名空间 `Computation`。
形式化陈述：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~ u
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`.
-/
protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm, e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩

@[simps]
/-
**Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans Equiv Equiv Equiv where
  trans := Equiv.trans

/-- `Equiv.symm` defines an equivalence between `α ≃ β` and `β ≃ α`. -/
@[simps! (attr := grind =)]
/-
**Equiv.symmEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：symmEquiv (α β : Sort*) : (α ≃ β) ≃ (β ≃ α) where toFun
参数：α β : Sort*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`Equiv.symm` defines an equivalence between `α ≃ β` and `β ≃ α`.
-/
def symmEquiv (α β : Sort*) : (α ≃ β) ≃ (β ≃ α) where
  toFun := .symm
  invFun := .symm
/-
**Equiv.toFun_as_coe** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.toFun = ⇑e
参数：e : α ≃ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, mfld_simps] theorem toFun_as_coe (e : α ≃ β) : e.toFun = e := rfl
/-
**Equiv.invFun_as_coe** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.invFun = ⇑e.symm
参数：e : α ≃ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, mfld_simps] theorem invFun_as_coe (e : α ≃ β) : e.invFun = e.symm := rfl
/-
**Equiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injective ⇑e
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
-/
protected theorem injective (e : α ≃ β) : Injective e := EquivLike.injective e
/-
**Equiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surjective ⇑e
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
protected theorem surjective (e : α ≃ β) : Surjective e := EquivLike.surjective e
/-
**Equiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijective ⇑e
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e
-/
protected theorem bijective (e : α ≃ β) : Bijective e := EquivLike.bijective e
/-
**Equiv.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleton β], Subsingleton α
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem subsingleton (e : α ≃ β) [Subsingleton β] : Subsingleton α :=
  e.injective.subsingleton
/-
**Equiv.subsingleton.symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.subsingleton`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleton α], Subsingleton β
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem subsingleton.symm (e : α ≃ β) [Subsingleton α] : Subsingleton β :=
  e.symm.injective.subsingleton
/-
**Equiv.subsingleton_congr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：subsingleton_congr (e : α ≃ β) : Subsingleton α ↔ Subsingleton β
参数：e : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem subsingleton_congr (e : α ≃ β) : Subsingleton α ↔ Subsingleton β :=
  ⟨fun _ => e.symm.subsingleton, fun _ => e.subsingleton⟩
/-
**Equiv.equiv_subsingleton_cod** 是 Mathlib 中的一个实例，位于命名空间 `Equiv`。
形式化陈述：equiv_subsingleton_cod [Subsingleton β] : Subsingleton (α ≃ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance equiv_subsingleton_cod [Subsingleton β] : Subsingleton (α ≃ β) :=
  ⟨fun _ _ => Equiv.ext fun _ => Subsingleton.elim _ _⟩
/-
**Equiv.equiv_subsingleton_dom** 是 Mathlib 中的一个实例，位于命名空间 `Equiv`。
形式化陈述：equiv_subsingleton_dom [Subsingleton α] : Subsingleton (α ≃ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Equiv.subsingleton.symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsin
gleton α], Subsingleton β
-/
instance equiv_subsingleton_dom [Subsingleton α] : Subsingleton (α ≃ β) :=
  ⟨fun f _ => Equiv.ext fun _ => @Subsingleton.elim _ (Equiv.subsingleton.symm f) _ _⟩
/-
**Equiv.permUnique** 是 Mathlib 中的一个实例，位于命名空间 `Equiv`。
形式化陈述：permUnique [Subsingleton α] : Unique (Perm α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
instance permUnique [Subsingleton α] : Unique (Perm α) :=
  uniqueOfSubsingleton (Equiv.refl α)
/-
**Equiv.Perm.subsingleton_eq_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Sort u} [Subsingleton α] (e : Equiv.Perm α), e = Equiv.refl α
参数：e : Equiv.Perm α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem Perm.subsingleton_eq_refl [Subsingleton α] (e : Perm α) : e = Equiv.refl α :=
  Subsingleton.elim _ _
/-
**Equiv.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivial β], Nontrivial α
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontriv
ial β] {f : α → β}, Function.Surjective f → Nontrivial α
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem nontrivial {α β} (e : α ≃ β) [Nontrivial β] : Nontrivial α :=
  e.surjective.nontrivial
/-
**Equiv.nontrivial_congr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：nontrivial_congr {α β} (e : α ≃ β) : Nontrivial α ↔ Nontrivial β
参数：e : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem nontrivial_congr {α β} (e : α ≃ β) : Nontrivial α ↔ Nontrivial β :=
  ⟨fun _ ↦ e.symm.nontrivial, fun _ ↦ e.nontrivial⟩

/-- Transfer `DecidableEq` across an equivalence. -/
/-
**Equiv.decidableEq** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Sort u} → {β : Sort v} → α ≃ β → [DecidableEq β] → DecidableEq α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `DecidableEq` across an equivalence.
-/
protected abbrev decidableEq (e : α ≃ β) [DecidableEq β] : DecidableEq α :=
  e.injective.decidableEq
/-
**Equiv.nonempty_congr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty β
参数：e : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.congr`：∀ {α : Sort u_3} {β : Sort u_4} (f : α → β) (g : β → α),
 Nonempty α ↔ Nonempty β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty β := Nonempty.congr e e.symm
/-
**Equiv.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Nonempty β], Nonempty α
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
-/
protected theorem nonempty (e : α ≃ β) [Nonempty β] : Nonempty α := e.nonempty_congr.mpr ‹_›

/-- If `α ≃ β` and `β` is inhabited, then so is `α`. -/
/-
**Equiv.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Sort u} → {β : Sort v} → [Inhabited β] → α ≃ β → Inhabited α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α ≃ β` and `β` is inhabited, then so is `α`.
-/
protected abbrev inhabited [Inhabited β] (e : α ≃ β) : Inhabited α := ⟨e.symm default⟩

/-- If `α ≃ β` and `β` is a singleton type, then so is `α`. -/
/-
**Equiv.unique** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Sort u} → {β : Sort v} → [Unique β] → α ≃ β → Unique α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α ≃ β` and `β` is a singleton type, then so is `α`.
-/
protected abbrev unique [Unique β] (e : α ≃ β) : Unique α := e.symm.surjective.unique

/-- Equivalence between equal types. -/
/-
**Equiv.cast** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α β : Sort u_1} → α = β → α ≃ β
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Equivalence between equal types.
-/
protected def cast {α β : Sort _} (h : α = β) : α ≃ β where
  toFun := cast h
  invFun := cast h.symm
  left_inv := by grind
  right_inv := by grind
/-
**Equiv.coe_fn_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) (l : Function.LeftInve
rse g f) (r : Function.RightInverse g f),   ⇑{ toFun := f, invFun := g, left_inv
 := l, right_inv := r }.symm = g
参数：f : α → β；g : β → α；l : Function.LeftInverse g f；r : Function.RightInverse g 
f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem coe_fn_symm_mk (f : α → β) (g l r) : ((Equiv.mk f g l r).symm : β → α) = g := rfl
/-
**Equiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u}, ⇑(Equiv.refl α) = id
参数：Equiv.refl α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
@[simp] theorem coe_refl : (Equiv.refl α : α → α) = id := rfl

/-- This cannot be a `simp` lemmas as it incorrectly matches against `e : α ≃ synonym α`, when
`synonym α` is semireducible. This makes a mess of `Multiplicative.ofAdd` etc. -/
/-
**Equiv.Perm.coe_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Type u_1} [Subsingleton α] (e : Equiv.Perm α), ⇑e = id
参数：e : Equiv.Perm α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.subsingleton_eq_refl`：∀ {α : Sort u} [Subsingleton α] (e : Eq
uiv.Perm α), e = Equiv.refl α
· 使用定理 `Equiv.coe_refl`：∀ {α : Sort u}, ⇑(Equiv.refl α) = id

--- 原说明 ---
This cannot be a `simp` lemmas as it incorrectly matches against `e : α ≃ synony
m α`, when
`synonym α` is semireducible. This makes a mess of `Multiplicative.ofAdd` etc.
-/
theorem Perm.coe_subsingleton {α : Type*} [Subsingleton α] (e : Perm α) : (e : α → α) = id := by
  rw [Perm.subsingleton_eq_refl e, coe_refl]
/-
**Equiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} (x : α), (Equiv.refl α) x = x
参数：x : α；Equiv.refl α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
@[simp, grind =] theorem refl_apply (x : α) : Equiv.refl α x = x := rfl
/-
**Equiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {γ : Sort w} (f : α ≃ β) (g : β ≃ γ), ⇑(f.tran
s g) = ⇑g ∘ ⇑f
参数：f : α ≃ β；g : β ≃ γ；f.trans g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
@[simp] theorem coe_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g : α → γ) = g ∘ f := rfl
/-
**Equiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {γ : Sort w} (f : α ≃ β) (g : β ≃ γ) (a : α), 
(f.trans g) a = g (f a)
参数：f : α ≃ β；g : β ≃ γ；a : α；f.trans g；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
@[simp, grind =] theorem trans_apply (f : α ≃ β) (g : β ≃ γ) (a : α) :
    (f.trans g) a = g (f a) := rfl
/-
**Equiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β), e (e.symm x) = x
参数：e : α ≃ β；x : β；e.symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
@[simp, grind =] theorem apply_symm_apply (e : α ≃ β) (x : β) : e (e.symm x) = x := e.right_inv x
/-
**Equiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α), e.symm (e x) = x
参数：e : α ≃ β；x : α；e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
@[simp, grind =] theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x := e.left_inv x
/-
**Equiv.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘ ⇑e = id
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
@[simp] theorem symm_comp_self (e : α ≃ β) : e.symm ∘ e = id := funext e.symm_apply_apply
/-
**Equiv.self_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.symm = id
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
@[simp] theorem self_comp_symm (e : α ≃ β) : e ∘ e.symm = id := funext e.apply_symm_apply
/-
**Equiv._root_.EquivLike.apply_coe_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.EquivLike.apply_coe_symm_apply {F} [EquivLike F α β] (e : F) (x : β) :
    e ((e : α ≃ β).symm x) = x :=
  (e : α ≃ β).apply_symm_apply x
/-
**Equiv._root_.EquivLike.coe_symm_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.EquivLike.coe_symm_apply_apply {F} [EquivLike F α β] (e : F) (x : α) :
    (e : α ≃ β).symm (e x) = x :=
  (e : α ≃ β).symm_apply_apply x
/-
**Equiv._root_.EquivLike.coe_symm_comp_self** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.EquivLike.coe_symm_comp_self {F} [EquivLike F α β] (e : F) :
    (e : α ≃ β).symm ∘ e = id :=
  (e : α ≃ β).symm_comp_self
/-
**Equiv._root_.EquivLike.self_comp_coe_symm** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.EquivLike.self_comp_coe_symm {F} [EquivLike F α β] (e : F) :
    e ∘ (e : α ≃ β).symm = id :=
  (e : α ≃ β).self_comp_symm
/-
**Equiv.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：symm_trans_apply (f : α ≃ β) (g : β ≃ γ) (a : γ) : (f.trans g).symm a = f.
symm (g.symm a)
参数：f : α ≃ β；g : β ≃ γ；a : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem symm_trans_apply (f : α ≃ β) (g : β ≃ γ) (a : γ) :
    (f.trans g).symm a = f.symm (g.symm a) := rfl

@[simp, grind =]
/-
**Equiv.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：symm_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g).symm = g.symm.trans f.sym
m
参数：f : α ≃ β；g : β ≃ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem symm_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g).symm = g.symm.trans f.symm := rfl
/-
**Equiv.symm_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：symm_symm_apply (f : α ≃ β) (b : α) : f.symm.symm b = f b
参数：f : α ≃ β；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_symm_apply (f : α ≃ β) (b : α) : f.symm.symm b = f b := rfl
/-
**Equiv.apply_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y ↔ x = y
参数：f : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : E) {x y : α} : f x = f y
 ↔ x = y
-/
theorem apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y ↔ x = y := EquivLike.apply_eq_iff_eq f
/-
**Equiv.cast_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α β : Sort u_1} (h : α = β) (x : α), (Equiv.cast h) x = cast h x
参数：h : α = β；x : α；Equiv.cast h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem cast_apply {α β} (h : α = β) (x : α) : Equiv.cast h x = cast h x := rfl
/-
**Equiv.cast_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：cast_symm {α β} (h : α = β) : Equiv.cast h.symm = (Equiv.cast h).symm
参数：h : α = β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cast_symm {α β} (h : α = β) : Equiv.cast h.symm = (Equiv.cast h).symm := rfl
/-
**Equiv.cast_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u_1} (h : optParam (α = α) ⋯), Equiv.cast h = Equiv.refl α
参数：h : optParam (α = α) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem cast_refl {α} (h : α = α := rfl) : Equiv.cast h = Equiv.refl α := rfl
/-
**Equiv.cast_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：cast_trans {α β γ} (h : α = β) (h2 : β = γ) : Equiv.cast (h.trans h2) = (E
quiv.cast h).trans (Equiv.cast h2)
参数：h : α = β；h2 : β = γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem cast_trans {α β γ} (h : α = β) (h2 : β = γ) :
    Equiv.cast (h.trans h2) = (Equiv.cast h).trans (Equiv.cast h2) :=
  ext fun x => by subst h h2; rfl
/-
**Equiv.cast_eq_iff_heq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：cast_eq_iff_heq {α β} (h : α = β) {a : α} {b : β} : Equiv.cast h a = b ↔ a
 ≍ b
参数：h : α = β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cast_eq_iff_heq {α β} (h : α = β) {a : α} {b : β} : Equiv.cast h a = b ↔ a ≍ b := by
  subst h; simp
/-
**Equiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = y ↔ x = e y
参数：e : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = y ↔ x = e y := by grind
/-
**Equiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm x ↔ e y = x
参数：e : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm x ↔ e y = x := by grind

@[deprecated eq_symm_apply (since := "2026-07-26")]
/-
**Equiv.apply_eq_iff_eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：apply_eq_iff_eq_symm_apply {x : α} {y : β} (f : α ≃ β) : f x = y ↔ x = f.s
ymm y
参数：f : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem apply_eq_iff_eq_symm_apply {x : α} {y : β} (f : α ≃ β) : f x = y ↔ x = f.symm y :=
  f.eq_symm_apply.symm
/-
**Equiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.symm = e
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp, grind =] theorem symm_symm (e : α ≃ β) : e.symm.symm = e := rfl
/-
**Equiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：symm_bijective : Function.Bijective (Equiv.symm : (α ≃ β) -> β ≃ α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `Equiv.symm_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.symm = 
e
-/
theorem symm_bijective : Function.Bijective (Equiv.symm : (α ≃ β) → β ≃ α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
/-
**Equiv.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans (Equiv.refl β) = e
参数：e : α ≃ β；Equiv.refl β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem trans_refl (e : α ≃ β) : e.trans (Equiv.refl β) = e := by grind
/-
**Equiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u}, (Equiv.refl α).symm = Equiv.refl α
参数：Equiv.refl α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
@[simp, grind =] theorem refl_symm : (Equiv.refl α).symm = Equiv.refl α := rfl
/-
**Equiv.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), (Equiv.refl α).trans e = e
参数：e : α ≃ β；Equiv.refl α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] theorem refl_trans (e : α ≃ β) : (Equiv.refl α).trans e = e := by cases e; rfl
/-
**Equiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.trans e = Equiv.refl β
参数：e : α ≃ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem symm_trans_self (e : α ≃ β) : e.symm.trans e = Equiv.refl β := by grind
/-
**Equiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans e.symm = Equiv.refl α
参数：e : α ≃ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem self_trans_symm (e : α ≃ β) : e.trans e.symm = Equiv.refl α := by grind
/-
**Equiv.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) : (ab.trans bc).tra
ns cd = ab.trans (bc.trans cd)
参数：ab : α ≃ β；bc : β ≃ γ；cd : γ ≃ δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) :
    (ab.trans bc).trans cd = ab.trans (bc.trans cd) := by grind
/-
**Equiv.trans_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：trans_cancel_left (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ) : e.trans f = g ↔ f 
= e.symm.trans g
参数：e : α ≃ β；f : β ≃ γ；g : α ≃ γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_cancel_left (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ) :
    e.trans f = g ↔ f = e.symm.trans g := by
  grind
/-
**Equiv.trans_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：trans_cancel_right (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ) : e.trans f = g ↔ e
 = g.trans f.symm
参数：e : α ≃ β；f : β ≃ γ；g : α ≃ γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_cancel_right (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ) :
    e.trans f = g ↔ e = g.trans f.symm := by
  grind
/-
**Equiv.leftInverse_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：leftInverse_symm (f : α ≃ β) : LeftInverse f.symm f
参数：f : α ≃ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem leftInverse_symm (f : α ≃ β) : LeftInverse f.symm f := f.left_inv
/-
**Equiv.rightInverse_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：rightInverse_symm (f : α ≃ β) : Function.RightInverse f.symm f
参数：f : α ≃ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem rightInverse_symm (f : α ≃ β) : Function.RightInverse f.symm f := f.right_inv
/-
**Equiv.injective_comp** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：injective_comp (e : α ≃ β) (f : β -> γ) : Injective (f ∘ e) ↔ Injective f
参数：e : α ≃ β；f : β -> γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.injective_comp`：injective_comp (e : E) (f : β -> γ) : Function
.Injective (f ∘ e) ↔ Function.Injective f
-/
theorem injective_comp (e : α ≃ β) (f : β → γ) : Injective (f ∘ e) ↔ Injective f :=
  EquivLike.injective_comp e f
/-
**Equiv.comp_injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：comp_injective (f : α -> β) (e : β ≃ γ) : Injective (e ∘ f) ↔ Injective f
参数：f : α -> β；e : β ≃ γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.comp_injective`：comp_injective (f : α -> β) (e : F) : Function
.Injective (e ∘ f) ↔ Function.Injective f
-/
theorem comp_injective (f : α → β) (e : β ≃ γ) : Injective (e ∘ f) ↔ Injective f :=
  EquivLike.comp_injective f e
/-
**Equiv.surjective_comp** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：surjective_comp (e : α ≃ β) (f : β -> γ) : Surjective (f ∘ e) ↔ Surjective
 f
参数：e : α ≃ β；f : β -> γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.surjective_comp`：surjective_comp (e : E) (f : β -> γ) : Functi
on.Surjective (f ∘ e) ↔ Function.Surjective f
-/
theorem surjective_comp (e : α ≃ β) (f : β → γ) : Surjective (f ∘ e) ↔ Surjective f :=
  EquivLike.surjective_comp e f
/-
**Equiv.comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：comp_surjective (f : α -> β) (e : β ≃ γ) : Surjective (e ∘ f) ↔ Surjective
 f
参数：f : α -> β；e : β ≃ γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.comp_surjective`：comp_surjective (f : α -> β) (e : F) : Functi
on.Surjective (e ∘ f) ↔ Function.Surjective f
-/
theorem comp_surjective (f : α → β) (e : β ≃ γ) : Surjective (e ∘ f) ↔ Surjective f :=
  EquivLike.comp_surjective f e
/-
**Equiv.bijective_comp** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：bijective_comp (e : α ≃ β) (f : β -> γ) : Bijective (f ∘ e) ↔ Bijective f
参数：e : α ≃ β；f : β -> γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.bijective_comp`：bijective_comp (e : E) (f : β -> γ) : Function
.Bijective (f ∘ e) ↔ Function.Bijective f
-/
theorem bijective_comp (e : α ≃ β) (f : β → γ) : Bijective (f ∘ e) ↔ Bijective f :=
  EquivLike.bijective_comp e f
/-
**Equiv.comp_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：comp_bijective (f : α -> β) (e : β ≃ γ) : Bijective (e ∘ f) ↔ Bijective f
参数：f : α -> β；e : β ≃ γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.comp_bijective`：comp_bijective (f : α -> β) (e : F) : Function
.Bijective (e ∘ f) ↔ Function.Bijective f
-/
theorem comp_bijective (f : α → β) (e : β ≃ γ) : Bijective (e ∘ f) ↔ Bijective f :=
  EquivLike.comp_bijective f e

@[simp]
/-
**Equiv.extend_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：extend_apply {f : α ≃ β} (g : α -> γ) (e' : β -> γ) (b : β) : extend f g e
' b = g (f.symm b)
参数：g : α -> γ；e' : β -> γ；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem extend_apply {f : α ≃ β} (g : α → γ) (e' : β → γ) (b : β) :
    extend f g e' b = g (f.symm b) := by
  rw [← f.apply_symm_apply b, f.injective.extend_apply, apply_symm_apply]

/-- If `α` is equivalent to `β` and `γ` is equivalent to `δ`, then the type of equivalences `α ≃ γ`
is equivalent to the type of equivalences `β ≃ δ`. -/
/-
**Equiv.equivCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：equivCongr {δ : Sort*} (ab : α ≃ β) (cd : γ ≃ δ) : (α ≃ γ) ≃ (β ≃ δ) where
 toFun ac
参数：ab : α ≃ β；cd : γ ≃ δ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α` is equivalent to `β` and `γ` is equivalent to `δ`, then the type of equiv
alences `α ≃ γ`
is equivalent to the type of equivalences `β ≃ δ`.
-/
def equivCongr {δ : Sort*} (ab : α ≃ β) (cd : γ ≃ δ) : (α ≃ γ) ≃ (β ≃ δ) where
  toFun ac := (ab.symm.trans ac).trans cd
  invFun bd := ab.trans <| bd.trans <| cd.symm
  left_inv ac := by grind
  right_inv ac := by grind
/-
**Equiv.equivCongr_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort u_1} (ab : α ≃ β) (cd :
 γ ≃ δ) (e : α ≃ γ) (x : β),   ((ab.equivCongr cd) e) x = cd (e (ab.symm x))
参数：ab : α ≃ β；cd : γ ≃ δ；e : α ≃ γ；x : β；(ab.equivCongr cd) e；e (ab.symm x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] theorem equivCongr_apply_apply {δ} (ab : α ≃ β) (cd : γ ≃ δ) (e : α ≃ γ) (x) :
    ab.equivCongr cd e x = cd (e (ab.symm x)) := rfl
/-
**Equiv.equivCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort u_1} (ab : α ≃ β) (cd :
 γ ≃ δ),   (ab.equivCongr cd).symm = ab.symm.equivCongr cd.symm
参数：ab : α ≃ β；cd : γ ≃ δ；ab.equivCongr cd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp, grind =] theorem equivCongr_symm {δ} (ab : α ≃ β) (cd : γ ≃ δ) :
    (ab.equivCongr cd).symm = ab.symm.equivCongr cd.symm := by ext; rfl
/-
**Equiv.equivCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2}, (Equiv.refl α).equivCongr (Equiv.refl β) 
= Equiv.refl (α ≃ β)
参数：Equiv.refl α；Equiv.refl β；α ≃ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem equivCongr_refl {α β} :
    (Equiv.refl α).equivCongr (Equiv.refl β) = Equiv.refl (α ≃ β) := by grind
/-
**Equiv.equivCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort u_1} {ε : Sort u_2} {ζ 
: Sort u_3} (ab : α ≃ β) (de : δ ≃ ε)   (bc : β ≃ γ) (ef : ε ≃ ζ), (ab.equivCong
r de).trans (bc.equivCongr ef) = (ab.trans bc).equivCongr (de.trans ef)
参数：ab : α ≃ β；de : δ ≃ ε；bc : β ≃ γ；ef : ε ≃ ζ；ab.equivCongr de；bc.equivCongr ef
；ab.trans bc；de.trans ef。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem equivCongr_trans {δ ε ζ} (ab : α ≃ β) (de : δ ≃ ε) (bc : β ≃ γ) (ef : ε ≃ ζ) :
    (ab.equivCongr de).trans (bc.equivCongr ef) = (ab.trans bc).equivCongr (de.trans ef) := by
  grind
/-
**Equiv.equivCongr_refl_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (bg : β ≃ γ) (e : α ≃ β), (
(Equiv.refl α).equivCongr bg) e = e.trans bg
参数：bg : β ≃ γ；e : α ≃ β；(Equiv.refl α).equivCongr bg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
@[simp] theorem equivCongr_refl_left {α β γ} (bg : β ≃ γ) (e : α ≃ β) :
    (Equiv.refl α).equivCongr bg e = e.trans bg := rfl
/-
**Equiv.equivCongr_refl_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} (ab e : α ≃ β), (ab.equivCongr (Equiv.refl
 β)) e = ab.symm.trans e
参数：ab e : α ≃ β；ab.equivCongr (Equiv.refl β)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
@[simp] theorem equivCongr_refl_right {α β} (ab e : α ≃ β) :
    ab.equivCongr (Equiv.refl β) e = ab.symm.trans e := rfl
section permCongr

variable {α' β' : Type*} (e : α' ≃ β')

/-- If `α` is equivalent to `β`, then `Perm α` is equivalent to `Perm β`. -/
/-
**Equiv.permCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：permCongr : Perm α' ≃ Perm β'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is equivalent to `β`, then `Perm α` is equivalent to `Perm β`.
-/
def permCongr : Perm α' ≃ Perm β' := equivCongr e e
/-
**Equiv.permCongr_def** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：permCongr_def (p : Equiv.Perm α') : e.permCongr p = (e.symm.trans p).trans
 e
参数：p : Equiv.Perm α'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem permCongr_def (p : Equiv.Perm α') : e.permCongr p = (e.symm.trans p).trans e := rfl
/-
**Equiv.permCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α' : Type u_1} {β' : Type u_2} (e : α' ≃ β'), e.permCongr (Equiv.refl α
') = Equiv.refl β'
参数：e : α' ≃ β'；Equiv.refl α'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans_refl`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans (Equi
v.refl β) = e
· 使用定理 `Equiv.symm_trans_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.t
rans e = Equiv.refl β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem permCongr_refl : e.permCongr (Equiv.refl _) = Equiv.refl _ := by
  simp [permCongr_def]
/-
**Equiv.permCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α' : Type u_1} {β' : Type u_2} (e : α' ≃ β'), e.permCongr.symm = e.symm
.permCongr
参数：e : α' ≃ β'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp, grind =] theorem permCongr_symm : e.permCongr.symm = e.symm.permCongr := rfl
/-
**Equiv.permCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α' : Type u_1} {β' : Type u_2} (e : α' ≃ β') (p : Equiv.Perm α') (x : β
'), (e.permCongr p) x = e (p (e.symm x))
参数：e : α' ≃ β'；p : Equiv.Perm α'；x : β'；e.permCongr p；p (e.symm x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] theorem permCongr_apply (p : Equiv.Perm α') (x) :
    e.permCongr p x = e (p (e.symm x)) := rfl
/-
**Equiv.permCongr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：permCongr_symm_apply (p : Equiv.Perm β') (x) : e.permCongr.symm p x = e.sy
mm (p (e x))
参数：p : Equiv.Perm β'；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem permCongr_symm_apply (p : Equiv.Perm β') (x) :
    e.permCongr.symm p x = e.symm (p (e x)) := rfl
/-
**Equiv.permCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：permCongr_trans (p p' : Equiv.Perm α') : (e.permCongr p).trans (e.permCong
r p') = e.permCongr (p.trans p')
参数：p p' : Equiv.Perm α'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem permCongr_trans (p p' : Equiv.Perm α') :
    (e.permCongr p).trans (e.permCongr p') = e.permCongr (p.trans p') := by grind

end permCongr

/-- Two empty types are equivalent. -/
/-
**Equiv.equivOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：equivOfIsEmpty (α β : Sort*) [IsEmpty α] [IsEmpty β] : α ≃ β
参数：α β : Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two empty types are equivalent.
-/
def equivOfIsEmpty (α β : Sort*) [IsEmpty α] [IsEmpty β] : α ≃ β :=
  ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩

/-- If `α` is an empty type, then it is equivalent to the `Empty` type. -/
/-
**Equiv.equivEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：equivEmpty (α : Sort u) [IsEmpty α] : α ≃ Empty
参数：α : Sort u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is an empty type, then it is equivalent to the `Empty` type.
-/
def equivEmpty (α : Sort u) [IsEmpty α] : α ≃ Empty := equivOfIsEmpty α _

/-- If `α` is an empty type, then it is equivalent to the `PEmpty` type in any universe. -/
/-
**Equiv.equivPEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：equivPEmpty (α : Sort v) [IsEmpty α] : α ≃ PEmpty.{u}
参数：α : Sort v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is an empty type, then it is equivalent to the `PEmpty` type in any unive
rse.
-/
def equivPEmpty (α : Sort v) [IsEmpty α] : α ≃ PEmpty.{u} := equivOfIsEmpty α _

/-- `α` is equivalent to an empty type iff `α` is empty. -/
/-
**Equiv.equivEmptyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：equivEmptyEquiv (α : Sort u) : α ≃ Empty ≃ IsEmpty α
参数：α : Sort u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α` is equivalent to an empty type iff `α` is empty.
-/
def equivEmptyEquiv (α : Sort u) : α ≃ Empty ≃ IsEmpty α :=
  ⟨fun e => Function.isEmpty e, @equivEmpty α, fun e => ext fun x => (e x).elim, fun _ => rfl⟩

/-- The `Sort` of proofs of a false proposition is equivalent to `PEmpty`. -/
/-
**Equiv.propEquivPEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：propEquivPEmpty {p : Prop} (h : ¬p) : p ≃ PEmpty
参数：h : ¬p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Sort` of proofs of a false proposition is equivalent to `PEmpty`.
-/
def propEquivPEmpty {p : Prop} (h : ¬p) : p ≃ PEmpty := @equivPEmpty p <| IsEmpty.prop_iff.2 h

/-- If both `α` and `β` have a unique element, then `α ≃ β`. -/
@[simps (attr := grind =)]
/-
**Equiv.ofUnique** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：ofUnique (α β : Sort _) [Unique.{u} α] [Unique.{v} β] : α ≃ β where toFun
参数：α β : Sort _。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If both `α` and `β` have a unique element, then `α ≃ β`.
-/
def ofUnique (α β : Sort _) [Unique.{u} α] [Unique.{v} β] : α ≃ β where
  toFun := default
  invFun := default
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- If `α` has a unique element, then it is equivalent to any `PUnit`. -/
@[simps! (attr := grind =)]
/-
**Equiv.equivPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：equivPUnit (α : Sort u) [Unique α] : α ≃ PUnit.{v}
参数：α : Sort u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` has a unique element, then it is equivalent to any `PUnit`.
-/
def equivPUnit (α : Sort u) [Unique α] : α ≃ PUnit.{v} := ofUnique α _

/-- The `Sort` of proofs of a true proposition is equivalent to `PUnit`. -/
/-
**Equiv.propEquivPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：propEquivPUnit {p : Prop} (h : p) : p ≃ PUnit.{0}
参数：h : p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Sort` of proofs of a true proposition is equivalent to `PUnit`.
-/
def propEquivPUnit {p : Prop} (h : p) : p ≃ PUnit.{0} := @equivPUnit p <| uniqueProp h

/-- `ULift α` is equivalent to `α`. -/
@[simps (attr := grind =) -fullyApplied apply symm_apply]
/-
**Equiv.ulift** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type v} → ULift.{u, v} α ≃ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ULift.up_down`：∀ {α : Type u} (b : ULift.{v, u} α), { down := b.down } =
 b
· 使用定理 `ULift.down_up`：∀ {α : Type u} (a : α), { down := a }.down = a

--- 原说明 ---
`ULift α` is equivalent to `α`.
-/
protected def ulift {α : Type v} : ULift.{u} α ≃ α :=
  ⟨ULift.down, ULift.up, ULift.up_down, ULift.down_up.{v, u}⟩

/-- `PLift α` is equivalent to `α`. -/
@[simps (attr := grind =) -fullyApplied apply symm_apply]
/-
**Equiv.plift** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Sort u} → PLift α ≃ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PLift.up_down`：∀ {α : Sort u} (b : PLift α), { down := b.down } = b
· 使用定理 `PLift.down_up`：∀ {α : Sort u} (a : α), { down := a }.down = a

--- 原说明 ---
`PLift α` is equivalent to `α`.
-/
protected def plift : PLift α ≃ α := ⟨PLift.down, PLift.up, PLift.up_down, PLift.down_up⟩

/-- equivalence of propositions is the same as iff -/
/-
**Equiv.ofIff** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：ofIff {P Q : Prop} (h : P ↔ Q) : P ≃ Q
参数：h : P ↔ Q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
equivalence of propositions is the same as iff
-/
def ofIff {P Q : Prop} (h : P ↔ Q) : P ≃ Q := ⟨h.mp, h.mpr, fun _ => rfl, fun _ => rfl⟩

/-- If `α₁` is equivalent to `α₂` and `β₁` is equivalent to `β₂`, then the type of maps `α₁ → β₁`
is equivalent to the type of maps `α₂ → β₂`. -/
@[simps (attr := grind =) apply]
/-
**Equiv.arrowCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：arrowCongr {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : (α₁ -> β₁
) ≃ (α₂ -> β₂) where toFun f
参数：e₁ : α₁ ≃ α₂；e₂ : β₁ ≃ β₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α₁` is equivalent to `α₂` and `β₁` is equivalent to `β₂`, then the type of m
aps `α₁ → β₁`
is equivalent to the type of maps `α₂ → β₂`.
-/
def arrowCongr {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) where
  toFun f := e₂ ∘ f ∘ e₁.symm
  invFun f := e₂.symm ∘ f ∘ e₁
  left_inv f := by grind
  right_inv f := by grind
/-
**Equiv.arrowCongr_comp** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：arrowCongr_comp {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) 
(ec : γ₁ ≃ γ₂) (f : α₁ -> β₁) (g : β₁ -> γ₁) : arrowCongr ea ec (g ∘ f) = arrowC
ongr eb ec g ∘ arrowCongr ea eb f
参数：ea : α₁ ≃ α₂；eb : β₁ ≃ β₂；ec : γ₁ ≃ γ₂；f : α₁ -> β₁；g : β₁ -> γ₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongr_comp {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (f : α₁ → β₁) (g : β₁ → γ₁) :
    arrowCongr ea ec (g ∘ f) = arrowCongr eb ec g ∘ arrowCongr ea eb f := by grind
/-
**Equiv.arrowCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2}, (Equiv.refl α).arrowCongr (Equiv.refl β) 
= Equiv.refl (α → β)
参数：Equiv.refl α；Equiv.refl β；α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
@[simp] theorem arrowCongr_refl {α β : Sort*} :
    arrowCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α → β) := rfl
/-
**Equiv.arrowCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α₁ : Sort u_1} {α₂ : Sort u_2} {α₃ : Sort u_3} {β₁ : Sort u_4} {β₂ : So
rt u_5} {β₃ : Sort u_6} (e₁ : α₁ ≃ α₂)   (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β
₂ ≃ β₃),   (e₁.trans e₂).arrowCongr (e₁'.trans e₂') = (e₁.arrowCongr e₁').trans 
(e₂.arrowCongr e₂')
参数：e₁ : α₁ ≃ α₂；e₁' : β₁ ≃ β₂；e₂ : α₂ ≃ α₃；e₂' : β₂ ≃ β₃；e₁.trans e₂；e₁'.trans e
₂'；e₁.arrowCongr e₁'；e₂.arrowCongr e₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
@[simp] theorem arrowCongr_trans {α₁ α₂ α₃ β₁ β₂ β₃ : Sort*}
    (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') := rfl
/-
**Equiv.arrowCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α₁ : Sort u_1} {α₂ : Sort u_2} {β₁ : Sort u_3} {β₂ : Sort u_4} (e₁ : α₁
 ≃ α₂) (e₂ : β₁ ≃ β₂),   (e₁.arrowCongr e₂).symm = e₁.symm.arrowCongr e₂.symm
参数：e₁ : α₁ ≃ α₂；e₂ : β₁ ≃ β₂；e₁.arrowCongr e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp, grind =] theorem arrowCongr_symm {α₁ α₂ β₁ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm := rfl

/-- A version of `Equiv.arrowCongr` in `Type`, rather than `Sort`.

The `equiv_rw` tactic is not able to use the default `Sort` level `Equiv.arrowCongr`,
because Lean's universe rules will not unify `?l_1` with `imax (1 ?m_1)`.
-/
@[simps! (attr := grind =) apply]
/-
**Equiv.arrowCongr'** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：arrowCongr' {α₁ β₁ α₂ β₂ : Type*} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ -> β
₁) ≃ (α₂ -> β₂)
参数：hα : α₁ ≃ α₂；hβ : β₁ ≃ β₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Equiv.arrowCongr` in `Type`, rather than `Sort`.

The `equiv_rw` tactic is not able to use the default `Sort` level `Equiv.arrowCo
ngr`,
because Lean's universe rules will not unify `?l_1` with `imax (1 ?m_1)`.
-/
def arrowCongr' {α₁ β₁ α₂ β₂ : Type*} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
  Equiv.arrowCongr hα hβ
/-
**Equiv.arrowCongr'_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2}, (Equiv.refl α).arrowCongr' (Equiv.refl β)
 = Equiv.refl (α → β)
参数：Equiv.refl α；Equiv.refl β；α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
@[simp] theorem arrowCongr'_refl {α β : Type*} :
    arrowCongr' (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α → β) := rfl
/-
**Equiv.arrowCongr'_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} {α₃ : Ty
pe u_5} {β₃ : Type u_6} (e₁ : α₁ ≃ α₂)   (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β
₂ ≃ β₃),   (e₁.trans e₂).arrowCongr' (e₁'.trans e₂') = (e₁.arrowCongr' e₁').tran
s (e₂.arrowCongr' e₂')
参数：e₁ : α₁ ≃ α₂；e₁' : β₁ ≃ β₂；e₂ : α₂ ≃ α₃；e₂' : β₂ ≃ β₃；e₁.trans e₂；e₁'.trans e
₂'；e₁.arrowCongr' e₁'；e₂.arrowCongr' e₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
@[simp] theorem arrowCongr'_trans {α₁ α₂ β₁ β₂ α₃ β₃ : Type*}
    (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    arrowCongr' (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr' e₁ e₁').trans (arrowCongr' e₂ e₂') :=
  rfl
/-
**Equiv.arrowCongr'_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} (e₁ : α₁
 ≃ α₂) (e₂ : β₁ ≃ β₂),   (e₁.arrowCongr' e₂).symm = e₁.symm.arrowCongr' e₂.symm
参数：e₁ : α₁ ≃ α₂；e₂ : β₁ ≃ β₂；e₁.arrowCongr' e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp, grind =] theorem arrowCongr'_symm {α₁ α₂ β₁ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr' e₁ e₂).symm = arrowCongr' e₁.symm e₂.symm := rfl

/-- Conjugate a map `f : α → α` by an equivalence `α ≃ β`. -/
/-
**Equiv.conj** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Sort u} → {β : Sort v} → α ≃ β → (α → α) ≃ (β → β)
参数：α → α；β → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugate a map `f : α → α` by an equivalence `α ≃ β`.
-/
@[simps! (attr := grind =) apply] def conj (e : α ≃ β) : (α → α) ≃ (β → β) := arrowCongr e e
/-
**Equiv.conj_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u}, (Equiv.refl α).conj = Equiv.refl (α → α)
参数：Equiv.refl α；α → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Conjugate a map `f : α → α` by an equivalence `α ≃ β`.
-/
@[simp] theorem conj_refl : conj (Equiv.refl α) = Equiv.refl (α → α) := rfl
/-
**Equiv.conj_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.conj.symm = e.symm.conj
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Conjugate a map `f : α → α` by an equivalence `α ≃ β`.
-/
@[simp, grind =] theorem conj_symm (e : α ≃ β) : e.conj.symm = e.symm.conj := rfl
/-
**Equiv.conj_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {γ : Sort w} (e₁ : α ≃ β) (e₂ : β ≃ γ), (e₁.tr
ans e₂).conj = e₁.conj.trans e₂.conj
参数：e₁ : α ≃ β；e₂ : β ≃ γ；e₁.trans e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Conjugate a map `f : α → α` by an equivalence `α ≃ β`.
-/
@[simp] theorem conj_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    (e₁.trans e₂).conj = e₁.conj.trans e₂.conj := rfl

-- This should not be a simp lemma as long as `(∘)` is reducible:
-- when `(∘)` is reducible, Lean can unify `f₁ ∘ f₂` with any `g` using
-- `f₁ := g` and `f₂ := fun x ↦ x`. This causes nontermination.
/-
**Equiv.conj_comp** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：conj_comp (e : α ≃ β) (f₁ f₂ : α -> α) : e.conj (f₁ ∘ f₂) = e.conj f₁ ∘ e.
conj f₂
参数：e : α ≃ β；f₁ f₂ : α -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.arrowCongr_comp`：arrowCongr_comp {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea :
 α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂) (f : α₁ -> β₁) (g : β₁ -> γ₁) : arrowCon
gr ea ec (g…
-/
theorem conj_comp (e : α ≃ β) (f₁ f₂ : α → α) : e.conj (f₁ ∘ f₂) = e.conj f₁ ∘ e.conj f₂ := by
  apply arrowCongr_comp
/-
**Equiv.eq_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：eq_comp_symm {α β γ} (e : α ≃ β) (f : β -> γ) (g : α -> γ) : f = g ∘ e.sym
m ↔ f ∘ e = g
参数：e : α ≃ β；f : β -> γ；g : α -> γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem eq_comp_symm {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) : f = g ∘ e.symm ↔ f ∘ e = g :=
  (e.arrowCongr (Equiv.refl γ)).symm_apply_eq.symm
/-
**Equiv.comp_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：comp_symm_eq {α β γ} (e : α ≃ β) (f : β -> γ) (g : α -> γ) : g ∘ e.symm = 
f ↔ g = f ∘ e
参数：e : α ≃ β；f : β -> γ；g : α -> γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem comp_symm_eq {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) : g ∘ e.symm = f ↔ g = f ∘ e :=
  (e.arrowCongr (Equiv.refl γ)).eq_symm_apply.symm
/-
**Equiv.eq_symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：eq_symm_comp {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ -> β) : f = e.symm ∘ 
g ↔ e ∘ f = g
参数：e : α ≃ β；f : γ -> α；g : γ -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem eq_symm_comp {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) : f = e.symm ∘ g ↔ e ∘ f = g :=
  ((Equiv.refl γ).arrowCongr e).eq_symm_apply
/-
**Equiv.symm_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：symm_comp_eq {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ -> β) : e.symm ∘ g = 
f ↔ g = e ∘ f
参数：e : α ≃ β；f : γ -> α；g : γ -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem symm_comp_eq {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) : e.symm ∘ g = f ↔ g = e ∘ f :=
  ((Equiv.refl γ).arrowCongr e).symm_apply_eq
/-
**Equiv.trans_eq_refl_iff_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：trans_eq_refl_iff_eq_symm {f : α ≃ β} {g : β ≃ α} : f.trans g = Equiv.refl
 α ↔ f = g.symm
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.coe_inj`：∀ {α : Sort u} {β : Sort v} {e₁ e₂ : α ≃ β}, ⇑e₁ = ⇑e₂ ↔ 
e₁ = e₂
· 使用定理 `Equiv.coe_trans`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} (f : α ≃ β) (g
 : β ≃ γ), ⇑(f.trans g) = ⇑g ∘ ⇑f
· 使用定理 `Equiv.coe_refl`：∀ {α : Sort u}, ⇑(Equiv.refl α) = id
· 使用定理 `Equiv.eq_symm_comp`：eq_symm_comp {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ
 -> β) : f = e.symm ∘ g ↔ e ∘ f = g
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem trans_eq_refl_iff_eq_symm {f : α ≃ β} {g : β ≃ α} :
    f.trans g = Equiv.refl α ↔ f = g.symm := by
  rw [← Equiv.coe_inj, coe_trans, coe_refl, ← eq_symm_comp, comp_id, Equiv.coe_inj]
/-
**Equiv.trans_eq_refl_iff_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：trans_eq_refl_iff_symm_eq {f : α ≃ β} {g : β ≃ α} : f.trans g = Equiv.refl
 α ↔ f.symm = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans_eq_refl_iff_eq_symm`：trans_eq_refl_iff_eq_symm {f : α ≃ β} {
g : β ≃ α} : f.trans g = Equiv.refl α ↔ f = g.symm
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem trans_eq_refl_iff_symm_eq {f : α ≃ β} {g : β ≃ α} :
    f.trans g = Equiv.refl α ↔ f.symm = g := by
  rw [trans_eq_refl_iff_eq_symm]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ h ▸ rfl⟩
/-
**Equiv.eq_symm_iff_trans_eq_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：eq_symm_iff_trans_eq_refl {f : α ≃ β} {g : β ≃ α} : f = g.symm ↔ f.trans g
 = Equiv.refl α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans_eq_refl_iff_eq_symm`：trans_eq_refl_iff_eq_symm {f : α ≃ β} {
g : β ≃ α} : f.trans g = Equiv.refl α ↔ f = g.symm
-/
theorem eq_symm_iff_trans_eq_refl {f : α ≃ β} {g : β ≃ α} :
    f = g.symm ↔ f.trans g = Equiv.refl α :=
  trans_eq_refl_iff_eq_symm.symm
/-
**Equiv.symm_eq_iff_trans_eq_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：symm_eq_iff_trans_eq_refl {f : α ≃ β} {g : β ≃ α} : f.symm = g ↔ f.trans g
 = Equiv.refl α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans_eq_refl_iff_symm_eq`：trans_eq_refl_iff_symm_eq {f : α ≃ β} {
g : β ≃ α} : f.trans g = Equiv.refl α ↔ f.symm = g
-/
theorem symm_eq_iff_trans_eq_refl {f : α ≃ β} {g : β ≃ α} :
    f.symm = g ↔ f.trans g = Equiv.refl α :=
  trans_eq_refl_iff_symm_eq.symm

/-- `PUnit` sorts in any two universes are equivalent. -/
/-
**Equiv.punitEquivPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：punitEquivPUnit : PUnit.{v} ≃ PUnit.{w} where toFun _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PUnit` sorts in any two universes are equivalent.
-/
def punitEquivPUnit : PUnit.{v} ≃ PUnit.{w} where
  toFun _ := .unit
  invFun _ := .unit

/-- `Prop` is noncomputably equivalent to `Bool`. -/
/-
**Equiv.propEquivBool** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：propEquivBool : Prop ≃ Bool where toFun p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prop` is noncomputably equivalent to `Bool`.
-/
noncomputable def propEquivBool : Prop ≃ Bool where
  toFun p := @decide p (Classical.propDecidable _)
  invFun b := b
  left_inv p := by simp
  right_inv b := by simp

section

/-- The sort of maps to `PUnit.{v}` is equivalent to `PUnit.{w}`. -/
/-
**Equiv.arrowPUnitEquivPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：arrowPUnitEquivPUnit (α : Sort*) : (α -> PUnit.{v}) ≃ PUnit.{w} where toFu
n _
参数：α : Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sort of maps to `PUnit.{v}` is equivalent to `PUnit.{w}`.
-/
def arrowPUnitEquivPUnit (α : Sort*) : (α → PUnit.{v}) ≃ PUnit.{w} where
  toFun _ := .unit
  invFun _ _ := .unit

/-- The equivalence `(∀ i, β i) ≃ β ⋆` when the domain of `β` only contains `⋆` -/
@[simps (attr := grind =) -fullyApplied]
/-
**Equiv.piUnique** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：piUnique [Unique α] (β : α -> Sort*) : (forall i, β i) ≃ β default where t
oFun f
参数：β : α -> Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `(∀ i, β i) ≃ β ⋆` when the domain of `β` only contains `⋆`
-/
def piUnique [Unique α] (β : α → Sort*) : (∀ i, β i) ≃ β default where
  toFun f := f default
  invFun := uniqueElim
  left_inv f := by ext i; cases Unique.eq_default i; rfl

/-- If `α` has a unique term, then the type of function `α → β` is equivalent to `β`. -/
@[simps! (attr := grind =) -fullyApplied apply symm_apply]
/-
**Equiv.funUnique** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：funUnique (α β) [Unique.{u} α] : (α -> β) ≃ β
参数：α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` has a unique term, then the type of function `α → β` is equivalent to `β`
.
-/
def funUnique (α β) [Unique.{u} α] : (α → β) ≃ β := piUnique _

/-- The sort of maps from `PUnit` is equivalent to the codomain. -/
/-
**Equiv.punitArrowEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：punitArrowEquiv (α : Sort*) : (PUnit.{u} -> α) ≃ α
参数：α : Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sort of maps from `PUnit` is equivalent to the codomain.
-/
def punitArrowEquiv (α : Sort*) : (PUnit.{u} → α) ≃ α := funUnique PUnit.{u} α

/-- The sort of maps from `True` is equivalent to the codomain. -/
/-
**Equiv.trueArrowEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：trueArrowEquiv (α : Sort*) : (True -> α) ≃ α
参数：α : Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sort of maps from `True` is equivalent to the codomain.
-/
def trueArrowEquiv (α : Sort*) : (True → α) ≃ α := funUnique _ _

/-- The sort of maps from a type that `IsEmpty` is equivalent to `PUnit`. -/
/-
**Equiv.arrowPUnitOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：arrowPUnitOfIsEmpty (α β : Sort*) [IsEmpty α] : (α -> β) ≃ PUnit.{u} where
 toFun _
参数：α β : Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sort of maps from a type that `IsEmpty` is equivalent to `PUnit`.
-/
def arrowPUnitOfIsEmpty (α β : Sort*) [IsEmpty α] : (α → β) ≃ PUnit.{u} where
  toFun _ := PUnit.unit
  invFun _ := isEmptyElim
  left_inv _ := funext isEmptyElim

/-- The sort of maps from `Empty` is equivalent to `PUnit`. -/
/-
**Equiv.emptyArrowEquivPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：emptyArrowEquivPUnit (α : Sort*) : (Empty -> α) ≃ PUnit.{u}
参数：α : Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sort of maps from `Empty` is equivalent to `PUnit`.
-/
def emptyArrowEquivPUnit (α : Sort*) : (Empty → α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _

/-- The sort of maps from `PEmpty` is equivalent to `PUnit`. -/
/-
**Equiv.pemptyArrowEquivPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：pemptyArrowEquivPUnit (α : Sort*) : (PEmpty -> α) ≃ PUnit.{u}
参数：α : Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sort of maps from `PEmpty` is equivalent to `PUnit`.
-/
def pemptyArrowEquivPUnit (α : Sort*) : (PEmpty → α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _

/-- The sort of maps from `False` is equivalent to `PUnit`. -/
/-
**Equiv.falseArrowEquivPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：falseArrowEquivPUnit (α : Sort*) : (False -> α) ≃ PUnit.{u}
参数：α : Sort*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
The sort of maps from `False` is equivalent to `PUnit`.
-/
def falseArrowEquivPUnit (α : Sort*) : (False → α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _

end

section

/-- A `PSigma`-type is equivalent to the corresponding `Sigma`-type. -/
@[simps (attr := grind =) apply symm_apply]
/-
**Equiv.psigmaEquivSigma** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：psigmaEquivSigma {α} (β : α -> Type*) : (Σ' i, β i) ≃ Σ i, β i where toFun
 a
参数：β : α -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PSigma`-type is equivalent to the corresponding `Sigma`-type.
-/
def psigmaEquivSigma {α} (β : α → Type*) : (Σ' i, β i) ≃ Σ i, β i where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩

/-- A `PSigma`-type is equivalent to the corresponding `Sigma`-type. -/
@[simps (attr := grind =) apply symm_apply]
/-
**Equiv.psigmaEquivSigmaPLift** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：psigmaEquivSigmaPLift {α} (β : α -> Sort*) : (Σ' i, β i) ≃ Σ i : PLift α, 
PLift (β i.down) where toFun a
参数：β : α -> Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PSigma`-type is equivalent to the corresponding `Sigma`-type.
-/
def psigmaEquivSigmaPLift {α} (β : α → Sort*) : (Σ' i, β i) ≃ Σ i : PLift α, PLift (β i.down) where
  toFun a := ⟨PLift.up a.1, PLift.up a.2⟩
  invFun a := ⟨a.1.down, a.2.down⟩

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ' a, β₁ a` and
`Σ' a, β₂ a`. -/
@[simps (attr := grind =) apply]
/-
**Equiv.psigmaCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：psigmaCongrRight {β₁ β₂ : α -> Sort*} (F : forall a, β₁ a ≃ β₂ a) : (Σ' a,
 β₁ a) ≃ Σ' a, β₂ a where toFun a
参数：F : forall a, β₁ a ≃ β₂ a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ'
 a, β₁ a` and
`Σ' a, β₂ a`.
-/
def psigmaCongrRight {β₁ β₂ : α → Sort*} (F : ∀ a, β₁ a ≃ β₂ a) : (Σ' a, β₁ a) ≃ Σ' a, β₂ a where
  toFun a := ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv := by grind
  right_inv := by grind
/-
**Equiv.psigmaCongrRight_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：psigmaCongrRight_trans {α} {β₁ β₂ β₃ : α -> Sort*} (F : forall a, β₁ a ≃ β
₂ a) (G : forall a, β₂ a ≃ β₃ a) : (psigmaCongrRight F).trans (psigmaCongrRight 
G) = psigmaCongrRight fun a => (F a).trans (G a)
参数：F : forall a, β₁ a ≃ β₂ a；G : forall a, β₂ a ≃ β₃ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem psigmaCongrRight_trans {α} {β₁ β₂ β₃ : α → Sort*}
    (F : ∀ a, β₁ a ≃ β₂ a) (G : ∀ a, β₂ a ≃ β₃ a) :
    (psigmaCongrRight F).trans (psigmaCongrRight G) =
      psigmaCongrRight fun a => (F a).trans (G a) := rfl

@[grind =]
/-
**Equiv.psigmaCongrRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：psigmaCongrRight_symm {α} {β₁ β₂ : α -> Sort*} (F : forall a, β₁ a ≃ β₂ a)
 : (psigmaCongrRight F).symm = psigmaCongrRight fun a => (F a).symm
参数：F : forall a, β₁ a ≃ β₂ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem psigmaCongrRight_symm {α} {β₁ β₂ : α → Sort*} (F : ∀ a, β₁ a ≃ β₂ a) :
    (psigmaCongrRight F).symm = psigmaCongrRight fun a => (F a).symm := rfl

@[simp]
/-
**Equiv.psigmaCongrRight_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：psigmaCongrRight_refl {α} {β : α -> Sort*} : (psigmaCongrRight fun a => Eq
uiv.refl (β a)) = Equiv.refl (Σ' a, β a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem psigmaCongrRight_refl {α} {β : α → Sort*} :
    (psigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ' a, β a) := rfl

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ a, β₁ a` and
`Σ a, β₂ a`. -/
@[simps (attr := grind =) apply]
/-
**Equiv.sigmaCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaCongrRight {α} {β₁ β₂ : α -> Type*} (F : forall a, β₁ a ≃ β₂ a) : (Σ 
a, β₁ a) ≃ Σ a, β₂ a where toFun a
参数：F : forall a, β₁ a ≃ β₂ a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ 
a, β₁ a` and
`Σ a, β₂ a`.
-/
def sigmaCongrRight {α} {β₁ β₂ : α → Type*} (F : ∀ a, β₁ a ≃ β₂ a) : (Σ a, β₁ a) ≃ Σ a, β₂ a where
  toFun a := ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv := by grind
  right_inv := by grind
/-
**Equiv.sigmaCongrRight_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sigmaCongrRight_trans {α} {β₁ β₂ β₃ : α -> Type*} (F : forall a, β₁ a ≃ β₂
 a) (G : forall a, β₂ a ≃ β₃ a) : (sigmaCongrRight F).trans (sigmaCongrRight G) 
= sigmaCongrRight fun a => (F a).trans (G a)
参数：F : forall a, β₁ a ≃ β₂ a；G : forall a, β₂ a ≃ β₃ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem sigmaCongrRight_trans {α} {β₁ β₂ β₃ : α → Type*}
    (F : ∀ a, β₁ a ≃ β₂ a) (G : ∀ a, β₂ a ≃ β₃ a) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) =
      sigmaCongrRight fun a => (F a).trans (G a) := rfl

@[grind =]
/-
**Equiv.sigmaCongrRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sigmaCongrRight_symm {α} {β₁ β₂ : α -> Type*} (F : forall a, β₁ a ≃ β₂ a) 
: (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm
参数：F : forall a, β₁ a ≃ β₂ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem sigmaCongrRight_symm {α} {β₁ β₂ : α → Type*} (F : ∀ a, β₁ a ≃ β₂ a) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm := rfl

@[simp]
/-
**Equiv.sigmaCongrRight_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：sigmaCongrRight_refl {α} {β : α -> Type*} : (sigmaCongrRight fun a => Equi
v.refl (β a)) = Equiv.refl (Σ a, β a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem sigmaCongrRight_refl {α} {β : α → Type*} :
    (sigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ a, β a) := rfl

/-- A `PSigma` with `Prop` fibers is equivalent to the subtype. -/
/-
**Equiv.psigmaEquivSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：psigmaEquivSubtype {α : Type v} (P : α -> Prop) : (Σ' i, P i) ≃ Subtype P 
where toFun x
参数：P : α -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
A `PSigma` with `Prop` fibers is equivalent to the subtype.
-/
def psigmaEquivSubtype {α : Type v} (P : α → Prop) : (Σ' i, P i) ≃ Subtype P where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩

/-- A `Sigma` with `PLift` fibers is equivalent to the subtype. -/
/-
**Equiv.sigmaPLiftEquivSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaPLiftEquivSubtype {α : Type v} (P : α -> Prop) : (Σ i, PLift (P i)) ≃
 Subtype P
参数：P : α -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A `Sigma` with `PLift` fibers is equivalent to the subtype.
-/
def sigmaPLiftEquivSubtype {α : Type v} (P : α → Prop) : (Σ i, PLift (P i)) ≃ Subtype P :=
  ((psigmaEquivSigma _).symm.trans
    (psigmaCongrRight fun _ => Equiv.plift)).trans (psigmaEquivSubtype P)

/-- A `Sigma` with `fun i ↦ ULift (PLift (P i))` fibers is equivalent to `{ x // P x }`.
Variant of `sigmaPLiftEquivSubtype`.
-/
/-
**Equiv.sigmaULiftPLiftEquivSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaULiftPLiftEquivSubtype {α : Type v} (P : α -> Prop) : (Σ i, ULift (PL
ift (P i))) ≃ Subtype P
参数：P : α -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
A `Sigma` with `fun i ↦ ULift (PLift (P i))` fibers is equivalent to `{ x // P x
 }`.
Variant of `sigmaPLiftEquivSubtype`.
-/
def sigmaULiftPLiftEquivSubtype {α : Type v} (P : α → Prop) :
    (Σ i, ULift (PLift (P i))) ≃ Subtype P :=
  (sigmaCongrRight fun _ => Equiv.ulift).trans (sigmaPLiftEquivSubtype P)

namespace Perm

/-- A family of permutations `Π a, Perm (β a)` generates a permutation `Perm (Σ a, β₁ a)`. -/
/-
**Equiv.Perm.sigmaCongrRight** 是 Mathlib 中的一个缩写定义，位于命名空间 `Equiv.Perm`。
形式化陈述：sigmaCongrRight {α} {β : α -> Sort _} (F : forall a, Perm (β a)) : Perm (Σ
 a, β a)
参数：F : forall a, Perm (β a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of permutations `Π a, Perm (β a)` generates a permutation `Perm (Σ a, β
₁ a)`.
-/
abbrev sigmaCongrRight {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) : Perm (Σ a, β a) :=
  Equiv.sigmaCongrRight F
/-
**Equiv.Perm.sigmaCongrRight_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Type u_1} {β : α → Type u_2} (F G : (a : α) → Equiv.Perm (β a)),   
Equiv.trans (Equiv.Perm.sigmaCongrRight F) (Equiv.Perm.sigmaCongrRight G) =     
Equiv.Perm.sigmaCongrRight fun a => Equiv.trans (F a) (G a)
参数：F G : (a : α) → Equiv.Perm (β a)；Equiv.Perm.sigmaCongrRight F；Equiv.Perm.sigm
aCongrRight G；F a；G a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
@[simp] theorem sigmaCongrRight_trans {α} {β : α → Sort _}
    (F : ∀ a, Perm (β a)) (G : ∀ a, Perm (β a)) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) = sigmaCongrRight fun a => (F a).trans (G a) :=
  rfl
/-
**Equiv.Perm.sigmaCongrRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Type u_1} {β : α → Type u_2} (F : (a : α) → Equiv.Perm (β a)),   Eq
uiv.symm (Equiv.Perm.sigmaCongrRight F) = Equiv.Perm.sigmaCongrRight fun a => Eq
uiv.symm (F a)
参数：F : (a : α) → Equiv.Perm (β a)；Equiv.Perm.sigmaCongrRight F；F a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem sigmaCongrRight_symm {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm :=
  rfl
/-
**Equiv.Perm.sigmaCongrRight_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Type u_1} {β : α → Type u_2}, (Equiv.Perm.sigmaCongrRight fun a => 
Equiv.refl (β a)) = Equiv.refl ((a : α) × β a)
参数：Equiv.Perm.sigmaCongrRight fun a => Equiv.refl (β a)；(a : α) × β a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
@[simp] theorem sigmaCongrRight_refl {α} {β : α → Sort _} :
    (sigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ a, β a) :=
  rfl

end Perm

/-- `Function.swap` as an equivalence. -/
@[simps (attr := grind =) -fullyApplied]
/-
**Equiv.functionSwap** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：functionSwap (α β : Sort*) (γ : α -> β -> Sort*) : ((a : α) -> (b : β) -> 
γ a b) ≃ ((b : β) -> (a : α) -> γ a b) where toFun
参数：α β : Sort*；γ : α -> β -> Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.swap` as an equivalence.
-/
def functionSwap (α β : Sort*) (γ : α → β → Sort*) :
    ((a : α) → (b : β) → γ a b) ≃ ((b : β) → (a : α) → γ a b) where
  toFun := Function.swap
  invFun := Function.swap
/-
**Equiv._root_.Function.swap_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.swap_bijective {α β : Sort*} {γ : α → β → Sort*} :
    Function.Bijective (@Function.swap _ _ γ) :=
  functionSwap _ _ _ |>.bijective

/-- An equivalence `f : α₁ ≃ α₂` generates an equivalence between `Σ a, β (f a)` and `Σ a, β a`. -/
@[simps (attr := grind =) apply]
/-
**Equiv.sigmaCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaCongrLeft {α₁ α₂ : Type*} {β : α₂ -> Sort _} (e : α₁ ≃ α₂) : (Σ a : α
₁, β (e a)) ≃ Σ a : α₂, β a where toFun a
参数：e : α₁ ≃ α₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence `f : α₁ ≃ α₂` generates an equivalence between `Σ a, β (f a)` and
 `Σ a, β a`.
-/
def sigmaCongrLeft {α₁ α₂ : Type*} {β : α₂ → Sort _} (e : α₁ ≃ α₂) :
    (Σ a : α₁, β (e a)) ≃ Σ a : α₂, β a where
  toFun a := ⟨e a.1, a.2⟩
  invFun a := ⟨e.symm a.1, (e.right_inv' a.1).symm ▸ a.2⟩
  left_inv := fun ⟨a, b⟩ => by simp
  right_inv := fun ⟨a, b⟩ => by simp

/-- Transporting a sigma type through an equivalence of the base -/
/-
**Equiv.sigmaCongrLeft'** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaCongrLeft' {α₁ α₂} {β : α₁ -> Sort _} (f : α₁ ≃ α₂) : (Σ a : α₁, β a)
 ≃ Σ a : α₂, β (f.symm a)
参数：f : α₁ ≃ α₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transporting a sigma type through an equivalence of the base
-/
def sigmaCongrLeft' {α₁ α₂} {β : α₁ → Sort _} (f : α₁ ≃ α₂) :
    (Σ a : α₁, β a) ≃ Σ a : α₂, β (f.symm a) := (sigmaCongrLeft f.symm).symm

/-- Transporting a sigma type through an equivalence of the base and a family of equivalences
of matching fibers -/
/-
**Equiv.sigmaCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaCongr {α₁ α₂} {β₁ : α₁ -> Sort _} {β₂ : α₂ -> Sort _} (f : α₁ ≃ α₂) (
F : forall a, β₁ a ≃ β₂ (f a)) : Sigma β₁ ≃ Sigma β₂
参数：f : α₁ ≃ α₂；F : forall a, β₁ a ≃ β₂ (f a)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Transporting a sigma type through an equivalence of the base and a family of equ
ivalences
of matching fibers
-/
def sigmaCongr {α₁ α₂} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _} (f : α₁ ≃ α₂)
    (F : ∀ a, β₁ a ≃ β₂ (f a)) : Sigma β₁ ≃ Sigma β₂ :=
  (sigmaCongrRight F).trans (sigmaCongrLeft f)

/-- `Sigma` type with a constant fiber is equivalent to the product. -/
@[simps (attr := mfld_simps, grind =) apply symm_apply]
/-
**Equiv.sigmaEquivProd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaEquivProd (α β : Type*) : (Σ _ : α, β) ≃ α × β where toFun a
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sigma` type with a constant fiber is equivalent to the product.
-/
def sigmaEquivProd (α β : Type*) : (Σ _ : α, β) ≃ α × β where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩

/-- If each fiber of a `Sigma` type is equivalent to a fixed type, then the sigma type
is equivalent to the product. -/
/-
**Equiv.sigmaEquivProdOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaEquivProdOfEquiv {α β} {β₁ : α -> Sort _} (F : forall a, β₁ a ≃ β) : 
Sigma β₁ ≃ α × β
参数：F : forall a, β₁ a ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If each fiber of a `Sigma` type is equivalent to a fixed type, then the sigma ty
pe
is equivalent to the product.
-/
def sigmaEquivProdOfEquiv {α β} {β₁ : α → Sort _} (F : ∀ a, β₁ a ≃ β) : Sigma β₁ ≃ α × β :=
  (sigmaCongrRight F).trans (sigmaEquivProd α β)

/-- The dependent product of types is associative up to an equivalence. -/
/-
**Equiv.sigmaAssoc** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sigmaAssoc {α : Type*} {β : α -> Type*} (γ : forall a : α, β a -> Type*) :
 (Σ ab : Σ a : α, β a, γ ab.1 ab.2) ≃ Σ a : α, Σ b : β a, γ a b where toFun x
参数：γ : forall a : α, β a -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dependent product of types is associative up to an equivalence.
-/
def sigmaAssoc {α : Type*} {β : α → Type*} (γ : ∀ a : α, β a → Type*) :
    (Σ ab : Σ a : α, β a, γ ab.1 ab.2) ≃ Σ a : α, Σ b : β a, γ a b where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩

/-- The dependent product of sorts is associative up to an equivalence. -/
/-
**Equiv.pSigmaAssoc** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：pSigmaAssoc {α : Sort*} {β : α -> Sort*} (γ : forall a : α, β a -> Sort*) 
: (Σ' ab : Σ' a : α, β a, γ ab.1 ab.2) ≃ Σ' a : α, Σ' b : β a, γ a b where toFun
 x
参数：γ : forall a : α, β a -> Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dependent product of sorts is associative up to an equivalence.
-/
def pSigmaAssoc {α : Sort*} {β : α → Sort*} (γ : ∀ a : α, β a → Sort*) :
    (Σ' ab : Σ' a : α, β a, γ ab.1 ab.2) ≃ Σ' a : α, Σ' b : β a, γ a b where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩

end

variable {p : α → Prop} {q : β → Prop} (e : α ≃ β)

/-
**Equiv.forall_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e : α ≃ β), (∀ (a : α), q (e a
)) ↔ ∀ (b : β), q b
参数：e : α ≃ β；∀ (a : α), q (e a)；b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
protected lemma forall_congr_right : (∀ a, q (e a)) ↔ ∀ b, q b :=
  ⟨fun h a ↦ by simpa using h (e.symm a), fun h _ ↦ h _⟩
/-
**Equiv.forall_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e : α ≃ β), (∀ (a : α), p a) ↔
 ∀ (b : β), p (e.symm b)
参数：e : α ≃ β；∀ (a : α), p a；b : β；e.symm b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
-/
protected lemma forall_congr_left : (∀ a, p a) ↔ ∀ b, p (e.symm b) :=
  e.symm.forall_congr_right.symm
/-
**Equiv.forall_congr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (e : α ≃ β),   (
∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β), q b)
参数：e : α ≃ β；∀ (a : α), p a ↔ q (e a)；(∀ (a : α), p a) ↔ ∀ (b : β), q b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma forall_congr (h : ∀ a, p a ↔ q (e a)) : (∀ a, p a) ↔ ∀ b, q b :=
  e.forall_congr_left.trans (by simp [h])
/-
**Equiv.forall_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (e : α ≃ β),   (
∀ (b : β), p (e.symm b) ↔ q b) → ((∀ (a : α), p a) ↔ ∀ (b : β), q b)
参数：e : α ≃ β；∀ (b : β), p (e.symm b) ↔ q b；(∀ (a : α), p a) ↔ ∀ (b : β), q b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma forall_congr' (h : ∀ b, p (e.symm b) ↔ q b) : (∀ a, p a) ↔ ∀ b, q b :=
  e.forall_congr_left.trans (by simp [h])
/-
**Equiv.exists_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e : α ≃ β), (∃ a, q (e a)) ↔ ∃
 b, q b
参数：e : α ≃ β；∃ a, q (e a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
protected lemma exists_congr_right : (∃ a, q (e a)) ↔ ∃ b, q b :=
  ⟨fun ⟨_, h⟩ ↦ ⟨_, h⟩, fun ⟨a, h⟩ ↦ ⟨e.symm a, by simpa using h⟩⟩
/-
**Equiv.exists_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e : α ≃ β), (∃ a, p a) ↔ ∃ b, 
p (e.symm b)
参数：e : α ≃ β；∃ a, p a；e.symm b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.exists_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∃ a, q (e a)) ↔ ∃ b, q b
-/
protected lemma exists_congr_left : (∃ a, p a) ↔ ∃ b, p (e.symm b) :=
  e.symm.exists_congr_right.symm
/-
**Equiv.exists_congr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (e : α ≃ β),   (
∀ (a : α), p a ↔ q (e a)) → ((∃ a, p a) ↔ ∃ b, q b)
参数：e : α ≃ β；∀ (a : α), p a ↔ q (e a)；(∃ a, p a) ↔ ∃ b, q b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma exists_congr (h : ∀ a, p a ↔ q (e a)) : (∃ a, p a) ↔ ∃ b, q b :=
  e.exists_congr_left.trans <| by simp [h]
/-
**Equiv.exists_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (e : α ≃ β),   (
∀ (b : β), p (e.symm b) ↔ q b) → ((∃ a, p a) ↔ ∃ b, q b)
参数：e : α ≃ β；∀ (b : β), p (e.symm b) ↔ q b；(∃ a, p a) ↔ ∃ b, q b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma exists_congr' (h : ∀ b, p (e.symm b) ↔ q b) : (∃ a, p a) ↔ ∃ b, q b :=
  e.exists_congr_left.trans <| by simp [h]
/-
**Equiv.exists_subtype_congr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (e : { a // p a 
} ≃ { b // q b }), (∃ a, p a) ↔ ∃ b, q b
参数：e : { a // p a } ≃ { b // q b }；∃ a, p a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma exists_subtype_congr (e : {a // p a} ≃ {b // q b}) : (∃ a, p a) ↔ ∃ b, q b := by
  simp [← nonempty_subtype, nonempty_congr e]
/-
**Equiv.existsUnique_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e : α ≃ β), (∃! a, q (e a)) ↔ 
∃! b, q b
参数：e : α ≃ β；∃! a, q (e a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.exists_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∃ a, p a) ↔ ∃ b, q b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma existsUnique_congr_right : (∃! a, q (e a)) ↔ ∃! b, q b :=
  e.exists_congr <| by simpa using fun _ _ ↦ e.forall_congr (by simp)
/-
**Equiv.existsUnique_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e : α ≃ β), (∃! a, p a) ↔ ∃! b
, p (e.symm b)
参数：e : α ≃ β；∃! a, p a；e.symm b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.existsUnique_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Pro
p} (e : α ≃ β), (∃! a, q (e a)) ↔ ∃! b, q b
-/
protected lemma existsUnique_congr_left : (∃! a, p a) ↔ ∃! b, p (e.symm b) :=
  e.symm.existsUnique_congr_right.symm
/-
**Equiv.existsUnique_congr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (e : α ≃ β),   (
∀ (a : α), p a ↔ q (e a)) → ((∃! a, p a) ↔ ∃! b, q b)
参数：e : α ≃ β；∀ (a : α), p a ↔ q (e a)；(∃! a, p a) ↔ ∃! b, q b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.existsUnique_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop
} (e : α ≃ β), (∃! a, p a) ↔ ∃! b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma existsUnique_congr (h : ∀ a, p a ↔ q (e a)) : (∃! a, p a) ↔ ∃! b, q b :=
  e.existsUnique_congr_left.trans <| by simp [h]
/-
**Equiv.existsUnique_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (e : α ≃ β),   (
∀ (b : β), p (e.symm b) ↔ q b) → ((∃! a, p a) ↔ ∃! b, q b)
参数：e : α ≃ β；∀ (b : β), p (e.symm b) ↔ q b；(∃! a, p a) ↔ ∃! b, q b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.existsUnique_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop
} (e : α ≃ β), (∃! a, p a) ↔ ∃! b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma existsUnique_congr' (h : ∀ b, p (e.symm b) ↔ q b) : (∃! a, p a) ↔ ∃! b, q b :=
  e.existsUnique_congr_left.trans <| by simp [h]
/-
**Equiv.existsUnique_subtype_congr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → Prop} (e : { a // p a 
} ≃ { b // q b }), (∃! a, p a) ↔ ∃! b, q b
参数：e : { a // p a } ≃ { b // q b }；∃! a, p a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma existsUnique_subtype_congr (e : {a // p a} ≃ {b // q b}) :
    (∃! a, p a) ↔ ∃! b, q b := by
  simp [← unique_subtype_iff_existsUnique, unique_iff_subsingleton_and_nonempty,
        nonempty_congr e, subsingleton_congr e]

-- We next build some higher arity versions of `Equiv.forall_congr`.
-- Although they appear to just be repeated applications of `Equiv.forall_congr`,
-- unification of metavariables works better with these versions.
-- In particular, they are necessary in `equiv_rw`.
-- (Stopping at ternary functions seems reasonable: at least in 1-categorical mathematics,
-- it's rare to have axioms involving more than 3 elements at once.)
/-
**Equiv.forall** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem forall₂_congr {α₁ α₂ β₁ β₂ : Sort*} {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (h : ∀ {x y}, p x y ↔ q (eα x) (eβ y)) :
    (∀ x y, p x y) ↔ ∀ x y, q x y :=
  eα.forall_congr fun _ ↦ eβ.forall_congr <| @h _
/-
**Equiv.forall** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem forall₂_congr' {α₁ α₂ β₁ β₂ : Sort*} {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (h : ∀ {x y}, p (eα.symm x) (eβ.symm y) ↔ q x y) :
    (∀ x y, p x y) ↔ ∀ x y, q x y := (Equiv.forall₂_congr eα.symm eβ.symm h.symm).symm
/-
**Equiv.forall** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem forall₃_congr
    {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort*} {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂) (h : ∀ {x y z}, p x y z ↔ q (eα x) (eβ y) (eγ z)) :
    (∀ x y z, p x y z) ↔ ∀ x y z, q x y z :=
  Equiv.forall₂_congr _ _ <| Equiv.forall_congr _ <| @h _ _
/-
**Equiv.forall** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem forall₃_congr'
    {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort*} {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂)
    (h : ∀ {x y z}, p (eα.symm x) (eβ.symm y) (eγ.symm z) ↔ q x y z) :
    (∀ x y z, p x y z) ↔ ∀ x y z, q x y z :=
  (Equiv.forall₃_congr eα.symm eβ.symm eγ.symm h.symm).symm

/-- If `f` is a bijective function, then its domain is equivalent to its codomain. -/
@[simps (attr := grind =) apply]
/-
**Equiv.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：ofBijective (f : α -> β) (hf : Bijective f) : α ≃ β where toFun
参数：f : α -> β；hf : Bijective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Function.leftInverse_surjInv`：leftInverse_surjInv (hf : Bijective f) : L
eftInverse (surjInv hf.2) f

--- 原说明 ---
If `f` is a bijective function, then its domain is equivalent to its codomain.
-/
noncomputable def ofBijective (f : α → β) (hf : Bijective f) : α ≃ β where
  toFun := f
  invFun := surjInv hf.surjective
  left_inv := leftInverse_surjInv hf
  right_inv := rightInverse_surjInv _
/-
**Equiv.coe_ofBijective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} (f : α → β) (hf : Function.Bijective f), ⇑(Equ
iv.ofBijective f hf) = f
参数：f : α → β；hf : Function.Bijective f；Equiv.ofBijective f hf。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_ofBijective (f : α → β) (hf : Bijective f) : ⇑(ofBijective f hf) = f := rfl
/-
**Equiv.ofBijective_coe** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {f : α ≃ β}, Equiv.ofBijective ⇑f ⋯ = f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
@[simp] lemma ofBijective_coe {f : α ≃ β} :
    Equiv.ofBijective f f.bijective = f := Equiv.ext (congrFun rfl)
/-
**Equiv.ofBijective_apply_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：ofBijective_apply_symm_apply (f : α -> β) (hf : Bijective f) (x : β) : f (
(ofBijective f hf).symm x) = x
参数：f : α -> β；hf : Bijective f；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma ofBijective_apply_symm_apply (f : α → β) (hf : Bijective f) (x : β) :
    f ((ofBijective f hf).symm x) = x :=
  (ofBijective f hf).apply_symm_apply x

@[simp]
/-
**Equiv.ofBijective_symm_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：ofBijective_symm_apply_apply (f : α -> β) (hf : Bijective f) (x : α) : (of
Bijective f hf).symm (f x) = x
参数：f : α -> β；hf : Bijective f；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma ofBijective_symm_apply_apply (f : α → β) (hf : Bijective f) (x : α) :
    (ofBijective f hf).symm (f x) = x :=
  (ofBijective f hf).symm_apply_apply x

/-- Bijective functions are equivalent to equivalences. -/
@[simps]
/-
**Equiv.bijectiveEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：bijectiveEquiv : { f : α -> β // Bijective f } ≃ (α ≃ β) where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e

--- 原说明 ---
Bijective functions are equivalent to equivalences.
-/
noncomputable def bijectiveEquiv : { f : α → β // Bijective f } ≃ (α ≃ β) where
  toFun f := .ofBijective f f.prop
  invFun f := ⟨f, f.bijective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

end Equiv

namespace Quot

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂)`. -/
/-
**Quot.congr** 是 Mathlib 中的一个定义，位于命名空间 `Quot`。
形式化陈述：{α : Sort u} →   {β : Sort v} →     {ra : α → α → Prop} →       {rb : β → 
β → Prop} → (e : α ≃ β) → (∀ (a₁ a₂ : α), ra a₁ a₂ ↔ rb (e a₁) (e a₂)) → Quot ra
 ≃ Quot rb
参数：e : α ≃ β；∀ (a₁ a₂ : α), ra a₁ a₂ ↔ rb (e a₁) (e a₂)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂)`.
-/
protected def congr {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β)
    (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) : Quot ra ≃ Quot rb where
  toFun := Quot.map e fun a₁ a₂ => (eq a₁ a₂).1
  invFun := Quot.map e.symm fun b₁ b₂ h =>
    (eq (e.symm b₁) (e.symm b₂)).2
      ((e.apply_symm_apply b₁).symm ▸ (e.apply_symm_apply b₂).symm ▸ h)
  left_inv := by rintro ⟨a⟩; simp only [Quot.map, Equiv.symm_apply_apply]
  right_inv := by rintro ⟨a⟩; simp only [Quot.map, Equiv.apply_symm_apply]
/-
**Quot.congr_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quot`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {ra : α → α → Prop} {rb : β → β → Prop} (e : α
 ≃ β)   (eq : ∀ (a₁ a₂ : α), ra a₁ a₂ ↔ rb (e a₁) (e a₂)) (a : α), (Quot.congr e
 eq) (Quot.mk ra a) = Quot.mk rb (e a)
参数：e : α ≃ β；eq : ∀ (a₁ a₂ : α), ra a₁ a₂ ↔ rb (e a₁) (e a₂)；a : α；Quot.congr e 
eq；Quot.mk ra a；e a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem congr_mk {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β)
    (eq : ∀ a₁ a₂ : α, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) (a : α) :
    Quot.congr e eq (Quot.mk ra a) = Quot.mk rb (e a) := rfl

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
/-
**Quot.congrRight** 是 Mathlib 中的一个定义，位于命名空间 `Quot`。
形式化陈述：{α : Sort u} → {r r' : α → α → Prop} → (∀ (a₁ a₂ : α), r a₁ a₂ ↔ r' a₁ a₂)
 → Quot r ≃ Quot r'
参数：∀ (a₁ a₂ : α), r a₁ a₂ ↔ r' a₁ a₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs
 get stuck.
-/
protected def congrRight {r r' : α → α → Prop} (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) :
    Quot r ≃ Quot r' := Quot.congr (Equiv.refl α) eq

/-- An equivalence `e : α ≃ β` generates an equivalence between the quotient space of `α`
by a relation `ra` and the quotient space of `β` by the image of this relation under `e`. -/
/-
**Quot.congrLeft** 是 Mathlib 中的一个定义，位于命名空间 `Quot`。
形式化陈述：{α : Sort u} → {β : Sort v} → {r : α → α → Prop} → (e : α ≃ β) → Quot r ≃ 
Quot fun b b' => r (e.symm b) (e.symm b')
参数：e : α ≃ β；e.symm b；e.symm b'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence `e : α ≃ β` generates an equivalence between the quotient space o
f `α`
by a relation `ra` and the quotient space of `β` by the image of this relation u
nder `e`.
-/
protected def congrLeft {r : α → α → Prop} (e : α ≃ β) :
    Quot r ≃ Quot fun b b' => r (e.symm b) (e.symm b') :=
  Quot.congr e fun _ _ => by simp only [e.symm_apply_apply]

end Quot

namespace Quotient

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂)`. -/
/-
**Quotient.congr** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u} →   {β : Sort v} →     {ra : Setoid α} →       {rb : Setoid β
} → (e : α ≃ β) → (∀ (a₁ a₂ : α), ra a₁ a₂ ↔ rb (e a₁) (e a₂)) → Quotient ra ≃ Q
uotient rb
参数：e : α ≃ β；∀ (a₁ a₂ : α), ra a₁ a₂ ↔ rb (e a₁) (e a₂)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂)`.
-/
protected def congr {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
    (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) :
    Quotient ra ≃ Quotient rb := Quot.congr e eq
/-
**Quotient.congr_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)   
(eq : ∀ (a₁ a₂ : α), ra a₁ a₂ ↔ rb (e a₁) (e a₂)) (a : α), (Quotient.congr e eq)
 ⟦a⟧ = ⟦e a⟧
参数：e : α ≃ β；eq : ∀ (a₁ a₂ : α), ra a₁ a₂ ↔ rb (e a₁) (e a₂)；a : α；Quotient.cong
r e eq。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem congr_mk {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
    (eq : ∀ a₁ a₂ : α, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) (a : α) :
    Quotient.congr e eq (Quotient.mk ra a) = Quotient.mk rb (e a) := rfl

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
/-
**Quotient.congrRight** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u} → {r r' : Setoid α} → (∀ (a₁ a₂ : α), r a₁ a₂ ↔ r' a₁ a₂) → Q
uotient r ≃ Quotient r'
参数：∀ (a₁ a₂ : α), r a₁ a₂ ↔ r' a₁ a₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs
 get stuck.
-/
protected def congrRight {r r' : Setoid α}
    (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) : Quotient r ≃ Quotient r' :=
  Quot.congrRight eq

end Quotient

/-- Equivalence between `Fin 0` and `Empty`. -/
/-
**finZeroEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finZeroEquiv : Fin 0 ≃ Empty
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `Fin 0` and `Empty`.
-/
def finZeroEquiv : Fin 0 ≃ Empty := .equivEmpty _

/-- Equivalence between `Fin 0` and `PEmpty`. -/
/-
**finZeroEquiv'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finZeroEquiv' : Fin 0 ≃ PEmpty.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `Fin 0` and `PEmpty`.
-/
def finZeroEquiv' : Fin 0 ≃ PEmpty.{u} := .equivPEmpty _

/-- Equivalence between `Fin 1` and `Unit`. -/
/-
**finOneEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finOneEquiv : Fin 1 ≃ Unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `Fin 1` and `Unit`.
-/
def finOneEquiv : Fin 1 ≃ Unit := .equivPUnit _

/-- Equivalence between `Fin 2` and `Bool`. -/
/-
**finTwoEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finTwoEquiv : Fin 2 ≃ Bool where toFun i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `Fin 2` and `Bool`.
-/
def finTwoEquiv : Fin 2 ≃ Bool where
  toFun i := i == 1
  invFun b := bif b then 1 else 0
  left_inv i := by grind
  right_inv b := by grind

namespace Equiv

variable {α β : Type*}

/-- The left summand of `α ⊕ β` is equivalent to `α`. -/
@[simps (attr := grind =)]
/-
**Equiv.sumIsLeft** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sumIsLeft : {x : α oplus β // x.isLeft} ≃ α where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.isLeft_inl`：∀ {α : Type u_1} {β : Type u_2} {x : α}, (Sum.inl x).isL
eft = true

--- 原说明 ---
The left summand of `α ⊕ β` is equivalent to `α`.
-/
def sumIsLeft : {x : α ⊕ β // x.isLeft} ≃ α where
  toFun x := x.1.getLeft x.2
  invFun a := ⟨.inl a, Sum.isLeft_inl⟩
  left_inv | ⟨.inl _a, _⟩ => rfl

/-- The right summand of `α ⊕ β` is equivalent to `β`. -/
@[simps (attr := grind =)]
/-
**Equiv.sumIsRight** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：sumIsRight : {x : α oplus β // x.isRight} ≃ β where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.isRight_inr`：∀ {α : Type u_1} {β : Type u_2} {x : β}, (Sum.inr x).is
Right = true

--- 原说明 ---
The right summand of `α ⊕ β` is equivalent to `β`.
-/
def sumIsRight : {x : α ⊕ β // x.isRight} ≃ β where
  toFun x := x.1.getRight x.2
  invFun b := ⟨.inr b, Sum.isRight_inr⟩
  left_inv | ⟨.inr _b, _⟩ => rfl

variable (e : α ≃ β)

/-- Transfer `LE` across an `Equiv`. -/
/-
**Equiv.le** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [LE β] → LE α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `LE` across an `Equiv`.
-/
protected abbrev le [LE β] : LE α where
  le a b := e a ≤ e b
/-
**Equiv.le_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：le_def [LE β] (a b : α) : letI
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def [LE β] (a b : α) :
    letI := e.le
    e a ≤ e b ↔ a ≤ b := Iff.rfl

/-- Transfer `LT` across an `Equiv`. -/
/-
**Equiv.lt** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [LT β] → LT α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `LT` across an `Equiv`.
-/
protected abbrev lt [LT β] : LT α where
  lt a b := e a < e b
/-
**Equiv.lt_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：lt_def [LT β] (a b : α) : letI
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lt_def [LT β] (a b : α) :
    letI := e.lt
    e a < e b ↔ a < b := Iff.rfl

/-- Transfer `Max` across an `Equiv`. -/
/-
**Equiv.max** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [Max β] → Max α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transfer `Max` across an `Equiv`.
-/
protected abbrev max [Max β] : Max α where
  max a b := e.symm (max (e a) (e b))
/-
**Equiv.max_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：max_def [Max β] (a b : α) : letI
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma max_def [Max β] (a b : α) :
    letI := e.max
    max a b = e.symm (max (e a) (e b)) := rfl

/-- Transfer `Min` across an `Equiv`. -/
/-
**Equiv.min** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [Min β] → Min α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transfer `Min` across an `Equiv`.
-/
protected abbrev min [Min β] : Min α where
  min a b := e.symm (min (e a) (e b))
/-
**Equiv.min_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：min_def [Min β] (a b : α) : letI
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma min_def [Min β] (a b : α) :
    letI := e.min
    min a b = e.symm (min (e a) (e b)) := rfl

/-- Transfer `Ord` across an `Equiv`. -/
/-
**Equiv.ord** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [Ord β] → Ord α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `Ord` across an `Equiv`.
-/
protected abbrev ord [Ord β] : Ord α where
  compare a b := compare (e a) (e b)
/-
**Equiv.ord_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：ord_def [Ord β] (a b : α) : letI
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ord_def [Ord β] (a b : α) :
    letI := e.ord
    compare a b = compare (e a) (e b) := rfl

end Equiv

