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

Implicit `{}` brackets are often used instead of type class `[]` brackets. This is done when the
instances can be inferred because they are implicit arguments to the type `MonoidHom`. When they
can be inferred from the type it is faster to use this method than to use type class inference.

## Tags

monoid homomorphism
-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

open Function

namespace NeZero
variable {F α β : Type*} [Zero α] [Zero β] [FunLike F α β] [ZeroHomClass F α β] {a : α}

/--
lemma `of_map` / 引理 `of_map`

English:
lemma of_map
  given: (f : F) [neZero : NeZero (f a)]
  statement: NeZero a
  proof: ⟨fun h => ne (f a) by rw [h]; exact ZeroHomClass.map_zero f⟩

中文:
引理 of_map
  条件: (f : F) [neZero : NeZero (f a)]
  结论: NeZero a
  证明: ⟨fun h => ne (f a) by rw [h]; exact ZeroHomClass.map_zero f⟩

Depends on / 依赖: ZeroHomClass, ZeroHomClass.map_zero, map_zero
-/
lemma of_map (f : F) [neZero : NeZero (f a)] : NeZero a :=
⟨fun h => ne (f a) by rw [h]; exact ZeroHomClass.map_zero f⟩

/--
lemma `of_injective` / 引理 `of_injective`

English:
lemma of_injective
  given: {f : F} (hf : Injective f) [NeZero a]
  statement: NeZero (f a)
  proof: ⟨by rw [← ZeroHomClass.map_zero f]; exact hf.ne NeZero.out⟩

中文:
引理 of_injective
  条件: {f : F} (hf : Injective f) [NeZero a]
  结论: NeZero (f a)
  证明: ⟨by rw [← ZeroHomClass.map_zero f]; exact hf.ne NeZero.out⟩

Depends on / 依赖: NeZero, NeZero.out, ZeroHomClass, ZeroHomClass.map_zero, hf.ne, map_zero
-/
lemma of_injective {f : F} (hf : Injective f) [NeZero a] : NeZero (f a) :=
  ⟨by rw [← ZeroHomClass.map_zero f]; exact hf.ne NeZero.out⟩

end NeZero

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

/--
Definition of `MonoidWithZeroHomClass` / `MonoidWithZeroHomClass` 的定义

English:
class MonoidWithZeroHomClass
  parameters: (F : Type*) (α β : outParam Type*) [MulZeroOneClass α]
  extends: MonoidHomClass F α β, ZeroHomClass F α β
  (no additional axioms)

中文:
类 MonoidWithZeroHomClass
  参数: (F : 类型) (α β : outParam 类型) [MulZeroOneClass α]
  继承: MonoidHomClass F α β, ZeroHomClass F α β
  (无附加公理)
-/
class MonoidWithZeroHomClass (F : Type*) (α β : outParam Type*) [MulZeroOneClass α]
    [MulZeroOneClass β] [FunLike F α β] : Prop
  extends MonoidHomClass F α β, ZeroHomClass F α β

/--
Definition of `MonoidWithZeroHom` / `MonoidWithZeroHom` 的定义

English:
structure MonoidWithZeroHom
  parameters: (α β : Type*) [MulZeroOneClass α] [MulZeroOneClass β]
  extends: ZeroHom α β, MonoidHom α β
  (no additional axioms)

中文:
结构 MonoidWithZeroHom
  参数: (α β : 类型) [MulZeroOneClass α] [MulZeroOneClass β]
  继承: ZeroHom α β, MonoidHom α β
  (无附加公理)
-/
structure MonoidWithZeroHom (α β : Type*) [MulZeroOneClass α] [MulZeroOneClass β]
  extends ZeroHom α β, MonoidHom α β

/-- `α →*₀ β` denotes the type of zero-preserving monoid homomorphisms from `α` to `β`. -/
infixr:25 " ->*₀ " => MonoidWithZeroHom

/--
Definition of `MonoidWithZeroHom.ofClass` / `MonoidWithZeroHom.ofClass` 的定义

English:
definition MonoidWithZeroHom.ofClass
  signature: [FunLike F α β] [MonoidWithZeroHomClass F α β]
  body: { (f : α ->* β), (f : ZeroHom α β) with }

中文:
定义 MonoidWithZeroHom.ofClass
  签名: [FunLike F α β] [MonoidWithZeroHomClass F α β]
  定义体: { (f : α ->* β), (f : ZeroHom α β) with }

Depends on / 依赖: ZeroHom
-/
def MonoidWithZeroHom.ofClass [FunLike F α β] [MonoidWithZeroHomClass F α β]
    (f : F) : α ->*₀ β := { (f : α ->* β), (f : ZeroHom α β) with }

namespace MonoidWithZeroHom

attribute [nolint docBlame] toMonoidHom
attribute [nolint docBlame] toZeroHom

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (α ->*₀ β) α β where
  body: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

中文:
实例 funLike
  签名: : FunLike (α ->*₀ β) α β where
  定义体: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (α ->*₀ β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

/--
Instance `monoidWithZeroHomClass` / 实例 `monoidWithZeroHomClass`

English:
instance monoidWithZeroHomClass
  signature: : MonoidWithZeroHomClass (α ->*₀ β) α β where
  body: MonoidWithZeroHom.map_mul'
  map_one := MonoidWithZeroHom.map_one'
  map_zero f := f.map_zero'

中文:
实例 monoidWithZeroHomClass
  签名: : MonoidWithZeroHomClass (α ->*₀ β) α β where
  定义体: MonoidWithZeroHom.map_mul'
  map_one := MonoidWithZeroHom.map_one'
  map_zero f := f.map_zero'

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.map_mul, map_mul
-/
instance monoidWithZeroHomClass : MonoidWithZeroHomClass (α ->*₀ β) α β where
  map_mul := MonoidWithZeroHom.map_mul'
  map_one := MonoidWithZeroHom.map_one'
  map_zero f := f.map_zero'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] : Subsingleton (α ->*₀ β)
  body: .of_oneHomClass

中文:
实例 [Subsingleton
  签名: α] : Subsingleton (α ->*₀ β)
  定义体: .of_oneHomClass

Depends on / 依赖: of_oneHomClass
-/
instance [Subsingleton α] : Subsingleton (α ->*₀ β) := .of_oneHomClass

variable [FunLike F α β]

/--
lemma `coe_ofClass` / 引理 `coe_ofClass`

English:
lemma coe_ofClass
  given: [MonoidWithZeroHomClass F α β] (f : F)
  proof: rfl

中文:
引理 coe_ofClass
  条件: [MonoidWithZeroHomClass F α β] (f : F)
  证明: rfl
-/
@[simp] lemma coe_ofClass [MonoidWithZeroHomClass F α β] (f : F) :
    (MonoidWithZeroHom.ofClass f : α -> β) = f := rfl

-- Completely uninteresting lemmas about coercion to function, that all homs need
section Coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/

attribute [coe] toMonoidHom

/--
Instance `coeToMonoidHom` / 实例 `coeToMonoidHom`

English:
instance coeToMonoidHom
  signature: : Coe (α ->*₀ β) (α ->* β)
  body: ⟨toMonoidHom⟩

中文:
实例 coeToMonoidHom
  签名: : Coe (α ->*₀ β) (α ->* β)
  定义体: ⟨toMonoidHom⟩

Depends on / 依赖: toMonoidHom
-/
instance coeToMonoidHom : Coe (α ->*₀ β) (α ->* β) :=
  ⟨toMonoidHom⟩

attribute [coe] toZeroHom

/--
Instance `coeToZeroHom` / 实例 `coeToZeroHom`

English:
instance coeToZeroHom
  signature: : Coe (α ->*₀ β) (ZeroHom α β)
  body: ⟨toZeroHom⟩

中文:
实例 coeToZeroHom
  签名: : Coe (α ->*₀ β) (ZeroHom α β)
  定义体: ⟨toZeroHom⟩

Depends on / 依赖: toZeroHom
-/
instance coeToZeroHom : Coe (α ->*₀ β) (ZeroHom α β) := ⟨toZeroHom⟩

-- This must come after the coe_toFun definitions
initialize_simps_projections MonoidWithZeroHom (toFun -> apply)

/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (f h1 hmul)
  statement: (mk f h1 hmul : α -> β) = (f : α -> β)
  proof: rfl

中文:
引理 coe_mk
  条件: (f h1 hmul)
  结论: (mk f h1 hmul : α -> β) = (f : α -> β)
  证明: rfl

Depends on / 依赖: IsSplitEpi
-/
@[simp] lemma coe_mk (f h1 hmul) : (mk f h1 hmul : α -> β) = (f : α -> β) := rfl

/--
lemma `toZeroHom_coe` / 引理 `toZeroHom_coe`

English:
lemma toZeroHom_coe
  given: (f : α ->*₀ β)
  statement: (f.toZeroHom : α -> β) = f
  proof: rfl

中文:
引理 toZeroHom_coe
  条件: (f : α ->*₀ β)
  结论: (f.toZeroHom : α -> β) = f
  证明: rfl

Depends on / 依赖: IsSplitMono
-/
@[simp] lemma toZeroHom_coe (f : α ->*₀ β) : (f.toZeroHom : α -> β) = f := rfl

/--
lemma `toMonoidHom_coe` / 引理 `toMonoidHom_coe`

English:
lemma toMonoidHom_coe
  given: (f : α ->*₀ β)
  statement: f.toMonoidHom.toFun = f
  proof: rfl

中文:
引理 toMonoidHom_coe
  条件: (f : α ->*₀ β)
  结论: f.toMonoidHom.toFun = f
  证明: rfl
-/
lemma toMonoidHom_coe (f : α ->*₀ β) : f.toMonoidHom.toFun = f := rfl

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: ⦃f g
  statement: α ->*₀ β⦄ (h : forall x, f x = g x) : f = g
  proof: DFunLike.ext _ _ h

中文:
引理 ext
  条件: ⦃f g
  结论: α ->*₀ β⦄ (h : 对任意 x, f x = g x) : f = g
  证明: DFunLike.ext _ _ h
-/
@[ext] lemma ext ⦃f g : α ->*₀ β⦄ (h : forall x, f x = g x) : f = g := DFunLike.ext _ _ h

/--
lemma `mk_coe` / 引理 `mk_coe`

English:
lemma mk_coe
  given: (f : α ->*₀ β) (h1 hmul)
  statement: mk f h1 hmul = f
  proof: ext fun _ => rfl

中文:
引理 mk_coe
  条件: (f : α ->*₀ β) (h1 hmul)
  结论: mk f h1 hmul = f
  证明: ext fun _ => rfl
-/
@[simp] lemma mk_coe (f : α ->*₀ β) (h1 hmul) : mk f h1 hmul = f := ext fun _ => rfl

end Coes

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : α ->*₀ β) (f' : α -> β) (h : f' = f)
  body: { f.toZeroHom.copy f' h, f.toMonoidHom.copy f' h with }

@[simp]

中文:
定义 copy
  签名: (f : α ->*₀ β) (f' : α -> β) (h : f' = f)
  定义体: { f.toZeroHom.copy f' h, f.toMonoidHom.copy f' h with }

@[simp]
-/
protected def copy (f : α ->*₀ β) (f' : α -> β) (h : f' = f) : α ->* β :=
  { f.toZeroHom.copy f' h, f.toMonoidHom.copy f' h with }

@[simp]
/--
lemma `coe_copy` / 引理 `coe_copy`

English:
lemma coe_copy
  given: (f : α ->*₀ β) (f' : α -> β) (h)
  statement: (f.copy f' h) = f'
  proof: rfl

中文:
引理 coe_copy
  条件: (f : α ->*₀ β) (f' : α -> β) (h)
  结论: (f.copy f' h) = f'
  证明: rfl
-/
lemma coe_copy (f : α ->*₀ β) (f' : α -> β) (h) : (f.copy f' h) = f' := rfl

/--
lemma `copy_eq` / 引理 `copy_eq`

English:
lemma copy_eq
  given: (f : α ->*₀ β) (f' : α -> β) (h)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
引理 copy_eq
  条件: (f : α ->*₀ β) (f' : α -> β) (h)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
lemma copy_eq (f : α ->*₀ β) (f' : α -> β) (h) : f.copy f' h = f := DFunLike.ext' h

/--
lemma `map_one` / 引理 `map_one`

English:
lemma map_one
  given: (f : α ->*₀ β)
  statement: f 1 = 1
  proof: f.map_one'

中文:
引理 map_one
  条件: (f : α ->*₀ β)
  结论: f 1 = 1
  证明: f.map_one'
-/
protected lemma map_one (f : α ->*₀ β) : f 1 = 1 := f.map_one'

/--
lemma `map_zero` / 引理 `map_zero`

English:
lemma map_zero
  given: (f : α ->*₀ β)
  statement: f 0 = 0
  proof: f.map_zero'

中文:
引理 map_zero
  条件: (f : α ->*₀ β)
  结论: f 0 = 0
  证明: f.map_zero'
-/
protected lemma map_zero (f : α ->*₀ β) : f 0 = 0 := f.map_zero'

/--
lemma `map_mul` / 引理 `map_mul`

English:
lemma map_mul
  given: (f : α ->*₀ β) (a b : α)
  statement: f (a * b) = f a * f b
  proof: f.map_mul' a b

@[simp]

中文:
引理 map_mul
  条件: (f : α ->*₀ β) (a b : α)
  结论: f (a * b) = f a * f b
  证明: f.map_mul' a b

@[simp]
-/
protected lemma map_mul (f : α ->*₀ β) (a b : α) : f (a * b) = f a * f b := f.map_mul' a b

@[simp]
/--
theorem `map_ite_zero_one` / 定理 `map_ite_zero_one`

English:
theorem map_ite_zero_one
  statement: {F : Type*} [FunLike F α β] [MonoidWithZeroHomClass F α β] (f : F)
  proof: by
  split_ifs with h <;> simp

@[simp]

中文:
定理 map_ite_zero_one
  结论: {F : 类型} [FunLike F α β] [MonoidWithZeroHomClass F α β] (f : F)
  证明: by
  split_ifs with h <;> simp

@[simp]

Depends on / 依赖: split_ifs
-/
theorem map_ite_zero_one {F : Type*} [FunLike F α β] [MonoidWithZeroHomClass F α β] (f : F)
    (p : Prop) [Decidable p] :
    f (ite p 0 1) = ite p 0 1 := by
  split_ifs with h <;> simp

@[simp]
/--
theorem `map_ite_one_zero` / 定理 `map_ite_one_zero`

English:
theorem map_ite_one_zero
  statement: {F : Type*} [FunLike F α β] [MonoidWithZeroHomClass F α β] (f : F)
  proof: by
  split_ifs with h <;> simp

中文:
定理 map_ite_one_zero
  结论: {F : 类型} [FunLike F α β] [MonoidWithZeroHomClass F α β] (f : F)
  证明: by
  split_ifs with h <;> simp

Depends on / 依赖: split_ifs
-/
theorem map_ite_one_zero {F : Type*} [FunLike F α β] [MonoidWithZeroHomClass F α β] (f : F)
    (p : Prop) [Decidable p] :
    f (ite p 1 0) = ite p 1 0 := by
  split_ifs with h <;> simp

/-- The identity map from a `MonoidWithZero` to itself. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (α : Type*) [MulZeroOneClass α]
  body: x
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 id
  签名: (α : 类型) [MulZeroOneClass α]
  定义体: x
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
-/
def id (α : Type*) [MulZeroOneClass α] : α ->*₀ α where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (hnp : β ->*₀ γ) (hmn : α ->*₀ β)
  body: hnp ∘ hmn
  map_zero' := by rw [comp_apply, map_zero, map_zero]
  map_one' := by simp
  map_mul' := by simp

中文:
定义 comp
  签名: (hnp : β ->*₀ γ) (hmn : α ->*₀ β)
  定义体: hnp ∘ hmn
  map_zero' := by rw [comp_apply, map_zero, map_zero]
  map_one' := by simp
  map_mul' := by simp
-/
def comp (hnp : β ->*₀ γ) (hmn : α ->*₀ β) : α ->*₀ γ where
  toFun := hnp ∘ hmn
  map_zero' := by rw [comp_apply, map_zero, map_zero]
  map_one' := by simp
  map_mul' := by simp

/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: (g : β ->*₀ γ) (f : α ->*₀ β)
  statement: ↑(g.comp f) = g ∘ f
  proof: rfl

中文:
引理 coe_comp
  条件: (g : β ->*₀ γ) (f : α ->*₀ β)
  结论: ↑(g.comp f) = g ∘ f
  证明: rfl
-/
@[simp] lemma coe_comp (g : β ->*₀ γ) (f : α ->*₀ β) : ↑(g.comp f) = g ∘ f := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: (g : β ->*₀ γ) (f : α ->*₀ β) (x : α)
  statement: g.comp f x = g (f x)
  proof: rfl

中文:
引理 comp_apply
  条件: (g : β ->*₀ γ) (f : α ->*₀ β) (x : α)
  结论: g.comp f x = g (f x)
  证明: rfl
-/
lemma comp_apply (g : β ->*₀ γ) (f : α ->*₀ β) (x : α) : g.comp f x = g (f x) := rfl

/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  given: (f : α ->*₀ β) (g : β ->*₀ γ) (h : γ ->*₀ δ)
  proof: rfl

中文:
引理 comp_assoc
  条件: (f : α ->*₀ β) (g : β ->*₀ γ) (h : γ ->*₀ δ)
  证明: rfl
-/
lemma comp_assoc (f : α ->*₀ β) (g : β ->*₀ γ) (h : γ ->*₀ δ) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

/--
lemma `cancel_right` / 引理 `cancel_right`

English:
lemma cancel_right
  given: {g₁ g₂ : β ->*₀ γ} {f : α ->*₀ β} (hf : Surjective f)
  proof: ⟨fun h => ext hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

中文:
引理 cancel_right
  条件: {g₁ g₂ : β ->*₀ γ} {f : α ->*₀ β} (hf : Surjective f)
  证明: ⟨fun h => ext hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, hf.forall
-/
lemma cancel_right {g₁ g₂ : β ->*₀ γ} {f : α ->*₀ β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

/--
lemma `cancel_left` / 引理 `cancel_left`

English:
lemma cancel_left
  given: {g : β ->*₀ γ} {f₁ f₂ : α ->*₀ β} (hg : Injective g)
  proof: ⟨fun h => ext fun x => hg by rw [← comp_apply, h,
    comp_apply], fun h => h ▸ rfl⟩

中文:
引理 cancel_left
  条件: {g : β ->*₀ γ} {f₁ f₂ : α ->*₀ β} (hg : Injective g)
  证明: ⟨fun h => ext fun x => hg by rw [← comp_apply, h,
    comp_apply], fun h => h ▸ rfl⟩

Depends on / 依赖: comp_apply
-/
lemma cancel_left {g : β ->*₀ γ} {f₁ f₂ : α ->*₀ β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun x => hg by rw [← comp_apply, h,
    comp_apply], fun h => h ▸ rfl⟩

/--
lemma `toMonoidHom_injective` / 引理 `toMonoidHom_injective`

English:
lemma toMonoidHom_injective
  statement: Injective (toMonoidHom : (α ->*₀ β) -> α ->* β)
  proof: Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

中文:
引理 toMonoidHom_injective
  结论: Injective (toMonoidHom : (α ->*₀ β) -> α ->* β)
  证明: Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Injective, Injective.of_comp, coe_injective, of_comp
-/
lemma toMonoidHom_injective : Injective (toMonoidHom : (α ->*₀ β) -> α ->* β) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

/--
lemma `toZeroHom_injective` / 引理 `toZeroHom_injective`

English:
lemma toZeroHom_injective
  statement: Injective (toZeroHom : (α ->*₀ β) -> ZeroHom α β)
  proof: Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

中文:
引理 toZeroHom_injective
  结论: Injective (toZeroHom : (α ->*₀ β) -> ZeroHom α β)
  证明: Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Injective, Injective.of_comp, coe_injective, of_comp
-/
lemma toZeroHom_injective : Injective (toZeroHom : (α ->*₀ β) -> ZeroHom α β) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  given: (f : α ->*₀ β)
  statement: f.comp (id α) = f
  proof: ext fun _ => rfl

中文:
引理 comp_id
  条件: (f : α ->*₀ β)
  结论: f.comp (id α) = f
  证明: ext fun _ => rfl
-/
@[simp] lemma comp_id (f : α ->*₀ β) : f.comp (id α) = f := ext fun _ => rfl

/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  given: (f : α ->*₀ β)
  statement: (id β).comp f = f
  proof: ext fun _ => rfl

中文:
引理 id_comp
  条件: (f : α ->*₀ β)
  结论: (id β).comp f = f
  证明: ext fun _ => rfl

Depends on / 依赖: Category, Category.id_comp, id_comp, if_pos
-/
@[simp] lemma id_comp (f : α ->*₀ β) : (id β).comp f = f := ext fun _ => rfl

-- Unlike the other homs, `MonoidWithZeroHom` does not have a `1` or `0`
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (α ->*₀ α)
  body: ⟨id α⟩

中文:
实例 :
  签名: Inhabited (α ->*₀ α)
  定义体: ⟨id α⟩

Depends on / 依赖: eqToIso, id_comp, mkXIso, of.d
-/
instance : Inhabited (α ->*₀ α) := ⟨id α⟩

/-- Given two monoid with zero morphisms `f`, `g` to a commutative monoid with zero, `f * g` is the
monoid with zero morphism sending `x` to `f x * g x`. -/
instance {β} [CommMonoidWithZero β] : Mul (α ->*₀ β) where
  mul f g :=
    { (f * g : α ->* β) with
      map_zero' := by dsimp; rw [map_zero, zero_mul] }

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: (M₀ N₀ : Type*) [MulZeroOneClass M₀] [MulZeroOneClass N₀]
  body: if x = 0 then 0 else 1
  one.map_zero' := by simp
  one.map_one' := by simp
  one.map_mul' x y := by split_ifs <;> simp_all

中文:
实例 one
  签名: (M₀ N₀ : 类型) [MulZeroOneClass M₀] [MulZeroOneClass N₀]
  定义体: if x = 0 then 0 else 1
  one.map_zero' := by simp
  one.map_one' := by simp
  one.map_mul' x y := by split_ifs <;> simp_all
-/
protected instance one (M₀ N₀ : Type*) [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ => x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] :
    One (M₀ ->*₀ N₀) where
  one.toFun x := if x = 0 then 0 else 1
  one.map_zero' := by simp
  one.map_one' := by simp
  one.map_mul' x y := by split_ifs <;> simp_all

/--
lemma `one_apply_def` / 引理 `one_apply_def`

English:
lemma one_apply_def
  statement: {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
  proof: rfl

@[simp]

中文:
引理 one_apply_def
  结论: {M₀ N₀ : 类型} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
  证明: rfl

@[simp]

Depends on / 依赖: _congr_succ, mk_d, mk_d_1_0, mk_d_2_1
-/
lemma one_apply_def {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ => x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] (x : M₀) :
    (1 : M₀ ->*₀ N₀) x = if x = 0 then 0 else 1 :=
  rfl

@[simp]
/--
lemma `one_apply_zero` / 引理 `one_apply_zero`

English:
lemma one_apply_zero
  statement: {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
  proof: if_pos rfl

中文:
引理 one_apply_zero
  结论: {M₀ N₀ : 类型} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
lemma one_apply_zero {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ => x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] :
    (1 : M₀ ->*₀ N₀) 0 = 0 :=
  if_pos rfl

/--
lemma `one_apply_of_ne_zero` / 引理 `one_apply_of_ne_zero`

English:
lemma one_apply_of_ne_zero
  statement: {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
  proof: if_neg hx

@[simp]

中文:
引理 one_apply_of_ne_zero
  结论: {M₀ N₀ : 类型} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
  证明: if_neg hx

@[simp]

Depends on / 依赖: if_neg
-/
lemma one_apply_of_ne_zero {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ => x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] {x : M₀} (hx : x != 0) :
    (1 : M₀ ->*₀ N₀) x = 1 :=
  if_neg hx

@[simp]
/--
lemma `one_apply_eq_zero_iff` / 引理 `one_apply_eq_zero_iff`

English:
lemma one_apply_eq_zero_iff
  statement: {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
  proof: by
  rcases eq_or_ne x 0 with rfl | hx <;> simp_all [one_apply_of_ne_zero]

@[simp]

中文:
引理 one_apply_eq_zero_iff
  结论: {M₀ N₀ : 类型} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
  证明: by
  rcases eq_or_ne x 0 with rfl | hx <;> simp_all [one_apply_of_ne_zero]

@[simp]

Depends on / 依赖: eq_or_ne, one_apply_of_ne_zero
-/
lemma one_apply_eq_zero_iff {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ => x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] [Nontrivial N₀]
    {x : M₀} :
    (1 : M₀ ->*₀ N₀) x = 0 ↔ x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx <;> simp_all [one_apply_of_ne_zero]

@[simp]
/--
lemma `one_apply_eq_one_iff` / 引理 `one_apply_eq_one_iff`

English:
lemma one_apply_eq_one_iff
  statement: {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
  proof: by
  rcases eq_or_ne x 0 with rfl | hx <;> simp_all [one_apply_of_ne_zero]

中文:
引理 one_apply_eq_one_iff
  结论: {M₀ N₀ : 类型} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
  证明: by
  rcases eq_or_ne x 0 with rfl | hx <;> simp_all [one_apply_of_ne_zero]

Depends on / 依赖: eq_or_ne, one_apply_of_ne_zero
-/
lemma one_apply_eq_one_iff {M₀ N₀ : Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ => x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] [Nontrivial N₀]
    {x : M₀} :
    (1 : M₀ ->*₀ N₀) x = 1 ↔ x != 0 := by
  rcases eq_or_ne x 0 with rfl | hx <;> simp_all [one_apply_of_ne_zero]

end MonoidWithZeroHom

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] {n : Nat} (hn : n != 0)

/--
Definition of `powMonoidWithZeroHom` / `powMonoidWithZeroHom` 的定义

English:
definition powMonoidWithZeroHom
  signature: : M₀ ->*₀ M₀
  body: { powMonoidHom n with map_zero' := zero_pow hn }

中文:
定义 powMonoidWithZeroHom
  签名: : M₀ ->*₀ M₀
  定义体: { powMonoidHom n with map_zero' := zero_pow hn }

Depends on / 依赖: eqToHom, map_zero, powMonoidHom, zero_pow
-/
def powMonoidWithZeroHom : M₀ ->*₀ M₀ :=
  { powMonoidHom n with map_zero' := zero_pow hn }

/--
lemma `coe_powMonoidWithZeroHom` / 引理 `coe_powMonoidWithZeroHom`

English:
lemma coe_powMonoidWithZeroHom
  statement: (powMonoidWithZeroHom hn : M₀ -> M₀) = fun x => x ^ n
  proof: rfl

中文:
引理 coe_powMonoidWithZeroHom
  结论: (powMonoidWithZeroHom hn : M₀ -> M₀) = fun x => x ^ n
  证明: rfl
-/
@[simp] lemma coe_powMonoidWithZeroHom : (powMonoidWithZeroHom hn : M₀ -> M₀) = fun x => x ^ n := rfl

/--
lemma `powMonoidWithZeroHom_apply` / 引理 `powMonoidWithZeroHom_apply`

English:
lemma powMonoidWithZeroHom_apply
  given: (a : M₀)
  statement: powMonoidWithZeroHom hn a = a ^ n
  proof: rfl

中文:
引理 powMonoidWithZeroHom_apply
  条件: (a : M₀)
  结论: powMonoidWithZeroHom hn a = a ^ n
  证明: rfl
-/
@[simp] lemma powMonoidWithZeroHom_apply (a : M₀) : powMonoidWithZeroHom hn a = a ^ n := rfl

end CommMonoidWithZero
