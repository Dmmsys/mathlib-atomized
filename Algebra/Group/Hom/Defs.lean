/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Kim Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Monoid and group homomorphisms

This file defines the bundled structures for monoid and group homomorphisms. Namely, we define
`MonoidHom` (resp., `AddMonoidHom`) to be bundled homomorphisms between multiplicative (resp.,
additive) monoids or groups.

We also define coercion to a function, and usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.

This file also defines the lesser-used (and notation-less) homomorphism types which are used as
building blocks for other homomorphisms:

* `ZeroHom`
* `OneHom`
* `AddHom`
* `MulHom`

## Notation

* `→+`: Bundled `AddMonoid` homs. Also use for `AddGroup` homs.
* `→*`: Bundled `Monoid` homs. Also use for `Group` homs.
* `→ₙ+`: Bundled `AddSemigroup` homs.
* `→ₙ*`: Bundled `Semigroup` homs.

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `GroupHom` -- the idea is that `MonoidHom` is used.
The constructor for `MonoidHom` needs a proof of `map_one` as well
as `map_mul`; a separate constructor `MonoidHom.mk'` will construct
group homs (i.e. monoid homs between groups) given only a proof
that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets.  This is done when the
instances can be inferred because they are implicit arguments to the type `MonoidHom`.  When they
can be inferred from the type it is faster to use this method than to use type class inference.

Historically this file also included definitions of unbundled homomorphism classes; they were
deprecated and moved to `Deprecated/Group`.

## Tags

MonoidHom, AddMonoidHom

-/

@[expose] public section

open Function

variable {ι α β M N P : Type*}

-- monoids
variable {G : Type*} {H : Type*}

-- groups
variable {F : Type*}

-- homs
section Zero

/-- `ZeroHom M N` is the type of functions `M → N` that preserve zero.

When possible, instead of parametrizing results over `(f : ZeroHom M N)`,
you should parametrize over `(F : Type*) [ZeroHomClass F M N] (f : F)`.

When you extend this structure, make sure to also extend `ZeroHomClass`.
-/
/-
**ZeroHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_10) → (N : Type u_11) → [Zero M] → [Zero N] → Type (max u_10 u
_11)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ZeroHom M N` is the type of functions `M → N` that preserve zero.

When possible, instead of parametrizing results over `(f : ZeroHom M N)`,
you should parametrize over `(F : Type*) [ZeroHomClass F M N] (f : F)`.

When you extend this structure, make sure to also extend `ZeroHomClass`.
-/
structure ZeroHom (M : Type*) (N : Type*) [Zero M] [Zero N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves 0 -/
  protected map_zero' : toFun 0 = 0

/-- `ZeroHomClass F M N` states that `F` is a type of zero-preserving homomorphisms.

You should extend this typeclass when you extend `ZeroHom`.
-/
/-
**ZeroHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_10) → (M : outParam (Type u_11)) → (N : outParam (Type u_12)) 
→ [Zero M] → [Zero N] → [FunLike F M N] → Prop
参数：Type u_11；Type u_12。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ZeroHomClass F M N` states that `F` is a type of zero-preserving homomorphisms.

You should extend this typeclass when you extend `ZeroHom`.
-/
class ZeroHomClass (F : Type*) (M N : outParam Type*) [Zero M] [Zero N] [FunLike F M N] :
    Prop where
  /-- The proposition that the function preserves 0 -/
  map_zero : ∀ f : F, f 0 = 0

-- Instances and lemmas are defined below through `@[to_additive]`.
end Zero

section Add

/-- `M →ₙ+ N` is the type of functions `M → N` that preserve addition. The `ₙ` in the notation
stands for "non-unital" because it is intended to match the notation for `NonUnitalAlgHom` and
`NonUnitalRingHom`, so a `AddHom` is a non-unital additive monoid hom.

When possible, instead of parametrizing results over `(f : AddHom M N)`,
you should parametrize over `(F : Type*) [AddHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `AddHomClass`.
-/
/-
**AddHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_10) → (N : Type u_11) → [Add M] → [Add N] → Type (max u_10 u_1
1)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M →ₙ+ N` is the type of functions `M → N` that preserve addition. The `ₙ` in th
e notation
stands for "non-unital" because it is intended to match the notation for `NonUni
talAlgHom` and
`NonUnitalRingHom`, so a `AddHom` is a non-unital additive monoid hom.

When possible, instead of parametrizing results over `(f : AddHom M N)`,
you should parametrize over `(F : Type*) [AddHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `AddHomClass`.
-/
structure AddHom (M : Type*) (N : Type*) [Add M] [Add N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves addition -/
  protected map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y

/-- `M →ₙ+ N` denotes the type of addition-preserving maps from `M` to `N`. -/
infixr:25 " →ₙ+ " => AddHom

/-- `AddHomClass F M N` states that `F` is a type of addition-preserving homomorphisms.
You should declare an instance of this typeclass when you extend `AddHom`.
-/
/-
**AddHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_10) → (M : outParam (Type u_11)) → (N : outParam (Type u_12)) 
→ [Add M] → [Add N] → [FunLike F M N] → Prop
参数：Type u_11；Type u_12。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddHomClass F M N` states that `F` is a type of addition-preserving homomorphis
ms.
You should declare an instance of this typeclass when you extend `AddHom`.
-/
class AddHomClass (F : Type*) (M N : outParam Type*) [Add M] [Add N] [FunLike F M N] : Prop where
  /-- The proposition that the function preserves addition -/
  map_add : ∀ (f : F) (x y : M), f (x + y) = f x + f y

-- Instances and lemmas are defined below through `@[to_additive]`.
end Add

section add_zero

/-- `M →+ N` is the type of functions `M → N` that preserve the `AddZero` structure.

`AddMonoidHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →+ N)`,
you should parametrize over `(F : Type*) [AddMonoidHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `AddMonoidHomClass`.
-/
/-
**AddMonoidHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_10) → (N : Type u_11) → [AddZero M] → [AddZero N] → Type (max 
u_10 u_11)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M →+ N` is the type of functions `M → N` that preserve the `AddZero` structure.

`AddMonoidHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →+ N)`,
you should parametrize over `(F : Type*) [AddMonoidHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `AddMonoidHomClass`.
-/
structure AddMonoidHom (M : Type*) (N : Type*) [AddZero M] [AddZero N]
  extends ZeroHom M N, AddHom M N

attribute [nolint docBlame] AddMonoidHom.toAddHom
attribute [nolint docBlame] AddMonoidHom.toZeroHom

/-- `M →+ N` denotes the type of additive monoid homomorphisms from `M` to `N`. -/
infixr:25 " →+ " => AddMonoidHom

/-- `AddMonoidHomClass F M N` states that `F` is a type of `AddZero`-preserving
homomorphisms.

You should also extend this typeclass when you extend `AddMonoidHom`.
-/
/-
**AddMonoidHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_10) →   (M : outParam (Type u_11)) → (N : outParam (Type u_12)
) → [AddZero M] → [AddZero N] → [FunLike F M N] → Prop
参数：Type u_11；Type u_12。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddMonoidHomClass F M N` states that `F` is a type of `AddZero`-preserving
homomorphisms.

You should also extend this typeclass when you extend `AddMonoidHom`.
-/
class AddMonoidHomClass (F : Type*) (M N : outParam Type*)
    [AddZero M] [AddZero N] [FunLike F M N] : Prop
    extends AddHomClass F M N, ZeroHomClass F M N

-- Instances and lemmas are defined below through `@[to_additive]`.
end add_zero

section One

variable [One M] [One N]

/-- `OneHom M N` is the type of functions `M → N` that preserve one.

When possible, instead of parametrizing results over `(f : OneHom M N)`,
you should parametrize over `(F : Type*) [OneHomClass F M N] (f : F)`.

When you extend this structure, make sure to also extend `OneHomClass`.
-/
@[to_additive]
/-
**OneHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_10) → (N : Type u_11) → [One M] → [One N] → Type (max u_10 u_1
1)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OneHom M N` is the type of functions `M → N` that preserve one.

When possible, instead of parametrizing results over `(f : OneHom M N)`,
you should parametrize over `(F : Type*) [OneHomClass F M N] (f : F)`.

When you extend this structure, make sure to also extend `OneHomClass`.
-/
structure OneHom (M : Type*) (N : Type*) [One M] [One N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves 1 -/
  protected map_one' : toFun 1 = 1

/-- `OneHomClass F M N` states that `F` is a type of one-preserving homomorphisms.
You should extend this typeclass when you extend `OneHom`.
-/
@[to_additive]
/-
**OneHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_10) → (M : outParam (Type u_11)) → (N : outParam (Type u_12)) 
→ [One M] → [One N] → [FunLike F M N] → Prop
参数：Type u_11；Type u_12。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OneHomClass F M N` states that `F` is a type of one-preserving homomorphisms.
You should extend this typeclass when you extend `OneHom`.
-/
class OneHomClass (F : Type*) (M N : outParam Type*) [One M] [One N] [FunLike F M N] : Prop where
  /-- The proposition that the function preserves 1 -/
  map_one : ∀ f : F, f 1 = 1

@[to_additive]
/-
**OneHom.funLike** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OneHom.funLike : FunLike (OneHom M N) M N where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OneHom.funLike : FunLike (OneHom M N) M N where
  coe := OneHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_additive]
/-
**OneHom.oneHomClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OneHom.oneHomClass : OneHomClass (OneHom M N) M N where map_one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OneHom.map_one'`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [inst_
1 : One N] (self : OneHom M N), self.toFun 1 = 1
-/
instance OneHom.oneHomClass : OneHomClass (OneHom M N) M N where
  map_one := OneHom.map_one'

library_note «hom simp lemma priority»
/--
The hom class hierarchy allows for a single lemma, such as `map_one`, to apply to a large variety
of morphism types, so long as they have an instance of `OneHomClass`. For example, this applies to
to `MonoidHom`, `RingHom`, `AlgHom`, `StarAlgHom`, as well as their `Equiv` variants, etc. However,
precisely because these lemmas are so widely applicable, they keys in the `simp` discrimination tree
are necessarily highly non-specific. For example, the key for `map_one` is
`@DFunLike.coe _ _ _ _ _ 1`.

Consequently, whenever lean sees `⇑f 1`, for some `f : F`, it will attempt to synthesize a
`OneHomClass F ?A ?B` instance. If no such instance exists, then Lean will need to traverse (almost)
the entirety of the `FunLike` hierarchy in order to determine this because so many classes have a
`OneHomClass` instance (in fact, this problem is likely worse for `ZeroHomClass`). This can lead to
a significant performance hit when `map_one` fails to apply.

To avoid this problem, we mark these widely applicable simp lemmas with key discrimination tree keys
with `mid` priority in order to ensure that they are not tried first.

We do not use `low`, to allow bundled morphisms to unfold themselves with `low` priority such that
the generic morphism lemmas are applied first. For instance, we might have
```lean
def fooMonoidHom : M →* N where
  toFun := foo; map_one' := sorry; map_mul' := sorry

@[simp low] lemma fooMonoidHom_apply (x : M) : fooMonoidHom x = foo x := rfl
```
As `map_mul` is tagged `simp mid`, this means that it still fires before `fooMonoidHom_apply`, which
is the behavior we desire.
-/

variable [FunLike F M N]

/-- See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid, grind =)]
/-
**map_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_one [OneHomClass F M N] (f : F) : f 1 = 1
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneHomClass.map_one`：∀ {F : Type u_10} {M : outParam (Type u_11)} {N : o
utParam (Type u_12)} {inst : One M} {inst_1 : One N}   {inst_2 : FunLike F M N} 
[self : O…

--- 原说明 ---
See note [hom simp lemma priority]
-/
theorem map_one [OneHomClass F M N] (f : F) : f 1 = 1 :=
  OneHomClass.map_one f
/-
**map_comp_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : One 
M] [inst_1 : One N] [inst_2 : FunLike F M N]   [OneHomClass F M N] (f : F), ⇑f ∘
 1 = 1
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma map_comp_one [OneHomClass F M N] (f : F) : f ∘ (1 : ι → M) = 1 := by simp

/-- In principle this could be an instance, but in practice it causes performance issues. -/
@[to_additive]
/-
**Subsingleton.of_oneHomClass** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsingleton.of_oneHomClass [Subsingleton M] [OneHomClass F M N] : Subsing
leton F where allEq f g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In principle this could be an instance, but in practice it causes performance is
sues.
-/
theorem Subsingleton.of_oneHomClass [Subsingleton M] [OneHomClass F M N] :
    Subsingleton F where
  allEq f g := DFunLike.ext _ _ fun x ↦ by simp [Subsingleton.elim x 1]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Subsingleton M] : Subsingleton (OneHom M N) := .of_oneHomClass

@[to_additive]
/-
**map_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Function.Injective f) {x 
: M} : f x = 1 ↔ x = 1
参数：f : F；hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
-/
theorem map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Function.Injective f)
    {x : M} :
    f x = 1 ↔ x = 1 := hf.eq_iff' (map_one f)

@[to_additive]
/-
**map_ne_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_ne_one_iff {R S F : Type*} [One R] [One S] [FunLike F R S] [OneHomClas
s F R S] (f : F) (hf : Function.Injective f) {x : R} : f x != 1 ↔ x != 1
参数：f : F；hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `map_eq_one_iff`：map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Functio
n.Injective f) {x : M} : f x = 1 ↔ x = 1
-/
theorem map_ne_one_iff {R S F : Type*} [One R] [One S] [FunLike F R S] [OneHomClass F R S] (f : F)
    (hf : Function.Injective f) {x : R} : f x ≠ 1 ↔ x ≠ 1 := (map_eq_one_iff f hf).not

@[to_additive]
/-
**ne_one_of_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_one_of_map {R S F : Type*} [One R] [One S] [FunLike F R S] [OneHomClass
 F R S] {f : F} {x : R} (hx : f x != 1) : x != 1
参数：hx : f x != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
-/
theorem ne_one_of_map {R S F : Type*} [One R] [One S] [FunLike F R S] [OneHomClass F R S]
    {f : F} {x : R} (hx : f x ≠ 1) : x ≠ 1 := ne_of_apply_ne f <| (by rwa [(map_one f)])

/-- Turn an element of a type `F` satisfying `OneHomClass F M N` into an actual
`OneHom`. This is declared as the default coercion from `F` to `OneHom M N`. -/
@[to_additive (attr := coe)
/-- Turn an element of a type `F` satisfying `ZeroHomClass F M N` into an actual
`ZeroHom`. This is declared as the default coercion from `F` to `ZeroHom M N`. -/]
/-
**OneHomClass.toOneHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OneHomClass.toOneHom [OneHomClass F M N] (f : F) : OneHom M N where toFun
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OneHomClass.map_one`：∀ {F : Type u_10} {M : outParam (Type u_11)} {N : o
utParam (Type u_12)} {inst : One M} {inst_1 : One N}   {inst_2 : FunLike F M N} 
[self : O…
-/
def OneHomClass.toOneHom [OneHomClass F M N] (f : F) : OneHom M N where
  toFun := f
  map_one' := map_one f

/-- Any type satisfying `OneHomClass` can be cast into `OneHom` via `OneHomClass.toOneHom`. -/
@[to_additive /-- Any type satisfying `ZeroHomClass` can be cast into `ZeroHom` via
`ZeroHomClass.toZeroHom`. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [OneHomClass F M N] : CoeTC F (OneHom M N) :=
  ⟨OneHomClass.toOneHom⟩

@[to_additive (attr := simp)]
/-
**OneHom.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.coe_coe [OneHomClass F M N] (f : F) : ((f : OneHom M N) : M -> N) =
 f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem OneHom.coe_coe [OneHomClass F M N] (f : F) :
    ((f : OneHom M N) : M → N) = f := rfl

end One

section Mul

variable [Mul M] [Mul N]

/-- `M →ₙ* N` is the type of functions `M → N` that preserve multiplication. The `ₙ` in the notation
stands for "non-unital" because it is intended to match the notation for `NonUnitalAlgHom` and
`NonUnitalRingHom`, so a `MulHom` is a non-unital monoid hom.

When possible, instead of parametrizing results over `(f : M →ₙ* N)`,
you should parametrize over `(F : Type*) [MulHomClass F M N] (f : F)`.
When you extend this structure, make sure to extend `MulHomClass`.
-/
@[to_additive]
/-
**MulHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_10) → (N : Type u_11) → [Mul M] → [Mul N] → Type (max u_10 u_1
1)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M →ₙ* N` is the type of functions `M → N` that preserve multiplication. The `ₙ`
 in the notation
stands for "non-unital" because it is intended to match the notation for `NonUni
talAlgHom` and
`NonUnitalRingHom`, so a `MulHom` is a non-unital monoid hom.

When possible, instead of parametrizing results over `(f : M →ₙ* N)`,
you should parametrize over `(F : Type*) [MulHomClass F M N] (f : F)`.
When you extend this structure, make sure to extend `MulHomClass`.
-/
structure MulHom (M : Type*) (N : Type*) [Mul M] [Mul N] where
  /-- The underlying function -/
  protected toFun : M → N
  /-- The proposition that the function preserves multiplication -/
  protected map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y

/-- `M →ₙ* N` denotes the type of multiplication-preserving maps from `M` to `N`. -/
infixr:25 " →ₙ* " => MulHom

/-- `MulHomClass F M N` states that `F` is a type of multiplication-preserving homomorphisms.

You should declare an instance of this typeclass when you extend `MulHom`.
-/
@[to_additive]
/-
**MulHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_10) → (M : outParam (Type u_11)) → (N : outParam (Type u_12)) 
→ [Mul M] → [Mul N] → [FunLike F M N] → Prop
参数：Type u_11；Type u_12。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MulHomClass F M N` states that `F` is a type of multiplication-preserving homom
orphisms.

You should declare an instance of this typeclass when you extend `MulHom`.
-/
class MulHomClass (F : Type*) (M N : outParam Type*) [Mul M] [Mul N] [FunLike F M N] : Prop where
  /-- The proposition that the function preserves multiplication -/
  map_mul : ∀ (f : F) (x y : M), f (x * y) = f x * f y

@[to_additive]
/-
**MulHom.funLike** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulHom.funLike : FunLike (M ->ₙ* N) M N where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulHom.funLike : FunLike (M →ₙ* N) M N where
  coe := MulHom.toFun
  coe_injective f g h := by cases f; cases g; congr

/-- `MulHom` is a type of multiplication-preserving homomorphisms -/
@[to_additive /-- `AddHom` is a type of addition-preserving homomorphisms -/]
/-
**MulHom.mulHomClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulHom.mulHomClass : MulHomClass (M ->ₙ* N) M N where map_mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : Mul M] [inst_
1 : Mul N] (self : M →ₙ* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toF…

--- 原说明 ---
`MulHom` is a type of multiplication-preserving homomorphisms
-/
instance MulHom.mulHomClass : MulHomClass (M →ₙ* N) M N where
  map_mul := MulHom.map_mul'

variable [FunLike F M N]

/-- See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid, grind =)]
/-
**map_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x * f y
参数：f : F；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHomClass.map_mul`：∀ {F : Type u_10} {M : outParam (Type u_11)} {N : o
utParam (Type u_12)} {inst : Mul M} {inst_1 : Mul N}   {inst_2 : FunLike F M N} 
[self : M…

--- 原说明 ---
See note [hom simp lemma priority]
-/
theorem map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x * f y :=
  MulHomClass.map_mul f x y

@[to_additive (attr := simp)]
/-
**map_comp_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_comp_mul [MulHomClass F M N] (f : F) (g h : ι -> M) : f ∘ (g * h) = f 
∘ g * f ∘ h
参数：f : F；g h : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_mul [MulHomClass F M N] (f : F) (g h : ι → M) : f ∘ (g * h) = f ∘ g * f ∘ h := by
  ext; simp

/-- Turn an element of a type `F` satisfying `MulHomClass F M N` into an actual
`MulHom`. This is declared as the default coercion from `F` to `M →ₙ* N`. -/
@[to_additive (attr := coe)
/-- Turn an element of a type `F` satisfying `AddHomClass F M N` into an actual
`AddHom`. This is declared as the default coercion from `F` to `M →ₙ+ N`. -/]
/-
**MulHomClass.toMulHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulHomClass.toMulHom [MulHomClass F M N] (f : F) : M ->ₙ* N where toFun
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulHomClass.map_mul`：∀ {F : Type u_10} {M : outParam (Type u_11)} {N : o
utParam (Type u_12)} {inst : Mul M} {inst_1 : Mul N}   {inst_2 : FunLike F M N} 
[self : M…
-/
def MulHomClass.toMulHom [MulHomClass F M N] (f : F) : M →ₙ* N where
  toFun := f
  map_mul' := map_mul f

/-- Any type satisfying `MulHomClass` can be cast into `MulHom` via `MulHomClass.toMulHom`. -/
@[to_additive /-- Any type satisfying `AddHomClass` can be cast into `AddHom` via
`AddHomClass.toAddHom`. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulHomClass F M N] : CoeTC F (M →ₙ* N) :=
  ⟨MulHomClass.toMulHom⟩

@[to_additive (attr := simp)]
/-
**MulHom.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.coe_coe [MulHomClass F M N] (f : F) : ((f : MulHom M N) : M -> N) =
 f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MulHom.coe_coe [MulHomClass F M N] (f : F) : ((f : MulHom M N) : M → N) = f := rfl

end Mul

section mul_one

variable [MulOne M] [MulOne N]

/-- `M →* N` is the type of functions `M → N` that preserve the `MulOne` structure.
`MonoidHom` is used for both monoid and group homomorphisms.

When possible, instead of parametrizing results over `(f : M →* N)`,
you should parametrize over `(F : Type*) [MonoidHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `MonoidHomClass`.
-/
@[to_additive (attr := wikidata Q868169)]
/-
**MonoidHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_10) → (N : Type u_11) → [MulOne M] → [MulOne N] → Type (max u_
10 u_11)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M →* N` is the type of functions `M → N` that preserve the `MulOne` structure.
`MonoidHom` is used for both monoid and group homomorphisms.

When possible, instead of parametrizing results over `(f : M →* N)`,
you should parametrize over `(F : Type*) [MonoidHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `MonoidHomClass`.
-/
structure MonoidHom (M : Type*) (N : Type*) [MulOne M] [MulOne N]
  extends OneHom M N, M →ₙ* N

attribute [nolint docBlame] MonoidHom.toMulHom
attribute [nolint docBlame] MonoidHom.toOneHom

/-- `M →* N` denotes the type of monoid homomorphisms from `M` to `N`. -/
infixr:25 " →* " => MonoidHom

/-- `MonoidHomClass F M N` states that `F` is a type of `Monoid`-preserving homomorphisms.
You should also extend this typeclass when you extend `MonoidHom`. -/
@[to_additive]
/-
**MonoidHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_10) →   (M : outParam (Type u_11)) → (N : outParam (Type u_12)
) → [MulOne M] → [MulOne N] → [FunLike F M N] → Prop
参数：Type u_11；Type u_12。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoidHomClass F M N` states that `F` is a type of `Monoid`-preserving homomorp
hisms.
You should also extend this typeclass when you extend `MonoidHom`.
-/
class MonoidHomClass (F : Type*) (M N : outParam Type*) [MulOne M] [MulOne N]
  [FunLike F M N] : Prop
  extends MulHomClass F M N, OneHomClass F M N

@[to_additive]
/-
**MonoidHom.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MonoidHom.instFunLike : FunLike (M ->* N) M N where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MonoidHom.instFunLike : FunLike (M →* N) M N where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

@[to_additive]
/-
**MonoidHom.instMonoidHomClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MonoidHom.instMonoidHomClass : MonoidHomClass (M ->* N) M N where map_mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `OneHom.map_one'`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [inst_
1 : One N] (self : OneHom M N), self.toFun 1 = 1
-/
instance MonoidHom.instMonoidHomClass : MonoidHomClass (M →* N) M N where
  map_mul := MonoidHom.map_mul'
  map_one f := f.toOneHom.map_one'
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Subsingleton M] : Subsingleton (M →* N) := .of_oneHomClass

variable [FunLike F M N]

/-- Turn an element of a type `F` satisfying `MonoidHomClass F M N` into an actual
`MonoidHom`. This is declared as the default coercion from `F` to `M →* N`. -/
@[to_additive (attr := coe)
/-- Turn an element of a type `F` satisfying `AddMonoidHomClass F M N` into an
actual `MonoidHom`. This is declared as the default coercion from `F` to `M →+ N`. -/]
/-
**MonoidHomClass.toMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHomClass.toMonoidHom [MonoidHomClass F M N] (f : F) : M ->* N
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
def MonoidHomClass.toMonoidHom [MonoidHomClass F M N] (f : F) : M →* N :=
  { (f : M →ₙ* N), (f : OneHom M N) with }

/-- Any type satisfying `MonoidHomClass` can be cast into `MonoidHom` via
`MonoidHomClass.toMonoidHom`. -/
@[to_additive /-- Any type satisfying `AddMonoidHomClass` can be cast into `AddMonoidHom` via
`AddMonoidHomClass.toAddMonoidHom`. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MonoidHomClass F M N] : CoeTC F (M →* N) :=
  ⟨MonoidHomClass.toMonoidHom⟩

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.coe_coe [MonoidHomClass F M N] (f : F) : ((f : M ->* N) : M -> N
) = f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidHom.coe_coe [MonoidHomClass F M N] (f : F) : ((f : M →* N) : M → N) = f := rfl

@[to_additive]
/-
**map_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} (h : a * b = 1) : 
f a * f b = 1
参数：f : F；h : a * b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} (h : a * b = 1) :
    f a * f b = 1 := by
  rw [← map_mul, h, map_one]

variable [FunLike F G H]

@[to_additive]
/-
**map_div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_div' [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H] (f : F) (hf
 : forall a, f a⁻¹ = (f a)⁻¹) (a b : G) : f (a / b) = f a / f b
参数：f : F；hf : forall a, f a⁻¹ = (f a)⁻¹；a b : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_div' [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H]
    (f : F) (hf : ∀ a, f a⁻¹ = (f a)⁻¹) (a b : G) : f (a / b) = f a / f b := by
  grind [div_eq_mul_inv]

@[to_additive]
/-
**map_comp_div'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_comp_div' [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H] (f : F
) (hf : forall a, f a⁻¹ = (f a)⁻¹) (g h : ι -> G) : f ∘ (g / h) = f ∘ g / f ∘ h
参数：f : F；hf : forall a, f a⁻¹ = (f a)⁻¹；g h : ι -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div'`：map_div' [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H]
 (f : F) (hf : forall a, f a⁻¹ = (f a)⁻¹) (a b : G) : f (a / b) = f a / f b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_div' [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H] (f : F)
    (hf : ∀ a, f a⁻¹ = (f a)⁻¹) (g h : ι → G) : f ∘ (g / h) = f ∘ g / f ∘ h := by
  ext; simp [map_div' f hf]

/-- Group homomorphisms preserve inverse.

See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid, grind =) /-- Additive group homomorphisms preserve negation. -/]
/-
**map_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (a : G
) : f a⁻¹ = (f a)⁻¹
参数：f : F；a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
· 使用定理 `map_mul_eq_one`：map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} 
(h : a * b = 1) : f a * f b = 1
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1

--- 原说明 ---
Group homomorphisms preserve inverse.

See note [hom simp lemma priority]
-/
theorem map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H]
    (f : F) (a : G) : f a⁻¹ = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| map_mul_eq_one f <| inv_mul_cancel _

@[to_additive (attr := simp)]
/-
**map_comp_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_comp_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (
g : ι -> G) : f ∘ g⁻¹ = (f ∘ g)⁻¹
参数：f : F；g : ι -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g : ι → G) :
    f ∘ g⁻¹ = (f ∘ g)⁻¹ := by ext; simp

/-- Group homomorphisms preserve division. -/
@[to_additive /-- Additive group homomorphisms preserve subtraction. -/]
/-
**map_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mul_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (a
 b : G) : f (a * b⁻¹) = f a * (f b)⁻¹
参数：f : F；a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹

--- 原说明 ---
Group homomorphisms preserve division.
-/
theorem map_mul_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (a b : G) :
    f (a * b⁻¹) = f a * (f b)⁻¹ := by rw [map_mul, map_inv]

@[to_additive]
/-
**map_comp_mul_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_comp_mul_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : 
F) (g h : ι -> G) : f ∘ (g * h⁻¹) = f ∘ g * (f ∘ h)⁻¹
参数：f : F；g h : ι -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `map_comp_mul`：map_comp_mul [MulHomClass F M N] (f : F) (g h : ι -> M) : 
f ∘ (g * h) = f ∘ g * f ∘ h
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `map_comp_inv`：map_comp_inv [Group G] [DivisionMonoid H] [MonoidHomClass 
F G H] (f : F) (g : ι -> G) : f ∘ g⁻¹ = (f ∘ g)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_mul_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g h : ι → G) :
    f ∘ (g * h⁻¹) = f ∘ g * (f ∘ h)⁻¹ := by simp

/-- Group homomorphisms preserve division.

See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid, grind =) /-- Additive group homomorphisms preserve subtraction. -/]
/-
**map_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) : fora
ll a b, f (a / b) = f a / f b
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div'`：map_div' [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H]
 (f : F) (hf : forall a, f a⁻¹ = (f a)⁻¹) (a b : G) : f (a / b) = f a / f b
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹

--- 原说明 ---
Group homomorphisms preserve division.

See note [hom simp lemma priority]
-/
theorem map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) :
    ∀ a b, f (a / b) = f a / f b := map_div' _ <| map_inv f

@[to_additive (attr := simp)]
/-
**map_comp_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_comp_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (
g h : ι -> G) : f ∘ (g / h) = f ∘ g / f ∘ h
参数：f : F；g h : ι -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g h : ι → G) :
    f ∘ (g / h) = f ∘ g / f ∘ h := by ext; simp

/-- See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid, grind =) (reorder := a n)]
/-
**map_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike F G H] [ins
t_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : F) (a : G) (n 
: ℕ), f (a ^ n) = f a ^ n
参数：f : F；a : G；n : ℕ；a ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See note [hom simp lemma priority]
-/
theorem map_pow [Monoid G] [Monoid H] [MonoidHomClass F G H] (f : F) (a : G) :
    ∀ n : ℕ, f (a ^ n) = f a ^ n
  | 0 => by rw [pow_zero, pow_zero, map_one]
  | n + 1 => by rw [pow_succ, pow_succ, map_mul, map_pow f a n]

@[to_additive (attr := simp)]
/-
**map_comp_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_comp_pow [Monoid G] [Monoid H] [MonoidHomClass F G H] (f : F) (g : ι -
> G) (n : Nat) : f ∘ (g ^ n) = f ∘ g ^ n
参数：f : F；g : ι -> G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_pow [Monoid G] [Monoid H] [MonoidHomClass F G H] (f : F) (g : ι → G) (n : ℕ) :
    f ∘ (g ^ n) = f ∘ g ^ n := by ext; simp

@[to_additive]
/-
**map_zpow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike F G H] [ins
t_1 : DivInvMonoid G]   [inst_2 : DivInvMonoid H] [MonoidHomClass F G H] (f : F)
,   (∀ (x : G), f x⁻¹ = (f x)⁻¹) → ∀ (a : G) (n : ℤ), f (a ^ n) = f a ^ n
参数：f : F；∀ (x : G), f x⁻¹ = (f x)⁻¹；a : G；n : ℤ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_zpow' [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H]
    (f : F) (hf : ∀ x : G, f x⁻¹ = (f x)⁻¹) (a : G) : ∀ n : ℤ, f (a ^ n) = f a ^ n
  | (n : ℕ) => by rw [zpow_natCast, map_pow, zpow_natCast]
  | Int.negSucc n => by rw [zpow_negSucc, hf, map_pow, ← zpow_negSucc]

@[to_additive (attr := simp)]
/-
**map_comp_zpow'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_comp_zpow' [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H] (f
 : F) (hf : forall x : G, f x⁻¹ = (f x)⁻¹) (g : ι -> G) (n : Int) : f ∘ (g ^ n) 
= f ∘ g ^ n
参数：f : F；hf : forall x : G, f x⁻¹ = (f x)⁻¹；g : ι -> G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zpow'`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : DivInvMonoid G]   [inst_2 : DivInvMonoid H] [MonoidHomClass …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_zpow' [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H] (f : F)
    (hf : ∀ x : G, f x⁻¹ = (f x)⁻¹) (g : ι → G) (n : ℤ) : f ∘ (g ^ n) = f ∘ g ^ n := by
  ext; simp [map_zpow' f hf]

/-- Group homomorphisms preserve integer power.

See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid, grind =) (reorder := g n)
/-- Additive group homomorphisms preserve integer scaling. -/]
/-
**map_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g : 
G) (n : Int) : f (g ^ n) = f g ^ n
参数：f : F；g : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow'`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : DivInvMonoid G]   [inst_2 : DivInvMonoid H] [MonoidHomClass …
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
-/
theorem map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H]
    (f : F) (g : G) (n : ℤ) : f (g ^ n) = f g ^ n := map_zpow' f (map_inv f) g n

@[to_additive]
/-
**map_comp_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_comp_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) 
(g : ι -> G) (n : Int) : f ∘ (g ^ n) = f ∘ g ^ n
参数：f : F；g : ι -> G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `map_comp_zpow'`：map_comp_zpow' [DivInvMonoid G] [DivInvMonoid H] [Monoid
HomClass F G H] (f : F) (hf : forall x : G, f x⁻¹ = (f x)⁻¹) (g : ι -> G) (n : I
nt) …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma map_comp_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g : ι → G)
    (n : ℤ) : f ∘ (g ^ n) = f ∘ g ^ n := by simp

end mul_one

/-- If the codomain of an injective monoid homomorphism is torsion free,
then so is the domain. -/
@[to_additive /-- If the codomain of an injective additive monoid homomorphism is torsion free,
then so is the domain. -/]
/-
**Function.Injective.isMulTorsionFree** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.isMulTorsionFree [Monoid M] [Monoid N] [IsMulTorsionFre
e N] (f : M ->* N) (hf : Function.Injective f) : IsMulTorsionFree M where pow_le
ft_injective n hn x y hxy
参数：f : M ->* N；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulTorsionFree.pow_left_injective`：∀ {M : Type u_2} {inst : Monoid M} 
[self : IsMulTorsionFree M] ⦃n : ℕ⦄, n ≠ 0 → Function.Injective fun a => a ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
-/
theorem Function.Injective.isMulTorsionFree [Monoid M] [Monoid N] [IsMulTorsionFree N]
    (f : M →* N) (hf : Function.Injective f) : IsMulTorsionFree M where
  pow_left_injective n hn x y hxy := hf <| IsMulTorsionFree.pow_left_injective hn <| by
    simpa using congrArg f hxy

-- completely uninteresting lemmas about coercion to function, that all homs need
section Coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/

attribute [coe] MonoidHom.toOneHom
attribute [coe] AddMonoidHom.toZeroHom

/-- `MonoidHom` down-cast to a `OneHom`, forgetting the multiplicative property. -/
@[to_additive /-- `AddMonoidHom` down-cast to a `ZeroHom`, forgetting the additive property -/]
/-
**MonoidHom.coeToOneHom** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MonoidHom.coeToOneHom [MulOne M] [MulOne N] : Coe (M ->* N) (OneHom M N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoidHom` down-cast to a `OneHom`, forgetting the multiplicative property.
-/
instance MonoidHom.coeToOneHom [MulOne M] [MulOne N] : Coe (M →* N) (OneHom M N) :=
  ⟨MonoidHom.toOneHom⟩

attribute [coe] MonoidHom.toMulHom
attribute [coe] AddMonoidHom.toAddHom

/-- `MonoidHom` down-cast to a `MulHom`, forgetting the 1-preserving property. -/
@[to_additive /-- `AddMonoidHom` down-cast to an `AddHom`, forgetting the 0-preserving property. -/]
/-
**MonoidHom.coeToMulHom** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MonoidHom.coeToMulHom [MulOne M] [MulOne N] : Coe (M ->* N) (M ->ₙ* N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoidHom` down-cast to a `MulHom`, forgetting the 1-preserving property.
-/
instance MonoidHom.coeToMulHom [MulOne M] [MulOne N] : Coe (M →* N) (M →ₙ* N) :=
  ⟨MonoidHom.toMulHom⟩

-- these must come after the coe_toFun definitions
initialize_simps_projections ZeroHom (toFun → apply)
initialize_simps_projections AddHom (toFun → apply)
initialize_simps_projections AddMonoidHom (toFun → apply)
initialize_simps_projections OneHom (toFun → apply)
initialize_simps_projections MulHom (toFun → apply)
initialize_simps_projections MonoidHom (toFun → apply)

@[to_additive (attr := simp)]
/-
**OneHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.coe_mk [One M] [One N] (f : M -> N) (h1) : (OneHom.mk f h1 : M -> N
) = f
参数：f : M -> N；h1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem OneHom.coe_mk [One M] [One N] (f : M → N) (h1) : (OneHom.mk f h1 : M → N) = f := rfl

@[to_additive (attr := simp)]
/-
**OneHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.toFun_eq_coe [One M] [One N] (f : OneHom M N) : f.toFun = f
参数：f : OneHom M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem OneHom.toFun_eq_coe [One M] [One N] (f : OneHom M N) : f.toFun = f := rfl

@[to_additive (attr := simp)]
/-
**MulHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.coe_mk [Mul M] [Mul N] (f : M -> N) (hmul) : (MulHom.mk f hmul : M 
-> N) = f
参数：f : M -> N；hmul。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MulHom.coe_mk [Mul M] [Mul N] (f : M → N) (hmul) : (MulHom.mk f hmul : M → N) = f := rfl

@[to_additive (attr := simp)]
/-
**MulHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.toFun_eq_coe [Mul M] [Mul N] (f : M ->ₙ* N) : f.toFun = f
参数：f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MulHom.toFun_eq_coe [Mul M] [Mul N] (f : M →ₙ* N) : f.toFun = f := rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.coe_mk [MulOne M] [MulOne N] (f hmul) : (MonoidHom.mk f hmul : M
 -> N) = f
参数：f hmul。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidHom.coe_mk [MulOne M] [MulOne N] (f hmul) :
    (MonoidHom.mk f hmul : M → N) = f := rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.toOneHom_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.toOneHom_coe [MulOne M] [MulOne N] (f : M ->* N) : (f.toOneHom :
 M -> N) = f
参数：f : M ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidHom.toOneHom_coe [MulOne M] [MulOne N] (f : M →* N) :
    (f.toOneHom : M → N) = f := rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.toMulHom_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.toMulHom_coe [MulOne M] [MulOne N] (f : M ->* N) : f.toMulHom.to
Fun = f
参数：f : M ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidHom.toMulHom_coe [MulOne M] [MulOne N] (f : M →* N) :
    f.toMulHom.toFun = f := rfl

@[to_additive]
/-
**MonoidHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.toFun_eq_coe [MulOne M] [MulOne N] (f : M ->* N) : f.toFun = f
参数：f : M ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidHom.toFun_eq_coe [MulOne M] [MulOne N] (f : M →* N) : f.toFun = f := rfl

@[to_additive (attr := ext)]
/-
**OneHom.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.ext [One M] [One N] ⦃f g : OneHom M N⦄ (h : forall x, f x = g x) : 
f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem OneHom.ext [One M] [One N] ⦃f g : OneHom M N⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[to_additive (attr := ext)]
/-
**MulHom.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f x = g x) : f 
= g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem MulHom.ext [Mul M] [Mul N] ⦃f g : M →ₙ* N⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[to_additive (attr := ext)]
/-
**MonoidHom.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : forall x, f x = g
 x) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M →* N⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

namespace MonoidHom

variable [Group G]
variable [MulOneClass M]

/-- Makes a group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Makes an additive group homomorphism from a proof that the map preserves addition. -/]
/-
**MonoidHom.mk'** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：mk' (f : M -> G) (map_mul : forall a b : M, f (a * b) = f a * f b) : M ->*
 G where toFun
参数：f : M -> G；map_mul : forall a b : M, f (a * b) = f a * f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mk' (f : M → G) (map_mul : ∀ a b : M, f (a * b) = f a * f b) : M →* G where
  toFun := f
  map_mul' := map_mul
  map_one' := by rw [← mul_right_cancel_iff, ← map_mul _ 1, one_mul, one_mul]

end MonoidHom

@[to_additive (attr := simp)]
/-
**OneHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.mk_coe [One M] [One N] (f : OneHom M N) (h1) : OneHom.mk f h1 = f
参数：f : OneHom M N；h1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneHom.ext`：OneHom.ext [One M] [One N] ⦃f g : OneHom M N⦄ (h : forall x,
 f x = g x) : f = g
-/
theorem OneHom.mk_coe [One M] [One N] (f : OneHom M N) (h1) : OneHom.mk f h1 = f :=
  OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/-
**MulHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.mk_coe [Mul M] [Mul N] (f : M ->ₙ* N) (hmul) : MulHom.mk f hmul = f
参数：f : M ->ₙ* N；hmul。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.ext`：MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f
 x = g x) : f = g
-/
theorem MulHom.mk_coe [Mul M] [Mul N] (f : M →ₙ* N) (hmul) : MulHom.mk f hmul = f :=
  MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.mk_coe [MulOne M] [MulOne N] (f : M ->* N) (hmul) : MonoidHom.mk
 f hmul = f
参数：f : M ->* N；hmul。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
-/
theorem MonoidHom.mk_coe [MulOne M] [MulOne N] (f : M →* N) (hmul) :
    MonoidHom.mk f hmul = f := MonoidHom.ext fun _ => rfl

end Coes

/-- Copy of a `OneHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive
  /-- Copy of a `ZeroHom` with a new `toFun` equal to the old one. Useful to fix
  definitional equalities. -/]
/-
**OneHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `OneHom`。
形式化陈述：{M : Type u_4} →   {N : Type u_5} → [inst : One M] → [inst_1 : One N] → (f
 : OneHom M N) → (f' : M → N) → f' = ⇑f → OneHom M N
参数：f : OneHom M N；f' : M → N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def OneHom.copy [One M] [One N] (f : OneHom M N) (f' : M → N) (h : f' = f) :
    OneHom M N where
  toFun := f'
  map_one' := h.symm ▸ f.map_one'

@[to_additive (attr := simp)]
/-
**OneHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.coe_copy {_ : One M} {_ : One N} (f : OneHom M N) (f' : M -> N) (h 
: f' = f) : (f.copy f' h) = f'
参数：f : OneHom M N；f' : M -> N；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem OneHom.coe_copy {_ : One M} {_ : One N} (f : OneHom M N) (f' : M → N) (h : f' = f) :
    (f.copy f' h) = f' :=
  rfl

@[to_additive]
/-
**OneHom.coe_copy_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.coe_copy_eq {_ : One M} {_ : One N} (f : OneHom M N) (f' : M -> N) 
(h : f' = f) : f.copy f' h = f
参数：f : OneHom M N；f' : M -> N；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem OneHom.coe_copy_eq {_ : One M} {_ : One N} (f : OneHom M N) (f' : M → N) (h : f' = f) :
    f.copy f' h = f :=
  DFunLike.ext' h

/-- Copy of a `MulHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive
  /-- Copy of an `AddHom` with a new `toFun` equal to the old one. Useful to fix
  definitional equalities. -/]
/-
**MulHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：{M : Type u_4} → {N : Type u_5} → [inst : Mul M] → [inst_1 : Mul N] → (f :
 M →ₙ* N) → (f' : M → N) → f' = ⇑f → M →ₙ* N
参数：f : M →ₙ* N；f' : M → N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def MulHom.copy [Mul M] [Mul N] (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    M →ₙ* N where
  toFun := f'
  map_mul' := h.symm ▸ f.map_mul'

@[to_additive (attr := simp)]
/-
**MulHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.coe_copy {_ : Mul M} {_ : Mul N} (f : M ->ₙ* N) (f' : M -> N) (h : 
f' = f) : (f.copy f' h) = f'
参数：f : M ->ₙ* N；f' : M -> N；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MulHom.coe_copy {_ : Mul M} {_ : Mul N} (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    (f.copy f' h) = f' :=
  rfl

@[to_additive]
/-
**MulHom.coe_copy_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.coe_copy_eq {_ : Mul M} {_ : Mul N} (f : M ->ₙ* N) (f' : M -> N) (h
 : f' = f) : f.copy f' h = f
参数：f : M ->ₙ* N；f' : M -> N；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem MulHom.coe_copy_eq {_ : Mul M} {_ : Mul N} (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    f.copy f' h = f :=
  DFunLike.ext' h

/-- Copy of a `MonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
@[to_additive
  /-- Copy of an `AddMonoidHom` with a new `toFun` equal to the old one. Useful to fix
  definitional equalities. -/]
/-
**MonoidHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：{M : Type u_4} →   {N : Type u_5} → [inst : MulOne M] → [inst_1 : MulOne N
] → (f : M →* N) → (f' : M → N) → f' = ⇑f → M →* N
参数：f : M →* N；f' : M → N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def MonoidHom.copy [MulOne M] [MulOne N] (f : M →* N) (f' : M → N)
    (h : f' = f) : M →* N :=
  { f.toOneHom.copy f' h, f.toMulHom.copy f' h with }

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.coe_copy {_ : MulOne M} {_ : MulOne N} (f : M ->* N) (f' : M -> 
N) (h : f' = f) : (f.copy f' h) = f'
参数：f : M ->* N；f' : M -> N；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidHom.coe_copy {_ : MulOne M} {_ : MulOne N} (f : M →* N) (f' : M → N)
    (h : f' = f) : (f.copy f' h) = f' :=
  rfl

@[to_additive]
/-
**MonoidHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.copy_eq {_ : MulOne M} {_ : MulOne N} (f : M ->* N) (f' : M -> N
) (h : f' = f) : f.copy f' h = f
参数：f : M ->* N；f' : M -> N；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem MonoidHom.copy_eq {_ : MulOne M} {_ : MulOne N} (f : M →* N) (f' : M → N)
    (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[to_additive]
/-
**OneHom.map_one** 是 Mathlib 中的一个定理，位于命名空间 `OneHom`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : One M] [inst_1 : One N] (f : OneHo
m M N), f 1 = 1
参数：f : OneHom M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneHom.map_one'`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [inst_
1 : One N] (self : OneHom M N), self.toFun 1 = 1
-/
protected theorem OneHom.map_one [One M] [One N] (f : OneHom M N) : f 1 = 1 :=
  f.map_one'

/-- If `f` is a monoid homomorphism then `f 1 = 1`. -/
@[to_additive /-- If `f` is an additive monoid homomorphism then `f 0 = 0`. -/]
/-
**MonoidHom.map_one** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [inst_1 : MulOne N] (f :
 M →* N), f 1 = 1
参数：f : M →* N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneHom.map_one'`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [inst_
1 : One N] (self : OneHom M N), self.toFun 1 = 1

--- 原说明 ---
If `f` is a monoid homomorphism then `f 1 = 1`.
-/
protected theorem MonoidHom.map_one [MulOne M] [MulOne N] (f : M →* N) : f 1 = 1 :=
  f.map_one'

@[to_additive]
/-
**MulHom.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst_1 : Mul N] (f : M →ₙ*
 N) (a b : M), f (a * b) = f a * f b
参数：f : M →ₙ* N；a b : M；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : Mul M] [inst_
1 : Mul N] (self : M →ₙ* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toF…
-/
protected theorem MulHom.map_mul [Mul M] [Mul N] (f : M →ₙ* N) (a b : M) : f (a * b) = f a * f b :=
  f.map_mul' a b

/-- If `f` is a monoid homomorphism then `f (a * b) = f a * f b`. -/
@[to_additive /-- If `f` is an additive monoid homomorphism then `f (a + b) = f a + f b`. -/]
/-
**MonoidHom.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [inst_1 : MulOne N] (f :
 M →* N) (a b : M), f (a * b) = f a * f b
参数：f : M →* N；a b : M；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…

--- 原说明 ---
If `f` is a monoid homomorphism then `f (a * b) = f a * f b`.
-/
protected theorem MonoidHom.map_mul [MulOne M] [MulOne N] (f : M →* N) (a b : M) :
    f (a * b) = f a * f b := f.map_mul' a b

namespace MonoidHom

variable [MulOne M] [MulOne N] [FunLike F M N] [MonoidHomClass F M N]

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a right inverse,
then `f x` has a right inverse too. For elements invertible on both sides see `IsUnit.map`. -/
@[to_additive
  /-- Given an AddMonoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has
  a right inverse, then `f x` has a right inverse too. -/]
/-
**MonoidHom.map_exists_right_inv** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：map_exists_right_inv (f : F) {x : M} (hx : exists y, x * y = 1) : exists y
, f x * y = 1
参数：f : F；hx : exists y, x * y = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul_eq_one`：map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} 
(h : a * b = 1) : f a * f b = 1
-/
theorem map_exists_right_inv (f : F) {x : M} (hx : ∃ y, x * y = 1) : ∃ y, f x * y = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a left inverse,
then `f x` has a left inverse too. For elements invertible on both sides see `IsUnit.map`. -/
@[to_additive
  /-- Given an AddMonoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has
  a left inverse, then `f x` has a left inverse too. For elements invertible on both sides see
  `IsAddUnit.map`. -/]
/-
**MonoidHom.map_exists_left_inv** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：map_exists_left_inv (f : F) {x : M} (hx : exists y, y * x = 1) : exists y,
 y * f x = 1
参数：f : F；hx : exists y, y * x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul_eq_one`：map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} 
(h : a * b = 1) : f a * f b = 1
-/
theorem map_exists_left_inv (f : F) {x : M} (hx : ∃ y, y * x = 1) : ∃ y, y * f x = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩
/-
**MonoidHom._root_.IsDedekindFiniteMonoid.of_injective** 是 Mathlib 中的一个定理，位于命名空间
 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] theorem _root_.IsDedekindFiniteMonoid.of_injective (f : F)
    (hf : Function.Injective f) [IsDedekindFiniteMonoid N] : IsDedekindFiniteMonoid M where
  mul_eq_one_symm eq := hf <| by simpa [mul_eq_one_comm] using congr_arg f eq

@[to_additive]
/-
**MonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Type*} [Monoid M] [LeftCancelMonoid N] : MonoidHomClass (M →ₙ* N) M N where
  map_mul := MulHom.map_mul'
  map_one f := by
    have h : f 1 * 1 = f 1 * f 1 := by simpa using f.map_mul' 1 1
    exact (mul_left_cancel h).symm

@[to_additive]
/-
**MonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Type*} [Monoid M] [RightCancelMonoid N] : MonoidHomClass (M →ₙ* N) M N where
  map_mul := MulHom.map_mul'
  map_one f := by
    have h : 1 * f 1 = f 1 * f 1 := by simpa using f.map_mul' 1 1
    exact (mul_right_cancel h).symm

@[to_additive]
/-
**MonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Type*} [Monoid M] [CancelMonoid N] : MonoidHomClass (M →ₙ* N) M N where

end MonoidHom

/-- The identity map from a type with 1 to itself. -/
@[to_additive (attr := simps, instance_reducible)
/-- The identity map from a type with zero to itself. -/]
/-
**OneHom.id** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OneHom.id (M : Type*) [One M] : OneHom M M where toFun x
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def OneHom.id (M : Type*) [One M] : OneHom M M where
  toFun x := x
  map_one' := rfl

/-- The identity map from a type with multiplication to itself. -/
@[to_additive (attr := simps, instance_reducible)
/-- The identity map from a type with addition to itself. -/]
/-
**MulHom.id** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulHom.id (M : Type*) [Mul M] : M ->ₙ* M where toFun x
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulHom.id (M : Type*) [Mul M] : M →ₙ* M where
  toFun x := x
  map_mul' _ _ := rfl

/-- The identity map from a monoid to itself. -/
@[to_additive (attr := simps, instance_reducible)
/-- The identity map from an additive monoid to itself. -/]
/-
**MonoidHom.id** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.id (M : Type*) [MulOne M] : M ->* M where toFun x
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MonoidHom.id (M : Type*) [MulOne M] : M →* M where
  toFun x := x
  map_one' := rfl
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]
/-
**OneHom.coe_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OneHom.coe_id {M : Type*} [One M] : (OneHom.id M : M -> M) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma OneHom.coe_id {M : Type*} [One M] : (OneHom.id M : M → M) = _root_.id := rfl

@[to_additive (attr := simp)]
/-
**MulHom.coe_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulHom.coe_id {M : Type*} [Mul M] : (MulHom.id M : M -> M) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MulHom.coe_id {M : Type*} [Mul M] : (MulHom.id M : M → M) = _root_.id := rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.coe_id {M : Type*} [MulOne M] : (MonoidHom.id M : M -> M) = _roo
t_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MonoidHom.coe_id {M : Type*} [MulOne M] : (MonoidHom.id M : M → M) = _root_.id := rfl

/-- Composition of `OneHom`s as a `OneHom`. -/
@[to_additive (attr := instance_reducible) /-- Composition of `ZeroHom`s as a `ZeroHom`. -/]
/-
**OneHom.comp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OneHom.comp [One M] [One N] [One P] (hnp : OneHom N P) (hmn : OneHom M N) 
: OneHom M P where toFun x
参数：hnp : OneHom N P；hmn : OneHom M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `OneHom`s as a `OneHom`.
-/
def OneHom.comp [One M] [One N] [One P] (hnp : OneHom N P) (hmn : OneHom M N) : OneHom M P where
  toFun x := hnp (hmn x)
  map_one' := by simp

/-- Composition of `MulHom`s as a `MulHom`. -/
@[to_additive (attr := instance_reducible) /-- Composition of `AddHom`s as an `AddHom`. -/]
/-
**MulHom.comp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulHom.comp [Mul M] [Mul N] [Mul P] (hnp : N ->ₙ* P) (hmn : M ->ₙ* N) : M 
->ₙ* P where toFun x
参数：hnp : N ->ₙ* P；hmn : M ->ₙ* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `MulHom`s as a `MulHom`.
-/
def MulHom.comp [Mul M] [Mul N] [Mul P] (hnp : N →ₙ* P) (hmn : M →ₙ* N) : M →ₙ* P where
  toFun x := hnp (hmn x)
  map_mul' x y := by simp

/-- Composition of monoid morphisms as a monoid morphism. -/
@[to_additive (attr := instance_reducible)
/-- Composition of additive monoid morphisms as an additive monoid morphism. -/]
/-
**MonoidHom.comp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.comp [MulOne M] [MulOne N] [MulOne P] (hnp : N ->* P) (hmn : M -
>* N) : M ->* P where toFun x
参数：hnp : N ->* P；hmn : M ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MonoidHom.comp [MulOne M] [MulOne N] [MulOne P] (hnp : N →* P) (hmn : M →* N) :
    M →* P where
  toFun x := hnp (hmn x)
  map_one' := by simp
  map_mul' := by simp

@[to_additive (attr := simp)]
/-
**OneHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.coe_comp [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) 
: ↑(g.comp f) = g ∘ f
参数：g : OneHom N P；f : OneHom M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem OneHom.coe_comp [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) :
    ↑(g.comp f) = g ∘ f := rfl

@[to_additive (attr := simp)]
/-
**MulHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.coe_comp [Mul M] [Mul N] [Mul P] (g : N ->ₙ* P) (f : M ->ₙ* N) : ↑(
g.comp f) = g ∘ f
参数：g : N ->ₙ* P；f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MulHom.coe_comp [Mul M] [Mul N] [Mul P] (g : N →ₙ* P) (f : M →ₙ* N) :
    ↑(g.comp f) = g ∘ f := rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.coe_comp [MulOne M] [MulOne N] [MulOne P] (g : N ->* P) (f : M -
>* N) : ↑(g.comp f) = g ∘ f
参数：g : N ->* P；f : M ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidHom.coe_comp [MulOne M] [MulOne N] [MulOne P]
    (g : N →* P) (f : M →* N) : ↑(g.comp f) = g ∘ f := rfl

@[to_additive]
/-
**OneHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.comp_apply [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N
) (x : M) : g.comp f x = g (f x)
参数：g : OneHom N P；f : OneHom M N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem OneHom.comp_apply [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) (x : M) :
    g.comp f x = g (f x) := rfl

@[to_additive]
/-
**MulHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.comp_apply [Mul M] [Mul N] [Mul P] (g : N ->ₙ* P) (f : M ->ₙ* N) (x
 : M) : g.comp f x = g (f x)
参数：g : N ->ₙ* P；f : M ->ₙ* N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MulHom.comp_apply [Mul M] [Mul N] [Mul P] (g : N →ₙ* P) (f : M →ₙ* N) (x : M) :
    g.comp f x = g (f x) := rfl

@[to_additive]
/-
**MonoidHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne P] (g : N ->* P) (f : M
 ->* N) (x : M) : g.comp f x = g (f x)
参数：g : N ->* P；f : M ->* N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne P]
    (g : N →* P) (f : M →* N) (x : M) : g.comp f x = g (f x) := rfl

/-- Composition of monoid homomorphisms is associative. -/
@[to_additive /-- Composition of additive monoid homomorphisms is associative. -/]
/-
**OneHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.comp_assoc {Q : Type*} [One M] [One N] [One P] [One Q] (f : OneHom 
M N) (g : OneHom N P) (h : OneHom P Q) : (h.comp g).comp f = h.comp (g.comp f)
参数：f : OneHom M N；g : OneHom N P；h : OneHom P Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of monoid homomorphisms is associative.
-/
theorem OneHom.comp_assoc {Q : Type*} [One M] [One N] [One P] [One Q]
    (f : OneHom M N) (g : OneHom N P) (h : OneHom P Q) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

@[to_additive]
/-
**MulHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.comp_assoc {Q : Type*} [Mul M] [Mul N] [Mul P] [Mul Q] (f : M ->ₙ* 
N) (g : N ->ₙ* P) (h : P ->ₙ* Q) : (h.comp g).comp f = h.comp (g.comp f)
参数：f : M ->ₙ* N；g : N ->ₙ* P；h : P ->ₙ* Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MulHom.comp_assoc {Q : Type*} [Mul M] [Mul N] [Mul P] [Mul Q]
    (f : M →ₙ* N) (g : N →ₙ* P) (h : P →ₙ* Q) : (h.comp g).comp f = h.comp (g.comp f) := rfl

@[to_additive]
/-
**MonoidHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.comp_assoc {Q : Type*} [MulOne M] [MulOne N] [MulOne P] [MulOne 
Q] (f : M ->* N) (g : N ->* P) (h : P ->* Q) : (h.comp g).comp f = h.comp (g.com
p f)
参数：f : M ->* N；g : N ->* P；h : P ->* Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidHom.comp_assoc {Q : Type*} [MulOne M] [MulOne N] [MulOne P]
    [MulOne Q] (f : M →* N) (g : N →* P) (h : P →* Q) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

@[to_additive]
/-
**OneHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.cancel_right [One M] [One N] [One P] {g₁ g₂ : OneHom N P} {f : OneH
om M N} (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneHom.ext`：OneHom.ext [One M] [One N] ⦃f g : OneHom M N⦄ (h : forall x,
 f x = g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem OneHom.cancel_right [One M] [One N] [One P] {g₁ g₂ : OneHom N P} {f : OneHom M N}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => OneHom.ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]
/-
**MulHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.cancel_right [Mul M] [Mul N] [Mul P] {g₁ g₂ : N ->ₙ* P} {f : M ->ₙ*
 N} (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.ext`：MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem MulHom.cancel_right [Mul M] [Mul N] [Mul P] {g₁ g₂ : N →ₙ* P} {f : M →ₙ* N}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MulHom.ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]
/-
**MonoidHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.cancel_right [MulOne M] [MulOne N] [MulOne P] {g₁ g₂ : N ->* P} 
{f : M ->* N} (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem MonoidHom.cancel_right [MulOne M] [MulOne N] [MulOne P]
    {g₁ g₂ : N →* P} {f : M →* N} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MonoidHom.ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]
/-
**OneHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.cancel_left [One M] [One N] [One P] {g : OneHom N P} {f₁ f₂ : OneHo
m M N} (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Function.Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneHom.ext`：OneHom.ext [One M] [One N] ⦃f g : OneHom M N⦄ (h : forall x,
 f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OneHom.comp_apply`：OneHom.comp_apply [One M] [One N] [One P] (g : OneHom
 N P) (f : OneHom M N) (x : M) : g.comp f x = g (f x)
-/
theorem OneHom.cancel_left [One M] [One N] [One P] {g : OneHom N P} {f₁ f₂ : OneHom M N}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => OneHom.ext fun x => hg <| by rw [← OneHom.comp_apply, h, OneHom.comp_apply],
    fun h => h ▸ rfl⟩

@[to_additive]
/-
**MulHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.cancel_left [Mul M] [Mul N] [Mul P] {g : N ->ₙ* P} {f₁ f₂ : M ->ₙ* 
N} (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Function.Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.ext`：MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulHom.comp_apply`：MulHom.comp_apply [Mul M] [Mul N] [Mul P] (g : N ->ₙ*
 P) (f : M ->ₙ* N) (x : M) : g.comp f x = g (f x)
-/
theorem MulHom.cancel_left [Mul M] [Mul N] [Mul P] {g : N →ₙ* P} {f₁ f₂ : M →ₙ* N}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => MulHom.ext fun x => hg <| by rw [← MulHom.comp_apply, h, MulHom.comp_apply],
    fun h => h ▸ rfl⟩

@[to_additive]
/-
**MonoidHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.cancel_left [MulOne M] [MulOne N] [MulOne P] {g : N ->* P} {f₁ f
₂ : M ->* N} (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Function.Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.comp_apply`：MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne
 P] (g : N ->* P) (f : M ->* N) (x : M) : g.comp f x = g (f x)
-/
theorem MonoidHom.cancel_left [MulOne M] [MulOne N] [MulOne P]
    {g : N →* P} {f₁ f₂ : M →* N} (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => MonoidHom.ext fun x => hg <| by rw [← MonoidHom.comp_apply, h, MonoidHom.comp_apply],
    fun h => h ▸ rfl⟩

section

@[to_additive]
/-
**MonoidHom.toOneHom_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.toOneHom_injective [MulOne M] [MulOne N] : Function.Injective (M
onoidHom.toOneHom : (M ->* N) -> OneHom M N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem MonoidHom.toOneHom_injective [MulOne M] [MulOne N] :
    Function.Injective (MonoidHom.toOneHom : (M →* N) → OneHom M N) :=
  Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

@[to_additive]
/-
**MonoidHom.toMulHom_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.toMulHom_injective [MulOne M] [MulOne N] : Function.Injective (M
onoidHom.toMulHom : (M ->* N) -> M ->ₙ* N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem MonoidHom.toMulHom_injective [MulOne M] [MulOne N] :
    Function.Injective (MonoidHom.toMulHom : (M →* N) → M →ₙ* N) :=
  Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

end

@[to_additive (attr := simp)]
/-
**OneHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.comp_id [One M] [One N] (f : OneHom M N) : f.comp (OneHom.id M) = f
参数：f : OneHom M N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneHom.ext`：OneHom.ext [One M] [One N] ⦃f g : OneHom M N⦄ (h : forall x,
 f x = g x) : f = g
-/
theorem OneHom.comp_id [One M] [One N] (f : OneHom M N) : f.comp (OneHom.id M) = f :=
  OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/-
**MulHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.comp_id [Mul M] [Mul N] (f : M ->ₙ* N) : f.comp (MulHom.id M) = f
参数：f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.ext`：MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f
 x = g x) : f = g
-/
theorem MulHom.comp_id [Mul M] [Mul N] (f : M →ₙ* N) : f.comp (MulHom.id M) = f :=
  MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.comp_id [MulOne M] [MulOne N] (f : M ->* N) : f.comp (MonoidHom.
id M) = f
参数：f : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
-/
theorem MonoidHom.comp_id [MulOne M] [MulOne N] (f : M →* N) :
    f.comp (MonoidHom.id M) = f := MonoidHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/-
**OneHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.id_comp [One M] [One N] (f : OneHom M N) : (OneHom.id N).comp f = f
参数：f : OneHom M N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneHom.ext`：OneHom.ext [One M] [One N] ⦃f g : OneHom M N⦄ (h : forall x,
 f x = g x) : f = g
-/
theorem OneHom.id_comp [One M] [One N] (f : OneHom M N) : (OneHom.id N).comp f = f :=
  OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/-
**MulHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.id_comp [Mul M] [Mul N] (f : M ->ₙ* N) : (MulHom.id N).comp f = f
参数：f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.ext`：MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f
 x = g x) : f = g
-/
theorem MulHom.id_comp [Mul M] [Mul N] (f : M →ₙ* N) : (MulHom.id N).comp f = f :=
  MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.id_comp [MulOne M] [MulOne N] (f : M ->* N) : (MonoidHom.id N).c
omp f = f
参数：f : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
-/
theorem MonoidHom.id_comp [MulOne M] [MulOne N] (f : M →* N) :
    (MonoidHom.id N).comp f = f := MonoidHom.ext fun _ => rfl

@[to_additive (reorder := a n)]
/-
**MonoidHom.map_pow** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [inst_1 : Monoid N] (f :
 M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
参数：f : M →* N；a : M；n : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
-/
protected theorem MonoidHom.map_pow [Monoid M] [Monoid N] (f : M →* N) (a : M) (n : ℕ) :
    f (a ^ n) = f a ^ n := map_pow f a n

@[to_additive (reorder := a n)]
/-
**MonoidHom.map_zpow'** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : DivInvMonoid M] [inst_1 : DivInvMo
noid N] (f : M →* N),   (∀ (x : M), f x⁻¹ = (f x)⁻¹) → ∀ (a : M) (n : ℤ), f (a ^
 n) = f a ^ n
参数：f : M →* N；∀ (x : M), f x⁻¹ = (f x)⁻¹；a : M；n : ℤ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow'`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : DivInvMonoid G]   [inst_2 : DivInvMonoid H] [MonoidHomClass …
-/
protected theorem MonoidHom.map_zpow' [DivInvMonoid M] [DivInvMonoid N] (f : M →* N)
    (hf : ∀ x, f x⁻¹ = (f x)⁻¹) (a : M) (n : ℤ) :
    f (a ^ n) = f a ^ n := map_zpow' f hf a n

/-- Makes a `OneHom` inverse from the bijective inverse of a `OneHom` -/
@[to_additive (attr := simps)
/-- Make a `ZeroHom` inverse from the bijective inverse of a `ZeroHom` -/]
/-
**OneHom.inverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OneHom.inverse [One M] [One N] (f : OneHom M N) (g : N -> M) (h₁ : Functio
n.LeftInverse g f) : OneHom N M
参数：f : OneHom M N；g : N -> M；h₁ : Function.LeftInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def OneHom.inverse [One M] [One N] (f : OneHom M N) (g : N → M) (h₁ : Function.LeftInverse g f) :
    OneHom N M :=
  { toFun := g,
    map_one' := by rw [← f.map_one, h₁] }

/-- Makes a multiplicative inverse from a bijection which preserves multiplication. -/
@[to_additive (attr := simps)
  /-- Makes an additive inverse from a bijection which preserves addition. -/]
/-
**MulHom.inverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulHom.inverse [Mul M] [Mul N] (f : M ->ₙ* N) (g : N -> M) (h₁ : Function.
LeftInverse g f) (h₂ : Function.RightInverse g f) : N ->ₙ* M where toFun
参数：f : M ->ₙ* N；g : N -> M；h₁ : Function.LeftInverse g f；h₂ : Function.RightInve
rse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulHom.inverse [Mul M] [Mul N] (f : M →ₙ* N) (g : N → M)
    (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N →ₙ* M where
  toFun := g
  map_mul' x y :=
    calc
      g (x * y) = g (f (g x) * f (g y)) := by rw [h₂ x, h₂ y]
      _ = g (f (g x * g y)) := by rw [f.map_mul]
      _ = g x * g y := h₁ _

/-- If `M` and `N` have multiplications, `f : M →ₙ* N` is a surjective multiplicative map,
and `M` is commutative, then `N` is commutative. -/
@[to_additive
/-- If `M` and `N` have additions, `f : M →ₙ+ N` is a surjective additive map,
and `M` is commutative, then `N` is commutative. -/]
/-
**Function.Surjective.mul_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.mul_comm [Mul M] [Mul N] {f : M ->ₙ* N} (is_surj : Fun
ction.Surjective f) (is_comm : IsMulCommutative M) : IsMulCommutative N where is
_comm.comm a b
参数：is_surj : Function.Surjective f；is_comm : IsMulCommutative M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_comm'`：mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) 
: a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Function.Surjective.mul_comm [Mul M] [Mul N] {f : M →ₙ* N} (is_surj : Function.Surjective f)
    (is_comm : IsMulCommutative M) : IsMulCommutative N where
  is_comm.comm a b := by
    have ⟨a', ha'⟩ := is_surj a
    have ⟨b', hb'⟩ := is_surj b
    simp [← ha', ← hb', ← map_mul, mul_comm']

/-- The inverse of a bijective `MonoidHom` is a `MonoidHom`. -/
@[to_additive (attr := simps)
  /-- The inverse of a bijective `AddMonoidHom` is an `AddMonoidHom`. -/]
/-
**MonoidHom.inverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.inverse {A B : Type*} [Monoid A] [Monoid B] (f : A ->* B) (g : B
 -> A) (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : B ->* 
A
参数：f : A ->* B；g : B -> A；h₁ : Function.LeftInverse g f；h₂ : Function.RightInver
se g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MonoidHom.inverse {A B : Type*} [Monoid A] [Monoid B] (f : A →* B) (g : B → A)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : B →* A :=
  { (f : OneHom A B).inverse g h₁,
    (f : A →ₙ* B).inverse g h₁ h₂ with toFun := g }

section End

namespace Monoid

variable (M) [MulOne M]

/-- The monoid of endomorphisms. -/
@[to_additive /-- The monoid of endomorphisms. -/, to_additive_dont_translate]
/-
**Monoid.End** 是 Mathlib 中的一个定义，位于命名空间 `Monoid`。
形式化陈述：(M : Type u_4) → [MulOne M] → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoid of endomorphisms.
-/
protected def End := M →* M

namespace End

@[to_additive]
/-
**Monoid.End.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.End`。
形式化陈述：instFunLike : FunLike (Monoid.End M) M M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (Monoid.End M) M M := inferInstanceAs <| FunLike (M →* M) M M

@[to_additive (attr := ext)]
/-
**Monoid.End.ext** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.End`。
形式化陈述：ext {f g : Monoid.End M} (h : forall x : M, f x = g x) : f = g
参数：h : forall x : M, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : Monoid.End M} (h : ∀ x : M, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[to_additive]
/-
**Monoid.End.instMonoidHomClass** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.End`。
形式化陈述：instMonoidHomClass : MonoidHomClass (Monoid.End M) M M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidHomClass : MonoidHomClass (Monoid.End M) M M :=
  inferInstanceAs <| MonoidHomClass (M →* M) M M

@[to_additive instOne]
/-
**Monoid.End.instOne** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.End`。
形式化陈述：instOne : One (Monoid.End M) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One (Monoid.End M) where one := .id _
@[to_additive instMul]
/-
**Monoid.End.instMul** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.End`。
形式化陈述：instMul : Mul (Monoid.End M) where mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (Monoid.End M) where mul := .comp

@[to_additive instMonoid]
/-
**Monoid.End.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.End`。
形式化陈述：instMonoid : Monoid (Monoid.End M) where mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.comp_assoc`：MonoidHom.comp_assoc {Q : Type*} [MulOne M] [MulOn
e N] [MulOne P] [MulOne Q] (f : M ->* N) (g : N ->* P) (h : P ->* Q) : (h.comp g
).comp f =…
· 使用定理 `MonoidHom.id_comp`：MonoidHom.id_comp [MulOne M] [MulOne N] (f : M ->* N)
 : (MonoidHom.id N).comp f = f
· 使用定理 `MonoidHom.comp_id`：MonoidHom.comp_id [MulOne M] [MulOne N] (f : M ->* N)
 : f.comp (MonoidHom.id M) = f
-/
instance instMonoid : Monoid (Monoid.End M) where
  mul := MonoidHom.comp
  one := MonoidHom.id M
  mul_assoc _ _ _ := MonoidHom.comp_assoc _ _ _
  mul_one := MonoidHom.comp_id
  one_mul := MonoidHom.id_comp
  npow n f := (npowRec n f).copy f^[n] <| by induction n <;> simp [npowRec, *] <;> rfl
  npow_succ _ _ := DFunLike.coe_injective <| Function.iterate_succ _ _

@[to_additive]
/-
**Monoid.End.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.End`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Monoid.End M) := ⟨1⟩

@[to_additive (attr := simp, norm_cast) coe_pow]
/-
**Monoid.End.coe_pow** 是 Mathlib 中的一个引理，位于命名空间 `Monoid.End`。
形式化陈述：coe_pow (f : Monoid.End M) (n : Nat) : (↑(f ^ n) : M -> M) = f^[n]
参数：f : Monoid.End M；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_pow (f : Monoid.End M) (n : ℕ) : (↑(f ^ n) : M → M) = f^[n] := rfl

@[to_additive (attr := simp) coe_one]
/-
**Monoid.End.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.End`。
形式化陈述：coe_one : ((1 : Monoid.End M) : M -> M) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : Monoid.End M) : M → M) = id := rfl

@[to_additive (attr := simp) coe_mul]
/-
**Monoid.End.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.End`。
形式化陈述：coe_mul (f g) : ((f * g : Monoid.End M) : M -> M) = f ∘ g
参数：f g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (f g) : ((f * g : Monoid.End M) : M → M) = f ∘ g := rfl

end End

end Monoid

end End

/-- `1` is the homomorphism sending all elements to `1`. -/
@[to_additive /-- `0` is the homomorphism sending all elements to `0`. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`1` is the homomorphism sending all elements to `1`.
-/
instance [One M] [One N] : One (OneHom M N) := ⟨⟨fun _ => 1, rfl⟩⟩

/-- `1` is the multiplicative homomorphism sending all elements to `1`. -/
@[to_additive /-- `0` is the additive homomorphism sending all elements to `0` -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`1` is the multiplicative homomorphism sending all elements to `1`.
-/
instance [Mul M] [MulOneClass N] : One (M →ₙ* N) :=
  ⟨⟨fun _ => 1, fun _ _ => (one_mul 1).symm⟩⟩

/-- `1` is the monoid homomorphism sending all elements to `1`. -/
@[to_additive /-- `0` is the additive monoid homomorphism sending all elements to `0`. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`1` is the monoid homomorphism sending all elements to `1`.
-/
instance [MulOne M] [MulOneClass N] : One (M →* N) :=
  ⟨⟨⟨fun _ => 1, rfl⟩, fun _ _ => (one_mul 1).symm⟩⟩

@[to_additive (attr := simp)]
/-
**OneHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.one_apply [One M] [One N] (x : M) : (1 : OneHom M N) x = 1
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem OneHom.one_apply [One M] [One N] (x : M) : (1 : OneHom M N) x = 1 := rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.one_apply [MulOne M] [MulOneClass N] (x : M) : (1 : M ->* N) x =
 1
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidHom.one_apply [MulOne M] [MulOneClass N] (x : M) : (1 : M →* N) x = 1 := rfl

@[to_additive (attr := simp)]
/-
**OneHom.one_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.one_comp [One M] [One N] [One P] (f : OneHom M N) : (1 : OneHom N P
).comp f = 1
参数：f : OneHom M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem OneHom.one_comp [One M] [One N] [One P] (f : OneHom M N) :
    (1 : OneHom N P).comp f = 1 := rfl

@[to_additive (attr := simp)]
/-
**OneHom.comp_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.comp_one [One M] [One N] [One P] (f : OneHom N P) : f.comp (1 : One
Hom M N) = 1
参数：f : OneHom N P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneHom.ext`：OneHom.ext [One M] [One N] ⦃f g : OneHom M N⦄ (h : forall x,
 f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem OneHom.comp_one [One M] [One N] [One P] (f : OneHom N P) : f.comp (1 : OneHom M N) = 1 := by
  ext
  simp only [map_one, OneHom.coe_comp, Function.comp_apply, OneHom.one_apply]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [One M] [One N] : Inhabited (OneHom M N) := ⟨1⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul M] [MulOneClass N] : Inhabited (M →ₙ* N) := ⟨1⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulOne M] [MulOneClass N] : Inhabited (M →* N) := ⟨1⟩

namespace MonoidHom

@[to_additive (attr := simp)]
/-
**MonoidHom.one_comp** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：one_comp [MulOne M] [MulOne N] [MulOneClass P] (f : M ->* N) : (1 : N ->* 
P).comp f = 1
参数：f : M ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_comp [MulOne M] [MulOne N] [MulOneClass P] (f : M →* N) :
    (1 : N →* P).comp f = 1 := rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.comp_one** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：comp_one [MulOne M] [MulOneClass N] [MulOneClass P] (f : N ->* P) : f.comp
 (1 : M ->* N) = 1
参数：f : N ->* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_one [MulOne M] [MulOneClass N] [MulOneClass P] (f : N →* P) :
    f.comp (1 : M →* N) = 1 := by
  ext
  simp only [map_one, coe_comp, Function.comp_apply, one_apply]

/-- Group homomorphisms preserve inverse. -/
@[to_additive /-- Additive group homomorphisms preserve negation. -/]
/-
**MonoidHom.map_inv** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [inst_1 : DivisionMonoid 
β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
参数：f : α →* β；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹

--- 原说明 ---
Group homomorphisms preserve inverse.
-/
protected theorem map_inv [Group α] [DivisionMonoid β] (f : α →* β) (a : α) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f _

/-- Group homomorphisms preserve integer power. -/
@[to_additive (reorder := g n) /-- Additive group homomorphisms preserve integer scaling. -/]
/-
**MonoidHom.map_zpow** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [inst_1 : DivisionMonoid 
β] (f : α →* β) (g : α) (n : ℤ),   f (g ^ n) = f g ^ n
参数：f : α →* β；g : α；n : ℤ；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n

--- 原说明 ---
Group homomorphisms preserve integer power.
-/
protected theorem map_zpow [Group α] [DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ) :
    f (g ^ n) = f g ^ n := map_zpow f g n

/-- Group homomorphisms preserve division. -/
@[to_additive /-- Additive group homomorphisms preserve subtraction. -/]
/-
**MonoidHom.map_div** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [inst_1 : DivisionMonoid 
β] (f : α →* β) (g h : α),   f (g / h) = f g / f h
参数：f : α →* β；g h : α；g / h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b

--- 原说明 ---
Group homomorphisms preserve division.
-/
protected theorem map_div [Group α] [DivisionMonoid β] (f : α →* β) (g h : α) :
    f (g / h) = f g / f h := map_div f g h

/-- Group homomorphisms preserve division. -/
@[to_additive /-- Additive group homomorphisms preserve subtraction. -/]
/-
**MonoidHom.map_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [inst_1 : DivisionMonoid 
β] (f : α →* β) (g h : α),   f (g * h⁻¹) = f g * (f h)⁻¹
参数：f : α →* β；g h : α；g * h⁻¹；f h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Group homomorphisms preserve division.
-/
protected theorem map_mul_inv [Group α] [DivisionMonoid β] (f : α →* β) (g h : α) :
    f (g * h⁻¹) = f g * (f h)⁻¹ := by simp

end MonoidHom

@[to_additive (attr := simp)]
/-
**iterate_map_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterate_map_mul {M F : Type*} [Mul M] [FunLike F M M] [MulHomClass F M M] 
(f : F) (n : Nat) (x y : M) : f^[n] (x * y) = f^[n] x * f^[n] y
参数：f : F；n : Nat；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Semiconj₂.iterate`：∀ {α : Type u} {f : α → α} {op : α → α → α},
 Function.Semiconj₂ f op op → ∀ (n : ℕ), Function.Semiconj₂ f^[n] op op
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
lemma iterate_map_mul {M F : Type*} [Mul M] [FunLike F M M] [MulHomClass F M M]
    (f : F) (n : ℕ) (x y : M) :
    f^[n] (x * y) = f^[n] x * f^[n] y :=
  Function.Semiconj₂.iterate (map_mul f) n x y

@[to_additive (attr := simp)]
/-
**iterate_map_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterate_map_one {M F : Type*} [One M] [FunLike F M M] [OneHomClass F M M] 
(f : F) (n : Nat) : f^[n] 1 = 1
参数：f : F；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.iterate_fixed`：iterate_fixed {x} (h : f x = x) (n : Nat) : f^[n
] x = x
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
-/
lemma iterate_map_one {M F : Type*} [One M] [FunLike F M M] [OneHomClass F M M]
    (f : F) (n : ℕ) :
    f^[n] 1 = 1 :=
  iterate_fixed (map_one f) n

@[to_additive (attr := simp)]
/-
**iterate_map_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterate_map_inv {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F 
M M] (f : F) (n : Nat) (x : M) : f^[n] x⁻¹ = (f^[n] x)⁻¹
参数：f : F；n : Nat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Commute.iterate_left`：iterate_left (h : Commute f g) (n : Nat) 
: Commute f^[n] g
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
-/
lemma iterate_map_inv {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : ℕ) (x : M) :
    f^[n] x⁻¹ = (f^[n] x)⁻¹ :=
  Commute.iterate_left (map_inv f) n x

@[to_additive (attr := simp)]
/-
**iterate_map_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterate_map_div {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F 
M M] (f : F) (n : Nat) (x y : M) : f^[n] (x / y) = f^[n] x / f^[n] y
参数：f : F；n : Nat；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Semiconj₂.iterate`：∀ {α : Type u} {f : α → α} {op : α → α → α},
 Function.Semiconj₂ f op op → ∀ (n : ℕ), Function.Semiconj₂ f^[n] op op
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
-/
lemma iterate_map_div {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : ℕ) (x y : M) :
    f^[n] (x / y) = f^[n] x / f^[n] y :=
  Semiconj₂.iterate (map_div f) n x y

@[to_additive (attr := simp)]
/-
**iterate_map_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterate_map_pow {M F : Type*} [Monoid M] [FunLike F M M] [MonoidHomClass F
 M M] (f : F) (n : Nat) (x : M) (k : Nat) : f^[n] (x ^ k) = f^[n] x ^ k
参数：f : F；n : Nat；x : M；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Commute.iterate_left`：iterate_left (h : Commute f g) (n : Nat) 
: Commute f^[n] g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
-/
lemma iterate_map_pow {M F : Type*} [Monoid M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : ℕ) (x : M) (k : ℕ) :
    f^[n] (x ^ k) = f^[n] x ^ k :=
  Commute.iterate_left (map_pow f · k) n x

@[to_additive (attr := simp)]
/-
**iterate_map_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterate_map_zpow {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F
 M M] (f : F) (n : Nat) (x : M) (k : Int) : f^[n] (x ^ k) = f^[n] x ^ k
参数：f : F；n : Nat；x : M；k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Commute.iterate_left`：iterate_left (h : Commute f g) (n : Nat) 
: Commute f^[n] g
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
-/
lemma iterate_map_zpow {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : ℕ) (x : M) (k : ℤ) :
    f^[n] (x ^ k) = f^[n] x ^ k :=
  Commute.iterate_left (map_zpow f · k) n x
