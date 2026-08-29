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

Implicit `{}` brackets are often used instead of type class `[]` brackets. This is done when the
instances can be inferred because they are implicit arguments to the type `MonoidHom`. When they
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

/--
Definition of `ZeroHom` / `ZeroHom` 的定义

English:
structure ZeroHom
  parameters: (M : Type*) (N : Type*) [Zero M] [Zero N]
  axioms and operations (2):
    - toFun : M -> N
    - map_zero' : toFun 0 = 0

中文:
结构 保零态射
  参数: (M : 类型) (N : 类型) [零 M] [零 N]
  公理与运算 (2 个):
    - toFun : M -> N
    - map_zero' : toFun 0 = 0
-/
structure ZeroHom (M : Type*) (N : Type*) [Zero M] [Zero N] where
  /-- The underlying function -/
  protected toFun : M -> N
  /-- The proposition that the function preserves 0 -/
  protected map_zero' : toFun 0 = 0

/--
Definition of `ZeroHomClass` / `ZeroHomClass` 的定义

English:
class ZeroHomClass
  parameters: (F : Type*) (M N : outParam Type*) [Zero M] [Zero N] [FunLike F M N]
  axioms and operations (1):
    - map_zero : forall f : F, f 0 = 0

中文:
类 保零态射类
  参数: (F : 类型) (M N : outParam 类型) [零 M] [零 N] [函数状 F M N]
  公理与运算 (1 个):
    - map_zero : 对任意 f : F, f 0 = 0
-/
class ZeroHomClass (F : Type*) (M N : outParam Type*) [Zero M] [Zero N] [FunLike F M N] :
    Prop where
  /-- The proposition that the function preserves 0 -/
  map_zero : forall f : F, f 0 = 0

-- Instances and lemmas are defined below through `@[to_additive]`.
end Zero

section Add

/--
Definition of `AddHom` / `AddHom` 的定义

English:
structure AddHom
  parameters: (M : Type*) (N : Type*) [Add M] [Add N]
  axioms and operations (2):
    - toFun : M -> N
    - map_add' : forall x y, toFun (x + y) = toFun x + toFun y

中文:
结构 加法半群态射
  参数: (M : 类型) (N : 类型) [加法 M] [加法 N]
  公理与运算 (2 个):
    - toFun : M -> N
    - map_add' : 对任意 x y, toFun (x + y) = toFun x + toFun y
-/
structure AddHom (M : Type*) (N : Type*) [Add M] [Add N] where
  /-- The underlying function -/
  protected toFun : M -> N
  /-- The proposition that the function preserves addition -/
  protected map_add' : forall x y, toFun (x + y) = toFun x + toFun y

/-- `M →ₙ+ N` denotes the type of addition-preserving maps from `M` to `N`. -/
infixr:25 " ->ₙ+ " => AddHom

/--
Definition of `AddHomClass` / `AddHomClass` 的定义

English:
class AddHomClass
  parameters: (F : Type*) (M N : outParam Type*) [Add M] [Add N] [FunLike F M N]
  axioms and operations (1):
    - map_add : forall (f : F) (x y : M), f (x + y) = f x + f y

中文:
类 加法态射类
  参数: (F : 类型) (M N : outParam 类型) [加法 M] [加法 N] [函数状 F M N]
  公理与运算 (1 个):
    - map_add : 对任意 (f : F) (x y : M), f (x + y) = f x + f y
-/
class AddHomClass (F : Type*) (M N : outParam Type*) [Add M] [Add N] [FunLike F M N] : Prop where
  /-- The proposition that the function preserves addition -/
  map_add : forall (f : F) (x y : M), f (x + y) = f x + f y

-- Instances and lemmas are defined below through `@[to_additive]`.
end Add

section add_zero

/--
Definition of `AddMonoidHom` / `AddMonoidHom` 的定义

English:
structure AddMonoidHom
  parameters: (M : Type*) (N : Type*) [AddZero M] [AddZero N]
  extends: ZeroHom M N, AddHom M N
  (no additional axioms)

中文:
结构 加法幺半群态射
  参数: (M : 类型) (N : 类型) [加法零 M] [加法零 N]
  继承: 保零态射 M N, 加法半群态射 M N
  (无附加公理)
-/
structure AddMonoidHom (M : Type*) (N : Type*) [AddZero M] [AddZero N]
  extends ZeroHom M N, AddHom M N

attribute [nolint docBlame] AddMonoidHom.toAddHom
attribute [nolint docBlame] AddMonoidHom.toZeroHom

/-- `M →+ N` denotes the type of additive monoid homomorphisms from `M` to `N`. -/
infixr:25 " ->+ " => AddMonoidHom

/--
Definition of `AddMonoidHomClass` / `AddMonoidHomClass` 的定义

English:
class AddMonoidHomClass
  parameters: (F : Type*) (M N : outParam Type*)
  extends: AddHomClass F M N, ZeroHomClass F M N
  (no additional axioms)

中文:
类 加法幺半群态射类
  参数: (F : 类型) (M N : outParam 类型)
  继承: 加法态射类 F M N, 保零态射类 F M N
  (无附加公理)
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
/--
Definition of `OneHom` / `OneHom` 的定义

English:
structure OneHom
  parameters: (M : Type*) (N : Type*) [One M] [One N]
  axioms and operations (2):
    - toFun : M -> N
    - map_one' : toFun 1 = 1

中文:
结构 幺态射
  参数: (M : 类型) (N : 类型) [幺 M] [幺 N]
  公理与运算 (2 个):
    - toFun : M -> N
    - map_one' : toFun 1 = 1
-/
structure OneHom (M : Type*) (N : Type*) [One M] [One N] where
  /-- The underlying function -/
  protected toFun : M -> N
  /-- The proposition that the function preserves 1 -/
  protected map_one' : toFun 1 = 1

/-- `OneHomClass F M N` states that `F` is a type of one-preserving homomorphisms.
You should extend this typeclass when you extend `OneHom`.
-/
@[to_additive]
/--
Definition of `OneHomClass` / `OneHomClass` 的定义

English:
class OneHomClass
  parameters: (F : Type*) (M N : outParam Type*) [One M] [One N] [FunLike F M N]
  axioms and operations (1):
    - map_one : forall f : F, f 1 = 1

中文:
类 幺态射类
  参数: (F : 类型) (M N : outParam 类型) [幺 M] [幺 N] [函数状 F M N]
  公理与运算 (1 个):
    - map_one : 对任意 f : F, f 1 = 1
-/
class OneHomClass (F : Type*) (M N : outParam Type*) [One M] [One N] [FunLike F M N] : Prop where
  /-- The proposition that the function preserves 1 -/
  map_one : forall f : F, f 1 = 1

@[to_additive]
/--
Instance `OneHom.funLike` / 实例 `OneHom.funLike`

English:
instance OneHom.funLike
  signature: : FunLike (OneHom M N) M N where
  body: OneHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_additive]

中文:
实例 幺态射.funLike
  签名: : 函数状 (幺态射 M N) M N where
  定义体: OneHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_additive]

Depends on / 依赖: OneHom, OneHom.toFun
-/
instance OneHom.funLike : FunLike (OneHom M N) M N where
  coe := OneHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_additive]
/--
Instance `OneHom.oneHomClass` / 实例 `OneHom.oneHomClass`

English:
instance OneHom.oneHomClass
  signature: : OneHomClass (OneHom M N) M N where
  body: OneHom.map_one'

library_note «hom simp lemma priority»

中文:
实例 幺态射.oneHomClass
  签名: : 幺态射类 (幺态射 M N) M N where
  定义体: OneHom.map_one'

library_note «hom simp lemma priority»

Depends on / 依赖: OneHom, OneHom.map_one, map_one
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
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: [OneHomClass F M N] (f : F)
  statement: f 1 = 1
  proof: OneHomClass.map_one f

中文:
定理 map_one
  条件: [幺态射类 F M N] (f : F)
  结论: f 1 = 1
  证明: OneHomClass.map_one f

Depends on / 依赖: OneHomClass, OneHomClass.map_one, map_one
-/
theorem map_one [OneHomClass F M N] (f : F) : f 1 = 1 :=
  OneHomClass.map_one f

/--
lemma `map_comp_one` / 引理 `map_comp_one`

English:
lemma map_comp_one
  given: [OneHomClass F M N] (f : F)
  statement: f ∘ (1 : ι -> M) = 1
  proof: by simp

中文:
引理 map_comp_one
  条件: [幺态射类 F M N] (f : F)
  结论: f ∘ (1 : ι -> M) = 1
  证明: by simp
-/
@[to_additive] lemma map_comp_one [OneHomClass F M N] (f : F) : f ∘ (1 : ι -> M) = 1 := by simp

/-- In principle this could be an instance, but in practice it causes performance issues. -/
@[to_additive]
/--
theorem `Subsingleton.of_oneHomClass` / 定理 `Subsingleton.of_oneHomClass`

English:
theorem Subsingleton.of_oneHomClass
  given: [Subsingleton M] [OneHomClass F M N]
  proof: DFunLike.ext _ _ fun x => by simp [Subsingleton.elim x 1]

中文:
定理 子单例.of_oneHomClass
  条件: [子单例 M] [幺态射类 F M N]
  证明: DFunLike.ext _ _ fun x => by simp [Subsingleton.elim x 1]

Depends on / 依赖: DFunLike, DFunLike.ext, Subsingleton, Subsingleton.elim
-/
theorem Subsingleton.of_oneHomClass [Subsingleton M] [OneHomClass F M N] :
    Subsingleton F where
  allEq f g := DFunLike.ext _ _ fun x => by simp [Subsingleton.elim x 1]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: M] : Subsingleton (OneHom M N)
  body: .of_oneHomClass

@[to_additive]

中文:
实例 [子单例
  签名: M] : 子单例 (幺态射 M N)
  定义体: .of_oneHomClass

@[to_additive]
-/
@[to_additive] instance [Subsingleton M] : Subsingleton (OneHom M N) := .of_oneHomClass

@[to_additive]
/--
theorem `map_eq_one_iff` / 定理 `map_eq_one_iff`

English:
theorem map_eq_one_iff
  statement: [OneHomClass F M N] (f : F) (hf : Function.Injective f)
  proof: hf.eq_iff' (map_one f)

@[to_additive]

中文:
定理 map_eq_one_iff
  结论: [幺态射类 F M N] (f : F) (hf : 函数.单射 f)
  证明: hf.eq_iff' (map_one f)

@[to_additive]

Depends on / 依赖: eq_iff, hf.eq_iff, map_one
-/
theorem map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Function.Injective f)
    {x : M} :
    f x = 1 ↔ x = 1 := hf.eq_iff' (map_one f)

@[to_additive]
/--
theorem `map_ne_one_iff` / 定理 `map_ne_one_iff`

English:
theorem map_ne_one_iff
  statement: {R S F : Type*} [One R] [One S] [FunLike F R S] [OneHomClass F R S] (f : F)
  proof: (map_eq_one_iff f hf).not

@[to_additive]

中文:
定理 map_ne_one_iff
  结论: {R S F : 类型} [幺 R] [幺 S] [函数状 F R S] [幺态射类 F R S] (f : F)
  证明: (map_eq_one_iff f hf).not

@[to_additive]

Depends on / 依赖: map_eq_one_iff
-/
theorem map_ne_one_iff {R S F : Type*} [One R] [One S] [FunLike F R S] [OneHomClass F R S] (f : F)
    (hf : Function.Injective f) {x : R} : f x != 1 ↔ x != 1 := (map_eq_one_iff f hf).not

@[to_additive]
/--
theorem `ne_one_of_map` / 定理 `ne_one_of_map`

English:
theorem ne_one_of_map
  statement: {R S F : Type*} [One R] [One S] [FunLike F R S] [OneHomClass F R S]
  proof: ne_of_apply_ne f (by rwa [(map_one f)])

中文:
定理 ne_one_of_map
  结论: {R S F : 类型} [幺 R] [幺 S] [函数状 F R S] [幺态射类 F R S]
  证明: ne_of_apply_ne f (by rwa [(map_one f)])

Depends on / 依赖: map_one, ne_of_apply_ne
-/
theorem ne_one_of_map {R S F : Type*} [One R] [One S] [FunLike F R S] [OneHomClass F R S]
{f : F} {x : R} (hx : f x != 1) : x != 1 := ne_of_apply_ne f (by rwa [(map_one f)])

/-- Turn an element of a type `F` satisfying `OneHomClass F M N` into an actual
`OneHom`. This is declared as the default coercion from `F` to `OneHom M N`. -/
@[to_additive (attr := coe)
/-- Turn an element of a type `F` satisfying `ZeroHomClass F M N` into an actual
`ZeroHom`. This is declared as the default coercion from `F` to `ZeroHom M N`. -/]
/--
Definition of `OneHomClass.toOneHom` / `OneHomClass.toOneHom` 的定义

English:
definition OneHomClass.toOneHom
  signature: [OneHomClass F M N] (f : F)
  body: f
  map_one' := map_one f

中文:
定义 幺态射类.toOneHom
  签名: [幺态射类 F M N] (f : F)
  定义体: f
  map_one' := map_one f
-/
def OneHomClass.toOneHom [OneHomClass F M N] (f : F) : OneHom M N where
  toFun := f
  map_one' := map_one f

/-- Any type satisfying `OneHomClass` can be cast into `OneHom` via `OneHomClass.toOneHom`. -/
@[to_additive /-- Any type satisfying `ZeroHomClass` can be cast into `ZeroHom` via
`ZeroHomClass.toZeroHom`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OneHomClass
  signature: F M N] : CoeTC F (OneHom M N)
  body: ⟨OneHomClass.toOneHom⟩

@[to_additive (attr := simp)]

中文:
实例 [幺态射类
  签名: F M N] : CoeTC F (幺态射 M N)
  定义体: ⟨OneHomClass.toOneHom⟩

@[to_additive (attr := simp)]

Depends on / 依赖: OneHomClass, OneHomClass.toOneHom, toOneHom
-/
instance [OneHomClass F M N] : CoeTC F (OneHom M N) :=
  ⟨OneHomClass.toOneHom⟩

@[to_additive (attr := simp)]
/--
theorem `OneHom.coe_coe` / 定理 `OneHom.coe_coe`

English:
theorem OneHom.coe_coe
  given: [OneHomClass F M N] (f : F)
  proof: rfl

中文:
定理 幺态射.coe_coe
  条件: [幺态射类 F M N] (f : F)
  证明: rfl
-/
theorem OneHom.coe_coe [OneHomClass F M N] (f : F) :
    ((f : OneHom M N) : M -> N) = f := rfl

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
/--
Definition of `MulHom` / `MulHom` 的定义

English:
structure MulHom
  parameters: (M : Type*) (N : Type*) [Mul M] [Mul N]
  axioms and operations (2):
    - toFun : M -> N
    - map_mul' : forall x y, toFun (x * y) = toFun x * toFun y

中文:
结构 乘法半群态射
  参数: (M : 类型) (N : 类型) [乘法 M] [乘法 N]
  公理与运算 (2 个):
    - toFun : M -> N
    - map_mul' : 对任意 x y, toFun (x * y) = toFun x * toFun y
-/
structure MulHom (M : Type*) (N : Type*) [Mul M] [Mul N] where
  /-- The underlying function -/
  protected toFun : M -> N
  /-- The proposition that the function preserves multiplication -/
  protected map_mul' : forall x y, toFun (x * y) = toFun x * toFun y

/-- `M →ₙ* N` denotes the type of multiplication-preserving maps from `M` to `N`. -/
infixr:25 " ->ₙ* " => MulHom

/-- `MulHomClass F M N` states that `F` is a type of multiplication-preserving homomorphisms.

You should declare an instance of this typeclass when you extend `MulHom`.
-/
@[to_additive]
/--
Definition of `MulHomClass` / `MulHomClass` 的定义

English:
class MulHomClass
  parameters: (F : Type*) (M N : outParam Type*) [Mul M] [Mul N] [FunLike F M N]
  axioms and operations (1):
    - map_mul : forall (f : F) (x y : M), f (x * y) = f x * f y

中文:
类 乘法态射类
  参数: (F : 类型) (M N : outParam 类型) [乘法 M] [乘法 N] [函数状 F M N]
  公理与运算 (1 个):
    - map_mul : 对任意 (f : F) (x y : M), f (x * y) = f x * f y
-/
class MulHomClass (F : Type*) (M N : outParam Type*) [Mul M] [Mul N] [FunLike F M N] : Prop where
  /-- The proposition that the function preserves multiplication -/
  map_mul : forall (f : F) (x y : M), f (x * y) = f x * f y

@[to_additive]
/--
Instance `MulHom.funLike` / 实例 `MulHom.funLike`

English:
instance MulHom.funLike
  signature: : FunLike (M ->ₙ* N) M N where
  body: MulHom.toFun
  coe_injective f g h := by cases f; cases g; congr

中文:
实例 乘法半群态射.funLike
  签名: : 函数状 (M ->ₙ* N) M N where
  定义体: MulHom.toFun
  coe_injective f g h := by cases f; cases g; congr

Depends on / 依赖: MulHom, MulHom.toFun
-/
instance MulHom.funLike : FunLike (M ->ₙ* N) M N where
  coe := MulHom.toFun
  coe_injective f g h := by cases f; cases g; congr

/-- `MulHom` is a type of multiplication-preserving homomorphisms -/
@[to_additive /-- `AddHom` is a type of addition-preserving homomorphisms -/]
/--
Instance `MulHom.mulHomClass` / 实例 `MulHom.mulHomClass`

English:
instance MulHom.mulHomClass
  signature: : MulHomClass (M ->ₙ* N) M N where
  body: MulHom.map_mul'

中文:
实例 乘法半群态射.mulHomClass
  签名: : 乘法态射类 (M ->ₙ* N) M N where
  定义体: MulHom.map_mul'

Depends on / 依赖: MulHom, MulHom.map_mul, map_mul
-/
instance MulHom.mulHomClass : MulHomClass (M ->ₙ* N) M N where
  map_mul := MulHom.map_mul'

variable [FunLike F M N]

/-- See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid, grind =)]
/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: [MulHomClass F M N] (f : F) (x y : M)
  statement: f (x * y) = f x * f y
  proof: MulHomClass.map_mul f x y

@[to_additive (attr := simp)]

中文:
定理 map_mul
  条件: [乘法态射类 F M N] (f : F) (x y : M)
  结论: f (x * y) = f x * f y
  证明: MulHomClass.map_mul f x y

@[to_additive (attr := simp)]

Depends on / 依赖: MulHomClass, MulHomClass.map_mul, map_mul
-/
theorem map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x * f y :=
  MulHomClass.map_mul f x y

@[to_additive (attr := simp)]
/--
lemma `map_comp_mul` / 引理 `map_comp_mul`

English:
lemma map_comp_mul
  given: [MulHomClass F M N] (f : F) (g h : ι -> M)
  statement: f ∘ (g * h) = f ∘ g * f ∘ h
  proof: by
  ext; simp

中文:
引理 map_comp_mul
  条件: [乘法态射类 F M N] (f : F) (g h : ι -> M)
  结论: f ∘ (g * h) = f ∘ g * f ∘ h
  证明: by
  ext; simp
-/
lemma map_comp_mul [MulHomClass F M N] (f : F) (g h : ι -> M) : f ∘ (g * h) = f ∘ g * f ∘ h := by
  ext; simp

/-- Turn an element of a type `F` satisfying `MulHomClass F M N` into an actual
`MulHom`. This is declared as the default coercion from `F` to `M →ₙ* N`. -/
@[to_additive (attr := coe)
/-- Turn an element of a type `F` satisfying `AddHomClass F M N` into an actual
`AddHom`. This is declared as the default coercion from `F` to `M →ₙ+ N`. -/]
/--
Definition of `MulHomClass.toMulHom` / `MulHomClass.toMulHom` 的定义

English:
definition MulHomClass.toMulHom
  signature: [MulHomClass F M N] (f : F)
  body: f
  map_mul' := map_mul f

中文:
定义 乘法态射类.toMulHom
  签名: [乘法态射类 F M N] (f : F)
  定义体: f
  map_mul' := map_mul f
-/
def MulHomClass.toMulHom [MulHomClass F M N] (f : F) : M ->ₙ* N where
  toFun := f
  map_mul' := map_mul f

/-- Any type satisfying `MulHomClass` can be cast into `MulHom` via `MulHomClass.toMulHom`. -/
@[to_additive /-- Any type satisfying `AddHomClass` can be cast into `AddHom` via
`AddHomClass.toAddHom`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulHomClass
  signature: F M N] : CoeTC F (M ->ₙ* N)
  body: ⟨MulHomClass.toMulHom⟩

@[to_additive (attr := simp)]

中文:
实例 [乘法态射类
  签名: F M N] : CoeTC F (M ->ₙ* N)
  定义体: ⟨MulHomClass.toMulHom⟩

@[to_additive (attr := simp)]

Depends on / 依赖: MulHomClass, MulHomClass.toMulHom, toMulHom
-/
instance [MulHomClass F M N] : CoeTC F (M ->ₙ* N) :=
  ⟨MulHomClass.toMulHom⟩

@[to_additive (attr := simp)]
/--
theorem `MulHom.coe_coe` / 定理 `MulHom.coe_coe`

English:
theorem MulHom.coe_coe
  given: [MulHomClass F M N] (f : F)
  statement: ((f : MulHom M N) : M -> N) = f
  proof: rfl

中文:
定理 乘法半群态射.coe_coe
  条件: [乘法态射类 F M N] (f : F)
  结论: ((f : 乘法半群态射 M N) : M -> N) = f
  证明: rfl
-/
theorem MulHom.coe_coe [MulHomClass F M N] (f : F) : ((f : MulHom M N) : M -> N) = f := rfl

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
/--
Definition of `MonoidHom` / `MonoidHom` 的定义

English:
structure MonoidHom
  parameters: (M : Type*) (N : Type*) [MulOne M] [MulOne N]
  extends: OneHom M N, M ->ₙ* N
  (no additional axioms)

中文:
结构 幺半群态射
  参数: (M : 类型) (N : 类型) [MulOne M] [MulOne N]
  继承: 幺态射 M N, M ->ₙ* N
  (无附加公理)
-/
structure MonoidHom (M : Type*) (N : Type*) [MulOne M] [MulOne N]
  extends OneHom M N, M ->ₙ* N

attribute [nolint docBlame] MonoidHom.toMulHom
attribute [nolint docBlame] MonoidHom.toOneHom

/-- `M →* N` denotes the type of monoid homomorphisms from `M` to `N`. -/
infixr:25 " ->* " => MonoidHom

/-- `MonoidHomClass F M N` states that `F` is a type of `Monoid`-preserving homomorphisms.
You should also extend this typeclass when you extend `MonoidHom`. -/
@[to_additive]
/--
Definition of `MonoidHomClass` / `MonoidHomClass` 的定义

English:
class MonoidHomClass
  parameters: (F : Type*) (M N : outParam Type*) [MulOne M] [MulOne N]
  extends: MulHomClass F M N, OneHomClass F M N
  (no additional axioms)

中文:
类 幺半群态射类
  参数: (F : 类型) (M N : outParam 类型) [MulOne M] [MulOne N]
  继承: 乘法态射类 F M N, 幺态射类 F M N
  (无附加公理)
-/
class MonoidHomClass (F : Type*) (M N : outParam Type*) [MulOne M] [MulOne N]
  [FunLike F M N] : Prop
  extends MulHomClass F M N, OneHomClass F M N

@[to_additive]
/--
Instance `MonoidHom.instFunLike` / 实例 `MonoidHom.instFunLike`

English:
instance MonoidHom.instFunLike
  signature: : FunLike (M ->* N) M N where
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

@[to_additive]

中文:
实例 幺半群态射.instFunLike
  签名: : 函数状 (M ->* N) M N where
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

@[to_additive]

Depends on / 依赖: f.toFun
-/
instance MonoidHom.instFunLike : FunLike (M ->* N) M N where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

@[to_additive]
/--
Instance `MonoidHom.instMonoidHomClass` / 实例 `MonoidHom.instMonoidHomClass`

English:
instance MonoidHom.instMonoidHomClass
  signature: : MonoidHomClass (M ->* N) M N where
  body: MonoidHom.map_mul'
  map_one f := f.toOneHom.map_one'

中文:
实例 幺半群态射.instMonoidHomClass
  签名: : 幺半群态射类 (M ->* N) M N where
  定义体: MonoidHom.map_mul'
  map_one f := f.toOneHom.map_one'

Depends on / 依赖: MonoidHom, MonoidHom.map_mul, map_mul
-/
instance MonoidHom.instMonoidHomClass : MonoidHomClass (M ->* N) M N where
  map_mul := MonoidHom.map_mul'
  map_one f := f.toOneHom.map_one'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: M] : Subsingleton (M ->* N)
  body: .of_oneHomClass

中文:
实例 [子单例
  签名: M] : 子单例 (M ->* N)
  定义体: .of_oneHomClass
-/
@[to_additive] instance [Subsingleton M] : Subsingleton (M ->* N) := .of_oneHomClass

variable [FunLike F M N]

/-- Turn an element of a type `F` satisfying `MonoidHomClass F M N` into an actual
`MonoidHom`. This is declared as the default coercion from `F` to `M →* N`. -/
@[to_additive (attr := coe)
/-- Turn an element of a type `F` satisfying `AddMonoidHomClass F M N` into an
actual `MonoidHom`. This is declared as the default coercion from `F` to `M →+ N`. -/]
/--
Definition of `MonoidHomClass.toMonoidHom` / `MonoidHomClass.toMonoidHom` 的定义

English:
definition MonoidHomClass.toMonoidHom
  signature: [MonoidHomClass F M N] (f : F)
  body: { (f : M ->ₙ* N), (f : OneHom M N) with }

中文:
定义 幺半群态射类.toMonoidHom
  签名: [幺半群态射类 F M N] (f : F)
  定义体: { (f : M ->ₙ* N), (f : OneHom M N) with }

Depends on / 依赖: OneHom
-/
def MonoidHomClass.toMonoidHom [MonoidHomClass F M N] (f : F) : M ->* N :=
  { (f : M ->ₙ* N), (f : OneHom M N) with }

/-- Any type satisfying `MonoidHomClass` can be cast into `MonoidHom` via
`MonoidHomClass.toMonoidHom`. -/
@[to_additive /-- Any type satisfying `AddMonoidHomClass` can be cast into `AddMonoidHom` via
`AddMonoidHomClass.toAddMonoidHom`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonoidHomClass
  signature: F M N] : CoeTC F (M ->* N)
  body: ⟨MonoidHomClass.toMonoidHom⟩

@[to_additive (attr := simp)]

中文:
实例 [幺半群态射类
  签名: F M N] : CoeTC F (M ->* N)
  定义体: ⟨MonoidHomClass.toMonoidHom⟩

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidHomClass, MonoidHomClass.toMonoidHom, toMonoidHom
-/
instance [MonoidHomClass F M N] : CoeTC F (M ->* N) :=
  ⟨MonoidHomClass.toMonoidHom⟩

@[to_additive (attr := simp)]
/--
theorem `MonoidHom.coe_coe` / 定理 `MonoidHom.coe_coe`

English:
theorem MonoidHom.coe_coe
  given: [MonoidHomClass F M N] (f : F)
  statement: ((f : M ->* N) : M -> N) = f
  proof: rfl

@[to_additive]

中文:
定理 幺半群态射.coe_coe
  条件: [幺半群态射类 F M N] (f : F)
  结论: ((f : M ->* N) : M -> N) = f
  证明: rfl

@[to_additive]
-/
theorem MonoidHom.coe_coe [MonoidHomClass F M N] (f : F) : ((f : M ->* N) : M -> N) = f := rfl

@[to_additive]
/--
theorem `map_mul_eq_one` / 定理 `map_mul_eq_one`

English:
theorem map_mul_eq_one
  given: [MonoidHomClass F M N] (f : F) {a b : M} (h : a * b = 1)
  proof: by
  rw [← map_mul]; rw [h]; rw [map_one]

中文:
定理 map_mul_eq_one
  条件: [幺半群态射类 F M N] (f : F) {a b : M} (h : a * b = 1)
  证明: by
  rw [← map_mul]; rw [h]; rw [map_one]

Depends on / 依赖: map_mul, map_one
-/
theorem map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} (h : a * b = 1) :
    f a * f b = 1 := by
  rw [← map_mul]; rw [h]; rw [map_one]

variable [FunLike F G H]

@[to_additive]
/--
theorem `map_div'` / 定理 `map_div'`

English:
theorem map_div'
  statement: [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H]
  proof: by
  grind [div_eq_mul_inv]

@[to_additive]

中文:
定理 map_div'
  结论: [除逆幺半群 G] [除逆幺半群 H] [乘法态射类 F G H]
  证明: by
  grind [div_eq_mul_inv]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv
-/
theorem map_div' [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H]
    (f : F) (hf : forall a, f a⁻¹ = (f a)⁻¹) (a b : G) : f (a / b) = f a / f b := by
  grind [div_eq_mul_inv]

@[to_additive]
/--
lemma `map_comp_div'` / 引理 `map_comp_div'`

English:
lemma map_comp_div'
  statement: [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H] (f : F)
  proof: by
  ext; simp [map_div' f hf]

中文:
引理 map_comp_div'
  结论: [除逆幺半群 G] [除逆幺半群 H] [乘法态射类 F G H] (f : F)
  证明: by
  ext; simp [map_div' f hf]

Depends on / 依赖: map_div
-/
lemma map_comp_div' [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H] (f : F)
    (hf : forall a, f a⁻¹ = (f a)⁻¹) (g h : ι -> G) : f ∘ (g / h) = f ∘ g / f ∘ h := by
  ext; simp [map_div' f hf]

/-- Group homomorphisms preserve inverse.

See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid, grind =) /-- Additive group homomorphisms preserve negation. -/]
/--
theorem `map_inv` / 定理 `map_inv`

English:
theorem map_inv
  statement: [Group G] [DivisionMonoid H] [MonoidHomClass F G H]
  proof: eq_inv_of_mul_eq_one_left map_mul_eq_one f inv_mul_cancel _

@[to_additive (attr := simp)]

中文:
定理 map_inv
  结论: [群 G] [Division幺半群 H] [幺半群态射类 F G H]
  证明: eq_inv_of_mul_eq_one_left map_mul_eq_one f inv_mul_cancel _

@[to_additive (attr := simp)]

Depends on / 依赖: eq_inv_of_mul_eq_one_left, inv_mul_cancel, map_mul_eq_one
-/
theorem map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H]
    (f : F) (a : G) : f a⁻¹ = (f a)⁻¹ :=
eq_inv_of_mul_eq_one_left map_mul_eq_one f inv_mul_cancel _

@[to_additive (attr := simp)]
/--
lemma `map_comp_inv` / 引理 `map_comp_inv`

English:
lemma map_comp_inv
  given: [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g : ι -> G)
  proof: by ext; simp

中文:
引理 map_comp_inv
  条件: [群 G] [Division幺半群 H] [幺半群态射类 F G H] (f : F) (g : ι -> G)
  证明: by ext; simp
-/
lemma map_comp_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g : ι -> G) :
    f ∘ g⁻¹ = (f ∘ g)⁻¹ := by ext; simp

/-- Group homomorphisms preserve division. -/
@[to_additive /-- Additive group homomorphisms preserve subtraction. -/]
/--
theorem `map_mul_inv` / 定理 `map_mul_inv`

English:
theorem map_mul_inv
  given: [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (a b : G)
  proof: by rw [map_mul, map_inv]

@[to_additive]

中文:
定理 map_mul_inv
  条件: [群 G] [Division幺半群 H] [幺半群态射类 F G H] (f : F) (a b : G)
  证明: by rw [map_mul, map_inv]

@[to_additive]

Depends on / 依赖: map_inv, map_mul
-/
theorem map_mul_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (a b : G) :
    f (a * b⁻¹) = f a * (f b)⁻¹ := by rw [map_mul, map_inv]

@[to_additive]
/--
lemma `map_comp_mul_inv` / 引理 `map_comp_mul_inv`

English:
lemma map_comp_mul_inv
  given: [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g h : ι -> G)
  proof: by simp

中文:
引理 map_comp_mul_inv
  条件: [群 G] [Division幺半群 H] [幺半群态射类 F G H] (f : F) (g h : ι -> G)
  证明: by simp
-/
lemma map_comp_mul_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g h : ι -> G) :
    f ∘ (g * h⁻¹) = f ∘ g * (f ∘ h)⁻¹ := by simp

/-- Group homomorphisms preserve division.

See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid, grind =) /-- Additive group homomorphisms preserve subtraction. -/]
/--
theorem `map_div` / 定理 `map_div`

English:
theorem map_div
  given: [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F)
  proof: map_div' _ map_inv f

@[to_additive (attr := simp)]

中文:
定理 map_div
  条件: [群 G] [Division幺半群 H] [幺半群态射类 F G H] (f : F)
  证明: map_div' _ map_inv f

@[to_additive (attr := simp)]

Depends on / 依赖: map_div, map_inv
-/
theorem map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) :
forall a b, f (a / b) = f a / f b := map_div' _ map_inv f

@[to_additive (attr := simp)]
/--
lemma `map_comp_div` / 引理 `map_comp_div`

English:
lemma map_comp_div
  given: [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g h : ι -> G)
  proof: by ext; simp

中文:
引理 map_comp_div
  条件: [群 G] [Division幺半群 H] [幺半群态射类 F G H] (f : F) (g h : ι -> G)
  证明: by ext; simp
-/
lemma map_comp_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g h : ι -> G) :
    f ∘ (g / h) = f ∘ g / f ∘ h := by ext; simp

/-- See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid, grind =) (reorder := a n)]
/--
theorem `map_pow` / 定理 `map_pow`

English:
theorem map_pow
  given: [Monoid G] [Monoid H] [MonoidHomClass F G H] (f : F) (a : G)

中文:
定理 map_pow
  条件: [幺半群 G] [幺半群 H] [幺半群态射类 F G H] (f : F) (a : G)
-/
theorem map_pow [Monoid G] [Monoid H] [MonoidHomClass F G H] (f : F) (a : G) :
    forall n : Nat, f (a ^ n) = f a ^ n
  | 0 => by rw [pow_zero, pow_zero, map_one]
  | n + 1 => by rw [pow_succ, pow_succ, map_mul, map_pow f a n]

@[to_additive (attr := simp)]
/--
lemma `map_comp_pow` / 引理 `map_comp_pow`

English:
lemma map_comp_pow
  given: [Monoid G] [Monoid H] [MonoidHomClass F G H] (f : F) (g : ι -> G) (n : Nat)
  proof: by ext; simp

@[to_additive]

中文:
引理 map_comp_pow
  条件: [幺半群 G] [幺半群 H] [幺半群态射类 F G H] (f : F) (g : ι -> G) (n : 自然数)
  证明: by ext; simp

@[to_additive]
-/
lemma map_comp_pow [Monoid G] [Monoid H] [MonoidHomClass F G H] (f : F) (g : ι -> G) (n : Nat) :
    f ∘ (g ^ n) = f ∘ g ^ n := by ext; simp

@[to_additive]
/--
theorem `map_zpow'` / 定理 `map_zpow'`

English:
theorem map_zpow'
  statement: [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H]

中文:
定理 map_zpow'
  结论: [除逆幺半群 G] [除逆幺半群 H] [幺半群态射类 F G H]
-/
theorem map_zpow' [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H]
    (f : F) (hf : forall x : G, f x⁻¹ = (f x)⁻¹) (a : G) : forall n : Int, f (a ^ n) = f a ^ n
  | (n : Nat) => by rw [zpow_natCast, map_pow, zpow_natCast]
  | Int.negSucc n => by rw [zpow_negSucc, hf, map_pow, ← zpow_negSucc]

@[to_additive (attr := simp)]
/--
lemma `map_comp_zpow'` / 引理 `map_comp_zpow'`

English:
lemma map_comp_zpow'
  statement: [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H] (f : F)
  proof: by
  ext; simp [map_zpow' f hf]

中文:
引理 map_comp_zpow'
  结论: [除逆幺半群 G] [除逆幺半群 H] [幺半群态射类 F G H] (f : F)
  证明: by
  ext; simp [map_zpow' f hf]

Depends on / 依赖: map_zpow
-/
lemma map_comp_zpow' [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H] (f : F)
    (hf : forall x : G, f x⁻¹ = (f x)⁻¹) (g : ι -> G) (n : Int) : f ∘ (g ^ n) = f ∘ g ^ n := by
  ext; simp [map_zpow' f hf]

/-- Group homomorphisms preserve integer power.

See note [hom simp lemma priority] -/
@[to_additive (attr := simp mid, grind =) (reorder := g n)
/-- Additive group homomorphisms preserve integer scaling. -/]
/--
theorem `map_zpow` / 定理 `map_zpow`

English:
theorem map_zpow
  statement: [Group G] [DivisionMonoid H] [MonoidHomClass F G H]
  proof: map_zpow' f (map_inv f) g n

@[to_additive]

中文:
定理 map_zpow
  结论: [群 G] [Division幺半群 H] [幺半群态射类 F G H]
  证明: map_zpow' f (map_inv f) g n

@[to_additive]

Depends on / 依赖: map_inv, map_zpow
-/
theorem map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H]
    (f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n := map_zpow' f (map_inv f) g n

@[to_additive]
/--
lemma `map_comp_zpow` / 引理 `map_comp_zpow`

English:
lemma map_comp_zpow
  statement: [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g : ι -> G)
  proof: by simp

中文:
引理 map_comp_zpow
  结论: [群 G] [Division幺半群 H] [幺半群态射类 F G H] (f : F) (g : ι -> G)
  证明: by simp
-/
lemma map_comp_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g : ι -> G)
    (n : Int) : f ∘ (g ^ n) = f ∘ g ^ n := by simp

end mul_one

/-- If the codomain of an injective monoid homomorphism is torsion free,
then so is the domain. -/
@[to_additive /-- If the codomain of an injective additive monoid homomorphism is torsion free,
then so is the domain. -/]
/--
theorem `Function.Injective.isMulTorsionFree` / 定理 `Function.Injective.isMulTorsionFree`

English:
theorem Function.Injective.isMulTorsionFree
  statement: [Monoid M] [Monoid N] [IsMulTorsionFree N]
  proof: hf IsMulTorsionFree.pow_left_injective hn by
    simpa using congrArg f hxy

中文:
定理 函数.单射.isMulTorsionFree
  结论: [幺半群 M] [幺半群 N] [是MulTorsionFree N]
  证明: hf IsMulTorsionFree.pow_left_injective hn by
    simpa using congrArg f hxy

Depends on / 依赖: IsMulTorsionFree, IsMulTorsionFree.pow_left_injective, pow_left_injective
-/
theorem Function.Injective.isMulTorsionFree [Monoid M] [Monoid N] [IsMulTorsionFree N]
    (f : M ->* N) (hf : Function.Injective f) : IsMulTorsionFree M where
pow_left_injective n hn x y hxy := hf IsMulTorsionFree.pow_left_injective hn by
    simpa using congrArg f hxy

-- completely uninteresting lemmas about coercion to function, that all homs need
section Coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/

attribute [coe] MonoidHom.toOneHom
attribute [coe] AddMonoidHom.toZeroHom

/-- `MonoidHom` down-cast to a `OneHom`, forgetting the multiplicative property. -/
@[to_additive /-- `AddMonoidHom` down-cast to a `ZeroHom`, forgetting the additive property -/]
/--
Instance `MonoidHom.coeToOneHom` / 实例 `MonoidHom.coeToOneHom`

English:
instance MonoidHom.coeToOneHom
  signature: [MulOne M] [MulOne N]
  body: ⟨MonoidHom.toOneHom⟩

中文:
实例 幺半群态射.coeToOneHom
  签名: [MulOne M] [MulOne N]
  定义体: ⟨MonoidHom.toOneHom⟩

Depends on / 依赖: MonoidHom, MonoidHom.toOneHom, toOneHom
-/
instance MonoidHom.coeToOneHom [MulOne M] [MulOne N] : Coe (M ->* N) (OneHom M N) :=
  ⟨MonoidHom.toOneHom⟩

attribute [coe] MonoidHom.toMulHom
attribute [coe] AddMonoidHom.toAddHom

/-- `MonoidHom` down-cast to a `MulHom`, forgetting the 1-preserving property. -/
@[to_additive /-- `AddMonoidHom` down-cast to an `AddHom`, forgetting the 0-preserving property. -/]
/--
Instance `MonoidHom.coeToMulHom` / 实例 `MonoidHom.coeToMulHom`

English:
instance MonoidHom.coeToMulHom
  signature: [MulOne M] [MulOne N]
  body: ⟨MonoidHom.toMulHom⟩

中文:
实例 幺半群态射.coeToMulHom
  签名: [MulOne M] [MulOne N]
  定义体: ⟨MonoidHom.toMulHom⟩

Depends on / 依赖: MonoidHom, MonoidHom.toMulHom, toMulHom
-/
instance MonoidHom.coeToMulHom [MulOne M] [MulOne N] : Coe (M ->* N) (M ->ₙ* N) :=
  ⟨MonoidHom.toMulHom⟩

-- these must come after the coe_toFun definitions
initialize_simps_projections ZeroHom (toFun -> apply)
initialize_simps_projections AddHom (toFun -> apply)
initialize_simps_projections AddMonoidHom (toFun -> apply)
initialize_simps_projections OneHom (toFun -> apply)
initialize_simps_projections MulHom (toFun -> apply)
initialize_simps_projections MonoidHom (toFun -> apply)

@[to_additive (attr := simp)]
/--
theorem `OneHom.coe_mk` / 定理 `OneHom.coe_mk`

English:
theorem OneHom.coe_mk
  given: [One M] [One N] (f : M -> N) (h1)
  statement: (OneHom.mk f h1 : M -> N) = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 幺态射.coe_mk
  条件: [幺 M] [幺 N] (f : M -> N) (h1)
  结论: (幺态射.mk f h1 : M -> N) = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem OneHom.coe_mk [One M] [One N] (f : M -> N) (h1) : (OneHom.mk f h1 : M -> N) = f := rfl

@[to_additive (attr := simp)]
/--
theorem `OneHom.toFun_eq_coe` / 定理 `OneHom.toFun_eq_coe`

English:
theorem OneHom.toFun_eq_coe
  given: [One M] [One N] (f : OneHom M N)
  statement: f.toFun = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 幺态射.toFun_eq_coe
  条件: [幺 M] [幺 N] (f : 幺态射 M N)
  结论: f.toFun = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem OneHom.toFun_eq_coe [One M] [One N] (f : OneHom M N) : f.toFun = f := rfl

@[to_additive (attr := simp)]
/--
theorem `MulHom.coe_mk` / 定理 `MulHom.coe_mk`

English:
theorem MulHom.coe_mk
  given: [Mul M] [Mul N] (f : M -> N) (hmul)
  statement: (MulHom.mk f hmul : M -> N) = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 乘法半群态射.coe_mk
  条件: [乘法 M] [乘法 N] (f : M -> N) (hmul)
  结论: (乘法半群态射.mk f hmul : M -> N) = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem MulHom.coe_mk [Mul M] [Mul N] (f : M -> N) (hmul) : (MulHom.mk f hmul : M -> N) = f := rfl

@[to_additive (attr := simp)]
/--
theorem `MulHom.toFun_eq_coe` / 定理 `MulHom.toFun_eq_coe`

English:
theorem MulHom.toFun_eq_coe
  given: [Mul M] [Mul N] (f : M ->ₙ* N)
  statement: f.toFun = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 乘法半群态射.toFun_eq_coe
  条件: [乘法 M] [乘法 N] (f : M ->ₙ* N)
  结论: f.toFun = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem MulHom.toFun_eq_coe [Mul M] [Mul N] (f : M ->ₙ* N) : f.toFun = f := rfl

@[to_additive (attr := simp)]
/--
theorem `MonoidHom.coe_mk` / 定理 `MonoidHom.coe_mk`

English:
theorem MonoidHom.coe_mk
  given: [MulOne M] [MulOne N] (f hmul)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 幺半群态射.coe_mk
  条件: [MulOne M] [MulOne N] (f hmul)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem MonoidHom.coe_mk [MulOne M] [MulOne N] (f hmul) :
    (MonoidHom.mk f hmul : M -> N) = f := rfl

@[to_additive (attr := simp)]
/--
theorem `MonoidHom.toOneHom_coe` / 定理 `MonoidHom.toOneHom_coe`

English:
theorem MonoidHom.toOneHom_coe
  given: [MulOne M] [MulOne N] (f : M ->* N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 幺半群态射.toOneHom_coe
  条件: [MulOne M] [MulOne N] (f : M ->* N)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem MonoidHom.toOneHom_coe [MulOne M] [MulOne N] (f : M ->* N) :
    (f.toOneHom : M -> N) = f := rfl

@[to_additive (attr := simp)]
/--
theorem `MonoidHom.toMulHom_coe` / 定理 `MonoidHom.toMulHom_coe`

English:
theorem MonoidHom.toMulHom_coe
  given: [MulOne M] [MulOne N] (f : M ->* N)
  proof: rfl

@[to_additive]

中文:
定理 幺半群态射.toMulHom_coe
  条件: [MulOne M] [MulOne N] (f : M ->* N)
  证明: rfl

@[to_additive]
-/
theorem MonoidHom.toMulHom_coe [MulOne M] [MulOne N] (f : M ->* N) :
    f.toMulHom.toFun = f := rfl

@[to_additive]
/--
theorem `MonoidHom.toFun_eq_coe` / 定理 `MonoidHom.toFun_eq_coe`

English:
theorem MonoidHom.toFun_eq_coe
  given: [MulOne M] [MulOne N] (f : M ->* N)
  statement: f.toFun = f
  proof: rfl

@[to_additive (attr := ext)]

中文:
定理 幺半群态射.toFun_eq_coe
  条件: [MulOne M] [MulOne N] (f : M ->* N)
  结论: f.toFun = f
  证明: rfl

@[to_additive (attr := ext)]
-/
theorem MonoidHom.toFun_eq_coe [MulOne M] [MulOne N] (f : M ->* N) : f.toFun = f := rfl

@[to_additive (attr := ext)]
/--
theorem `OneHom.ext` / 定理 `OneHom.ext`

English:
theorem OneHom.ext
  given: [One M] [One N] ⦃f g
  statement: OneHom M N⦄ (h : forall x, f x = g x) : f = g
  proof: DFunLike.ext _ _ h

@[to_additive (attr := ext)]

中文:
定理 幺态射.ext
  条件: [幺 M] [幺 N] ⦃f g
  结论: 幺态射 M N⦄ (h : 对任意 x, f x = g x) : f = g
  证明: DFunLike.ext _ _ h

@[to_additive (attr := ext)]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem OneHom.ext [One M] [One N] ⦃f g : OneHom M N⦄ (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[to_additive (attr := ext)]
/--
theorem `MulHom.ext` / 定理 `MulHom.ext`

English:
theorem MulHom.ext
  given: [Mul M] [Mul N] ⦃f g
  statement: M ->ₙ* N⦄ (h : forall x, f x = g x) : f = g
  proof: DFunLike.ext _ _ h

@[to_additive (attr := ext)]

中文:
定理 乘法半群态射.ext
  条件: [乘法 M] [乘法 N] ⦃f g
  结论: M ->ₙ* N⦄ (h : 对任意 x, f x = g x) : f = g
  证明: DFunLike.ext _ _ h

@[to_additive (attr := ext)]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[to_additive (attr := ext)]
/--
theorem `MonoidHom.ext` / 定理 `MonoidHom.ext`

English:
theorem MonoidHom.ext
  given: [MulOne M] [MulOne N] ⦃f g
  statement: M ->* N⦄ (h : forall x, f x = g x) : f = g
  proof: DFunLike.ext _ _ h

中文:
定理 幺半群态射.ext
  条件: [MulOne M] [MulOne N] ⦃f g
  结论: M ->* N⦄ (h : 对任意 x, f x = g x) : f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

namespace MonoidHom

variable [Group G]
variable [MulOneClass M]

/-- Makes a group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Makes an additive group homomorphism from a proof that the map preserves addition. -/]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (f : M -> G) (map_mul : forall a b : M, f (a * b) = f a * f b)
  body: f
  map_mul' := map_mul
  map_one' := by rw [← mul_right_cancel_iff, ← map_mul _ 1, one_mul, one_mul]

中文:
定义 mk'
  签名: (f : M -> G) (map_mul : 对任意 a b : M, f (a * b) = f a * f b)
  定义体: f
  map_mul' := map_mul
  map_one' := by rw [← mul_right_cancel_iff, ← map_mul _ 1, one_mul, one_mul]
-/
def mk' (f : M -> G) (map_mul : forall a b : M, f (a * b) = f a * f b) : M ->* G where
  toFun := f
  map_mul' := map_mul
  map_one' := by rw [← mul_right_cancel_iff, ← map_mul _ 1, one_mul, one_mul]

end MonoidHom

@[to_additive (attr := simp)]
/--
theorem `OneHom.mk_coe` / 定理 `OneHom.mk_coe`

English:
theorem OneHom.mk_coe
  given: [One M] [One N] (f : OneHom M N) (h1)
  statement: OneHom.mk f h1 = f
  proof: OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]

中文:
定理 幺态射.mk_coe
  条件: [幺 M] [幺 N] (f : 幺态射 M N) (h1)
  结论: 幺态射.mk f h1 = f
  证明: OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: OneHom, OneHom.ext
-/
theorem OneHom.mk_coe [One M] [One N] (f : OneHom M N) (h1) : OneHom.mk f h1 = f :=
  OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/--
theorem `MulHom.mk_coe` / 定理 `MulHom.mk_coe`

English:
theorem MulHom.mk_coe
  given: [Mul M] [Mul N] (f : M ->ₙ* N) (hmul)
  statement: MulHom.mk f hmul = f
  proof: MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]

中文:
定理 乘法半群态射.mk_coe
  条件: [乘法 M] [乘法 N] (f : M ->ₙ* N) (hmul)
  结论: 乘法半群态射.mk f hmul = f
  证明: MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: MulHom, MulHom.ext
-/
theorem MulHom.mk_coe [Mul M] [Mul N] (f : M ->ₙ* N) (hmul) : MulHom.mk f hmul = f :=
  MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/--
theorem `MonoidHom.mk_coe` / 定理 `MonoidHom.mk_coe`

English:
theorem MonoidHom.mk_coe
  given: [MulOne M] [MulOne N] (f : M ->* N) (hmul)
  proof: MonoidHom.ext fun _ => rfl

中文:
定理 幺半群态射.mk_coe
  条件: [MulOne M] [MulOne N] (f : M ->* N) (hmul)
  证明: MonoidHom.ext fun _ => rfl

Depends on / 依赖: MonoidHom, MonoidHom.ext
-/
theorem MonoidHom.mk_coe [MulOne M] [MulOne N] (f : M ->* N) (hmul) :
    MonoidHom.mk f hmul = f := MonoidHom.ext fun _ => rfl

end Coes

/-- Copy of a `OneHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive
  /-- Copy of a `ZeroHom` with a new `toFun` equal to the old one. Useful to fix
  definitional equalities. -/]
/--
Definition of `OneHom.copy` / `OneHom.copy` 的定义

English:
definition OneHom.copy
  signature: [One M] [One N] (f : OneHom M N) (f' : M -> N) (h : f' = f)
  body: f'
  map_one' := h.symm ▸ f.map_one'

@[to_additive (attr := simp)]

中文:
定义 幺态射.copy
  签名: [幺 M] [幺 N] (f : 幺态射 M N) (f' : M -> N) (h : f' = f)
  定义体: f'
  map_one' := h.symm ▸ f.map_one'

@[to_additive (attr := simp)]
-/
protected def OneHom.copy [One M] [One N] (f : OneHom M N) (f' : M -> N) (h : f' = f) :
    OneHom M N where
  toFun := f'
  map_one' := h.symm ▸ f.map_one'

@[to_additive (attr := simp)]
/--
theorem `OneHom.coe_copy` / 定理 `OneHom.coe_copy`

English:
theorem OneHom.coe_copy
  given: {_ : One M} {_ : One N} (f : OneHom M N) (f' : M -> N) (h : f' = f)
  proof: rfl

@[to_additive]

中文:
定理 幺态射.coe_copy
  条件: {_ : 幺 M} {_ : 幺 N} (f : 幺态射 M N) (f' : M -> N) (h : f' = f)
  证明: rfl

@[to_additive]
-/
theorem OneHom.coe_copy {_ : One M} {_ : One N} (f : OneHom M N) (f' : M -> N) (h : f' = f) :
    (f.copy f' h) = f' :=
  rfl

@[to_additive]
/--
theorem `OneHom.coe_copy_eq` / 定理 `OneHom.coe_copy_eq`

English:
theorem OneHom.coe_copy_eq
  given: {_ : One M} {_ : One N} (f : OneHom M N) (f' : M -> N) (h : f' = f)
  proof: DFunLike.ext' h

中文:
定理 幺态射.coe_copy_eq
  条件: {_ : 幺 M} {_ : 幺 N} (f : 幺态射 M N) (f' : M -> N) (h : f' = f)
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem OneHom.coe_copy_eq {_ : One M} {_ : One N} (f : OneHom M N) (f' : M -> N) (h : f' = f) :
    f.copy f' h = f :=
  DFunLike.ext' h

/-- Copy of a `MulHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive
  /-- Copy of an `AddHom` with a new `toFun` equal to the old one. Useful to fix
  definitional equalities. -/]
/--
Definition of `MulHom.copy` / `MulHom.copy` 的定义

English:
definition MulHom.copy
  signature: [Mul M] [Mul N] (f : M ->ₙ* N) (f' : M -> N) (h : f' = f)
  body: f'
  map_mul' := h.symm ▸ f.map_mul'

@[to_additive (attr := simp)]

中文:
定义 乘法半群态射.copy
  签名: [乘法 M] [乘法 N] (f : M ->ₙ* N) (f' : M -> N) (h : f' = f)
  定义体: f'
  map_mul' := h.symm ▸ f.map_mul'

@[to_additive (attr := simp)]
-/
protected def MulHom.copy [Mul M] [Mul N] (f : M ->ₙ* N) (f' : M -> N) (h : f' = f) :
    M ->ₙ* N where
  toFun := f'
  map_mul' := h.symm ▸ f.map_mul'

@[to_additive (attr := simp)]
/--
theorem `MulHom.coe_copy` / 定理 `MulHom.coe_copy`

English:
theorem MulHom.coe_copy
  given: {_ : Mul M} {_ : Mul N} (f : M ->ₙ* N) (f' : M -> N) (h : f' = f)
  proof: rfl

@[to_additive]

中文:
定理 乘法半群态射.coe_copy
  条件: {_ : 乘法 M} {_ : 乘法 N} (f : M ->ₙ* N) (f' : M -> N) (h : f' = f)
  证明: rfl

@[to_additive]
-/
theorem MulHom.coe_copy {_ : Mul M} {_ : Mul N} (f : M ->ₙ* N) (f' : M -> N) (h : f' = f) :
    (f.copy f' h) = f' :=
  rfl

@[to_additive]
/--
theorem `MulHom.coe_copy_eq` / 定理 `MulHom.coe_copy_eq`

English:
theorem MulHom.coe_copy_eq
  given: {_ : Mul M} {_ : Mul N} (f : M ->ₙ* N) (f' : M -> N) (h : f' = f)
  proof: DFunLike.ext' h

中文:
定理 乘法半群态射.coe_copy_eq
  条件: {_ : 乘法 M} {_ : 乘法 N} (f : M ->ₙ* N) (f' : M -> N) (h : f' = f)
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem MulHom.coe_copy_eq {_ : Mul M} {_ : Mul N} (f : M ->ₙ* N) (f' : M -> N) (h : f' = f) :
    f.copy f' h = f :=
  DFunLike.ext' h

/-- Copy of a `MonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
@[to_additive
  /-- Copy of an `AddMonoidHom` with a new `toFun` equal to the old one. Useful to fix
  definitional equalities. -/]
/--
Definition of `MonoidHom.copy` / `MonoidHom.copy` 的定义

English:
definition MonoidHom.copy
  signature: [MulOne M] [MulOne N] (f : M ->* N) (f' : M -> N)
  body: { f.toOneHom.copy f' h, f.toMulHom.copy f' h with }

@[to_additive (attr := simp)]

中文:
定义 幺半群态射.copy
  签名: [MulOne M] [MulOne N] (f : M ->* N) (f' : M -> N)
  定义体: { f.toOneHom.copy f' h, f.toMulHom.copy f' h with }

@[to_additive (attr := simp)]
-/
protected def MonoidHom.copy [MulOne M] [MulOne N] (f : M ->* N) (f' : M -> N)
    (h : f' = f) : M ->* N :=
  { f.toOneHom.copy f' h, f.toMulHom.copy f' h with }

@[to_additive (attr := simp)]
/--
theorem `MonoidHom.coe_copy` / 定理 `MonoidHom.coe_copy`

English:
theorem MonoidHom.coe_copy
  statement: {_ : MulOne M} {_ : MulOne N} (f : M ->* N) (f' : M -> N)
  proof: rfl

@[to_additive]

中文:
定理 幺半群态射.coe_copy
  结论: {_ : MulOne M} {_ : MulOne N} (f : M ->* N) (f' : M -> N)
  证明: rfl

@[to_additive]
-/
theorem MonoidHom.coe_copy {_ : MulOne M} {_ : MulOne N} (f : M ->* N) (f' : M -> N)
    (h : f' = f) : (f.copy f' h) = f' :=
  rfl

@[to_additive]
/--
theorem `MonoidHom.copy_eq` / 定理 `MonoidHom.copy_eq`

English:
theorem MonoidHom.copy_eq
  statement: {_ : MulOne M} {_ : MulOne N} (f : M ->* N) (f' : M -> N)
  proof: DFunLike.ext' h

@[to_additive]

中文:
定理 幺半群态射.copy_eq
  结论: {_ : MulOne M} {_ : MulOne N} (f : M ->* N) (f' : M -> N)
  证明: DFunLike.ext' h

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem MonoidHom.copy_eq {_ : MulOne M} {_ : MulOne N} (f : M ->* N) (f' : M -> N)
    (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[to_additive]
/--
theorem `OneHom.map_one` / 定理 `OneHom.map_one`

English:
theorem OneHom.map_one
  given: [One M] [One N] (f : OneHom M N)
  statement: f 1 = 1
  proof: f.map_one'

中文:
定理 幺态射.map_one
  条件: [幺 M] [幺 N] (f : 幺态射 M N)
  结论: f 1 = 1
  证明: f.map_one'
-/
protected theorem OneHom.map_one [One M] [One N] (f : OneHom M N) : f 1 = 1 :=
  f.map_one'

/-- If `f` is a monoid homomorphism then `f 1 = 1`. -/
@[to_additive /-- If `f` is an additive monoid homomorphism then `f 0 = 0`. -/]
/--
theorem `MonoidHom.map_one` / 定理 `MonoidHom.map_one`

English:
theorem MonoidHom.map_one
  given: [MulOne M] [MulOne N] (f : M ->* N)
  statement: f 1 = 1
  proof: f.map_one'

@[to_additive]

中文:
定理 幺半群态射.map_one
  条件: [MulOne M] [MulOne N] (f : M ->* N)
  结论: f 1 = 1
  证明: f.map_one'

@[to_additive]
-/
protected theorem MonoidHom.map_one [MulOne M] [MulOne N] (f : M ->* N) : f 1 = 1 :=
  f.map_one'

@[to_additive]
/--
theorem `MulHom.map_mul` / 定理 `MulHom.map_mul`

English:
theorem MulHom.map_mul
  given: [Mul M] [Mul N] (f : M ->ₙ* N) (a b : M)
  statement: f (a * b) = f a * f b
  proof: f.map_mul' a b

中文:
定理 乘法半群态射.map_mul
  条件: [乘法 M] [乘法 N] (f : M ->ₙ* N) (a b : M)
  结论: f (a * b) = f a * f b
  证明: f.map_mul' a b
-/
protected theorem MulHom.map_mul [Mul M] [Mul N] (f : M ->ₙ* N) (a b : M) : f (a * b) = f a * f b :=
  f.map_mul' a b

/-- If `f` is a monoid homomorphism then `f (a * b) = f a * f b`. -/
@[to_additive /-- If `f` is an additive monoid homomorphism then `f (a + b) = f a + f b`. -/]
/--
theorem `MonoidHom.map_mul` / 定理 `MonoidHom.map_mul`

English:
theorem MonoidHom.map_mul
  given: [MulOne M] [MulOne N] (f : M ->* N) (a b : M)
  proof: f.map_mul' a b

中文:
定理 幺半群态射.map_mul
  条件: [MulOne M] [MulOne N] (f : M ->* N) (a b : M)
  证明: f.map_mul' a b

Depends on / 依赖: something_that_needs_inverses
-/
protected theorem MonoidHom.map_mul [MulOne M] [MulOne N] (f : M ->* N) (a b : M) :
    f (a * b) = f a * f b := f.map_mul' a b

namespace MonoidHom

variable [MulOne M] [MulOne N] [FunLike F M N] [MonoidHomClass F M N]

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a right inverse,
then `f x` has a right inverse too. For elements invertible on both sides see `IsUnit.map`. -/
@[to_additive
  /-- Given an AddMonoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has
  a right inverse, then `f x` has a right inverse too. -/]
/--
theorem `map_exists_right_inv` / 定理 `map_exists_right_inv`

English:
theorem map_exists_right_inv
  given: (f : F) {x : M} (hx : exists y, x * y = 1)
  statement: exists y, f x * y = 1
  proof: let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩

中文:
定理 map_存在_right_inv
  条件: (f : F) {x : M} (hx : 存在 y, x * y = 1)
  结论: 存在 y, f x * y = 1
  证明: let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩

Depends on / 依赖: map_mul_eq_one
-/
theorem map_exists_right_inv (f : F) {x : M} (hx : exists y, x * y = 1) : exists y, f x * y = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩

/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a left inverse,
then `f x` has a left inverse too. For elements invertible on both sides see `IsUnit.map`. -/
@[to_additive
  /-- Given an AddMonoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has
  a left inverse, then `f x` has a left inverse too. For elements invertible on both sides see
  `IsAddUnit.map`. -/]
/--
theorem `map_exists_left_inv` / 定理 `map_exists_left_inv`

English:
theorem map_exists_left_inv
  given: (f : F) {x : M} (hx : exists y, y * x = 1)
  statement: exists y, y * f x = 1
  proof: let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩

中文:
定理 map_存在_left_inv
  条件: (f : F) {x : M} (hx : 存在 y, y * x = 1)
  结论: 存在 y, y * f x = 1
  证明: let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩

Depends on / 依赖: map_mul_eq_one
-/
theorem map_exists_left_inv (f : F) {x : M} (hx : exists y, y * x = 1) : exists y, y * f x = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩

/--
theorem `_root_.IsDedekindFiniteMonoid.of_injective` / 定理 `_root_.IsDedekindFiniteMonoid.of_injective`

English:
theorem _root_.IsDedekindFiniteMonoid.of_injective
  statement: (f : F)
  proof: hf by simpa [mul_eq_one_comm] using congr_arg f eq

@[to_additive]

中文:
定理 _root_.是DedekindFinite幺半群.of_injective
  结论: (f : F)
  证明: hf by simpa [mul_eq_one_comm] using congr_arg f eq

@[to_additive]
-/
@[to_additive] theorem _root_.IsDedekindFiniteMonoid.of_injective (f : F)
    (hf : Function.Injective f) [IsDedekindFiniteMonoid N] : IsDedekindFiniteMonoid M where
mul_eq_one_symm eq := hf by simpa [mul_eq_one_comm] using congr_arg f eq

@[to_additive]
instance {M N : Type*} [Monoid M] [LeftCancelMonoid N] : MonoidHomClass (M ->ₙ* N) M N where
  map_mul := MulHom.map_mul'
  map_one f := by
    have h : f 1 * 1 = f 1 * f 1 := by simpa using f.map_mul' 1 1
    exact (mul_left_cancel h).symm

@[to_additive]
instance {M N : Type*} [Monoid M] [RightCancelMonoid N] : MonoidHomClass (M ->ₙ* N) M N where
  map_mul := MulHom.map_mul'
  map_one f := by
    have h : 1 * f 1 = f 1 * f 1 := by simpa using f.map_mul' 1 1
    exact (mul_right_cancel h).symm

@[to_additive]
instance {M N : Type*} [Monoid M] [CancelMonoid N] : MonoidHomClass (M ->ₙ* N) M N where

end MonoidHom

/-- The identity map from a type with 1 to itself. -/
@[to_additive (attr := simps, instance_reducible)
/-- The identity map from a type with zero to itself. -/]
/--
Definition of `OneHom.id` / `OneHom.id` 的定义

English:
definition OneHom.id
  signature: (M : Type*) [One M]
  body: x
  map_one' := rfl

中文:
定义 幺态射.id
  签名: (M : 类型) [幺 M]
  定义体: x
  map_one' := rfl
-/
def OneHom.id (M : Type*) [One M] : OneHom M M where
  toFun x := x
  map_one' := rfl

/-- The identity map from a type with multiplication to itself. -/
@[to_additive (attr := simps, instance_reducible)
/-- The identity map from a type with addition to itself. -/]
/--
Definition of `MulHom.id` / `MulHom.id` 的定义

English:
definition MulHom.id
  signature: (M : Type*) [Mul M]
  body: x
  map_mul' _ _ := rfl

中文:
定义 乘法半群态射.id
  签名: (M : 类型) [乘法 M]
  定义体: x
  map_mul' _ _ := rfl
-/
def MulHom.id (M : Type*) [Mul M] : M ->ₙ* M where
  toFun x := x
  map_mul' _ _ := rfl

/-- The identity map from a monoid to itself. -/
@[to_additive (attr := simps, instance_reducible)
/-- The identity map from an additive monoid to itself. -/]
/--
Definition of `MonoidHom.id` / `MonoidHom.id` 的定义

English:
definition MonoidHom.id
  signature: (M : Type*) [MulOne M]
  body: x
  map_one' := rfl
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]

中文:
定义 幺半群态射.id
  签名: (M : 类型) [MulOne M]
  定义体: x
  map_one' := rfl
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]
-/
def MonoidHom.id (M : Type*) [MulOne M] : M ->* M where
  toFun x := x
  map_one' := rfl
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]
/--
lemma `OneHom.coe_id` / 引理 `OneHom.coe_id`

English:
lemma OneHom.coe_id
  given: {M : Type*} [One M]
  statement: (OneHom.id M : M -> M) = _root_.id
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 幺态射.coe_id
  条件: {M : 类型} [幺 M]
  结论: (幺态射.id M : M -> M) = _root_.id
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma OneHom.coe_id {M : Type*} [One M] : (OneHom.id M : M -> M) = _root_.id := rfl

@[to_additive (attr := simp)]
/--
lemma `MulHom.coe_id` / 引理 `MulHom.coe_id`

English:
lemma MulHom.coe_id
  given: {M : Type*} [Mul M]
  statement: (MulHom.id M : M -> M) = _root_.id
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 乘法半群态射.coe_id
  条件: {M : 类型} [乘法 M]
  结论: (乘法半群态射.id M : M -> M) = _root_.id
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma MulHom.coe_id {M : Type*} [Mul M] : (MulHom.id M : M -> M) = _root_.id := rfl

@[to_additive (attr := simp)]
/--
lemma `MonoidHom.coe_id` / 引理 `MonoidHom.coe_id`

English:
lemma MonoidHom.coe_id
  given: {M : Type*} [MulOne M]
  statement: (MonoidHom.id M : M -> M) = _root_.id
  proof: rfl

中文:
引理 幺半群态射.coe_id
  条件: {M : 类型} [MulOne M]
  结论: (幺半群态射.id M : M -> M) = _root_.id
  证明: rfl
-/
lemma MonoidHom.coe_id {M : Type*} [MulOne M] : (MonoidHom.id M : M -> M) = _root_.id := rfl

/-- Composition of `OneHom`s as a `OneHom`. -/
@[to_additive (attr := instance_reducible) /-- Composition of `ZeroHom`s as a `ZeroHom`. -/]
/--
Definition of `OneHom.comp` / `OneHom.comp` 的定义

English:
definition OneHom.comp
  signature: [One M] [One N] [One P] (hnp : OneHom N P) (hmn : OneHom M N)
  body: hnp (hmn x)
  map_one' := by simp

中文:
定义 幺态射.comp
  签名: [幺 M] [幺 N] [幺 P] (hnp : 幺态射 N P) (hmn : 幺态射 M N)
  定义体: hnp (hmn x)
  map_one' := by simp
-/
def OneHom.comp [One M] [One N] [One P] (hnp : OneHom N P) (hmn : OneHom M N) : OneHom M P where
  toFun x := hnp (hmn x)
  map_one' := by simp

/-- Composition of `MulHom`s as a `MulHom`. -/
@[to_additive (attr := instance_reducible) /-- Composition of `AddHom`s as an `AddHom`. -/]
/--
Definition of `MulHom.comp` / `MulHom.comp` 的定义

English:
definition MulHom.comp
  signature: [Mul M] [Mul N] [Mul P] (hnp : N ->ₙ* P) (hmn : M ->ₙ* N)
  body: hnp (hmn x)
  map_mul' x y := by simp

中文:
定义 乘法半群态射.comp
  签名: [乘法 M] [乘法 N] [乘法 P] (hnp : N ->ₙ* P) (hmn : M ->ₙ* N)
  定义体: hnp (hmn x)
  map_mul' x y := by simp
-/
def MulHom.comp [Mul M] [Mul N] [Mul P] (hnp : N ->ₙ* P) (hmn : M ->ₙ* N) : M ->ₙ* P where
  toFun x := hnp (hmn x)
  map_mul' x y := by simp

/-- Composition of monoid morphisms as a monoid morphism. -/
@[to_additive (attr := instance_reducible)
/-- Composition of additive monoid morphisms as an additive monoid morphism. -/]
/--
Definition of `MonoidHom.comp` / `MonoidHom.comp` 的定义

English:
definition MonoidHom.comp
  signature: [MulOne M] [MulOne N] [MulOne P] (hnp : N ->* P) (hmn : M ->* N)
  body: hnp (hmn x)
  map_one' := by simp
  map_mul' := by simp

@[to_additive (attr := simp)]

中文:
定义 幺半群态射.comp
  签名: [MulOne M] [MulOne N] [MulOne P] (hnp : N ->* P) (hmn : M ->* N)
  定义体: hnp (hmn x)
  map_one' := by simp
  map_mul' := by simp

@[to_additive (attr := simp)]
-/
def MonoidHom.comp [MulOne M] [MulOne N] [MulOne P] (hnp : N ->* P) (hmn : M ->* N) :
    M ->* P where
  toFun x := hnp (hmn x)
  map_one' := by simp
  map_mul' := by simp

@[to_additive (attr := simp)]
/--
theorem `OneHom.coe_comp` / 定理 `OneHom.coe_comp`

English:
theorem OneHom.coe_comp
  given: [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 幺态射.coe_comp
  条件: [幺 M] [幺 N] [幺 P] (g : 幺态射 N P) (f : 幺态射 M N)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem OneHom.coe_comp [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) :
    ↑(g.comp f) = g ∘ f := rfl

@[to_additive (attr := simp)]
/--
theorem `MulHom.coe_comp` / 定理 `MulHom.coe_comp`

English:
theorem MulHom.coe_comp
  given: [Mul M] [Mul N] [Mul P] (g : N ->ₙ* P) (f : M ->ₙ* N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 乘法半群态射.coe_comp
  条件: [乘法 M] [乘法 N] [乘法 P] (g : N ->ₙ* P) (f : M ->ₙ* N)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem MulHom.coe_comp [Mul M] [Mul N] [Mul P] (g : N ->ₙ* P) (f : M ->ₙ* N) :
    ↑(g.comp f) = g ∘ f := rfl

@[to_additive (attr := simp)]
/--
theorem `MonoidHom.coe_comp` / 定理 `MonoidHom.coe_comp`

English:
theorem MonoidHom.coe_comp
  statement: [MulOne M] [MulOne N] [MulOne P]
  proof: rfl

@[to_additive]

中文:
定理 幺半群态射.coe_comp
  结论: [MulOne M] [MulOne N] [MulOne P]
  证明: rfl

@[to_additive]
-/
theorem MonoidHom.coe_comp [MulOne M] [MulOne N] [MulOne P]
    (g : N ->* P) (f : M ->* N) : ↑(g.comp f) = g ∘ f := rfl

@[to_additive]
/--
theorem `OneHom.comp_apply` / 定理 `OneHom.comp_apply`

English:
theorem OneHom.comp_apply
  given: [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) (x : M)
  proof: rfl

@[to_additive]

中文:
定理 幺态射.comp_apply
  条件: [幺 M] [幺 N] [幺 P] (g : 幺态射 N P) (f : 幺态射 M N) (x : M)
  证明: rfl

@[to_additive]
-/
theorem OneHom.comp_apply [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) (x : M) :
    g.comp f x = g (f x) := rfl

@[to_additive]
/--
theorem `MulHom.comp_apply` / 定理 `MulHom.comp_apply`

English:
theorem MulHom.comp_apply
  given: [Mul M] [Mul N] [Mul P] (g : N ->ₙ* P) (f : M ->ₙ* N) (x : M)
  proof: rfl

@[to_additive]

中文:
定理 乘法半群态射.comp_apply
  条件: [乘法 M] [乘法 N] [乘法 P] (g : N ->ₙ* P) (f : M ->ₙ* N) (x : M)
  证明: rfl

@[to_additive]
-/
theorem MulHom.comp_apply [Mul M] [Mul N] [Mul P] (g : N ->ₙ* P) (f : M ->ₙ* N) (x : M) :
    g.comp f x = g (f x) := rfl

@[to_additive]
/--
theorem `MonoidHom.comp_apply` / 定理 `MonoidHom.comp_apply`

English:
theorem MonoidHom.comp_apply
  statement: [MulOne M] [MulOne N] [MulOne P]
  proof: rfl

中文:
定理 幺半群态射.comp_apply
  结论: [MulOne M] [MulOne N] [MulOne P]
  证明: rfl
-/
theorem MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne P]
    (g : N ->* P) (f : M ->* N) (x : M) : g.comp f x = g (f x) := rfl

/-- Composition of monoid homomorphisms is associative. -/
@[to_additive /-- Composition of additive monoid homomorphisms is associative. -/]
/--
theorem `OneHom.comp_assoc` / 定理 `OneHom.comp_assoc`

English:
theorem OneHom.comp_assoc
  statement: {Q : Type*} [One M] [One N] [One P] [One Q]
  proof: rfl

@[to_additive]

中文:
定理 幺态射.comp_assoc
  结论: {Q : 类型} [幺 M] [幺 N] [幺 P] [幺 Q]
  证明: rfl

@[to_additive]
-/
theorem OneHom.comp_assoc {Q : Type*} [One M] [One N] [One P] [One Q]
    (f : OneHom M N) (g : OneHom N P) (h : OneHom P Q) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

@[to_additive]
/--
theorem `MulHom.comp_assoc` / 定理 `MulHom.comp_assoc`

English:
theorem MulHom.comp_assoc
  statement: {Q : Type*} [Mul M] [Mul N] [Mul P] [Mul Q]
  proof: rfl

@[to_additive]

中文:
定理 乘法半群态射.comp_assoc
  结论: {Q : 类型} [乘法 M] [乘法 N] [乘法 P] [乘法 Q]
  证明: rfl

@[to_additive]
-/
theorem MulHom.comp_assoc {Q : Type*} [Mul M] [Mul N] [Mul P] [Mul Q]
    (f : M ->ₙ* N) (g : N ->ₙ* P) (h : P ->ₙ* Q) : (h.comp g).comp f = h.comp (g.comp f) := rfl

@[to_additive]
/--
theorem `MonoidHom.comp_assoc` / 定理 `MonoidHom.comp_assoc`

English:
theorem MonoidHom.comp_assoc
  statement: {Q : Type*} [MulOne M] [MulOne N] [MulOne P]
  proof: rfl

@[to_additive]

中文:
定理 幺半群态射.comp_assoc
  结论: {Q : 类型} [MulOne M] [MulOne N] [MulOne P]
  证明: rfl

@[to_additive]
-/
theorem MonoidHom.comp_assoc {Q : Type*} [MulOne M] [MulOne N] [MulOne P]
    [MulOne Q] (f : M ->* N) (g : N ->* P) (h : P ->* Q) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

@[to_additive]
/--
theorem `OneHom.cancel_right` / 定理 `OneHom.cancel_right`

English:
theorem OneHom.cancel_right
  statement: [One M] [One N] [One P] {g₁ g₂ : OneHom N P} {f : OneHom M N}
  proof: ⟨fun h => OneHom.ext hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]

中文:
定理 幺态射.cancel_right
  结论: [幺 M] [幺 N] [幺 P] {g₁ g₂ : 幺态射 N P} {f : 幺态射 M N}
  证明: ⟨fun h => OneHom.ext hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, OneHom, OneHom.ext, ext_iff, hf.forall
-/
theorem OneHom.cancel_right [One M] [One N] [One P] {g₁ g₂ : OneHom N P} {f : OneHom M N}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => OneHom.ext hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]
/--
theorem `MulHom.cancel_right` / 定理 `MulHom.cancel_right`

English:
theorem MulHom.cancel_right
  statement: [Mul M] [Mul N] [Mul P] {g₁ g₂ : N ->ₙ* P} {f : M ->ₙ* N}
  proof: ⟨fun h => MulHom.ext hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]

中文:
定理 乘法半群态射.cancel_right
  结论: [乘法 M] [乘法 N] [乘法 P] {g₁ g₂ : N ->ₙ* P} {f : M ->ₙ* N}
  证明: ⟨fun h => MulHom.ext hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, MulHom, MulHom.ext, ext_iff, hf.forall
-/
theorem MulHom.cancel_right [Mul M] [Mul N] [Mul P] {g₁ g₂ : N ->ₙ* P} {f : M ->ₙ* N}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => MulHom.ext hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]
/--
theorem `MonoidHom.cancel_right` / 定理 `MonoidHom.cancel_right`

English:
theorem MonoidHom.cancel_right
  statement: [MulOne M] [MulOne N] [MulOne P]
  proof: ⟨fun h => MonoidHom.ext hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]

中文:
定理 幺半群态射.cancel_right
  结论: [MulOne M] [MulOne N] [MulOne P]
  证明: ⟨fun h => MonoidHom.ext hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, MonoidHom, MonoidHom.ext, ext_iff, hf.forall
-/
theorem MonoidHom.cancel_right [MulOne M] [MulOne N] [MulOne P]
    {g₁ g₂ : N ->* P} {f : M ->* N} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => MonoidHom.ext hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

@[to_additive]
/--
theorem `OneHom.cancel_left` / 定理 `OneHom.cancel_left`

English:
theorem OneHom.cancel_left
  statement: [One M] [One N] [One P] {g : OneHom N P} {f₁ f₂ : OneHom M N}
  proof: ⟨fun h => OneHom.ext fun x => hg by rw [← OneHom.comp_apply, h, OneHom.comp_apply],
    fun h => h ▸ rfl⟩

@[to_additive]

中文:
定理 幺态射.cancel_left
  结论: [幺 M] [幺 N] [幺 P] {g : 幺态射 N P} {f₁ f₂ : 幺态射 M N}
  证明: ⟨fun h => OneHom.ext fun x => hg by rw [← OneHom.comp_apply, h, OneHom.comp_apply],
    fun h => h ▸ rfl⟩

@[to_additive]

Depends on / 依赖: OneHom, OneHom.comp_apply, OneHom.ext, comp_apply
-/
theorem OneHom.cancel_left [One M] [One N] [One P] {g : OneHom N P} {f₁ f₂ : OneHom M N}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => OneHom.ext fun x => hg by rw [← OneHom.comp_apply, h, OneHom.comp_apply],
    fun h => h ▸ rfl⟩

@[to_additive]
/--
theorem `MulHom.cancel_left` / 定理 `MulHom.cancel_left`

English:
theorem MulHom.cancel_left
  statement: [Mul M] [Mul N] [Mul P] {g : N ->ₙ* P} {f₁ f₂ : M ->ₙ* N}
  proof: ⟨fun h => MulHom.ext fun x => hg by rw [← MulHom.comp_apply, h, MulHom.comp_apply],
    fun h => h ▸ rfl⟩

@[to_additive]

中文:
定理 乘法半群态射.cancel_left
  结论: [乘法 M] [乘法 N] [乘法 P] {g : N ->ₙ* P} {f₁ f₂ : M ->ₙ* N}
  证明: ⟨fun h => MulHom.ext fun x => hg by rw [← MulHom.comp_apply, h, MulHom.comp_apply],
    fun h => h ▸ rfl⟩

@[to_additive]

Depends on / 依赖: MulHom, MulHom.comp_apply, MulHom.ext, comp_apply
-/
theorem MulHom.cancel_left [Mul M] [Mul N] [Mul P] {g : N ->ₙ* P} {f₁ f₂ : M ->ₙ* N}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => MulHom.ext fun x => hg by rw [← MulHom.comp_apply, h, MulHom.comp_apply],
    fun h => h ▸ rfl⟩

@[to_additive]
/--
theorem `MonoidHom.cancel_left` / 定理 `MonoidHom.cancel_left`

English:
theorem MonoidHom.cancel_left
  statement: [MulOne M] [MulOne N] [MulOne P]
  proof: ⟨fun h => MonoidHom.ext fun x => hg by rw [← MonoidHom.comp_apply, h, MonoidHom.comp_apply],
    fun h => h ▸ rfl⟩

中文:
定理 幺半群态射.cancel_left
  结论: [MulOne M] [MulOne N] [MulOne P]
  证明: ⟨fun h => MonoidHom.ext fun x => hg by rw [← MonoidHom.comp_apply, h, MonoidHom.comp_apply],
    fun h => h ▸ rfl⟩

Depends on / 依赖: MonoidHom, MonoidHom.comp_apply, MonoidHom.ext, comp_apply
-/
theorem MonoidHom.cancel_left [MulOne M] [MulOne N] [MulOne P]
    {g : N ->* P} {f₁ f₂ : M ->* N} (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => MonoidHom.ext fun x => hg by rw [← MonoidHom.comp_apply, h, MonoidHom.comp_apply],
    fun h => h ▸ rfl⟩

section

@[to_additive]
/--
theorem `MonoidHom.toOneHom_injective` / 定理 `MonoidHom.toOneHom_injective`

English:
theorem MonoidHom.toOneHom_injective
  given: [MulOne M] [MulOne N]
  proof: Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

@[to_additive]

中文:
定理 幺半群态射.toOneHom_injective
  条件: [MulOne M] [MulOne N]
  证明: Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.of_comp, Injective, coe_injective, of_comp
-/
theorem MonoidHom.toOneHom_injective [MulOne M] [MulOne N] :
    Function.Injective (MonoidHom.toOneHom : (M ->* N) -> OneHom M N) :=
  Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

@[to_additive]
/--
theorem `MonoidHom.toMulHom_injective` / 定理 `MonoidHom.toMulHom_injective`

English:
theorem MonoidHom.toMulHom_injective
  given: [MulOne M] [MulOne N]
  proof: Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

中文:
定理 幺半群态射.toMulHom_injective
  条件: [MulOne M] [MulOne N]
  证明: Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.of_comp, Injective, coe_injective, of_comp
-/
theorem MonoidHom.toMulHom_injective [MulOne M] [MulOne N] :
    Function.Injective (MonoidHom.toMulHom : (M ->* N) -> M ->ₙ* N) :=
  Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

end

@[to_additive (attr := simp)]
/--
theorem `OneHom.comp_id` / 定理 `OneHom.comp_id`

English:
theorem OneHom.comp_id
  given: [One M] [One N] (f : OneHom M N)
  statement: f.comp (OneHom.id M) = f
  proof: OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]

中文:
定理 幺态射.comp_id
  条件: [幺 M] [幺 N] (f : 幺态射 M N)
  结论: f.comp (幺态射.id M) = f
  证明: OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: OneHom, OneHom.ext
-/
theorem OneHom.comp_id [One M] [One N] (f : OneHom M N) : f.comp (OneHom.id M) = f :=
  OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/--
theorem `MulHom.comp_id` / 定理 `MulHom.comp_id`

English:
theorem MulHom.comp_id
  given: [Mul M] [Mul N] (f : M ->ₙ* N)
  statement: f.comp (MulHom.id M) = f
  proof: MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]

中文:
定理 乘法半群态射.comp_id
  条件: [乘法 M] [乘法 N] (f : M ->ₙ* N)
  结论: f.comp (乘法半群态射.id M) = f
  证明: MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: MulHom, MulHom.ext
-/
theorem MulHom.comp_id [Mul M] [Mul N] (f : M ->ₙ* N) : f.comp (MulHom.id M) = f :=
  MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/--
theorem `MonoidHom.comp_id` / 定理 `MonoidHom.comp_id`

English:
theorem MonoidHom.comp_id
  given: [MulOne M] [MulOne N] (f : M ->* N)
  proof: MonoidHom.ext fun _ => rfl

@[to_additive (attr := simp)]

中文:
定理 幺半群态射.comp_id
  条件: [MulOne M] [MulOne N] (f : M ->* N)
  证明: MonoidHom.ext fun _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidHom, MonoidHom.ext
-/
theorem MonoidHom.comp_id [MulOne M] [MulOne N] (f : M ->* N) :
    f.comp (MonoidHom.id M) = f := MonoidHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/--
theorem `OneHom.id_comp` / 定理 `OneHom.id_comp`

English:
theorem OneHom.id_comp
  given: [One M] [One N] (f : OneHom M N)
  statement: (OneHom.id N).comp f = f
  proof: OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]

中文:
定理 幺态射.id_comp
  条件: [幺 M] [幺 N] (f : 幺态射 M N)
  结论: (幺态射.id N).comp f = f
  证明: OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: OneHom, OneHom.ext
-/
theorem OneHom.id_comp [One M] [One N] (f : OneHom M N) : (OneHom.id N).comp f = f :=
  OneHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/--
theorem `MulHom.id_comp` / 定理 `MulHom.id_comp`

English:
theorem MulHom.id_comp
  given: [Mul M] [Mul N] (f : M ->ₙ* N)
  statement: (MulHom.id N).comp f = f
  proof: MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]

中文:
定理 乘法半群态射.id_comp
  条件: [乘法 M] [乘法 N] (f : M ->ₙ* N)
  结论: (乘法半群态射.id N).comp f = f
  证明: MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: MulHom, MulHom.ext
-/
theorem MulHom.id_comp [Mul M] [Mul N] (f : M ->ₙ* N) : (MulHom.id N).comp f = f :=
  MulHom.ext fun _ => rfl

@[to_additive (attr := simp)]
/--
theorem `MonoidHom.id_comp` / 定理 `MonoidHom.id_comp`

English:
theorem MonoidHom.id_comp
  given: [MulOne M] [MulOne N] (f : M ->* N)
  proof: MonoidHom.ext fun _ => rfl

@[to_additive (reorder := a n)]

中文:
定理 幺半群态射.id_comp
  条件: [MulOne M] [MulOne N] (f : M ->* N)
  证明: MonoidHom.ext fun _ => rfl

@[to_additive (reorder := a n)]

Depends on / 依赖: MonoidHom, MonoidHom.ext
-/
theorem MonoidHom.id_comp [MulOne M] [MulOne N] (f : M ->* N) :
    (MonoidHom.id N).comp f = f := MonoidHom.ext fun _ => rfl

@[to_additive (reorder := a n)]
/--
theorem `MonoidHom.map_pow` / 定理 `MonoidHom.map_pow`

English:
theorem MonoidHom.map_pow
  given: [Monoid M] [Monoid N] (f : M ->* N) (a : M) (n : Nat)
  proof: map_pow f a n

@[to_additive (reorder := a n)]

中文:
定理 幺半群态射.map_pow
  条件: [幺半群 M] [幺半群 N] (f : M ->* N) (a : M) (n : 自然数)
  证明: map_pow f a n

@[to_additive (reorder := a n)]
-/
protected theorem MonoidHom.map_pow [Monoid M] [Monoid N] (f : M ->* N) (a : M) (n : Nat) :
    f (a ^ n) = f a ^ n := map_pow f a n

@[to_additive (reorder := a n)]
/--
theorem `MonoidHom.map_zpow'` / 定理 `MonoidHom.map_zpow'`

English:
theorem MonoidHom.map_zpow'
  statement: [DivInvMonoid M] [DivInvMonoid N] (f : M ->* N)
  proof: map_zpow' f hf a n

中文:
定理 幺半群态射.map_zpow'
  结论: [除逆幺半群 M] [除逆幺半群 N] (f : M ->* N)
  证明: map_zpow' f hf a n
-/
protected theorem MonoidHom.map_zpow' [DivInvMonoid M] [DivInvMonoid N] (f : M ->* N)
    (hf : forall x, f x⁻¹ = (f x)⁻¹) (a : M) (n : Int) :
    f (a ^ n) = f a ^ n := map_zpow' f hf a n

/-- Makes a `OneHom` inverse from the bijective inverse of a `OneHom` -/
@[to_additive (attr := simps)
/-- Make a `ZeroHom` inverse from the bijective inverse of a `ZeroHom` -/]
/--
Definition of `OneHom.inverse` / `OneHom.inverse` 的定义

English:
definition OneHom.inverse
  signature: [One M] [One N] (f : OneHom M N) (g : N -> M) (h₁ : Function.LeftInverse g f)
  body: { toFun := g,
    map_one' := by rw [← f.map_one, h₁] }

中文:
定义 幺态射.inverse
  签名: [幺 M] [幺 N] (f : 幺态射 M N) (g : N -> M) (h₁ : 函数.左逆 g f)
  定义体: { toFun := g,
    map_one' := by rw [← f.map_one, h₁] }

Depends on / 依赖: f.map_one, map_one
-/
def OneHom.inverse [One M] [One N] (f : OneHom M N) (g : N -> M) (h₁ : Function.LeftInverse g f) :
    OneHom N M :=
  { toFun := g,
    map_one' := by rw [← f.map_one, h₁] }

/-- Makes a multiplicative inverse from a bijection which preserves multiplication. -/
@[to_additive (attr := simps)
  /-- Makes an additive inverse from a bijection which preserves addition. -/]
/--
Definition of `MulHom.inverse` / `MulHom.inverse` 的定义

English:
definition MulHom.inverse
  signature: [Mul M] [Mul N] (f : M ->ₙ* N) (g : N -> M)
  body: g
  map_mul' x y :=
    calc
      g (x * y) = g (f (g x) * f (g y)) := by rw [h₂ x, h₂ y]
      _ = g (f (g x * g y)) := by rw [f.map_mul]
      _ = g x * g y := h₁ _

中文:
定义 乘法半群态射.inverse
  签名: [乘法 M] [乘法 N] (f : M ->ₙ* N) (g : N -> M)
  定义体: g
  map_mul' x y :=
    calc
      g (x * y) = g (f (g x) * f (g y)) := by rw [h₂ x, h₂ y]
      _ = g (f (g x * g y)) := by rw [f.map_mul]
      _ = g x * g y := h₁ _
-/
def MulHom.inverse [Mul M] [Mul N] (f : M ->ₙ* N) (g : N -> M)
    (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N ->ₙ* M where
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
/--
theorem `Function.Surjective.mul_comm` / 定理 `Function.Surjective.mul_comm`

English:
theorem Function.Surjective.mul_comm
  statement: [Mul M] [Mul N] {f : M ->ₙ* N} (is_surj : Function.Surjective f)
  proof: by
    have ⟨a', ha'⟩ := is_surj a
    have ⟨b', hb'⟩ := is_surj b
    simp [← ha', ← hb', ← map_mul, mul_comm']

中文:
定理 函数.满射.mul_comm
  结论: [乘法 M] [乘法 N] {f : M ->ₙ* N} (is_surj : 函数.满射 f)
  证明: by
    have ⟨a', ha'⟩ := is_surj a
    have ⟨b', hb'⟩ := is_surj b
    simp [← ha', ← hb', ← map_mul, mul_comm']

Depends on / 依赖: is_surj, map_mul, mul_comm
-/
theorem Function.Surjective.mul_comm [Mul M] [Mul N] {f : M ->ₙ* N} (is_surj : Function.Surjective f)
    (is_comm : IsMulCommutative M) : IsMulCommutative N where
  is_comm.comm a b := by
    have ⟨a', ha'⟩ := is_surj a
    have ⟨b', hb'⟩ := is_surj b
    simp [← ha', ← hb', ← map_mul, mul_comm']

/-- The inverse of a bijective `MonoidHom` is a `MonoidHom`. -/
@[to_additive (attr := simps)
  /-- The inverse of a bijective `AddMonoidHom` is an `AddMonoidHom`. -/]
/--
Definition of `MonoidHom.inverse` / `MonoidHom.inverse` 的定义

English:
definition MonoidHom.inverse
  signature: {A B : Type*} [Monoid A] [Monoid B] (f : A ->* B) (g : B -> A)
  body: { (f : OneHom A B).inverse g h₁,
    (f : A ->ₙ* B).inverse g h₁ h₂ with toFun := g }

中文:
定义 幺半群态射.inverse
  签名: {A B : 类型} [幺半群 A] [幺半群 B] (f : A ->* B) (g : B -> A)
  定义体: { (f : OneHom A B).inverse g h₁,
    (f : A ->ₙ* B).inverse g h₁ h₂ with toFun := g }

Depends on / 依赖: OneHom, inverse
-/
def MonoidHom.inverse {A B : Type*} [Monoid A] [Monoid B] (f : A ->* B) (g : B -> A)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : B ->* A :=
  { (f : OneHom A B).inverse g h₁,
    (f : A ->ₙ* B).inverse g h₁ h₂ with toFun := g }

section End

namespace Monoid

variable (M) [MulOne M]

/-- The monoid of endomorphisms. -/
@[to_additive /-- The monoid of endomorphisms. -/, to_additive_dont_translate]
/--
Definition of `End` / `End` 的定义

English:
definition End
  body: M ->* M

中文:
定义 End
  定义体: M ->* M
-/
protected def End := M ->* M

namespace End

@[to_additive]
/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (Monoid.End M) M M
  body: inferInstanceAs FunLike (M ->* M) M M

@[to_additive (attr := ext)]

中文:
实例 instFunLike
  签名: : 函数状 (幺半群.End M) M M
  定义体: inferInstanceAs FunLike (M ->* M) M M

@[to_additive (attr := ext)]

Depends on / 依赖: FunLike
-/
instance instFunLike : FunLike (Monoid.End M) M M := inferInstanceAs FunLike (M ->* M) M M

@[to_additive (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : Monoid.End M} (h : forall x : M, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

@[to_additive]

中文:
定理 ext
  条件: {f g : 幺半群.End M} (h : 对任意 x : M, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : Monoid.End M} (h : forall x : M, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[to_additive]
/--
Instance `instMonoidHomClass` / 实例 `instMonoidHomClass`

English:
instance instMonoidHomClass
  signature: : MonoidHomClass (Monoid.End M) M M
  body: inferInstanceAs MonoidHomClass (M ->* M) M M

@[to_additive instOne]

中文:
实例 instMonoidHomClass
  签名: : 幺半群态射类 (幺半群.End M) M M
  定义体: inferInstanceAs MonoidHomClass (M ->* M) M M

@[to_additive instOne]

Depends on / 依赖: MonoidHomClass
-/
instance instMonoidHomClass : MonoidHomClass (Monoid.End M) M M :=
inferInstanceAs MonoidHomClass (M ->* M) M M

@[to_additive instOne]
/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (Monoid.End M) where one
  body: .id _
@[to_additive instMul]

中文:
实例 instOne
  签名: : 幺 (幺半群.End M) where one
  定义体: .id _
@[to_additive instMul]
-/
instance instOne : One (Monoid.End M) where one := .id _
@[to_additive instMul]
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (Monoid.End M) where mul
  body: .comp

@[to_additive instMonoid]

中文:
实例 instMul
  签名: : 乘法 (幺半群.End M) where mul
  定义体: .comp

@[to_additive instMonoid]
-/
instance instMul : Mul (Monoid.End M) where mul := .comp

@[to_additive instMonoid]
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid (Monoid.End M) where
  body: MonoidHom.comp
  one := MonoidHom.id M
  mul_assoc _ _ _ := MonoidHom.comp_assoc _ _ _
  mul_one := MonoidHom.comp_id
  one_mul := MonoidHom.id_comp
npow n f := (npowRec n f).copy f^[n] by induction n <;> simp [npowRec, *] <;> rfl
npow_succ _ _ := DFunLike.coe_injective Function.iterate_succ _ _

@[to_additive]

中文:
实例 instMonoid
  签名: : 幺半群 (幺半群.End M) where
  定义体: MonoidHom.comp
  one := MonoidHom.id M
  mul_assoc _ _ _ := MonoidHom.comp_assoc _ _ _
  mul_one := MonoidHom.comp_id
  one_mul := MonoidHom.id_comp
npow n f := (npowRec n f).copy f^[n] by induction n <;> simp [npowRec, *] <;> rfl
npow_succ _ _ := DFunLike.coe_injective Function.iterate_succ _ _

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.comp
-/
instance instMonoid : Monoid (Monoid.End M) where
  mul := MonoidHom.comp
  one := MonoidHom.id M
  mul_assoc _ _ _ := MonoidHom.comp_assoc _ _ _
  mul_one := MonoidHom.comp_id
  one_mul := MonoidHom.id_comp
npow n f := (npowRec n f).copy f^[n] by induction n <;> simp [npowRec, *] <;> rfl
npow_succ _ _ := DFunLike.coe_injective Function.iterate_succ _ _

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Monoid.End M)
  body: ⟨1⟩

@[to_additive (attr := simp, norm_cast) coe_pow]

中文:
实例 :
  签名: 可居 (幺半群.End M)
  定义体: ⟨1⟩

@[to_additive (attr := simp, norm_cast) coe_pow]
-/
instance : Inhabited (Monoid.End M) := ⟨1⟩

@[to_additive (attr := simp, norm_cast) coe_pow]
/--
lemma `coe_pow` / 引理 `coe_pow`

English:
lemma coe_pow
  given: (f : Monoid.End M) (n : Nat)
  statement: (↑(f ^ n) : M -> M) = f^[n]
  proof: rfl

@[to_additive (attr := simp) coe_one]

中文:
引理 coe_pow
  条件: (f : 幺半群.End M) (n : 自然数)
  结论: (↑(f ^ n) : M -> M) = f^[n]
  证明: rfl

@[to_additive (attr := simp) coe_one]
-/
lemma coe_pow (f : Monoid.End M) (n : Nat) : (↑(f ^ n) : M -> M) = f^[n] := rfl

@[to_additive (attr := simp) coe_one]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : Monoid.End M) : M -> M) = id
  proof: rfl

@[to_additive (attr := simp) coe_mul]

中文:
定理 coe_one
  结论: ((1 : 幺半群.End M) : M -> M) = id
  证明: rfl

@[to_additive (attr := simp) coe_mul]
-/
theorem coe_one : ((1 : Monoid.End M) : M -> M) = id := rfl

@[to_additive (attr := simp) coe_mul]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g)
  statement: ((f * g : Monoid.End M) : M -> M) = f ∘ g
  proof: rfl

中文:
定理 coe_mul
  条件: (f g)
  结论: ((f * g : 幺半群.End M) : M -> M) = f ∘ g
  证明: rfl
-/
theorem coe_mul (f g) : ((f * g : Monoid.End M) : M -> M) = f ∘ g := rfl

end End

end Monoid

end End

/-- `1` is the homomorphism sending all elements to `1`. -/
@[to_additive /-- `0` is the homomorphism sending all elements to `0`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: M] [One N] : One (OneHom M N)
  body: ⟨⟨fun _ => 1, rfl⟩⟩

中文:
实例 [幺
  签名: M] [幺 N] : 幺 (幺态射 M N)
  定义体: ⟨⟨fun _ => 1, rfl⟩⟩
-/
instance [One M] [One N] : One (OneHom M N) := ⟨⟨fun _ => 1, rfl⟩⟩

/-- `1` is the multiplicative homomorphism sending all elements to `1`. -/
@[to_additive /-- `0` is the additive homomorphism sending all elements to `0` -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: M] [MulOneClass N] : One (M ->ₙ* N)
  body: ⟨⟨fun _ => 1, fun _ _ => (one_mul 1).symm⟩⟩

中文:
实例 [乘法
  签名: M] [MulOne类 N] : 幺 (M ->ₙ* N)
  定义体: ⟨⟨fun _ => 1, fun _ _ => (one_mul 1).symm⟩⟩

Depends on / 依赖: one_mul
-/
instance [Mul M] [MulOneClass N] : One (M ->ₙ* N) :=
  ⟨⟨fun _ => 1, fun _ _ => (one_mul 1).symm⟩⟩

/-- `1` is the monoid homomorphism sending all elements to `1`. -/
@[to_additive /-- `0` is the additive monoid homomorphism sending all elements to `0`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOne
  signature: M] [MulOneClass N] : One (M ->* N)
  body: ⟨⟨⟨fun _ => 1, rfl⟩, fun _ _ => (one_mul 1).symm⟩⟩

@[to_additive (attr := simp)]

中文:
实例 [MulOne
  签名: M] [MulOne类 N] : 幺 (M ->* N)
  定义体: ⟨⟨⟨fun _ => 1, rfl⟩, fun _ _ => (one_mul 1).symm⟩⟩

@[to_additive (attr := simp)]

Depends on / 依赖: one_mul
-/
instance [MulOne M] [MulOneClass N] : One (M ->* N) :=
  ⟨⟨⟨fun _ => 1, rfl⟩, fun _ _ => (one_mul 1).symm⟩⟩

@[to_additive (attr := simp)]
/--
theorem `OneHom.one_apply` / 定理 `OneHom.one_apply`

English:
theorem OneHom.one_apply
  given: [One M] [One N] (x : M)
  statement: (1 : OneHom M N) x = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 幺态射.one_apply
  条件: [幺 M] [幺 N] (x : M)
  结论: (1 : 幺态射 M N) x = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem OneHom.one_apply [One M] [One N] (x : M) : (1 : OneHom M N) x = 1 := rfl

@[to_additive (attr := simp)]
/--
theorem `MonoidHom.one_apply` / 定理 `MonoidHom.one_apply`

English:
theorem MonoidHom.one_apply
  given: [MulOne M] [MulOneClass N] (x : M)
  statement: (1 : M ->* N) x = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 幺半群态射.one_apply
  条件: [MulOne M] [MulOne类 N] (x : M)
  结论: (1 : M ->* N) x = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem MonoidHom.one_apply [MulOne M] [MulOneClass N] (x : M) : (1 : M ->* N) x = 1 := rfl

@[to_additive (attr := simp)]
/--
theorem `OneHom.one_comp` / 定理 `OneHom.one_comp`

English:
theorem OneHom.one_comp
  given: [One M] [One N] [One P] (f : OneHom M N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 幺态射.one_comp
  条件: [幺 M] [幺 N] [幺 P] (f : 幺态射 M N)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem OneHom.one_comp [One M] [One N] [One P] (f : OneHom M N) :
    (1 : OneHom N P).comp f = 1 := rfl

@[to_additive (attr := simp)]
/--
theorem `OneHom.comp_one` / 定理 `OneHom.comp_one`

English:
theorem OneHom.comp_one
  given: [One M] [One N] [One P] (f : OneHom N P)
  statement: f.comp (1 : OneHom M N) = 1
  proof: by
  ext
  simp only [map_one, OneHom.coe_comp, Function.comp_apply, OneHom.one_apply]

@[to_additive]

中文:
定理 幺态射.comp_one
  条件: [幺 M] [幺 N] [幺 P] (f : 幺态射 N P)
  结论: f.comp (1 : 幺态射 M N) = 1
  证明: by
  ext
  simp only [map_one, OneHom.coe_comp, Function.comp_apply, OneHom.one_apply]

@[to_additive]

Depends on / 依赖: Function, Function.comp_apply, OneHom, OneHom.coe_comp, OneHom.one_apply, coe_comp, comp_apply, map_one, one_apply
-/
theorem OneHom.comp_one [One M] [One N] [One P] (f : OneHom N P) : f.comp (1 : OneHom M N) = 1 := by
  ext
  simp only [map_one, OneHom.coe_comp, Function.comp_apply, OneHom.one_apply]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: M] [One N] : Inhabited (OneHom M N)
  body: ⟨1⟩

@[to_additive]

中文:
实例 [幺
  签名: M] [幺 N] : 可居 (幺态射 M N)
  定义体: ⟨1⟩

@[to_additive]
-/
instance [One M] [One N] : Inhabited (OneHom M N) := ⟨1⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: M] [MulOneClass N] : Inhabited (M ->ₙ* N)
  body: ⟨1⟩

@[to_additive]

中文:
实例 [乘法
  签名: M] [MulOne类 N] : 可居 (M ->ₙ* N)
  定义体: ⟨1⟩

@[to_additive]
-/
instance [Mul M] [MulOneClass N] : Inhabited (M ->ₙ* N) := ⟨1⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOne
  signature: M] [MulOneClass N] : Inhabited (M ->* N)
  body: ⟨1⟩

中文:
实例 [MulOne
  签名: M] [MulOne类 N] : 可居 (M ->* N)
  定义体: ⟨1⟩
-/
instance [MulOne M] [MulOneClass N] : Inhabited (M ->* N) := ⟨1⟩

namespace MonoidHom

@[to_additive (attr := simp)]
/--
theorem `one_comp` / 定理 `one_comp`

English:
theorem one_comp
  given: [MulOne M] [MulOne N] [MulOneClass P] (f : M ->* N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 one_comp
  条件: [MulOne M] [MulOne N] [MulOne类 P] (f : M ->* N)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem one_comp [MulOne M] [MulOne N] [MulOneClass P] (f : M ->* N) :
    (1 : N ->* P).comp f = 1 := rfl

@[to_additive (attr := simp)]
/--
theorem `comp_one` / 定理 `comp_one`

English:
theorem comp_one
  given: [MulOne M] [MulOneClass N] [MulOneClass P] (f : N ->* P)
  proof: by
  ext
  simp only [map_one, coe_comp, Function.comp_apply, one_apply]

中文:
定理 comp_one
  条件: [MulOne M] [MulOne类 N] [MulOne类 P] (f : N ->* P)
  证明: by
  ext
  simp only [map_one, coe_comp, Function.comp_apply, one_apply]

Depends on / 依赖: Function, Function.comp_apply, coe_comp, comp_apply, map_one, one_apply
-/
theorem comp_one [MulOne M] [MulOneClass N] [MulOneClass P] (f : N ->* P) :
    f.comp (1 : M ->* N) = 1 := by
  ext
  simp only [map_one, coe_comp, Function.comp_apply, one_apply]

/-- Group homomorphisms preserve inverse. -/
@[to_additive /-- Additive group homomorphisms preserve negation. -/]
/--
theorem `map_inv` / 定理 `map_inv`

English:
theorem map_inv
  given: [Group α] [DivisionMonoid β] (f : α ->* β) (a : α)
  statement: f a⁻¹ = (f a)⁻¹
  proof: map_inv f _

中文:
定理 map_inv
  条件: [群 α] [Division幺半群 β] (f : α ->* β) (a : α)
  结论: f a⁻¹ = (f a)⁻¹
  证明: map_inv f _
-/
protected theorem map_inv [Group α] [DivisionMonoid β] (f : α ->* β) (a : α) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f _

/-- Group homomorphisms preserve integer power. -/
@[to_additive (reorder := g n) /-- Additive group homomorphisms preserve integer scaling. -/]
/--
theorem `map_zpow` / 定理 `map_zpow`

English:
theorem map_zpow
  given: [Group α] [DivisionMonoid β] (f : α ->* β) (g : α) (n : Int)
  proof: map_zpow f g n

中文:
定理 map_zpow
  条件: [群 α] [Division幺半群 β] (f : α ->* β) (g : α) (n : 整数)
  证明: map_zpow f g n
-/
protected theorem map_zpow [Group α] [DivisionMonoid β] (f : α ->* β) (g : α) (n : Int) :
    f (g ^ n) = f g ^ n := map_zpow f g n

/-- Group homomorphisms preserve division. -/
@[to_additive /-- Additive group homomorphisms preserve subtraction. -/]
/--
theorem `map_div` / 定理 `map_div`

English:
theorem map_div
  given: [Group α] [DivisionMonoid β] (f : α ->* β) (g h : α)
  proof: map_div f g h

中文:
定理 map_div
  条件: [群 α] [Division幺半群 β] (f : α ->* β) (g h : α)
  证明: map_div f g h
-/
protected theorem map_div [Group α] [DivisionMonoid β] (f : α ->* β) (g h : α) :
    f (g / h) = f g / f h := map_div f g h

/-- Group homomorphisms preserve division. -/
@[to_additive /-- Additive group homomorphisms preserve subtraction. -/]
/--
theorem `map_mul_inv` / 定理 `map_mul_inv`

English:
theorem map_mul_inv
  given: [Group α] [DivisionMonoid β] (f : α ->* β) (g h : α)
  proof: by simp

中文:
定理 map_mul_inv
  条件: [群 α] [Division幺半群 β] (f : α ->* β) (g h : α)
  证明: by simp
-/
protected theorem map_mul_inv [Group α] [DivisionMonoid β] (f : α ->* β) (g h : α) :
    f (g * h⁻¹) = f g * (f h)⁻¹ := by simp

end MonoidHom

@[to_additive (attr := simp)]
/--
lemma `iterate_map_mul` / 引理 `iterate_map_mul`

English:
lemma iterate_map_mul
  statement: {M F : Type*} [Mul M] [FunLike F M M] [MulHomClass F M M]
  proof: Function.Semiconj₂.iterate (map_mul f) n x y

@[to_additive (attr := simp)]

中文:
引理 iterate_map_mul
  结论: {M F : 类型} [乘法 M] [函数状 F M M] [乘法态射类 F M M]
  证明: Function.Semiconj₂.iterate (map_mul f) n x y

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.Semiconj, iterate, map_mul
-/
lemma iterate_map_mul {M F : Type*} [Mul M] [FunLike F M M] [MulHomClass F M M]
    (f : F) (n : Nat) (x y : M) :
    f^[n] (x * y) = f^[n] x * f^[n] y :=
  Function.Semiconj₂.iterate (map_mul f) n x y

@[to_additive (attr := simp)]
/--
lemma `iterate_map_one` / 引理 `iterate_map_one`

English:
lemma iterate_map_one
  statement: {M F : Type*} [One M] [FunLike F M M] [OneHomClass F M M]
  proof: iterate_fixed (map_one f) n

@[to_additive (attr := simp)]

中文:
引理 iterate_map_one
  结论: {M F : 类型} [幺 M] [函数状 F M M] [幺态射类 F M M]
  证明: iterate_fixed (map_one f) n

@[to_additive (attr := simp)]

Depends on / 依赖: iterate_fixed, map_one
-/
lemma iterate_map_one {M F : Type*} [One M] [FunLike F M M] [OneHomClass F M M]
    (f : F) (n : Nat) :
    f^[n] 1 = 1 :=
  iterate_fixed (map_one f) n

@[to_additive (attr := simp)]
/--
lemma `iterate_map_inv` / 引理 `iterate_map_inv`

English:
lemma iterate_map_inv
  statement: {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
  proof: Commute.iterate_left (map_inv f) n x

@[to_additive (attr := simp)]

中文:
引理 iterate_map_inv
  结论: {M F : 类型} [群 M] [函数状 F M M] [幺半群态射类 F M M]
  证明: Commute.iterate_left (map_inv f) n x

@[to_additive (attr := simp)]

Depends on / 依赖: Commute, Commute.iterate_left, iterate_left, map_inv
-/
lemma iterate_map_inv {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : Nat) (x : M) :
    f^[n] x⁻¹ = (f^[n] x)⁻¹ :=
  Commute.iterate_left (map_inv f) n x

@[to_additive (attr := simp)]
/--
lemma `iterate_map_div` / 引理 `iterate_map_div`

English:
lemma iterate_map_div
  statement: {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
  proof: Semiconj₂.iterate (map_div f) n x y

@[to_additive (attr := simp)]

中文:
引理 iterate_map_div
  结论: {M F : 类型} [群 M] [函数状 F M M] [幺半群态射类 F M M]
  证明: Semiconj₂.iterate (map_div f) n x y

@[to_additive (attr := simp)]

Depends on / 依赖: iterate, map_div
-/
lemma iterate_map_div {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : Nat) (x y : M) :
    f^[n] (x / y) = f^[n] x / f^[n] y :=
  Semiconj₂.iterate (map_div f) n x y

@[to_additive (attr := simp)]
/--
lemma `iterate_map_pow` / 引理 `iterate_map_pow`

English:
lemma iterate_map_pow
  statement: {M F : Type*} [Monoid M] [FunLike F M M] [MonoidHomClass F M M]
  proof: Commute.iterate_left (map_pow f · k) n x

@[to_additive (attr := simp)]

中文:
引理 iterate_map_pow
  结论: {M F : 类型} [幺半群 M] [函数状 F M M] [幺半群态射类 F M M]
  证明: Commute.iterate_left (map_pow f · k) n x

@[to_additive (attr := simp)]

Depends on / 依赖: Commute, Commute.iterate_left, iterate_left, map_pow
-/
lemma iterate_map_pow {M F : Type*} [Monoid M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : Nat) (x : M) (k : Nat) :
    f^[n] (x ^ k) = f^[n] x ^ k :=
  Commute.iterate_left (map_pow f · k) n x

@[to_additive (attr := simp)]
/--
lemma `iterate_map_zpow` / 引理 `iterate_map_zpow`

English:
lemma iterate_map_zpow
  statement: {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
  proof: Commute.iterate_left (map_zpow f · k) n x

中文:
引理 iterate_map_zpow
  结论: {M F : 类型} [群 M] [函数状 F M M] [幺半群态射类 F M M]
  证明: Commute.iterate_left (map_zpow f · k) n x

Depends on / 依赖: Commute, Commute.iterate_left, iterate_left, map_zpow
-/
lemma iterate_map_zpow {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : Nat) (x : M) (k : Int) :
    f^[n] (x ^ k) = f^[n] x ^ k :=
  Commute.iterate_left (map_zpow f · k) n x
