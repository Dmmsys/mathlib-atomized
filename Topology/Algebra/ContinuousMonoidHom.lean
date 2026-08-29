/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Nailin Guan
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Topology.Algebra.Group.Defs

/-!

# Continuous Monoid Homs

This file defines the space of continuous homomorphisms between two topological groups.

## Main definitions

* `ContinuousMonoidHom A B`: The continuous homomorphisms `A →* B`.
* `ContinuousAddMonoidHom A B`: The continuous additive homomorphisms `A →+ B`.
-/

@[expose] public section

assert_not_exists ContinuousLinearMap
assert_not_exists ContinuousLinearEquiv

section

open Function Topology

variable (F A B C D E : Type*)
variable [Monoid A] [Monoid B] [Monoid C] [Monoid D]
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]

/--
Definition of `ContinuousAddMonoidHom` / `ContinuousAddMonoidHom` 的定义

English:
structure ContinuousAddMonoidHom
  parameters: (A B : Type*) [AddMonoid A] [AddMonoid B] [TopologicalSpace A]
  extends: A ->+ B, C(A, B)
  (no additional axioms)

中文:
结构 ContinuousAddMonoidHom
  参数: (A B : 类型) [AddMonoid A] [AddMonoid B] [TopologicalSpace A]
  继承: A ->+ B, C(A, B)
  (无附加公理)
-/
structure ContinuousAddMonoidHom (A B : Type*) [AddMonoid A] [AddMonoid B] [TopologicalSpace A]
  [TopologicalSpace B] extends A ->+ B, C(A, B)

/-- The type of continuous monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousMonoidHom A B)`,
you should parametrize
over `(F : Type*) [FunLike F A B] [ContinuousMapClass F A B] [MonoidHomClass F A B] (f : F)`.

When you extend this structure,
make sure to extend `ContinuousMapClass` and/or `MonoidHomClass`, if needed. -/
@[to_additive]
/--
Definition of `ContinuousMonoidHom` / `ContinuousMonoidHom` 的定义

English:
structure ContinuousMonoidHom
  parameters: extends A ->* B, C(A, B)
  extends: A ->* B, C(A, B)
  (no additional axioms)

中文:
结构 ContinuousMonoidHom
  参数: extends A ->* B, C(A, B)
  继承: A ->* B, C(A, B)
  (无附加公理)
-/
structure ContinuousMonoidHom extends A ->* B, C(A, B)

/-- Reinterpret a `ContinuousMonoidHom` as a `MonoidHom`. -/
add_decl_doc ContinuousMonoidHom.toMonoidHom

/-- Reinterpret a `ContinuousAddMonoidHom` as an `AddMonoidHom`. -/
add_decl_doc ContinuousAddMonoidHom.toAddMonoidHom

/-- Reinterpret a `ContinuousMonoidHom` as a `ContinuousMap`. -/
add_decl_doc ContinuousMonoidHom.toContinuousMap

/-- Reinterpret a `ContinuousAddMonoidHom` as a `ContinuousMap`. -/
add_decl_doc ContinuousAddMonoidHom.toContinuousMap

namespace ContinuousMonoidHom

/-- The type of continuous monoid homomorphisms from `A` to `B`.-/
infixr:25 " ->ₜ+ " => ContinuousAddMonoidHom
/-- The type of continuous monoid homomorphisms from `A` to `B`.-/
infixr:25 " ->ₜ* " => ContinuousMonoidHom

variable {A B C D E}

@[to_additive]
/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (A ->ₜ* B) A B where
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

@[to_additive]

中文:
实例 instFunLike
  签名: : FunLike (A ->ₜ* B) A B where
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

@[to_additive]

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (A ->ₜ* B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

@[to_additive]
/--
Instance `instMonoidHomClass` / 实例 `instMonoidHomClass`

English:
instance instMonoidHomClass
  signature: : MonoidHomClass (A ->ₜ* B) A B where
  body: f.map_mul'
  map_one f := f.map_one'

@[to_additive]

中文:
实例 instMonoidHomClass
  签名: : MonoidHomClass (A ->ₜ* B) A B where
  定义体: f.map_mul'
  map_one f := f.map_one'

@[to_additive]

Depends on / 依赖: f.map_mul, map_mul
-/
instance instMonoidHomClass : MonoidHomClass (A ->ₜ* B) A B where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

@[to_additive]
/--
Instance `instContinuousMapClass` / 实例 `instContinuousMapClass`

English:
instance instContinuousMapClass
  signature: : ContinuousMapClass (A ->ₜ* B) A B where
  body: f.continuous_toFun

@[to_additive (attr := simp)]

中文:
实例 instContinuousMapClass
  签名: : ContinuousMapClass (A ->ₜ* B) A B where
  定义体: f.continuous_toFun

@[to_additive (attr := simp)]

Depends on / 依赖: continuous_toFun, f.continuous_toFun
-/
instance instContinuousMapClass : ContinuousMapClass (A ->ₜ* B) A B where
  map_continuous f := f.continuous_toFun

@[to_additive (attr := simp)]
/--
lemma `coe_toMonoidHom` / 引理 `coe_toMonoidHom`

English:
lemma coe_toMonoidHom
  given: (f : A ->ₜ* B)
  statement: f.toMonoidHom = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coe_toMonoidHom
  条件: (f : A ->ₜ* B)
  结论: f.toMonoidHom = f
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coe_toMonoidHom (f : A ->ₜ* B) : f.toMonoidHom = f := rfl

@[to_additive (attr := simp)]
/--
lemma `coe_toContinuousMap` / 引理 `coe_toContinuousMap`

English:
lemma coe_toContinuousMap
  given: (f : A ->ₜ* B)
  statement: f.toContinuousMap = f
  proof: rfl

中文:
引理 coe_toContinuousMap
  条件: (f : A ->ₜ* B)
  结论: f.toContinuousMap = f
  证明: rfl
-/
lemma coe_toContinuousMap (f : A ->ₜ* B) : f.toContinuousMap = f := rfl

section

variable {F : Type*} [FunLike F A B]

/-- Turn an element of a type `F` satisfying `MonoidHomClass F A B` and `ContinuousMapClass F A B`
into a `ContinuousMonoidHom`. This is declared as the default coercion from `F` to
`(A →ₜ* B)`. -/
@[to_additive (attr := coe) /-- Turn an element of a type `F` satisfying
`AddMonoidHomClass F A B` and `ContinuousMapClass F A B` into a `ContinuousAddMonoidHom`.
This is declared as the default coercion from `F` to `ContinuousAddMonoidHom A B`. -/]
/--
Definition of `toContinuousMonoidHom` / `toContinuousMonoidHom` 的定义

English:
definition toContinuousMonoidHom
  signature: [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F)
  body: { MonoidHomClass.toMonoidHom f with
    continuous_toFun := by dsimp; fun_prop }

中文:
定义 toContinuousMonoidHom
  签名: [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F)
  定义体: { MonoidHomClass.toMonoidHom f with
    continuous_toFun := by dsimp; fun_prop }

Depends on / 依赖: MonoidHomClass, MonoidHomClass.toMonoidHom, continuous_toFun, fun_prop, toMonoidHom
-/
def toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F) : A ->ₜ* B :=
  { MonoidHomClass.toMonoidHom f with
    continuous_toFun := by dsimp; fun_prop }

/-- Any type satisfying `MonoidHomClass` and `ContinuousMapClass` can be cast into
`ContinuousMonoidHom` via `ContinuousMonoidHom.toContinuousMonoidHom`. -/
@[to_additive /-- Any type satisfying `AddMonoidHomClass` and `ContinuousMapClass` can be cast into
`ContinuousAddMonoidHom` via `ContinuousAddMonoidHom.toContinuousAddMonoidHom`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonoidHomClass
  signature: F A B] [ContinuousMapClass F A B] : CoeOut F (A ->ₜ* B)
  body: ⟨ContinuousMonoidHom.toContinuousMonoidHom⟩

@[to_additive (attr := simp)]

中文:
实例 [MonoidHomClass
  签名: F A B] [ContinuousMapClass F A B] : CoeOut F (A ->ₜ* B)
  定义体: ⟨ContinuousMonoidHom.toContinuousMonoidHom⟩

@[to_additive (attr := simp)]

Depends on / 依赖: ContinuousMonoidHom, ContinuousMonoidHom.toContinuousMonoidHom, toContinuousMonoidHom
-/
instance [MonoidHomClass F A B] [ContinuousMapClass F A B] : CoeOut F (A ->ₜ* B) :=
  ⟨ContinuousMonoidHom.toContinuousMonoidHom⟩

@[to_additive (attr := simp)]
/--
lemma `coe_coe` / 引理 `coe_coe`

English:
lemma coe_coe
  given: [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F)
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
引理 coe_coe
  条件: [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F)
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
lemma coe_coe [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F) :
    ⇑(f : A ->ₜ* B) = f := rfl

@[to_additive (attr := simp, norm_cast)]
/--
lemma `toMonoidHom_toContinuousMonoidHom` / 引理 `toMonoidHom_toContinuousMonoidHom`

English:
lemma toMonoidHom_toContinuousMonoidHom
  given: [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F)
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
引理 toMonoidHom_toContinuousMonoidHom
  条件: [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F)
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
lemma toMonoidHom_toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F) :
    ((f : A ->ₜ* B) : A ->* B) = f := rfl

@[to_additive (attr := simp, norm_cast)]
/--
lemma `toContinuousMap_toContinuousMonoidHom` / 引理 `toContinuousMap_toContinuousMonoidHom`

English:
lemma toContinuousMap_toContinuousMonoidHom
  statement: [MonoidHomClass F A B] [ContinuousMapClass F A B]
  proof: rfl

中文:
引理 toContinuousMap_toContinuousMonoidHom
  结论: [MonoidHomClass F A B] [ContinuousMapClass F A B]
  证明: rfl
-/
lemma toContinuousMap_toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapClass F A B]
    (f : F) : ((f : A ->ₜ* B) : C(A, B)) = f := rfl

end

@[to_additive (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : A ->ₜ* B} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

@[to_additive]

中文:
定理 ext
  条件: {f g : A ->ₜ* B} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : A ->ₜ* B} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[to_additive]
/--
theorem `toContinuousMap_injective` / 定理 `toContinuousMap_injective`

English:
theorem toContinuousMap_injective
  statement: Injective (toContinuousMap : _ -> C(A, B))
  proof: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h

@[to_additive]

中文:
定理 toContinuousMap_injective
  结论: Injective (toContinuousMap : _ -> C(A, B))
  证明: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h

@[to_additive]
-/
theorem toContinuousMap_injective : Injective (toContinuousMap : _ -> C(A, B)) := fun f g h =>
ext by convert! DFunLike.ext_iff.1 h

@[to_additive]
/--
theorem `toMonoidHom_injective` / 定理 `toMonoidHom_injective`

English:
theorem toMonoidHom_injective
  statement: Injective (toMonoidHom : _ -> A ->* B)
  proof: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h

中文:
定理 toMonoidHom_injective
  结论: Injective (toMonoidHom : _ -> A ->* B)
  证明: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h
-/
theorem toMonoidHom_injective : Injective (toMonoidHom : _ -> A ->* B) := fun f g h =>
ext by convert! DFunLike.ext_iff.1 h

/-- Composition of two continuous homomorphisms. -/
@[to_additive (attr := simps!) /-- Composition of two continuous homomorphisms. -/]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : B ->ₜ* C) (f : A ->ₜ* B)
  body: ⟨g.toMonoidHom.comp f.toMonoidHom, (map_continuous g).comp (map_continuous f)⟩

@[to_additive (attr := simp)]

中文:
定义 comp
  签名: (g : B ->ₜ* C) (f : A ->ₜ* B)
  定义体: ⟨g.toMonoidHom.comp f.toMonoidHom, (map_continuous g).comp (map_continuous f)⟩

@[to_additive (attr := simp)]

Depends on / 依赖: f.toMonoidHom, g.toMonoidHom.comp, map_continuous, toMonoidHom
-/
def comp (g : B ->ₜ* C) (f : A ->ₜ* B) : A ->ₜ* C :=
  ⟨g.toMonoidHom.comp f.toMonoidHom, (map_continuous g).comp (map_continuous f)⟩

@[to_additive (attr := simp)]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B)
  proof: rfl

中文:
引理 coe_comp
  条件: (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B)
  证明: rfl
-/
lemma coe_comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) :
    ⇑(g.comp f) = ⇑g ∘ ⇑f := rfl

/-- Product of two continuous homomorphisms on the same space. -/
@[to_additive (attr := simps!) prod
/-- Product of two continuous homomorphisms on the same space. -/]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : A ->ₜ* B) (g : A ->ₜ* C)
  body: ⟨f.toMonoidHom.prod g.toMonoidHom, f.continuous_toFun.prodMk g.continuous_toFun⟩

中文:
定义 prod
  签名: (f : A ->ₜ* B) (g : A ->ₜ* C)
  定义体: ⟨f.toMonoidHom.prod g.toMonoidHom, f.continuous_toFun.prodMk g.continuous_toFun⟩

Depends on / 依赖: continuous_toFun, f.continuous_toFun.prodMk, f.toMonoidHom.prod, g.continuous_toFun, g.toMonoidHom, prodMk, toMonoidHom
-/
def prod (f : A ->ₜ* B) (g : A ->ₜ* C) : A ->ₜ* (B × C) :=
  ⟨f.toMonoidHom.prod g.toMonoidHom, f.continuous_toFun.prodMk g.continuous_toFun⟩

/-- Product of two continuous homomorphisms on different spaces. -/
@[to_additive (attr := simps!) prodMap
  /-- Product of two continuous homomorphisms on different spaces. -/]
/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: (f : A ->ₜ* C) (g : B ->ₜ* D)
  body: ⟨f.toMonoidHom.prodMap g.toMonoidHom, f.continuous_toFun.prodMap g.continuous_toFun⟩

中文:
定义 prodMap
  签名: (f : A ->ₜ* C) (g : B ->ₜ* D)
  定义体: ⟨f.toMonoidHom.prodMap g.toMonoidHom, f.continuous_toFun.prodMap g.continuous_toFun⟩

Depends on / 依赖: continuous_toFun, f.continuous_toFun.prodMap, f.toMonoidHom.prodMap, g.continuous_toFun, g.toMonoidHom, prodMap, toMonoidHom
-/
def prodMap (f : A ->ₜ* C) (g : B ->ₜ* D) :
    (A × B) ->ₜ* (C × D) :=
  ⟨f.toMonoidHom.prodMap g.toMonoidHom, f.continuous_toFun.prodMap g.continuous_toFun⟩

variable (A B C D E)

/-- The trivial continuous homomorphism. -/
@[to_additive (attr := simps!) /-- The trivial continuous homomorphism. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (A ->ₜ* B)
  body: ⟨1, continuous_const⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: One (A ->ₜ* B)
  定义体: ⟨1, continuous_const⟩

@[to_additive (attr := simp)]

Depends on / 依赖: continuous_const
-/
instance : One (A ->ₜ* B) where
  one := ⟨1, continuous_const⟩

@[to_additive (attr := simp)]
/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ⇑(1 : A ->ₜ* B) = 1
  proof: rfl

@[to_additive]

中文:
引理 coe_one
  结论: ⇑(1 : A ->ₜ* B) = 1
  证明: rfl

@[to_additive]
-/
lemma coe_one : ⇑(1 : A ->ₜ* B) = 1 :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (A ->ₜ* B)
  body: ⟨1⟩

中文:
实例 :
  签名: Inhabited (A ->ₜ* B)
  定义体: ⟨1⟩
-/
instance : Inhabited (A ->ₜ* B) := ⟨1⟩

/-- The identity continuous homomorphism. -/
@[to_additive (attr := simps!) /-- The identity continuous homomorphism. -/]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : A ->ₜ* A
  body: ⟨.id A, continuous_id⟩

@[to_additive (attr := simp)]

中文:
定义 id
  签名: : A ->ₜ* A
  定义体: ⟨.id A, continuous_id⟩

@[to_additive (attr := simp)]

Depends on / 依赖: continuous_id
-/
def id : A ->ₜ* A := ⟨.id A, continuous_id⟩

@[to_additive (attr := simp)]
/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  statement: ⇑(ContinuousMonoidHom.id A) = _root_.id
  proof: rfl

中文:
引理 coe_id
  结论: ⇑(ContinuousMonoidHom.id A) = _root_.id
  证明: rfl
-/
lemma coe_id : ⇑(ContinuousMonoidHom.id A) = _root_.id :=
  rfl

/-- The continuous homomorphism given by projection onto the first factor. -/
@[to_additive (attr := simps!)
  /-- The continuous homomorphism given by projection onto the first factor. -/]
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : (A × B) ->ₜ* A
  body: ⟨MonoidHom.fst A B, continuous_fst⟩

中文:
定义 fst
  签名: : (A × B) ->ₜ* A
  定义体: ⟨MonoidHom.fst A B, continuous_fst⟩

Depends on / 依赖: MonoidHom, MonoidHom.fst, continuous_fst
-/
def fst : (A × B) ->ₜ* A := ⟨MonoidHom.fst A B, continuous_fst⟩

/-- The continuous homomorphism given by projection onto the second factor. -/
@[to_additive (attr := simps!)
  /-- The continuous homomorphism given by projection onto the second factor. -/]
/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : (A × B) ->ₜ* B
  body: ⟨MonoidHom.snd A B, continuous_snd⟩

中文:
定义 snd
  签名: : (A × B) ->ₜ* B
  定义体: ⟨MonoidHom.snd A B, continuous_snd⟩

Depends on / 依赖: MonoidHom, MonoidHom.snd, continuous_snd
-/
def snd : (A × B) ->ₜ* B :=
  ⟨MonoidHom.snd A B, continuous_snd⟩

/-- The continuous homomorphism given by inclusion of the first factor. -/
@[to_additive (attr := simps!)
  /-- The continuous homomorphism given by inclusion of the first factor. -/]
/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : A ->ₜ* (A × B)
  body: prod (id A) 1

中文:
定义 inl
  签名: : A ->ₜ* (A × B)
  定义体: prod (id A) 1
-/
def inl : A ->ₜ* (A × B) :=
  prod (id A) 1

/-- The continuous homomorphism given by inclusion of the second factor. -/
@[to_additive (attr := simps!)
  /-- The continuous homomorphism given by inclusion of the second factor. -/]
/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : B ->ₜ* (A × B)
  body: prod 1 (id B)

中文:
定义 inr
  签名: : B ->ₜ* (A × B)
  定义体: prod 1 (id B)
-/
def inr : B ->ₜ* (A × B) :=
  prod 1 (id B)


/-- The continuous homomorphism given by the diagonal embedding. -/
@[to_additive (attr := simps!) /-- The continuous homomorphism given by the diagonal embedding. -/]
/--
Definition of `diag` / `diag` 的定义

English:
definition diag
  signature: : A ->ₜ* (A × A)
  body: prod (id A) (id A)

中文:
定义 diag
  签名: : A ->ₜ* (A × A)
  定义体: prod (id A) (id A)
-/
def diag : A ->ₜ* (A × A) := prod (id A) (id A)

/-- The continuous homomorphism given by swapping components. -/
@[to_additive (attr := simps!) /-- The continuous homomorphism given by swapping components. -/]
/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: : (A × B) ->ₜ* (B × A)
  body: prod (snd A B) (fst A B)

中文:
定义 swap
  签名: : (A × B) ->ₜ* (B × A)
  定义体: prod (snd A B) (fst A B)
-/
def swap : (A × B) ->ₜ* (B × A) := prod (snd A B) (fst A B)

section CommMonoid
variable [CommMonoid E] [TopologicalSpace E] [ContinuousMul E]

/-- The continuous homomorphism given by multiplication. -/
@[to_additive (attr := simps!) /-- The continuous homomorphism given by addition. -/]
/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : (E × E) ->ₜ* E
  body: ⟨mulMonoidHom, continuous_mul⟩

中文:
定义 mul
  签名: : (E × E) ->ₜ* E
  定义体: ⟨mulMonoidHom, continuous_mul⟩

Depends on / 依赖: continuous_mul, mulMonoidHom
-/
def mul : (E × E) ->ₜ* E := ⟨mulMonoidHom, continuous_mul⟩

variable {A B C D E}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoid (A ->ₜ* E)
  body: (mul E).comp (f.prod g)
  mul_comm f g := ext fun x => mul_comm (f x) (g x)
  mul_assoc f g h := ext fun x => mul_assoc (f x) (g x) (h x)
  one_mul f := ext fun x => one_mul (f x)
  mul_one f := ext fun x => mul_one (f x)

@[to_additive (attr := simp)]

中文:
实例 :
  签名: CommMonoid (A ->ₜ* E)
  定义体: (mul E).comp (f.prod g)
  mul_comm f g := ext fun x => mul_comm (f x) (g x)
  mul_assoc f g h := ext fun x => mul_assoc (f x) (g x) (h x)
  one_mul f := ext fun x => one_mul (f x)
  mul_one f := ext fun x => mul_one (f x)

@[to_additive (attr := simp)]

Depends on / 依赖: f.prod
-/
instance : CommMonoid (A ->ₜ* E) where
  mul f g := (mul E).comp (f.prod g)
  mul_comm f g := ext fun x => mul_comm (f x) (g x)
  mul_assoc f g h := ext fun x => mul_assoc (f x) (g x) (h x)
  one_mul f := ext fun x => one_mul (f x)
  mul_one f := ext fun x => mul_one (f x)

@[to_additive (attr := simp)]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (f g : A ->ₜ* E) (a : A)
  statement: (f * g) a = f a * g a
  proof: by
  rfl

@[to_additive (attr := simp)]

中文:
定理 mul_apply
  条件: (f g : A ->ₜ* E) (a : A)
  结论: (f * g) a = f a * g a
  证明: by
  rfl

@[to_additive (attr := simp)]
-/
theorem mul_apply (f g : A ->ₜ* E) (a : A) : (f * g) a = f a * g a := by
  rfl

@[to_additive (attr := simp)]
/--
theorem `pow_apply` / 定理 `pow_apply`

English:
theorem pow_apply
  given: (f : A ->ₜ* E) (n : Nat) (a : A)
  statement: (f ^ n) a = (f a) ^ n
  proof: by
  induction n
  case zero => rw [pow_zero, pow_zero, one_toFun]
  case succ n ih => rw [pow_succ, pow_succ, ContinuousMonoidHom.mul_apply, ih]

中文:
定理 pow_apply
  条件: (f : A ->ₜ* E) (n : 自然数) (a : A)
  结论: (f ^ n) a = (f a) ^ n
  证明: by
  induction n
  case zero => rw [pow_zero, pow_zero, one_toFun]
  case succ n ih => rw [pow_succ, pow_succ, ContinuousMonoidHom.mul_apply, ih]

Depends on / 依赖: ContinuousMonoidHom, ContinuousMonoidHom.mul_apply, mul_apply, one_toFun, pow_succ, pow_zero
-/
theorem pow_apply (f : A ->ₜ* E) (n : Nat) (a : A) : (f ^ n) a = (f a) ^ n := by
  induction n
  case zero => rw [pow_zero, pow_zero, one_toFun]
  case succ n ih => rw [pow_succ, pow_succ, ContinuousMonoidHom.mul_apply, ih]

/-- Coproduct of two continuous homomorphisms to the same space. -/
@[to_additive (attr := simps!) /-- Coproduct of two continuous homomorphisms to the same space. -/]
/--
Definition of `coprod` / `coprod` 的定义

English:
definition coprod
  signature: (f : ContinuousMonoidHom A E) (g : ContinuousMonoidHom B E)
  body: (mul E).comp (f.prodMap g)

中文:
定义 coprod
  签名: (f : ContinuousMonoidHom A E) (g : ContinuousMonoidHom B E)
  定义体: (mul E).comp (f.prodMap g)

Depends on / 依赖: f.prodMap, prodMap
-/
def coprod (f : ContinuousMonoidHom A E) (g : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (A × B) E :=
  (mul E).comp (f.prodMap g)

end CommMonoid

section CommGroup

variable [CommGroup E] [TopologicalSpace E] [IsTopologicalGroup E]
/-- The continuous homomorphism given by inversion. -/
@[to_additive (attr := simps!) /-- The continuous homomorphism given by negation. -/]
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : ContinuousMonoidHom E E
  body: ⟨invMonoidHom, continuous_inv⟩

@[to_additive]

中文:
定义 inv
  签名: : ContinuousMonoidHom E E
  定义体: ⟨invMonoidHom, continuous_inv⟩

@[to_additive]

Depends on / 依赖: continuous_inv, invMonoidHom
-/
def inv : ContinuousMonoidHom E E :=
  ⟨invMonoidHom, continuous_inv⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommGroup (ContinuousMonoidHom A E)
  body: inferInstance
  inv f := (inv E).comp f
  inv_mul_cancel f := ext fun x => inv_mul_cancel (f x)
  div f g := .comp ⟨divMonoidHom, continuous_div'⟩ (f.prod g)
  div_eq_mul_inv f g := ext fun x => div_eq_mul_inv (f x) (g x)

中文:
实例 :
  签名: CommGroup (ContinuousMonoidHom A E)
  定义体: inferInstance
  inv f := (inv E).comp f
  inv_mul_cancel f := ext fun x => inv_mul_cancel (f x)
  div f g := .comp ⟨divMonoidHom, continuous_div'⟩ (f.prod g)
  div_eq_mul_inv f g := ext fun x => div_eq_mul_inv (f x) (g x)
-/
instance : CommGroup (ContinuousMonoidHom A E) where
  __ : CommMonoid (ContinuousMonoidHom A E) := inferInstance
  inv f := (inv E).comp f
  inv_mul_cancel f := ext fun x => inv_mul_cancel (f x)
  div f g := .comp ⟨divMonoidHom, continuous_div'⟩ (f.prod g)
  div_eq_mul_inv f g := ext fun x => div_eq_mul_inv (f x) (g x)

end CommGroup

/-- For `f : F` where `F` is a class of continuous monoid hom, this yields an element
`ContinuousMonoidHom A B`. -/
@[to_additive /-- For `f : F` where `F` is a class of continuous additive monoid hom, this yields
an element `ContinuousAddMonoidHom A B`. -/]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: (F : Type*) [FunLike F A B] [ContinuousMapClass F A B]
  body: toContinuousMonoidHom f

中文:
定义 ofClass
  签名: (F : 类型) [FunLike F A B] [ContinuousMapClass F A B]
  定义体: toContinuousMonoidHom f

Depends on / 依赖: toContinuousMonoidHom
-/
def ofClass (F : Type*) [FunLike F A B] [ContinuousMapClass F A B]
    [MonoidHomClass F A B] (f : F) : (ContinuousMonoidHom A B) := toContinuousMonoidHom f

end ContinuousMonoidHom

end

section

/-!

### Continuous MulEquiv

This section defines the space of continuous isomorphisms between two topological groups.
-/

universe u v

variable (G : Type u) [TopologicalSpace G] (H : Type v) [TopologicalSpace H]

/--
Definition of `ContinuousAddEquiv` / `ContinuousAddEquiv` 的定义

English:
structure ContinuousAddEquiv
  parameters: [Add G] [Add H]
  extends: G ≃+ H, G ≃ₜ H
  (no additional axioms)

中文:
结构 ContinuousAddEquiv
  参数: [Add G] [Add H]
  继承: G ≃+ H, G ≃ₜ H
  (无附加公理)
-/
structure ContinuousAddEquiv [Add G] [Add H] extends G ≃+ H, G ≃ₜ H

/-- The structure of two-sided continuous isomorphisms between groups.
Note that both the map and its inverse have to be continuous. -/
@[to_additive]
/--
Definition of `ContinuousMulEquiv` / `ContinuousMulEquiv` 的定义

English:
structure ContinuousMulEquiv
  parameters: [Mul G] [Mul H]
  extends: G ≃* H, G ≃ₜ H
  (no additional axioms)

中文:
结构 ContinuousMulEquiv
  参数: [Mul G] [Mul H]
  继承: G ≃* H, G ≃ₜ H
  (无附加公理)
-/
structure ContinuousMulEquiv [Mul G] [Mul H] extends G ≃* H, G ≃ₜ H

/-- The homeomorphism induced from a two-sided continuous isomorphism of groups. -/
add_decl_doc ContinuousMulEquiv.toHomeomorph

/-- The homeomorphism induced from a two-sided continuous isomorphism additive groups. -/
add_decl_doc ContinuousAddEquiv.toHomeomorph

@[inherit_doc]
infixl:25 " ≃ₜ* " => ContinuousMulEquiv

@[inherit_doc]
infixl:25 " ≃ₜ+ " => ContinuousAddEquiv

section

namespace ContinuousMulEquiv

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [Mul M] [Mul N]

section coe

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (M ≃ₜ* N) M N
  body: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    exact MulEquiv.ext_iff.mpr (congrFun h₁)

@[to_additive]

中文:
实例 :
  签名: EquivLike (M ≃ₜ* N) M N
  定义体: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    exact MulEquiv.ext_iff.mpr (congrFun h₁)

@[to_additive]

Depends on / 依赖: f.toFun
-/
instance : EquivLike (M ≃ₜ* N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    exact MulEquiv.ext_iff.mpr (congrFun h₁)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulEquivClass (M ≃ₜ* N) M N
  body: f.map_mul'

@[to_additive]

中文:
实例 :
  签名: MulEquivClass (M ≃ₜ* N) M N
  定义体: f.map_mul'

@[to_additive]

Depends on / 依赖: f.map_mul, map_mul
-/
instance : MulEquivClass (M ≃ₜ* N) M N where
  map_mul f := f.map_mul'

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HomeomorphClass (M ≃ₜ* N) M N
  body: f.continuous_toFun
  inv_continuous f := f.continuous_invFun

中文:
实例 :
  签名: HomeomorphClass (M ≃ₜ* N) M N
  定义体: f.continuous_toFun
  inv_continuous f := f.continuous_invFun

Depends on / 依赖: continuous_toFun, f.continuous_toFun
-/
instance : HomeomorphClass (M ≃ₜ* N) M N where
  map_continuous f := f.continuous_toFun
  inv_continuous f := f.continuous_invFun

/-- Two continuous multiplicative isomorphisms agree if they are defined by the
same underlying function. -/
@[to_additive (attr := ext) /-- Two continuous additive isomorphisms agree if they are defined by
the same underlying function. -/]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : M ≃ₜ* N} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

@[to_additive (attr := simp)]

中文:
定理 ext
  条件: {f g : M ≃ₜ* N} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

@[to_additive (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : M ≃ₜ* N} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[to_additive (attr := simp)]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : M ≃* N) (hf1 hf2)
  statement: ⇑(mk f hf1 hf2) = f
  proof: rfl

@[to_additive]

中文:
定理 coe_mk
  条件: (f : M ≃* N) (hf1 hf2)
  结论: ⇑(mk f hf1 hf2) = f
  证明: rfl

@[to_additive]
-/
theorem coe_mk (f : M ≃* N) (hf1 hf2) : ⇑(mk f hf1 hf2) = f := rfl

@[to_additive]
/--
theorem `toEquiv_eq_coe` / 定理 `toEquiv_eq_coe`

English:
theorem toEquiv_eq_coe
  given: (f : M ≃ₜ* N)
  statement: f.toEquiv = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toEquiv_eq_coe
  条件: (f : M ≃ₜ* N)
  结论: f.toEquiv = f
  证明: rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Eventually, Eventually.of_forall, closure, closure.continuousAt, continuousAt, equicontinuousAt_iff_range, equicontinuousAt_iff_range.mp, mem_closure_of_tendsto, mem_range_self, of_forall
-/
theorem toEquiv_eq_coe (f : M ≃ₜ* N) : f.toEquiv = f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `toMulEquiv_eq_coe` / 定理 `toMulEquiv_eq_coe`

English:
theorem toMulEquiv_eq_coe
  given: (f : M ≃ₜ* N)
  statement: f.toMulEquiv = f
  proof: rfl

@[to_additive]

中文:
定理 toMulEquiv_eq_coe
  条件: (f : M ≃ₜ* N)
  结论: f.toMulEquiv = f
  证明: rfl

@[to_additive]

Depends on / 依赖: Eventually, Eventually.of_forall, closure, closure.uniformContinuous, mem_closure_of_tendsto, mem_range_self, of_forall, uniformContinuous, uniformEquicontinuous_iff_range, uniformEquicontinuous_iff_range.mp
-/
theorem toMulEquiv_eq_coe (f : M ≃ₜ* N) : f.toMulEquiv = f :=
  rfl

@[to_additive]
/--
theorem `toHomeomorph_eq_coe` / 定理 `toHomeomorph_eq_coe`

English:
theorem toHomeomorph_eq_coe
  given: (f : M ≃ₜ* N)
  statement: f.toHomeomorph = f
  proof: rfl

中文:
定理 toHomeomorph_eq_coe
  条件: (f : M ≃ₜ* N)
  结论: f.toHomeomorph = f
  证明: rfl
-/
theorem toHomeomorph_eq_coe (f : M ≃ₜ* N) : f.toHomeomorph = f :=
  rfl

/-- Makes a continuous multiplicative isomorphism from
a homeomorphism which preserves multiplication. -/
@[to_additive /-- Makes a continuous additive isomorphism from
a homeomorphism which preserves addition. -/]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (f : M ≃ₜ N) (h : forall x y, f (x * y) = f x * f y)
  body: ⟨⟨f.toEquiv,h⟩, f.continuous_toFun, f.continuous_invFun⟩

中文:
定义 mk'
  签名: (f : M ≃ₜ N) (h : 对任意 x y, f (x * y) = f x * f y)
  定义体: ⟨⟨f.toEquiv,h⟩, f.continuous_toFun, f.continuous_invFun⟩

Depends on / 依赖: continuousWithinAt_of_equicontinuousWithinAt, continuousWithinAt_univ, continuous_invFun, continuous_toFun, equicontinuousWithinAt_univ, f.continuous_invFun, f.continuous_toFun, f.toEquiv, tendsto_pi_nhds, toEquiv
-/
def mk' (f : M ≃ₜ N) (h : forall x y, f (x * y) = f x * f y) : M ≃ₜ* N :=
  ⟨⟨f.toEquiv,h⟩, f.continuous_toFun, f.continuous_invFun⟩

set_option linter.docPrime false in -- This is about `ContinuousMulEquiv.mk'`
@[simp]
/--
lemma `coe_mk'` / 引理 `coe_mk'`

English:
lemma coe_mk'
  given: (f : M ≃ₜ N) (h : forall x y, f (x * y) = f x * f y)
  statement: ⇑(mk' f h) = f
  proof: rfl

中文:
引理 coe_mk'
  条件: (f : M ≃ₜ N) (h : 对任意 x y, f (x * y) = f x * f y)
  结论: ⇑(mk' f h) = f
  证明: rfl
-/
lemma coe_mk' (f : M ≃ₜ N) (h : forall x y, f (x * y) = f x * f y) : ⇑(mk' f h) = f := rfl

end coe

section bijective

@[to_additive]
/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (e : M ≃ₜ* N)
  statement: Function.Bijective e
  proof: EquivLike.bijective e

@[to_additive]

中文:
定理 bijective
  条件: (e : M ≃ₜ* N)
  结论: Function.Bijective e
  证明: EquivLike.bijective e

@[to_additive]
-/
protected theorem bijective (e : M ≃ₜ* N) : Function.Bijective e :=
  EquivLike.bijective e

@[to_additive]
/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : M ≃ₜ* N)
  statement: Function.Injective e
  proof: EquivLike.injective e

@[to_additive]

中文:
定理 injective
  条件: (e : M ≃ₜ* N)
  结论: Function.Injective e
  证明: EquivLike.injective e

@[to_additive]
-/
protected theorem injective (e : M ≃ₜ* N) : Function.Injective e :=
  EquivLike.injective e

@[to_additive]
/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : M ≃ₜ* N)
  statement: Function.Surjective e
  proof: EquivLike.surjective e

@[to_additive]

中文:
定理 surjective
  条件: (e : M ≃ₜ* N)
  结论: Function.Surjective e
  证明: EquivLike.surjective e

@[to_additive]

Depends on / 依赖: tendsto_pi_nhds, uniformContinuousOn_of_uniformEquicontinuousOn, uniformContinuousOn_univ, uniformEquicontinuousOn_univ
-/
protected theorem surjective (e : M ≃ₜ* N) : Function.Surjective e :=
  EquivLike.surjective e

@[to_additive]
/--
theorem `apply_eq_iff_eq` / 定理 `apply_eq_iff_eq`

English:
theorem apply_eq_iff_eq
  given: (e : M ≃ₜ* N) {x y : M}
  statement: e x = e y ↔ x = y
  proof: e.injective.eq_iff

中文:
定理 apply_eq_iff_eq
  条件: (e : M ≃ₜ* N) {x y : M}
  结论: e x = e y ↔ x = y
  证明: e.injective.eq_iff

Depends on / 依赖: e.injective.eq_iff, eq_iff, injective
-/
theorem apply_eq_iff_eq (e : M ≃ₜ* N) {x y : M} : e x = e y ↔ x = y :=
  e.injective.eq_iff

end bijective

section refl

variable (M)

/-- The identity map is a continuous multiplicative isomorphism. -/
@[to_additive (attr := refl) /-- The identity map is a continuous additive isomorphism. -/]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : M ≃ₜ* M
  body: { MulEquiv.refl _ with
    continuous_toFun := by dsimp; fun_prop
    continuous_invFun := by dsimp; fun_prop }

@[to_additive]

中文:
定义 refl
  签名: : M ≃ₜ* M
  定义体: { MulEquiv.refl _ with
    continuous_toFun := by dsimp; fun_prop
    continuous_invFun := by dsimp; fun_prop }

@[to_additive]

Depends on / 依赖: MulEquiv, MulEquiv.refl, continuous_invFun, continuous_toFun, fun_prop
-/
def refl : M ≃ₜ* M :=
  { MulEquiv.refl _ with
    continuous_toFun := by dsimp; fun_prop
    continuous_invFun := by dsimp; fun_prop }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (M ≃ₜ* M)
  body: ⟨ContinuousMulEquiv.refl M⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 :
  签名: Inhabited (M ≃ₜ* M)
  定义体: ⟨ContinuousMulEquiv.refl M⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: ContinuousMulEquiv, ContinuousMulEquiv.refl
-/
instance : Inhabited (M ≃ₜ* M) := ⟨ContinuousMulEquiv.refl M⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: ↑(refl M) = id
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_refl
  结论: ↑(refl M) = id
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_refl : ↑(refl M) = id := rfl

@[to_additive (attr := simp)]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (m : M)
  statement: refl M m = m
  proof: rfl

中文:
定理 refl_apply
  条件: (m : M)
  结论: refl M m = m
  证明: rfl
-/
theorem refl_apply (m : M) : refl M m = m := rfl

end refl

section symm

/-- The inverse of a ContinuousMulEquiv. -/
@[to_additive (attr := symm) /-- The inverse of a ContinuousAddEquiv. -/]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (cme : M ≃ₜ* N)
  body: { cme.toMulEquiv.symm with
  continuous_toFun := cme.continuous_invFun
  continuous_invFun := cme.continuous_toFun }

中文:
定义 symm
  签名: (cme : M ≃ₜ* N)
  定义体: { cme.toMulEquiv.symm with
  continuous_toFun := cme.continuous_invFun
  continuous_invFun := cme.continuous_toFun }

Depends on / 依赖: cme.continuous_invFun, cme.continuous_toFun, cme.toMulEquiv.symm, continuous_invFun, continuous_toFun, h.symm, toMulEquiv
-/
def symm (cme : M ≃ₜ* N) : N ≃ₜ* M :=
  { cme.toMulEquiv.symm with
  continuous_toFun := cme.continuous_invFun
  continuous_invFun := cme.continuous_toFun }

/-- See Note [custom simps projection] -/
@[to_additive /-- See Note [custom simps projection] -/]
/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: [Mul G] [Mul H] (e : G ≃ₜ* H)
  body: e.symm

initialize_simps_projections ContinuousMulEquiv (toFun -> apply, invFun -> symm_apply)

initialize_simps_projections ContinuousAddEquiv (toFun -> apply, invFun -> symm_apply)

@[to_additive]

中文:
定义 Simps.symm_apply
  签名: [Mul G] [Mul H] (e : G ≃ₜ* H)
  定义体: e.symm

initialize_simps_projections ContinuousMulEquiv (toFun -> apply, invFun -> symm_apply)

initialize_simps_projections ContinuousAddEquiv (toFun -> apply, invFun -> symm_apply)

@[to_additive]
-/
def Simps.symm_apply [Mul G] [Mul H] (e : G ≃ₜ* H) : H -> G :=
  e.symm

initialize_simps_projections ContinuousMulEquiv (toFun -> apply, invFun -> symm_apply)

initialize_simps_projections ContinuousAddEquiv (toFun -> apply, invFun -> symm_apply)

@[to_additive]
/--
theorem `invFun_eq_symm` / 定理 `invFun_eq_symm`

English:
theorem invFun_eq_symm
  given: {f : M ≃ₜ* N}
  statement: f.invFun = f.symm
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 invFun_eq_symm
  条件: {f : M ≃ₜ* N}
  结论: f.invFun = f.symm
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem invFun_eq_symm {f : M ≃ₜ* N} : f.invFun = f.symm := rfl

@[to_additive (attr := simp)]
/--
theorem `coe_toHomeomorph_symm` / 定理 `coe_toHomeomorph_symm`

English:
theorem coe_toHomeomorph_symm
  given: (f : M ≃ₜ* N)
  statement: (f : M ≃ₜ N).symm = (f.symm : N ≃ₜ M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_toHomeomorph_symm
  条件: (f : M ≃ₜ* N)
  结论: (f : M ≃ₜ N).symm = (f.symm : N ≃ₜ M)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_toHomeomorph_symm (f : M ≃ₜ* N) : (f : M ≃ₜ N).symm = (f.symm : N ≃ₜ M) := rfl

@[to_additive (attr := simp)]
/--
theorem `equivLike_inv_eq_symm` / 定理 `equivLike_inv_eq_symm`

English:
theorem equivLike_inv_eq_symm
  given: (f : M ≃ₜ* N)
  statement: EquivLike.inv f = f.symm
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 equivLike_inv_eq_symm
  条件: (f : M ≃ₜ* N)
  结论: EquivLike.inv f = f.symm
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem equivLike_inv_eq_symm (f : M ≃ₜ* N) : EquivLike.inv f = f.symm := rfl

@[to_additive (attr := simp)]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (f : M ≃ₜ* N)
  statement: f.symm.symm = f
  proof: rfl

@[to_additive]

中文:
定理 symm_symm
  条件: (f : M ≃ₜ* N)
  结论: f.symm.symm = f
  证明: rfl

@[to_additive]
-/
theorem symm_symm (f : M ≃ₜ* N) : f.symm.symm = f := rfl

@[to_additive]
/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : M ≃ₜ* N -> _)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  结论: Function.Bijective (symm : M ≃ₜ* N -> _)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (symm : M ≃ₜ* N -> _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : M ≃ₜ* N) (y : N)
  statement: e (e.symm y) = y
  proof: e.toEquiv.apply_symm_apply y

中文:
定理 apply_symm_apply
  条件: (e : M ≃ₜ* N) (y : N)
  结论: e (e.symm y) = y
  证明: e.toEquiv.apply_symm_apply y

Depends on / 依赖: apply_symm_apply, e.toEquiv.apply_symm_apply, toEquiv
-/
theorem apply_symm_apply (e : M ≃ₜ* N) (y : N) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : M ≃ₜ* N) (x : M)
  statement: e.symm (e x) = x
  proof: e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]

中文:
定理 symm_apply_apply
  条件: (e : M ≃ₜ* N) (x : M)
  结论: e.symm (e x) = x
  证明: e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]

Depends on / 依赖: e.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
theorem symm_apply_apply (e : M ≃ₜ* N) (x : M) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]
/--
theorem `symm_comp_self` / 定理 `symm_comp_self`

English:
theorem symm_comp_self
  given: (e : M ≃ₜ* N)
  statement: e.symm ∘ e = id
  proof: funext e.symm_apply_apply

@[to_additive (attr := simp)]

中文:
定理 symm_comp_self
  条件: (e : M ≃ₜ* N)
  结论: e.symm ∘ e = id
  证明: funext e.symm_apply_apply

@[to_additive (attr := simp)]

Depends on / 依赖: e.symm_apply_apply, symm_apply_apply
-/
theorem symm_comp_self (e : M ≃ₜ* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[to_additive (attr := simp)]
/--
theorem `self_comp_symm` / 定理 `self_comp_symm`

English:
theorem self_comp_symm
  given: (e : M ≃ₜ* N)
  statement: e ∘ e.symm = id
  proof: funext e.apply_symm_apply

@[to_additive]

中文:
定理 self_comp_symm
  条件: (e : M ≃ₜ* N)
  结论: e ∘ e.symm = id
  证明: funext e.apply_symm_apply

@[to_additive]

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply
-/
theorem self_comp_symm (e : M ≃ₜ* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[to_additive]
/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : M ≃ₜ* N) {x y}
  statement: e.symm x = y ↔ x = e y
  proof: e.toEquiv.symm_apply_eq

@[to_additive]

中文:
定理 symm_apply_eq
  条件: (e : M ≃ₜ* N) {x y}
  结论: e.symm x = y ↔ x = e y
  证明: e.toEquiv.symm_apply_eq

@[to_additive]

Depends on / 依赖: e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq (e : M ≃ₜ* N) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

@[to_additive]
/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : M ≃ₜ* N) {x y}
  statement: y = e.symm x ↔ e y = x
  proof: e.toEquiv.eq_symm_apply

@[to_additive (attr := deprecated eq_symm_apply (since := "2026-07-26"))]

中文:
定理 eq_symm_apply
  条件: (e : M ≃ₜ* N) {x y}
  结论: y = e.symm x ↔ e y = x
  证明: e.toEquiv.eq_symm_apply

@[to_additive (attr := deprecated eq_symm_apply (since := "2026-07-26"))]

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
theorem eq_symm_apply (e : M ≃ₜ* N) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[to_additive (attr := deprecated eq_symm_apply (since := "2026-07-26"))]
/--
theorem `apply_eq_iff_symm_apply` / 定理 `apply_eq_iff_symm_apply`

English:
theorem apply_eq_iff_symm_apply
  given: (e : M ≃ₜ* N) {x : M} {y : N}
  statement: e x = y ↔ x = e.symm y
  proof: e.eq_symm_apply.symm

@[to_additive]

中文:
定理 apply_eq_iff_symm_apply
  条件: (e : M ≃ₜ* N) {x : M} {y : N}
  结论: e x = y ↔ x = e.symm y
  证明: e.eq_symm_apply.symm

@[to_additive]

Depends on / 依赖: e.eq_symm_apply.symm, eq_symm_apply
-/
theorem apply_eq_iff_symm_apply (e : M ≃ₜ* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.eq_symm_apply.symm

@[to_additive]
/--
theorem `eq_comp_symm` / 定理 `eq_comp_symm`

English:
theorem eq_comp_symm
  given: {α : Type*} (e : M ≃ₜ* N) (f : N -> α) (g : M -> α)
  proof: e.toEquiv.eq_comp_symm f g

@[to_additive]

中文:
定理 eq_comp_symm
  条件: {α : 类型} (e : M ≃ₜ* N) (f : N -> α) (g : M -> α)
  证明: e.toEquiv.eq_comp_symm f g

@[to_additive]

Depends on / 依赖: e.toEquiv.eq_comp_symm, eq_comp_symm, toEquiv
-/
theorem eq_comp_symm {α : Type*} (e : M ≃ₜ* N) (f : N -> α) (g : M -> α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

@[to_additive]
/--
theorem `comp_symm_eq` / 定理 `comp_symm_eq`

English:
theorem comp_symm_eq
  given: {α : Type*} (e : M ≃ₜ* N) (f : N -> α) (g : M -> α)
  proof: e.toEquiv.comp_symm_eq f g

@[to_additive]

中文:
定理 comp_symm_eq
  条件: {α : 类型} (e : M ≃ₜ* N) (f : N -> α) (g : M -> α)
  证明: e.toEquiv.comp_symm_eq f g

@[to_additive]

Depends on / 依赖: comp_symm_eq, e.toEquiv.comp_symm_eq, toEquiv
-/
theorem comp_symm_eq {α : Type*} (e : M ≃ₜ* N) (f : N -> α) (g : M -> α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g

@[to_additive]
/--
theorem `eq_symm_comp` / 定理 `eq_symm_comp`

English:
theorem eq_symm_comp
  given: {α : Type*} (e : M ≃ₜ* N) (f : α -> M) (g : α -> N)
  proof: e.toEquiv.eq_symm_comp f g

@[to_additive]

中文:
定理 eq_symm_comp
  条件: {α : 类型} (e : M ≃ₜ* N) (f : α -> M) (g : α -> N)
  证明: e.toEquiv.eq_symm_comp f g

@[to_additive]

Depends on / 依赖: e.toEquiv.eq_symm_comp, eq_symm_comp, toEquiv
-/
theorem eq_symm_comp {α : Type*} (e : M ≃ₜ* N) (f : α -> M) (g : α -> N) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g

@[to_additive]
/--
theorem `symm_comp_eq` / 定理 `symm_comp_eq`

English:
theorem symm_comp_eq
  given: {α : Type*} (e : M ≃ₜ* N) (f : α -> M) (g : α -> N)
  proof: e.toEquiv.symm_comp_eq f g

中文:
定理 symm_comp_eq
  条件: {α : 类型} (e : M ≃ₜ* N) (f : α -> M) (g : α -> N)
  证明: e.toEquiv.symm_comp_eq f g

Depends on / 依赖: e.toEquiv.symm_comp_eq, symm_comp_eq, toEquiv
-/
theorem symm_comp_eq {α : Type*} (e : M ≃ₜ* N) (f : α -> M) (g : α -> N) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g

end symm

section trans

variable {L : Type*} [Mul L] [TopologicalSpace L]

/-- The composition of two ContinuousMulEquiv. -/
@[to_additive /-- The composition of two ContinuousAddEquiv. -/]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (cme1 : M ≃ₜ* N) (cme2 : N ≃ₜ* L)
  body: cme1.toMulEquiv.trans cme2.toMulEquiv
  continuous_toFun := by convert! Continuous.comp cme2.continuous_toFun cme1.continuous_toFun
  continuous_invFun := by convert! Continuous.comp cme1.continuous_invFun cme2.continuous_invFun

@[to_additive (attr := simp)]

中文:
定义 trans
  签名: (cme1 : M ≃ₜ* N) (cme2 : N ≃ₜ* L)
  定义体: cme1.toMulEquiv.trans cme2.toMulEquiv
  continuous_toFun := by convert! Continuous.comp cme2.continuous_toFun cme1.continuous_toFun
  continuous_invFun := by convert! Continuous.comp cme1.continuous_invFun cme2.continuous_invFun

@[to_additive (attr := simp)]

Depends on / 依赖: cme1.toMulEquiv.trans, cme2.toMulEquiv, toMulEquiv
-/
def trans (cme1 : M ≃ₜ* N) (cme2 : N ≃ₜ* L) : M ≃ₜ* L where
  __ := cme1.toMulEquiv.trans cme2.toMulEquiv
  continuous_toFun := by convert! Continuous.comp cme2.continuous_toFun cme1.continuous_toFun
  continuous_invFun := by convert! Continuous.comp cme1.continuous_invFun cme2.continuous_invFun

@[to_additive (attr := simp)]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L)
  statement: ↑(e₁.trans e₂) = e₂ ∘ e₁
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_trans
  条件: (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L)
  结论: ↑(e₁.trans e₂) = e₂ ∘ e₁
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_trans (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) : ↑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[to_additive (attr := simp)]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (m : M)
  statement: e₁.trans e₂ m = e₂ (e₁ m)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 trans_apply
  条件: (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (m : M)
  结论: e₁.trans e₂ m = e₂ (e₁ m)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem trans_apply (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) := rfl

@[to_additive (attr := simp)]
/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (l : L)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 symm_trans_apply
  条件: (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (l : L)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem symm_trans_apply (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (l : L) :
    (e₁.trans e₂).symm l = e₁.symm (e₂.symm l) := rfl

@[to_additive (attr := simp)]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (e : M ≃ₜ* N)
  statement: e.symm.trans e = refl N
  proof: DFunLike.ext _ _ e.apply_symm_apply

@[to_additive (attr := simp)]

中文:
定理 symm_trans_self
  条件: (e : M ≃ₜ* N)
  结论: e.symm.trans e = refl N
  证明: DFunLike.ext _ _ e.apply_symm_apply

@[to_additive (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.ext, apply_symm_apply, e.apply_symm_apply
-/
theorem symm_trans_self (e : M ≃ₜ* N) : e.symm.trans e = refl N :=
  DFunLike.ext _ _ e.apply_symm_apply

@[to_additive (attr := simp)]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (e : M ≃ₜ* N)
  statement: e.trans e.symm = refl M
  proof: DFunLike.ext _ _ e.symm_apply_apply

中文:
定理 self_trans_symm
  条件: (e : M ≃ₜ* N)
  结论: e.trans e.symm = refl M
  证明: DFunLike.ext _ _ e.symm_apply_apply

Depends on / 依赖: DFunLike, DFunLike.ext, e.symm_apply_apply, symm_apply_apply
-/
theorem self_trans_symm (e : M ≃ₜ* N) : e.trans e.symm = refl M :=
  DFunLike.ext _ _ e.symm_apply_apply

end trans

section unique

/-- The `MulEquiv` between two monoids with a unique element. -/
@[to_additive /-- The `AddEquiv` between two `AddMonoid`s with a unique element. -/]
/--
Definition of `ofUnique` / `ofUnique` 的定义

English:
definition ofUnique
  signature: {M N} [Unique M] [Unique N] [Mul M] [Mul N]
  body: MulEquiv.ofUnique

中文:
定义 ofUnique
  签名: {M N} [Unique M] [Unique N] [Mul M] [Mul N]
  定义体: MulEquiv.ofUnique

Depends on / 依赖: MulEquiv, MulEquiv.ofUnique, ofUnique
-/
def ofUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N]
    [TopologicalSpace M] [TopologicalSpace N] : M ≃ₜ* N where
  __ := MulEquiv.ofUnique

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive /-- There is a unique additive monoid homomorphism between two additive monoids with
  a unique element. -/]
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N]
    [TopologicalSpace M] [TopologicalSpace N] : Unique (M ≃ₜ* N) where
  default := ofUnique
  uniq _ := ext fun _ => Subsingleton.elim _ _

end unique

end ContinuousMulEquiv

namespace MulEquiv

variable {G H} [Mul G] [Mul H] (e : G ≃* H) (he : forall s, IsOpen (e ⁻¹' s) ↔ IsOpen s)
include he

/-- A `MulEquiv` that respects open sets is a `ContinuousMulEquiv`. -/
@[to_additive (attr := simps apply symm_apply)
/-- An `AddEquiv` that respects open sets is a `ContinuousAddEquiv`. -/]
/--
Definition of `toContinuousMulEquiv` / `toContinuousMulEquiv` 的定义

English:
definition toContinuousMulEquiv
  signature: : G ≃ₜ* H where
  body: e
  invFun := e.symm
  __ := e
  __ := e.toEquiv.toHomeomorph he

中文:
定义 toContinuousMulEquiv
  签名: : G ≃ₜ* H where
  定义体: e
  invFun := e.symm
  __ := e
  __ := e.toEquiv.toHomeomorph he
-/
def toContinuousMulEquiv : G ≃ₜ* H where
  toFun := e
  invFun := e.symm
  __ := e
  __ := e.toEquiv.toHomeomorph he

variable {e}

@[to_additive, simp]
/--
lemma `toMulEquiv_toContinuousMulEquiv` / 引理 `toMulEquiv_toContinuousMulEquiv`

English:
lemma toMulEquiv_toContinuousMulEquiv
  statement: (e.toContinuousMulEquiv he : G ≃* H) = e
  proof: rfl

中文:
引理 toMulEquiv_toContinuousMulEquiv
  结论: (e.toContinuousMulEquiv he : G ≃* H) = e
  证明: rfl
-/
lemma toMulEquiv_toContinuousMulEquiv : (e.toContinuousMulEquiv he : G ≃* H) = e :=
  rfl

/--
lemma `toHomeomorph_toContinuousMulEquiv` / 引理 `toHomeomorph_toContinuousMulEquiv`

English:
lemma toHomeomorph_toContinuousMulEquiv
  proof: rfl

@[to_additive]

中文:
引理 toHomeomorph_toContinuousMulEquiv
  证明: rfl

@[to_additive]
-/
@[to_additive, simp] lemma toHomeomorph_toContinuousMulEquiv :
    (e.toContinuousMulEquiv he : G ≃ₜ H) = e.toHomeomorph he :=
  rfl

@[to_additive]
/--
lemma `symm_toContinuousMulEquiv` / 引理 `symm_toContinuousMulEquiv`

English:
lemma symm_toContinuousMulEquiv
  proof: rfl

中文:
引理 symm_toContinuousMulEquiv
  证明: rfl
-/
lemma symm_toContinuousMulEquiv :
    (e.toContinuousMulEquiv he).symm = e.symm.toContinuousMulEquiv
      (fun s => by convert! (he _).symm; exact (e.preimage_symm_preimage s).symm) :=
  rfl

end MulEquiv

end

end
