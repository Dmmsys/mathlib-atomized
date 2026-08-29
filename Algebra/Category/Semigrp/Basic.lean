/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.Algebra.PEmptyInstances
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Category instances for `Mul`, `Add`, `Semigroup` and `AddSemigroup`

We introduce the bundled categories:
* `MagmaCat`
* `AddMagmaCat`
* `Semigrp`
* `AddSemigrp`

along with the relevant forgetful functors between them.

This closely follows `Mathlib/Algebra/Category/MonCat/Basic.lean`.

## TODO

* Limits in these categories
* free/forgetful adjunctions
-/

@[expose] public section


universe u v

open CategoryTheory

/--
Definition of `AddMagmaCat` / `AddMagmaCat` 的定义

English:
structure AddMagmaCat
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - (carrier : Type u)
    - [str : Add carrier]

中文:
结构 AddMagmaCat
  参数: : Type (u + 1) where
  公理与运算 (2 个):
    - (carrier : 类型u)
    - [str : Add carrier]
-/
structure AddMagmaCat : Type (u + 1) where
  /-- The underlying additive magma. -/
  (carrier : Type u)
  [str : Add carrier]

/-- The category of magmas and magma morphisms. -/
@[to_additive]
/--
Definition of `MagmaCat` / `MagmaCat` 的定义

English:
structure MagmaCat
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - (carrier : Type u)
    - [str : Mul carrier]

中文:
结构 MagmaCat
  参数: : Type (u + 1) where
  公理与运算 (2 个):
    - (carrier : 类型u)
    - [str : Mul carrier]
-/
structure MagmaCat : Type (u + 1) where
  /-- The underlying magma. -/
  (carrier : Type u)
  [str : Mul carrier]

attribute [instance] AddMagmaCat.str MagmaCat.str

initialize_simps_projections AddMagmaCat (carrier -> coe, -str)
initialize_simps_projections MagmaCat (carrier -> coe, -str)

namespace MagmaCat

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort MagmaCat (Type u)
  body: ⟨MagmaCat.carrier⟩

中文:
实例 :
  签名: CoeSort MagmaCat (类型u)
  定义体: ⟨MagmaCat.carrier⟩

Depends on / 依赖: MagmaCat, MagmaCat.carrier, carrier
-/
instance : CoeSort MagmaCat (Type u) :=
  ⟨MagmaCat.carrier⟩

attribute [coe] AddMagmaCat.carrier MagmaCat.carrier

/-- Construct a bundled `MagmaCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddMagmaCat` from the underlying type and typeclass. -/]
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (M : Type u) [Mul M]
  body: ⟨M⟩

中文:
缩写 of
  签名: (M : 类型u) [Mul M]
  定义体: ⟨M⟩
-/
abbrev of (M : Type u) [Mul M] : MagmaCat := ⟨M⟩

end MagmaCat

/-- The type of morphisms in `AddMagmaCat R`. -/
@[ext]
/--
Definition of `AddMagmaCat.Hom` / `AddMagmaCat.Hom` 的定义

English:
structure AddMagmaCat.Hom
  parameters: (A B : AddMagmaCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->ₙ+ B

中文:
结构 AddMagmaCat.Hom
  参数: (A B : AddMagmaCat.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->ₙ+ B
-/
structure AddMagmaCat.Hom (A B : AddMagmaCat.{u}) where
  private mk ::
  /-- The underlying `AddHom`. -/
  hom' : A ->ₙ+ B

/-- The type of morphisms in `MagmaCat R`. -/
@[to_additive, ext]
/--
Definition of `MagmaCat.Hom` / `MagmaCat.Hom` 的定义

English:
structure MagmaCat.Hom
  parameters: (A B : MagmaCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->ₙ* B

中文:
结构 MagmaCat.Hom
  参数: (A B : MagmaCat.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->ₙ* B
-/
structure MagmaCat.Hom (A B : MagmaCat.{u}) where
  private mk ::
  /-- The underlying `MulHom`. -/
  hom' : A ->ₙ* B

namespace MagmaCat

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category MagmaCat.{u}
  body: Hom X Y
  id X := ⟨MulHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category MagmaCat.{u}
  定义体: Hom X Y
  id X := ⟨MulHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category MagmaCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MulHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory MagmaCat (· ->ₙ* ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: ConcreteCategory MagmaCat (· ->ₙ* ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory MagmaCat (· ->ₙ* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `MagmaCat` back into a `MulHom`. -/
@[to_additive /-- Turn a morphism in `AddMagmaCat` back into an `AddHom`. -/]
/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : MagmaCat.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := MagmaCat) f

中文:
缩写 Hom.hom
  签名: {X Y : MagmaCat.{u}} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := MagmaCat) f
-/
abbrev Hom.hom {X Y : MagmaCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := MagmaCat) f

/-- Typecheck a `MulHom` as a morphism in `MagmaCat`. -/
@[to_additive /-- Typecheck an `AddHom` as a morphism in `AddMagmaCat`. -/]
/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [Mul X] [Mul Y] (f : X ->ₙ* Y)
  body: ConcreteCategory.ofHom (C := MagmaCat) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [Mul X] [Mul Y] (f : X ->ₙ* Y)
  定义体: ConcreteCategory.ofHom (C := MagmaCat) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, MagmaCat
-/
abbrev ofHom {X Y : Type u} [Mul X] [Mul Y] (f : X ->ₙ* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := MagmaCat) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : MagmaCat.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddMagmaCat.Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (X Y : MagmaCat.{u}) (f : Hom X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddMagmaCat.Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : MagmaCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddMagmaCat.Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  given: {X : MagmaCat}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coe_id
  条件: {X : MagmaCat}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coe_id {X : MagmaCat} : (𝟙 X : X -> X) = id := rfl

@[to_additive (attr := simp)]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : MagmaCat} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]

中文:
引理 coe_comp
  条件: {X Y Z : MagmaCat} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
-/
lemma coe_comp {X Y Z : MagmaCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : MagmaCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

@[to_additive]

中文:
引理 ext
  条件: {X Y : MagmaCat} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

@[to_additive]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : MagmaCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (M : Type u) [Mul M]
  statement: (MagmaCat.of M : Type u) = M
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_of
  条件: (M : 类型u) [Mul M]
  结论: (MagmaCat.of M : 类型u) = M
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_of (M : Type u) [Mul M] : (MagmaCat.of M : Type u) = M := rfl

@[to_additive (attr := simp)]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {M : MagmaCat}
  statement: (𝟙 M : M ⟶ M).hom = MulHom.id M
  proof: rfl

中文:
引理 hom_id
  条件: {M : MagmaCat}
  结论: (𝟙 M : M ⟶ M).hom = MulHom.id M
  证明: rfl
-/
lemma hom_id {M : MagmaCat} : (𝟙 M : M ⟶ M).hom = MulHom.id M := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (M : MagmaCat) (x : M)
  proof: by simp

@[to_additive (attr := simp)]

中文:
引理 id_apply
  条件: (M : MagmaCat) (x : M)
  证明: by simp

@[to_additive (attr := simp)]
-/
lemma id_apply (M : MagmaCat) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[to_additive (attr := simp)]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T)
  proof: rfl

中文:
引理 hom_comp
  条件: {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T)
  证明: rfl
-/
lemma hom_comp {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) (x : M)
  proof: by simp

@[to_additive (attr := ext)]

中文:
引理 comp_apply
  条件: {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) (x : M)
  证明: by simp

@[to_additive (attr := ext)]
-/
lemma comp_apply {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {M N : MagmaCat} {f g : M ⟶ N} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[to_additive (attr := simp)]

中文:
引理 hom_ext
  条件: {M N : MagmaCat} {f g : M ⟶ N} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[to_additive (attr := simp)]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {M N : MagmaCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {M N : Type u} [Mul M] [Mul N] (f : M ->ₙ* N)
  statement: (ofHom f).hom = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 hom_ofHom
  条件: {M N : 类型u} [Mul M] [Mul N] (f : M ->ₙ* N)
  结论: (ofHom f).hom = f
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma hom_ofHom {M N : Type u} [Mul M] [Mul N] (f : M ->ₙ* N) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {M N : MagmaCat} (f : M ⟶ N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_hom
  条件: {M N : MagmaCat} (f : M ⟶ N)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_hom {M N : MagmaCat} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {M : Type u} [Mul M]
  statement: ofHom (MulHom.id M) = 𝟙 (of M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_id
  条件: {M : 类型u} [Mul M]
  结论: ofHom (MulHom.id M) = 𝟙 (of M)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_id {M : Type u} [Mul M] : ofHom (MulHom.id M) = 𝟙 (of M) := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {M N P : Type u} [Mul M] [Mul N] [Mul P]
  proof: rfl

@[to_additive]

中文:
引理 ofHom_comp
  结论: {M N P : 类型u} [Mul M] [Mul N] [Mul P]
  证明: rfl

@[to_additive]
-/
lemma ofHom_comp {M N P : Type u} [Mul M] [Mul N] [Mul P]
    (f : M ->ₙ* N) (g : N ->ₙ* P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} [Mul X] [Mul Y] (f : X ->ₙ* Y) (x : X)
  proof: rfl

@[to_additive]

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} [Mul X] [Mul Y] (f : X ->ₙ* Y) (x : X)
  证明: rfl

@[to_additive]
-/
lemma ofHom_apply {X Y : Type u} [Mul X] [Mul Y] (f : X ->ₙ* Y) (x : X) :
    (ofHom f) x = f x := rfl

@[to_additive]
/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {M N : MagmaCat} (e : M ≅ N) (x : M)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

@[to_additive]

中文:
引理 inv_hom_apply
  条件: {M N : MagmaCat} (e : M ≅ N) (x : M)
  结论: e.inv (e.hom x) = x
  证明: by
  simp

@[to_additive]
-/
lemma inv_hom_apply {M N : MagmaCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

@[to_additive]
/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {M N : MagmaCat} (e : M ≅ N) (s : N)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

@[to_additive (attr := simp)]

中文:
引理 hom_inv_apply
  条件: {M N : MagmaCat} (e : M ≅ N) (s : N)
  结论: e.hom (e.inv s) = s
  证明: by
  simp

@[to_additive (attr := simp)]
-/
lemma hom_inv_apply {M N : MagmaCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  simp

@[to_additive (attr := simp)]
/--
lemma `mulEquiv_coe_eq` / 引理 `mulEquiv_coe_eq`

English:
lemma mulEquiv_coe_eq
  given: {X Y : Type _} [Mul X] [Mul Y] (e : X ≃* Y)
  proof: rfl

@[to_additive]

中文:
引理 mulEquiv_coe_eq
  条件: {X Y : Type _} [Mul X] [Mul Y] (e : X ≃* Y)
  证明: rfl

@[to_additive]
-/
lemma mulEquiv_coe_eq {X Y : Type _} [Mul X] [Mul Y] (e : X ≃* Y) :
    (ofHom (e : X ->ₙ* Y)).hom = ↑e :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited MagmaCat
  body: ⟨MagmaCat.of PEmpty⟩

中文:
实例 :
  签名: Inhabited MagmaCat
  定义体: ⟨MagmaCat.of PEmpty⟩

Depends on / 依赖: MagmaCat, MagmaCat.of, PEmpty
-/
instance : Inhabited MagmaCat :=
  ⟨MagmaCat.of PEmpty⟩

end MagmaCat

/--
Definition of `AddSemigrp` / `AddSemigrp` 的定义

English:
structure AddSemigrp
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - (carrier : Type u)
    - [str : AddSemigroup carrier]

中文:
结构 AddSemigrp
  参数: : Type (u + 1) where
  公理与运算 (2 个):
    - (carrier : 类型u)
    - [str : AddSemigroup carrier]
-/
structure AddSemigrp : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddSemigroup carrier]

/-- The category of semigroups and semigroup morphisms. -/
@[to_additive]
/--
Definition of `Semigrp` / `Semigrp` 的定义

English:
structure Semigrp
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - (carrier : Type u)
    - [str : Semigroup carrier]

中文:
结构 Semigrp
  参数: : Type (u + 1) where
  公理与运算 (2 个):
    - (carrier : 类型u)
    - [str : Semigroup carrier]
-/
structure Semigrp : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : Semigroup carrier]

attribute [instance] AddSemigrp.str Semigrp.str

initialize_simps_projections AddSemigrp (carrier -> coe, -str)
initialize_simps_projections Semigrp (carrier -> coe, -str)

namespace Semigrp

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort Semigrp (Type u)
  body: ⟨Semigrp.carrier⟩

中文:
实例 :
  签名: CoeSort Semigrp (类型u)
  定义体: ⟨Semigrp.carrier⟩

Depends on / 依赖: Semigrp, Semigrp.carrier, carrier
-/
instance : CoeSort Semigrp (Type u) :=
  ⟨Semigrp.carrier⟩

attribute [coe] AddSemigrp.carrier Semigrp.carrier

/-- Construct a bundled `Semigrp` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddSemigrp` from the underlying type and typeclass. -/]
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (M : Type u) [Semigroup M]
  body: ⟨M⟩

中文:
缩写 of
  签名: (M : 类型u) [Semigroup M]
  定义体: ⟨M⟩
-/
abbrev of (M : Type u) [Semigroup M] : Semigrp := ⟨M⟩

end Semigrp

/-- The type of morphisms in `AddSemigrp R`. -/
@[ext]
/--
Definition of `AddSemigrp.Hom` / `AddSemigrp.Hom` 的定义

English:
structure AddSemigrp.Hom
  parameters: (A B : AddSemigrp.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->ₙ+ B

中文:
结构 AddSemigrp.Hom
  参数: (A B : AddSemigrp.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->ₙ+ B
-/
structure AddSemigrp.Hom (A B : AddSemigrp.{u}) where
  private mk ::
  /-- The underlying `AddHom`. -/
  hom' : A ->ₙ+ B

/-- The type of morphisms in `Semigrp R`. -/
@[to_additive, ext]
/--
Definition of `Semigrp.Hom` / `Semigrp.Hom` 的定义

English:
structure Semigrp.Hom
  parameters: (A B : Semigrp.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->ₙ* B

中文:
结构 Semigrp.Hom
  参数: (A B : Semigrp.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->ₙ* B
-/
structure Semigrp.Hom (A B : Semigrp.{u}) where
  private mk ::
  /-- The underlying `MulHom`. -/
  hom' : A ->ₙ* B

namespace Semigrp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category Semigrp.{u}
  body: Hom X Y
  id X := ⟨MulHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category Semigrp.{u}
  定义体: Hom X Y
  id X := ⟨MulHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category Semigrp.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MulHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory Semigrp (· ->ₙ* ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: ConcreteCategory Semigrp (· ->ₙ* ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory Semigrp (· ->ₙ* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `Semigrp` back into a `MulHom`. -/
@[to_additive /-- Turn a morphism in `AddSemigrp` back into an `AddHom`. -/]
/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : Semigrp.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := Semigrp) f

中文:
缩写 Hom.hom
  签名: {X Y : Semigrp.{u}} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := Semigrp) f
-/
abbrev Hom.hom {X Y : Semigrp.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Semigrp) f

/-- Typecheck a `MulHom` as a morphism in `Semigrp`. -/
@[to_additive /-- Typecheck an `AddHom` as a morphism in `AddSemigrp`. -/]
/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X ->ₙ* Y)
  body: ConcreteCategory.ofHom (C := Semigrp) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [Semigroup X] [Semigroup Y] (f : X ->ₙ* Y)
  定义体: ConcreteCategory.ofHom (C := Semigrp) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, Semigrp
-/
abbrev ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X ->ₙ* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Semigrp) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : Semigrp.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddSemigrp.Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (X Y : Semigrp.{u}) (f : Hom X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddSemigrp.Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : Semigrp.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddSemigrp.Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  given: {X : Semigrp}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coe_id
  条件: {X : Semigrp}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coe_id {X : Semigrp} : (𝟙 X : X -> X) = id := rfl

@[to_additive (attr := simp)]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : Semigrp} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]

中文:
引理 coe_comp
  条件: {X Y Z : Semigrp} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
-/
lemma coe_comp {X Y Z : Semigrp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : Semigrp} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

@[to_additive]

中文:
引理 ext
  条件: {X Y : Semigrp} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

@[to_additive]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : Semigrp} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (R : Type u) [Semigroup R]
  statement: ↑(Semigrp.of R) = R
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_of
  条件: (R : 类型u) [Semigroup R]
  结论: ↑(Semigrp.of R) = R
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_of (R : Type u) [Semigroup R] : ↑(Semigrp.of R) = R :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : Semigrp}
  statement: (𝟙 X : X ⟶ X).hom = MulHom.id X
  proof: rfl

中文:
引理 hom_id
  条件: {X : Semigrp}
  结论: (𝟙 X : X ⟶ X).hom = MulHom.id X
  证明: rfl
-/
lemma hom_id {X : Semigrp} : (𝟙 X : X ⟶ X).hom = MulHom.id X := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : Semigrp) (x : X)
  proof: by simp

@[to_additive (attr := simp)]

中文:
引理 id_apply
  条件: (X : Semigrp) (x : X)
  证明: by simp

@[to_additive (attr := simp)]
-/
lemma id_apply (X : Semigrp) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[to_additive (attr := simp)]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T)
  证明: rfl
-/
lemma hom_comp {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) (x : X)
  proof: by simp

@[to_additive (attr := ext)]

中文:
引理 comp_apply
  条件: {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) (x : X)
  证明: by simp

@[to_additive (attr := ext)]
-/
lemma comp_apply {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : Semigrp} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[to_additive (attr := simp)]

中文:
引理 hom_ext
  条件: {X Y : Semigrp} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[to_additive (attr := simp)]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : Semigrp} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X ->ₙ* Y)
  statement: (ofHom f).hom = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 hom_ofHom
  条件: {X Y : 类型u} [Semigroup X] [Semigroup Y] (f : X ->ₙ* Y)
  结论: (ofHom f).hom = f
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma hom_ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X ->ₙ* Y) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : Semigrp} (f : X ⟶ Y)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_hom
  条件: {X Y : Semigrp} (f : X ⟶ Y)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_hom {X Y : Semigrp} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [Semigroup X]
  statement: ofHom (MulHom.id X) = 𝟙 (of X)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_id
  条件: {X : 类型u} [Semigroup X]
  结论: ofHom (MulHom.id X) = 𝟙 (of X)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_id {X : Type u} [Semigroup X] : ofHom (MulHom.id X) = 𝟙 (of X) := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [Semigroup X] [Semigroup Y] [Semigroup Z]
  proof: rfl

@[to_additive]

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [Semigroup X] [Semigroup Y] [Semigroup Z]
  证明: rfl

@[to_additive]

Depends on / 依赖: F.obj
-/
lemma ofHom_comp {X Y Z : Type u} [Semigroup X] [Semigroup Y] [Semigroup Z]
    (f : X ->ₙ* Y) (g : Y ->ₙ* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X ->ₙ* Y) (x : X)
  proof: rfl

@[to_additive]

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} [Semigroup X] [Semigroup Y] (f : X ->ₙ* Y) (x : X)
  证明: rfl

@[to_additive]
-/
lemma ofHom_apply {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X ->ₙ* Y) (x : X) :
    (ofHom f) x = f x := rfl

@[to_additive]
/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {X Y : Semigrp} (e : X ≅ Y) (x : X)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

@[to_additive]

中文:
引理 inv_hom_apply
  条件: {X Y : Semigrp} (e : X ≅ Y) (x : X)
  结论: e.inv (e.hom x) = x
  证明: by
  simp

@[to_additive]
-/
lemma inv_hom_apply {X Y : Semigrp} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

@[to_additive]
/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {X Y : Semigrp} (e : X ≅ Y) (s : Y)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

@[to_additive (attr := simp)]

中文:
引理 hom_inv_apply
  条件: {X Y : Semigrp} (e : X ≅ Y) (s : Y)
  结论: e.hom (e.inv s) = s
  证明: by
  simp

@[to_additive (attr := simp)]
-/
lemma hom_inv_apply {X Y : Semigrp} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

@[to_additive (attr := simp)]
/--
lemma `mulEquiv_coe_eq` / 引理 `mulEquiv_coe_eq`

English:
lemma mulEquiv_coe_eq
  given: {X Y : Type _} [Semigroup X] [Semigroup Y] (e : X ≃* Y)
  proof: rfl

@[to_additive]

中文:
引理 mulEquiv_coe_eq
  条件: {X Y : Type _} [Semigroup X] [Semigroup Y] (e : X ≃* Y)
  证明: rfl

@[to_additive]
-/
lemma mulEquiv_coe_eq {X Y : Type _} [Semigroup X] [Semigroup Y] (e : X ≃* Y) :
    (ofHom (e : X ->ₙ* Y)).hom = ↑e :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Semigrp
  body: ⟨Semigrp.of PEmpty⟩

@[to_additive]

中文:
实例 :
  签名: Inhabited Semigrp
  定义体: ⟨Semigrp.of PEmpty⟩

@[to_additive]

Depends on / 依赖: PEmpty, Semigrp, Semigrp.of
-/
instance : Inhabited Semigrp :=
  ⟨Semigrp.of PEmpty⟩

@[to_additive]
/--
Instance `hasForgetToMagmaCat` / 实例 `hasForgetToMagmaCat`

English:
instance hasForgetToMagmaCat
  signature: : HasForget₂ Semigrp MagmaCat where
  body: { obj R := MagmaCat.of R
      map f := MagmaCat.ofHom f.hom }

中文:
实例 hasForgetToMagmaCat
  签名: : HasForget₂ Semigrp MagmaCat where
  定义体: { obj R := MagmaCat.of R
      map f := MagmaCat.ofHom f.hom }

Depends on / 依赖: MagmaCat, MagmaCat.of, MagmaCat.ofHom, f.hom
-/
instance hasForgetToMagmaCat : HasForget₂ Semigrp MagmaCat where
  forget₂ :=
    { obj R := MagmaCat.of R
      map f := MagmaCat.ofHom f.hom }

end Semigrp

variable {X Y : Type u}

section

variable [Mul X] [Mul Y]

/-- Build an isomorphism in the category `MagmaCat` from a `MulEquiv` between `Mul`s. -/
@[to_additive (attr := simps)
      /-- Build an isomorphism in the category `AddMagmaCat` from an `AddEquiv` between `Add`s. -/]
/--
Definition of `MulEquiv.toMagmaCatIso` / `MulEquiv.toMagmaCatIso` 的定义

English:
definition MulEquiv.toMagmaCatIso
  signature: (e : X ≃* Y)
  body: MagmaCat.ofHom e.toMulHom
  inv := MagmaCat.ofHom e.symm.toMulHom

中文:
定义 MulEquiv.toMagmaCatIso
  签名: (e : X ≃* Y)
  定义体: MagmaCat.ofHom e.toMulHom
  inv := MagmaCat.ofHom e.symm.toMulHom

Depends on / 依赖: MagmaCat, MagmaCat.ofHom, e.toMulHom, toMulHom
-/
def MulEquiv.toMagmaCatIso (e : X ≃* Y) : MagmaCat.of X ≅ MagmaCat.of Y where
  hom := MagmaCat.ofHom e.toMulHom
  inv := MagmaCat.ofHom e.symm.toMulHom

end

section

variable [Semigroup X] [Semigroup Y]

/-- Build an isomorphism in the category `Semigroup` from a `MulEquiv` between `Semigroup`s. -/
@[to_additive (attr := simps)
  /-- Build an isomorphism in the category
  `AddSemigroup` from an `AddEquiv` between `AddSemigroup`s. -/]
/--
Definition of `MulEquiv.toSemigrpIso` / `MulEquiv.toSemigrpIso` 的定义

English:
definition MulEquiv.toSemigrpIso
  signature: (e : X ≃* Y)
  body: Semigrp.ofHom e.toMulHom
  inv := Semigrp.ofHom e.symm.toMulHom

中文:
定义 MulEquiv.toSemigrpIso
  签名: (e : X ≃* Y)
  定义体: Semigrp.ofHom e.toMulHom
  inv := Semigrp.ofHom e.symm.toMulHom

Depends on / 依赖: Semigrp, Semigrp.ofHom, e.toMulHom, toMulHom
-/
def MulEquiv.toSemigrpIso (e : X ≃* Y) : Semigrp.of X ≅ Semigrp.of Y where
  hom := Semigrp.ofHom e.toMulHom
  inv := Semigrp.ofHom e.symm.toMulHom

end

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `MagmaCat`. -/
@[to_additive
      /-- Build an `AddEquiv` from an isomorphism in the category `AddMagmaCat`. -/]
/--
Definition of `magmaCatIsoToMulEquiv` / `magmaCatIsoToMulEquiv` 的定义

English:
definition magmaCatIsoToMulEquiv
  signature: {X Y : MagmaCat} (i : X ≅ Y)
  body: MulHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

中文:
定义 magmaCatIsoToMulEquiv
  签名: {X Y : MagmaCat} (i : X ≅ Y)
  定义体: MulHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

Depends on / 依赖: MulHom, MulHom.toMulEquiv, i.hom.hom, i.inv.hom, toMulEquiv
-/
def magmaCatIsoToMulEquiv {X Y : MagmaCat} (i : X ≅ Y) : X ≃* Y :=
  MulHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `MulEquiv` from an isomorphism in the category `Semigroup`. -/
@[to_additive
  /-- Build an `AddEquiv` from an isomorphism in the category `AddSemigroup`. -/]
/--
Definition of `semigrpIsoToMulEquiv` / `semigrpIsoToMulEquiv` 的定义

English:
definition semigrpIsoToMulEquiv
  signature: {X Y : Semigrp} (i : X ≅ Y)
  body: MulHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

中文:
定义 semigrpIsoToMulEquiv
  签名: {X Y : Semigrp} (i : X ≅ Y)
  定义体: MulHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

Depends on / 依赖: MulHom, MulHom.toMulEquiv, i.hom.hom, i.inv.hom, toMulEquiv
-/
def semigrpIsoToMulEquiv {X Y : Semigrp} (i : X ≅ Y) : X ≃* Y :=
  MulHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

end CategoryTheory.Iso

/-- multiplicative equivalences between `Mul`s are the same as (isomorphic to) isomorphisms
in `MagmaCat` -/
@[to_additive
    /-- additive equivalences between `Add`s are the same
    as (isomorphic to) isomorphisms in `AddMagmaCat` -/]
/--
Definition of `mulEquivIsoMagmaIso` / `mulEquivIsoMagmaIso` 的定义

English:
definition mulEquivIsoMagmaIso
  signature: {X Y : Type u} [Mul X] [Mul Y]
  body: ↾fun e => e.toMagmaCatIso
  inv := ↾fun i => i.magmaCatIsoToMulEquiv

中文:
定义 mulEquivIsoMagmaIso
  签名: {X Y : 类型u} [Mul X] [Mul Y]
  定义体: ↾fun e => e.toMagmaCatIso
  inv := ↾fun i => i.magmaCatIsoToMulEquiv

Depends on / 依赖: e.toMagmaCatIso, toMagmaCatIso
-/
def mulEquivIsoMagmaIso {X Y : Type u} [Mul X] [Mul Y] :
    (X ≃* Y) ≅ (MagmaCat.of X ≅ MagmaCat.of Y) where
  hom := ↾fun e => e.toMagmaCatIso
  inv := ↾fun i => i.magmaCatIsoToMulEquiv

/-- multiplicative equivalences between `Semigroup`s are the same as (isomorphic to) isomorphisms
in `Semigroup` -/
@[to_additive
  /-- additive equivalences between `AddSemigroup`s are
  the same as (isomorphic to) isomorphisms in `AddSemigroup` -/]
/--
Definition of `mulEquivIsoSemigrpIso` / `mulEquivIsoSemigrpIso` 的定义

English:
definition mulEquivIsoSemigrpIso
  signature: {X Y : Type u} [Semigroup X] [Semigroup Y]
  body: ↾fun e => e.toSemigrpIso
  inv := ↾fun i => i.semigrpIsoToMulEquiv

@[to_additive]

中文:
定义 mulEquivIsoSemigrpIso
  签名: {X Y : 类型u} [Semigroup X] [Semigroup Y]
  定义体: ↾fun e => e.toSemigrpIso
  inv := ↾fun i => i.semigrpIsoToMulEquiv

@[to_additive]

Depends on / 依赖: e.toSemigrpIso, toSemigrpIso
-/
def mulEquivIsoSemigrpIso {X Y : Type u} [Semigroup X] [Semigroup Y] :
    (X ≃* Y) ≅ (Semigrp.of X ≅ Semigrp.of Y) where
  hom := ↾fun e => e.toSemigrpIso
  inv := ↾fun i => i.semigrpIsoToMulEquiv

@[to_additive]
/--
Instance `MagmaCat.forgetReflectsIsos` / 实例 `MagmaCat.forgetReflectsIsos`

English:
instance MagmaCat.forgetReflectsIsos
  signature: : (forget MagmaCat.{u}).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget MagmaCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toMagmaCatIso.isIso_hom

@[to_additive]

中文:
实例 MagmaCat.forgetReflectsIsos
  签名: : (forget MagmaCat.{u}).ReflectsIsomorphisms where
  定义体: by
    let i := asIso ((forget MagmaCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toMagmaCatIso.isIso_hom

@[to_additive]

Depends on / 依赖: MagmaCat, coyonedaAdj, e.toMagmaCatIso.isIso_hom, f.hom, forget, i.toEquiv, isIso_hom, toEquiv, toMagmaCatIso
-/
instance MagmaCat.forgetReflectsIsos : (forget MagmaCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget MagmaCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toMagmaCatIso.isIso_hom

@[to_additive]
/--
Instance `Semigrp.forgetReflectsIsos` / 实例 `Semigrp.forgetReflectsIsos`

English:
instance Semigrp.forgetReflectsIsos
  signature: : (forget Semigrp.{u}).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget Semigrp).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toSemigrpIso.isIso_hom

中文:
实例 Semigrp.forgetReflectsIsos
  签名: : (forget Semigrp.{u}).ReflectsIsomorphisms where
  定义体: by
    let i := asIso ((forget Semigrp).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toSemigrpIso.isIso_hom

Depends on / 依赖: Semigrp, e.toSemigrpIso.isIso_hom, f.hom, forget, i.toEquiv, isIso_hom, toEquiv, toSemigrpIso
-/
instance Semigrp.forgetReflectsIsos : (forget Semigrp.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget Semigrp).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toSemigrpIso.isIso_hom

/-- Ensure that `forget₂ CommMonCat MonCat` automatically reflects isomorphisms. -/
@[to_additive /-- Ensure that `forget₂ AddCommMonCat AddMonCat` automatically reflects
isomorphisms. -/]
/--
Instance `Semigrp.forget₂_full` / 实例 `Semigrp.forget₂_full`

English:
instance Semigrp.forget₂_full
  signature: : (forget₂ Semigrp MagmaCat).Full where
  body: ⟨ofHom f.hom, rfl⟩

中文:
实例 Semigrp.forget₂_full
  签名: : (forget₂ Semigrp MagmaCat).Full where
  定义体: ⟨ofHom f.hom, rfl⟩

Depends on / 依赖: f.hom
-/
instance Semigrp.forget₂_full : (forget₂ Semigrp MagmaCat).Full where
  map_surjective f := ⟨ofHom f.hom, rfl⟩

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/

example : (forget₂ Semigrp MagmaCat).ReflectsIsomorphisms := inferInstance
