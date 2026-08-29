/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.ULift
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Category instances for `Monoid`, `AddMonoid`, `CommMonoid`, and `AddCommMonoid`.

We introduce the bundled categories:
* `MonCat`
* `AddMonCat`
* `CommMonCat`
* `AddCommMonCat`

along with the relevant forgetful functors between them.
-/

@[expose] public section

assert_not_exists MonoidWithZero

universe u v

open CategoryTheory

/--
Definition of `AddMonCat` / `AddMonCat` 的定义

English:
structure AddMonCat
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - (carrier : Type u)
    - [str : AddMonoid carrier]

中文:
结构 AddMonCat
  参数: : Type (u + 1) where
  公理与运算 (2 个):
    - (carrier : 类型u)
    - [str : AddMonoid carrier]
-/
structure AddMonCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddMonoid carrier]

/-- The category of monoids and monoid morphisms. -/
@[to_additive AddMonCat]
/--
Definition of `MonCat` / `MonCat` 的定义

English:
structure MonCat
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - (carrier : Type u)
    - [str : Monoid carrier]

中文:
结构 MonCat
  参数: : Type (u + 1) where
  公理与运算 (2 个):
    - (carrier : 类型u)
    - [str : Monoid carrier]
-/
structure MonCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : Monoid carrier]

attribute [instance] AddMonCat.str MonCat.str

initialize_simps_projections AddMonCat (carrier -> coe, -str)
initialize_simps_projections MonCat (carrier -> coe, -str)

namespace MonCat

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort MonCat (Type u)
  body: ⟨MonCat.carrier⟩

中文:
实例 :
  签名: CoeSort MonCat (类型u)
  定义体: ⟨MonCat.carrier⟩

Depends on / 依赖: MonCat, MonCat.carrier, carrier
-/
instance : CoeSort MonCat (Type u) :=
  ⟨MonCat.carrier⟩

attribute [coe] AddMonCat.carrier MonCat.carrier

/-- Construct a bundled `MonCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddMonCat` from the underlying type and typeclass. -/]
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (M : Type u) [Monoid M]
  body: ⟨M⟩

中文:
缩写 of
  签名: (M : 类型u) [Monoid M]
  定义体: ⟨M⟩
-/
abbrev of (M : Type u) [Monoid M] : MonCat := ⟨M⟩

end MonCat

/-- The type of morphisms in `AddMonCat`. -/
@[ext]
/--
Definition of `AddMonCat.Hom` / `AddMonCat.Hom` 的定义

English:
structure AddMonCat.Hom
  parameters: (A B : AddMonCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->+ B

中文:
结构 AddMonCat.Hom
  参数: (A B : AddMonCat.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->+ B
-/
structure AddMonCat.Hom (A B : AddMonCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A ->+ B

/-- The type of morphisms in `MonCat`. -/
@[to_additive, ext]
/--
Definition of `MonCat.Hom` / `MonCat.Hom` 的定义

English:
structure MonCat.Hom
  parameters: (A B : MonCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->* B

中文:
结构 MonCat.Hom
  参数: (A B : MonCat.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->* B
-/
structure MonCat.Hom (A B : MonCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A ->* B

namespace MonCat

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category MonCat.{u}
  body: Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category MonCat.{u}
  定义体: Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category MonCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory MonCat (· ->* ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: ConcreteCategory MonCat (· ->* ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory MonCat (· ->* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `MonCat` back into a `MonoidHom`. -/
@[to_additive /-- Turn a morphism in `AddMonCat` back into an `AddMonoidHom`. -/]
/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : MonCat.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := MonCat) f

中文:
缩写 Hom.hom
  签名: {X Y : MonCat.{u}} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := MonCat) f
-/
abbrev Hom.hom {X Y : MonCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := MonCat) f

/-- Typecheck a `MonoidHom` as a morphism in `MonCat`. -/
@[to_additive /-- Typecheck an `AddMonoidHom` as a morphism in `AddMonCat`. -/]
/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [Monoid X] [Monoid Y] (f : X ->* Y)
  body: ConcreteCategory.ofHom (C := MonCat) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [Monoid X] [Monoid Y] (f : X ->* Y)
  定义体: ConcreteCategory.ofHom (C := MonCat) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, MonCat
-/
abbrev ofHom {X Y : Type u} [Monoid X] [Monoid Y] (f : X ->* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := MonCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
@[to_additive /-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/]
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : MonCat.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddMonCat.Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (X Y : MonCat.{u}) (f : Hom X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddMonCat.Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : MonCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddMonCat.Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  given: {X : MonCat}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coe_id
  条件: {X : MonCat}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coe_id {X : MonCat} : (𝟙 X : X -> X) = id := rfl

@[to_additive (attr := simp)]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : MonCat} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coe_comp
  条件: {X Y Z : MonCat} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coe_comp {X Y Z : MonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[to_additive (attr := simp)]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {X Y : MonCat} (f : X ⟶ Y)
  proof: rfl

@[to_additive (attr := ext)]

中文:
引理 forget_map
  条件: {X Y : MonCat} (f : X ⟶ Y)
  证明: rfl

@[to_additive (attr := ext)]
-/
lemma forget_map {X Y : MonCat} (f : X ⟶ Y) :
    (forget MonCat).map f = (f : _ -> _) := rfl

@[to_additive (attr := ext)]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : MonCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

@[to_additive]

中文:
引理 ext
  条件: {X Y : MonCat} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

@[to_additive]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : MonCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (M : Type u) [Monoid M]
  statement: (MonCat.of M : Type u) = M
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_of
  条件: (M : 类型u) [Monoid M]
  结论: (MonCat.of M : 类型u) = M
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_of (M : Type u) [Monoid M] : (MonCat.of M : Type u) = M := rfl

@[to_additive (attr := simp)]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {M : MonCat}
  statement: (𝟙 M : M ⟶ M).hom = MonoidHom.id M
  proof: rfl

中文:
引理 hom_id
  条件: {M : MonCat}
  结论: (𝟙 M : M ⟶ M).hom = MonoidHom.id M
  证明: rfl
-/
lemma hom_id {M : MonCat} : (𝟙 M : M ⟶ M).hom = MonoidHom.id M := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (M : MonCat) (x : M)
  proof: by simp

@[to_additive (attr := simp)]

中文:
引理 id_apply
  条件: (M : MonCat) (x : M)
  证明: by simp

@[to_additive (attr := simp)]
-/
lemma id_apply (M : MonCat) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[to_additive (attr := simp)]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T)
  proof: rfl

中文:
引理 hom_comp
  条件: {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T)
  证明: rfl
-/
lemma hom_comp {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M)
  proof: by simp

@[to_additive (attr := ext)]

中文:
引理 comp_apply
  条件: {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M)
  证明: by simp

@[to_additive (attr := ext)]
-/
lemma comp_apply {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {M N : MonCat} {f g : M ⟶ N} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[to_additive (attr := simp)]

中文:
引理 hom_ext
  条件: {M N : MonCat} {f g : M ⟶ N} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[to_additive (attr := simp)]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {M N : MonCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {M N : Type u} [Monoid M] [Monoid N] (f : M ->* N)
  statement: (ofHom f).hom = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 hom_ofHom
  条件: {M N : 类型u} [Monoid M] [Monoid N] (f : M ->* N)
  结论: (ofHom f).hom = f
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma hom_ofHom {M N : Type u} [Monoid M] [Monoid N] (f : M ->* N) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {M N : MonCat} (f : M ⟶ N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_hom
  条件: {M N : MonCat} (f : M ⟶ N)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_hom {M N : MonCat} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {M : Type u} [Monoid M]
  statement: ofHom (MonoidHom.id M) = 𝟙 (of M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_id
  条件: {M : 类型u} [Monoid M]
  结论: ofHom (MonoidHom.id M) = 𝟙 (of M)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_id {M : Type u} [Monoid M] : ofHom (MonoidHom.id M) = 𝟙 (of M) := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {M N P : Type u} [Monoid M] [Monoid N] [Monoid P]
  proof: rfl

@[to_additive]

中文:
引理 ofHom_comp
  结论: {M N P : 类型u} [Monoid M] [Monoid N] [Monoid P]
  证明: rfl

@[to_additive]
-/
lemma ofHom_comp {M N P : Type u} [Monoid M] [Monoid N] [Monoid P]
    (f : M ->* N) (g : N ->* P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} [Monoid X] [Monoid Y] (f : X ->* Y) (x : X)
  proof: rfl

@[to_additive]

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} [Monoid X] [Monoid Y] (f : X ->* Y) (x : X)
  证明: rfl

@[to_additive]
-/
lemma ofHom_apply {X Y : Type u} [Monoid X] [Monoid Y] (f : X ->* Y) (x : X) :
    (ofHom f) x = f x := rfl

@[to_additive]
/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {M N : MonCat} (e : M ≅ N) (x : M)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

@[to_additive]

中文:
引理 inv_hom_apply
  条件: {M N : MonCat} (e : M ≅ N) (x : M)
  结论: e.inv (e.hom x) = x
  证明: by
  simp

@[to_additive]
-/
lemma inv_hom_apply {M N : MonCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

@[to_additive]
/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {M N : MonCat} (e : M ≅ N) (s : N)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

@[to_additive]

中文:
引理 hom_inv_apply
  条件: {M N : MonCat} (e : M ≅ N) (s : N)
  结论: e.hom (e.inv s) = s
  证明: by
  simp

@[to_additive]
-/
lemma hom_inv_apply {M N : MonCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  simp

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited MonCat
  body: -- The default instance for `Monoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _
    (@CommGroup.toGroup _ PUnit.commGroup)))⟩

@[to_additive]

中文:
实例 :
  签名: Inhabited MonCat
  定义体: -- The default instance for `Monoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _
    (@CommGroup.toGroup _ PUnit.commGroup)))⟩

@[to_additive]
-/
instance : Inhabited MonCat :=
  -- The default instance for `Monoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _
    (@CommGroup.toGroup _ PUnit.commGroup)))⟩

@[to_additive]
instance (X Y : MonCat.{u}) : One (X ⟶ Y) := ⟨ofHom 1⟩

@[to_additive (attr := simp)]
/--
lemma `hom_one` / 引理 `hom_one`

English:
lemma hom_one
  given: (X Y : MonCat.{u})
  statement: (1 : X ⟶ Y).hom = 1
  proof: rfl

@[to_additive]

中文:
引理 hom_one
  条件: (X Y : MonCat.{u})
  结论: (1 : X ⟶ Y).hom = 1
  证明: rfl

@[to_additive]
-/
lemma hom_one (X Y : MonCat.{u}) : (1 : X ⟶ Y).hom = 1 := rfl

@[to_additive]
/--
lemma `oneHom_apply` / 引理 `oneHom_apply`

English:
lemma oneHom_apply
  given: (X Y : MonCat.{u}) (x : X)
  statement: (1 : X ⟶ Y).hom x = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 oneHom_apply
  条件: (X Y : MonCat.{u}) (x : X)
  结论: (1 : X ⟶ Y).hom x = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma oneHom_apply (X Y : MonCat.{u}) (x : X) : (1 : X ⟶ Y).hom x = 1 := rfl

@[to_additive (attr := simp)]
/--
lemma `one_of` / 引理 `one_of`

English:
lemma one_of
  given: {A : Type*} [Monoid A]
  statement: (1 : MonCat.of A) = (1 : A)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 one_of
  条件: {A : 类型} [Monoid A]
  结论: (1 : MonCat.of A) = (1 : A)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma one_of {A : Type*} [Monoid A] : (1 : MonCat.of A) = (1 : A) := rfl

@[to_additive (attr := simp)]
/--
lemma `mul_of` / 引理 `mul_of`

English:
lemma mul_of
  given: {A : Type*} [Monoid A] (a b : A)
  proof: rfl

中文:
引理 mul_of
  条件: {A : 类型} [Monoid A] (a b : A)
  证明: rfl
-/
lemma mul_of {A : Type*} [Monoid A] (a b : A) :
    @HMul.hMul (MonCat.of A) (MonCat.of A) (MonCat.of A) _ a b = a * b := rfl

/-- Universe lift functor for monoids. -/
@[to_additive (attr := simps)
  /-- Universe lift functor for additive monoids. -/]
/--
Definition of `uliftFunctor` / `uliftFunctor` 的定义

English:
definition uliftFunctor
  signature: : MonCat.{v} ⥤ MonCat.{max v u} where
  body: MonCat.of (ULift.{u, v} X)
map {_ _} f := MonCat.ofHom
MulEquiv.ulift.symm.toMonoidHom.comp f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

中文:
定义 uliftFunctor
  签名: : MonCat.{v} ⥤ MonCat.{max v u} where
  定义体: MonCat.of (ULift.{u, v} X)
map {_ _} f := MonCat.ofHom
MulEquiv.ulift.symm.toMonoidHom.comp f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

Depends on / 依赖: MonCat, MonCat.of
-/
def uliftFunctor : MonCat.{v} ⥤ MonCat.{max v u} where
  obj X := MonCat.of (ULift.{u, v} X)
map {_ _} f := MonCat.ofHom
MulEquiv.ulift.symm.toMonoidHom.comp f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end MonCat

/--
Definition of `AddCommMonCat` / `AddCommMonCat` 的定义

English:
structure AddCommMonCat
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - (carrier : Type u)
    - [str : AddCommMonoid carrier]

中文:
结构 AddCommMonCat
  参数: : Type (u + 1) where
  公理与运算 (2 个):
    - (carrier : 类型u)
    - [str : AddCommMonoid carrier]
-/
structure AddCommMonCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddCommMonoid carrier]

/-- The category of commutative monoids and monoid morphisms. -/
@[to_additive AddCommMonCat]
/--
Definition of `CommMonCat` / `CommMonCat` 的定义

English:
structure CommMonCat
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - (carrier : Type u)
    - [str : CommMonoid carrier]

中文:
结构 CommMonCat
  参数: : Type (u + 1) where
  公理与运算 (2 个):
    - (carrier : 类型u)
    - [str : CommMonoid carrier]
-/
structure CommMonCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : CommMonoid carrier]

attribute [instance] AddCommMonCat.str CommMonCat.str

initialize_simps_projections AddCommMonCat (carrier -> coe, -str)
initialize_simps_projections CommMonCat (carrier -> coe, -str)

namespace CommMonCat

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort CommMonCat (Type u)
  body: ⟨CommMonCat.carrier⟩

中文:
实例 :
  签名: CoeSort CommMonCat (类型u)
  定义体: ⟨CommMonCat.carrier⟩

Depends on / 依赖: CommMonCat, CommMonCat.carrier, carrier
-/
instance : CoeSort CommMonCat (Type u) :=
  ⟨CommMonCat.carrier⟩

attribute [coe] AddCommMonCat.carrier CommMonCat.carrier

/-- Construct a bundled `CommMonCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddCommMonCat` from the underlying type and typeclass. -/]
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (M : Type u) [CommMonoid M]
  body: ⟨M⟩

中文:
缩写 of
  签名: (M : 类型u) [CommMonoid M]
  定义体: ⟨M⟩
-/
abbrev of (M : Type u) [CommMonoid M] : CommMonCat := ⟨M⟩

end CommMonCat

/-- The type of morphisms in `AddCommMonCat`. -/
@[ext]
/--
Definition of `AddCommMonCat.Hom` / `AddCommMonCat.Hom` 的定义

English:
structure AddCommMonCat.Hom
  parameters: (A B : AddCommMonCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->+ B

中文:
结构 AddCommMonCat.Hom
  参数: (A B : AddCommMonCat.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->+ B
-/
structure AddCommMonCat.Hom (A B : AddCommMonCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A ->+ B

/-- The type of morphisms in `CommMonCat`. -/
@[to_additive, ext]
/--
Definition of `CommMonCat.Hom` / `CommMonCat.Hom` 的定义

English:
structure CommMonCat.Hom
  parameters: (A B : CommMonCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->* B

中文:
结构 CommMonCat.Hom
  参数: (A B : CommMonCat.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->* B
-/
structure CommMonCat.Hom (A B : CommMonCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A ->* B

namespace CommMonCat

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category CommMonCat.{u}
  body: Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category CommMonCat.{u}
  定义体: Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category CommMonCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory CommMonCat (· ->* ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: ConcreteCategory CommMonCat (· ->* ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory CommMonCat (· ->* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommMonCat` back into a `MonoidHom`. -/
@[to_additive /-- Turn a morphism in `AddCommMonCat` back into an `AddMonoidHom`. -/]
/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : CommMonCat.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := CommMonCat) f

中文:
缩写 Hom.hom
  签名: {X Y : CommMonCat.{u}} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := CommMonCat) f
-/
abbrev Hom.hom {X Y : CommMonCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := CommMonCat) f

/-- Typecheck a `MonoidHom` as a morphism in `CommMonCat`. -/
@[to_additive /-- Typecheck an `AddMonoidHom` as a morphism in `AddCommMonCat`. -/]
/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X ->* Y)
  body: ConcreteCategory.ofHom (C := CommMonCat) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [CommMonoid X] [CommMonoid Y] (f : X ->* Y)
  定义体: ConcreteCategory.ofHom (C := CommMonCat) f

Depends on / 依赖: CommMonCat, ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X ->* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := CommMonCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
@[to_additive /-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/]
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : CommMonCat.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddCommMonCat.Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (X Y : CommMonCat.{u}) (f : Hom X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddCommMonCat.Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : CommMonCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddCommMonCat.Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  given: {X : CommMonCat}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coe_id
  条件: {X : CommMonCat}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coe_id {X : CommMonCat} : (𝟙 X : X -> X) = id := rfl

@[to_additive (attr := simp)]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : CommMonCat} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[deprecated (since := "2026-02-15")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]

中文:
引理 coe_comp
  条件: {X Y Z : CommMonCat} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[deprecated (since := "2026-02-15")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
-/
lemma coe_comp {X Y Z : CommMonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-15")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : CommMonCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

@[to_additive (attr := simp)]

中文:
引理 ext
  条件: {X Y : CommMonCat} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

@[to_additive (attr := simp)]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : CommMonCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive (attr := simp)]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {M : CommMonCat}
  statement: (𝟙 M : M ⟶ M).hom = MonoidHom.id M
  proof: rfl

中文:
引理 hom_id
  条件: {M : CommMonCat}
  结论: (𝟙 M : M ⟶ M).hom = MonoidHom.id M
  证明: rfl
-/
lemma hom_id {M : CommMonCat} : (𝟙 M : M ⟶ M).hom = MonoidHom.id M := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (M : CommMonCat) (x : M)
  proof: by simp

@[to_additive (attr := simp)]

中文:
引理 id_apply
  条件: (M : CommMonCat) (x : M)
  证明: by simp

@[to_additive (attr := simp)]
-/
lemma id_apply (M : CommMonCat) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[to_additive (attr := simp)]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {M N T : CommMonCat} (f : M ⟶ N) (g : N ⟶ T)
  proof: rfl

中文:
引理 hom_comp
  条件: {M N T : CommMonCat} (f : M ⟶ N) (g : N ⟶ T)
  证明: rfl

Depends on / 依赖: congr_map, map_injective, toPresheaf
-/
lemma hom_comp {M N T : CommMonCat} (f : M ⟶ N) (g : N ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {M N T : CommMonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M)
  proof: by simp

@[to_additive (attr := ext)]

中文:
引理 comp_apply
  条件: {M N T : CommMonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M)
  证明: by simp

@[to_additive (attr := ext)]
-/
lemma comp_apply {M N T : CommMonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {M N : CommMonCat} {f g : M ⟶ N} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[to_additive (attr := simp)]

中文:
引理 hom_ext
  条件: {M N : CommMonCat} {f g : M ⟶ N} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[to_additive (attr := simp)]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {M N : CommMonCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {M N : Type u} [CommMonoid M] [CommMonoid N] (f : M ->* N)
  statement: (ofHom f).hom = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 hom_ofHom
  条件: {M N : 类型u} [CommMonoid M] [CommMonoid N] (f : M ->* N)
  结论: (ofHom f).hom = f
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma hom_ofHom {M N : Type u} [CommMonoid M] [CommMonoid N] (f : M ->* N) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {M N : CommMonCat} (f : M ⟶ N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_hom
  条件: {M N : CommMonCat} (f : M ⟶ N)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_hom {M N : CommMonCat} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {M : Type u} [CommMonoid M]
  statement: ofHom (MonoidHom.id M) = 𝟙 (of M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_id
  条件: {M : 类型u} [CommMonoid M]
  结论: ofHom (MonoidHom.id M) = 𝟙 (of M)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_id {M : Type u} [CommMonoid M] : ofHom (MonoidHom.id M) = 𝟙 (of M) := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {M N P : Type u} [CommMonoid M] [CommMonoid N] [CommMonoid P]
  proof: rfl

@[to_additive]

中文:
引理 ofHom_comp
  结论: {M N P : 类型u} [CommMonoid M] [CommMonoid N] [CommMonoid P]
  证明: rfl

@[to_additive]
-/
lemma ofHom_comp {M N P : Type u} [CommMonoid M] [CommMonoid N] [CommMonoid P]
    (f : M ->* N) (g : N ->* P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X ->* Y) (x : X)
  proof: rfl

@[to_additive]

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} [CommMonoid X] [CommMonoid Y] (f : X ->* Y) (x : X)
  证明: rfl

@[to_additive]
-/
lemma ofHom_apply {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X ->* Y) (x : X) :
    (ofHom f) x = f x := rfl

@[to_additive]
/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {M N : CommMonCat} (e : M ≅ N) (x : M)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

@[to_additive]

中文:
引理 inv_hom_apply
  条件: {M N : CommMonCat} (e : M ≅ N) (x : M)
  结论: e.inv (e.hom x) = x
  证明: by
  simp

@[to_additive]
-/
lemma inv_hom_apply {M N : CommMonCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

@[to_additive]
/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {M N : CommMonCat} (e : M ≅ N) (s : N)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

@[to_additive]

中文:
引理 hom_inv_apply
  条件: {M N : CommMonCat} (e : M ≅ N) (s : N)
  结论: e.hom (e.inv s) = s
  证明: by
  simp

@[to_additive]
-/
lemma hom_inv_apply {M N : CommMonCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  simp

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited CommMonCat
  body: -- The default instance for `CommMonoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@CommGroup.toCommMonoid _ PUnit.commGroup)⟩

@[to_additive]

中文:
实例 :
  签名: Inhabited CommMonCat
  定义体: -- The default instance for `CommMonoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@CommGroup.toCommMonoid _ PUnit.commGroup)⟩

@[to_additive]
-/
instance : Inhabited CommMonCat :=
  -- The default instance for `CommMonoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@CommGroup.toCommMonoid _ PUnit.commGroup)⟩

@[to_additive]
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (R : Type u) [CommMonoid R]
  statement: (CommMonCat.of R : Type u) = R
  proof: rfl

@[to_additive hasForgetToAddMonCat]

中文:
定理 coe_of
  条件: (R : 类型u) [CommMonoid R]
  结论: (CommMonCat.of R : 类型u) = R
  证明: rfl

@[to_additive hasForgetToAddMonCat]
-/
theorem coe_of (R : Type u) [CommMonoid R] : (CommMonCat.of R : Type u) = R :=
  rfl

@[to_additive hasForgetToAddMonCat]
/--
Instance `hasForgetToMonCat` / 实例 `hasForgetToMonCat`

English:
instance hasForgetToMonCat
  signature: : HasForget₂ CommMonCat MonCat where
  body: { obj R := MonCat.of R
      map f := MonCat.ofHom f.hom }

中文:
实例 hasForgetToMonCat
  签名: : HasForget₂ CommMonCat MonCat where
  定义体: { obj R := MonCat.of R
      map f := MonCat.ofHom f.hom }

Depends on / 依赖: MonCat, MonCat.of, MonCat.ofHom, f.hom
-/
instance hasForgetToMonCat : HasForget₂ CommMonCat MonCat where
  forget₂ :=
    { obj R := MonCat.of R
      map f := MonCat.ofHom f.hom }

/--
lemma `coe_forget₂_obj` / 引理 `coe_forget₂_obj`

English:
lemma coe_forget₂_obj
  given: (X : CommMonCat)
  proof: rfl

中文:
引理 coe_forget₂_obj
  条件: (X : CommMonCat)
  证明: rfl
-/
@[to_additive (attr := simp)] lemma coe_forget₂_obj (X : CommMonCat) :
    ((forget₂ CommMonCat MonCat).obj X : Type _) = X := rfl

/--
lemma `hom_forget₂_map` / 引理 `hom_forget₂_map`

English:
lemma hom_forget₂_map
  statement: {X Y : CommMonCat}
  proof: rfl

中文:
引理 hom_forget₂_map
  结论: {X Y : CommMonCat}
  证明: rfl
-/
@[to_additive (attr := simp)] lemma hom_forget₂_map {X Y : CommMonCat}
    (f : X ⟶ Y) :
    ((forget₂ CommMonCat MonCat).map f).hom = f.hom := rfl

/--
lemma `forget₂_map_ofHom` / 引理 `forget₂_map_ofHom`

English:
lemma forget₂_map_ofHom
  statement: {X Y : Type u} [CommMonoid X] [CommMonoid Y]
  proof: rfl

中文:
引理 forget₂_map_ofHom
  结论: {X Y : 类型u} [CommMonoid X] [CommMonoid Y]
  证明: rfl
-/
@[to_additive (attr := simp)] lemma forget₂_map_ofHom {X Y : Type u} [CommMonoid X] [CommMonoid Y]
    (f : X ->* Y) :
    (forget₂ CommMonCat MonCat).map (ofHom f) = MonCat.ofHom f := rfl

/-- The forgetful functor from `CommMonCat` to `MonCat` is fully faithful. -/
@[to_additive fullyFaithfulForgetToAddMonCat
  /-- The forgetful functor from `AddCommMonCat` to `AddMonCat` is fully faithful. -/]
/--
Definition of `fullyFaithfulForgetToMonCat` / `fullyFaithfulForgetToMonCat` 的定义

English:
definition fullyFaithfulForgetToMonCat
  signature: : (forget₂ CommMonCat.{u} MonCat.{u}).FullyFaithful where
  body: ofHom f.hom

@[to_additive]

中文:
定义 fullyFaithfulForgetToMonCat
  签名: : (forget₂ CommMonCat.{u} MonCat.{u}).FullyFaithful where
  定义体: ofHom f.hom

@[to_additive]

Depends on / 依赖: f.hom
-/
def fullyFaithfulForgetToMonCat : (forget₂ CommMonCat.{u} MonCat.{u}).FullyFaithful where
  preimage f := ofHom f.hom

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ CommMonCat.{u} MonCat.{u}).Full
  body: fullyFaithfulForgetToMonCat.full

@[to_additive]

中文:
实例 :
  签名: (forget₂ CommMonCat.{u} MonCat.{u}).Full
  定义体: fullyFaithfulForgetToMonCat.full

@[to_additive]

Depends on / 依赖: fullyFaithfulForgetToMonCat, fullyFaithfulForgetToMonCat.full
-/
instance : (forget₂ CommMonCat.{u} MonCat.{u}).Full :=
  fullyFaithfulForgetToMonCat.full

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe CommMonCat.{u} MonCat.{u}
  body: (forget₂ CommMonCat MonCat).obj

中文:
实例 :
  签名: Coe CommMonCat.{u} MonCat.{u}
  定义体: (forget₂ CommMonCat MonCat).obj

Depends on / 依赖: CommMonCat, MonCat
-/
instance : Coe CommMonCat.{u} MonCat.{u} where coe := (forget₂ CommMonCat MonCat).obj

/-- Universe lift functor for commutative monoids. -/
@[to_additive (attr := simps)
  /-- Universe lift functor for additive commutative monoids. -/]
/--
Definition of `uliftFunctor` / `uliftFunctor` 的定义

English:
definition uliftFunctor
  signature: : CommMonCat.{v} ⥤ CommMonCat.{max v u} where
  body: CommMonCat.of (ULift.{u, v} X)
map {_ _} f := CommMonCat.ofHom
MulEquiv.ulift.symm.toMonoidHom.comp f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

中文:
定义 uliftFunctor
  签名: : CommMonCat.{v} ⥤ CommMonCat.{max v u} where
  定义体: CommMonCat.of (ULift.{u, v} X)
map {_ _} f := CommMonCat.ofHom
MulEquiv.ulift.symm.toMonoidHom.comp f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

Depends on / 依赖: CommMonCat, CommMonCat.of
-/
def uliftFunctor : CommMonCat.{v} ⥤ CommMonCat.{max v u} where
  obj X := CommMonCat.of (ULift.{u, v} X)
map {_ _} f := CommMonCat.ofHom
MulEquiv.ulift.symm.toMonoidHom.comp f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end CommMonCat

variable {X Y : Type u}

section

variable [Monoid X] [Monoid Y]

/-- Build an isomorphism in the category `MonCat` from a `MulEquiv` between `Monoid`s. -/
@[to_additive (attr := simps) AddEquiv.toAddMonCatIso
      /-- Build an isomorphism in the category `AddMonCat` from
an `AddEquiv` between `AddMonoid`s. -/]
/--
Definition of `MulEquiv.toMonCatIso` / `MulEquiv.toMonCatIso` 的定义

English:
definition MulEquiv.toMonCatIso
  signature: (e : X ≃* Y)
  body: MonCat.ofHom e.toMonoidHom
  inv := MonCat.ofHom e.symm.toMonoidHom

中文:
定义 MulEquiv.toMonCatIso
  签名: (e : X ≃* Y)
  定义体: MonCat.ofHom e.toMonoidHom
  inv := MonCat.ofHom e.symm.toMonoidHom

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, MonCat, MonCat.ofHom, congr_hom, e.toMonoidHom, toMonoidHom
-/
def MulEquiv.toMonCatIso (e : X ≃* Y) : MonCat.of X ≅ MonCat.of Y where
  hom := MonCat.ofHom e.toMonoidHom
  inv := MonCat.ofHom e.symm.toMonoidHom

end

section

variable [CommMonoid X] [CommMonoid Y]

/-- Build an isomorphism in the category `CommMonCat` from a `MulEquiv` between `CommMonoid`s. -/
@[to_additive (attr := simps) AddEquiv.toAddCommMonCatIso]
/--
Definition of `MulEquiv.toCommMonCatIso` / `MulEquiv.toCommMonCatIso` 的定义

English:
definition MulEquiv.toCommMonCatIso
  signature: (e : X ≃* Y)
  body: CommMonCat.ofHom e.toMonoidHom
  inv := CommMonCat.ofHom e.symm.toMonoidHom

中文:
定义 MulEquiv.toCommMonCatIso
  签名: (e : X ≃* Y)
  定义体: CommMonCat.ofHom e.toMonoidHom
  inv := CommMonCat.ofHom e.symm.toMonoidHom

Depends on / 依赖: CommMonCat, CommMonCat.ofHom, e.toMonoidHom, toMonoidHom
-/
def MulEquiv.toCommMonCatIso (e : X ≃* Y) : CommMonCat.of X ≅ CommMonCat.of Y where
  hom := CommMonCat.ofHom e.toMonoidHom
  inv := CommMonCat.ofHom e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddCommMonCat`
from an `AddEquiv` between `AddCommMonoid`s. -/
add_decl_doc AddEquiv.toAddCommMonCatIso

end

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `MonCat`. -/
@[to_additive addMonCatIsoToAddEquiv
      /-- Build an `AddEquiv` from an isomorphism in the category
`AddMonCat`. -/]
/--
Definition of `monCatIsoToMulEquiv` / `monCatIsoToMulEquiv` 的定义

English:
definition monCatIsoToMulEquiv
  signature: {X Y : MonCat} (i : X ≅ Y)
  body: MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

中文:
定义 monCatIsoToMulEquiv
  签名: {X Y : MonCat} (i : X ≅ Y)
  定义体: MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

Depends on / 依赖: MonoidHom, MonoidHom.toMulEquiv, i.hom.hom, i.inv.hom, toMulEquiv
-/
def monCatIsoToMulEquiv {X Y : MonCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `MulEquiv` from an isomorphism in the category `CommMonCat`. -/
@[to_additive /-- Build an `AddEquiv` from an isomorphism in the category
`AddCommMonCat`. -/]
/--
Definition of `commMonCatIsoToMulEquiv` / `commMonCatIsoToMulEquiv` 的定义

English:
definition commMonCatIsoToMulEquiv
  signature: {X Y : CommMonCat} (i : X ≅ Y)
  body: MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

中文:
定义 commMonCatIsoToMulEquiv
  签名: {X Y : CommMonCat} (i : X ≅ Y)
  定义体: MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

Depends on / 依赖: MonoidHom, MonoidHom.toMulEquiv, i.hom.hom, i.inv.hom, toMulEquiv
-/
def commMonCatIsoToMulEquiv {X Y : CommMonCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

end CategoryTheory.Iso

/-- multiplicative equivalences between `Monoid`s are the same as (isomorphic to) isomorphisms
in `MonCat` -/
@[to_additive addEquivIsoAddMonCatIso]
/--
Definition of `mulEquivIsoMonCatIso` / `mulEquivIsoMonCatIso` 的定义

English:
definition mulEquivIsoMonCatIso
  signature: {X Y : Type u} [Monoid X] [Monoid Y]
  body: ↾fun e => e.toMonCatIso
  inv := ↾fun i => i.monCatIsoToMulEquiv

中文:
定义 mulEquivIsoMonCatIso
  签名: {X Y : 类型u} [Monoid X] [Monoid Y]
  定义体: ↾fun e => e.toMonCatIso
  inv := ↾fun i => i.monCatIsoToMulEquiv

Depends on / 依赖: e.toMonCatIso, toMonCatIso
-/
def mulEquivIsoMonCatIso {X Y : Type u} [Monoid X] [Monoid Y] :
    (X ≃* Y) ≅ (MonCat.of X ≅ MonCat.of Y) where
  hom := ↾fun e => e.toMonCatIso
  inv := ↾fun i => i.monCatIsoToMulEquiv

/-- additive equivalences between `AddMonoid`s are the same
as (isomorphic to) isomorphisms in `AddMonCat` -/
add_decl_doc addEquivIsoAddMonCatIso

/-- multiplicative equivalences between `CommMonoid`s are the same as (isomorphic to) isomorphisms
in `CommMonCat` -/
@[to_additive addEquivIsoAddCommMonCatIso]
/--
Definition of `mulEquivIsoCommMonCatIso` / `mulEquivIsoCommMonCatIso` 的定义

English:
definition mulEquivIsoCommMonCatIso
  signature: {X Y : Type u} [CommMonoid X] [CommMonoid Y]
  body: ↾fun e => e.toCommMonCatIso
  inv := ↾fun i => i.commMonCatIsoToMulEquiv

中文:
定义 mulEquivIsoCommMonCatIso
  签名: {X Y : 类型u} [CommMonoid X] [CommMonoid Y]
  定义体: ↾fun e => e.toCommMonCatIso
  inv := ↾fun i => i.commMonCatIsoToMulEquiv

Depends on / 依赖: e.toCommMonCatIso, toCommMonCatIso
-/
def mulEquivIsoCommMonCatIso {X Y : Type u} [CommMonoid X] [CommMonoid Y] :
    (X ≃* Y) ≅ (CommMonCat.of X ≅ CommMonCat.of Y) where
  hom := ↾fun e => e.toCommMonCatIso
  inv := ↾fun i => i.commMonCatIsoToMulEquiv

/-- additive equivalences between `AddCommMonoid`s are
the same as (isomorphic to) isomorphisms in `AddCommMonCat` -/
add_decl_doc addEquivIsoAddCommMonCatIso

@[to_additive]
/--
Instance `MonCat.forget_reflects_isos` / 实例 `MonCat.forget_reflects_isos`

English:
instance MonCat.forget_reflects_isos
  signature: : (forget MonCat.{u}).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget MonCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toMonCatIso.isIso_hom

@[to_additive]

中文:
实例 MonCat.forget_reflects_isos
  签名: : (forget MonCat.{u}).ReflectsIsomorphisms where
  定义体: by
    let i := asIso ((forget MonCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toMonCatIso.isIso_hom

@[to_additive]

Depends on / 依赖: MonCat, e.toMonCatIso.isIso_hom, f.hom, forget, i.toEquiv, isIso_hom, toEquiv, toMonCatIso
-/
instance MonCat.forget_reflects_isos : (forget MonCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget MonCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toMonCatIso.isIso_hom

@[to_additive]
/--
Instance `CommMonCat.forget_reflects_isos` / 实例 `CommMonCat.forget_reflects_isos`

English:
instance CommMonCat.forget_reflects_isos
  signature: : (forget CommMonCat.{u}).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget CommMonCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toCommMonCatIso.isIso_hom

中文:
实例 CommMonCat.forget_reflects_isos
  签名: : (forget CommMonCat.{u}).ReflectsIsomorphisms where
  定义体: by
    let i := asIso ((forget CommMonCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toCommMonCatIso.isIso_hom

Depends on / 依赖: CommMonCat, e.toCommMonCatIso.isIso_hom, f.hom, forget, i.toEquiv, isIso_hom, toCommMonCatIso, toEquiv
-/
instance CommMonCat.forget_reflects_isos : (forget CommMonCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommMonCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toCommMonCatIso.isIso_hom

/-- Ensure that `forget₂ CommMonCat MonCat` automatically reflects isomorphisms. -/
@[to_additive
  /-- Ensure that `forget₂ AddCommMonCat AddMonCat` automatically reflects isomorphisms. -/]
/--
Instance `CommMonCat.forget₂_full` / 实例 `CommMonCat.forget₂_full`

English:
instance CommMonCat.forget₂_full
  signature: : (forget₂ CommMonCat MonCat).Full where
  body: ⟨ofHom f.hom, rfl⟩

example : (forget₂ CommMonCat MonCat).ReflectsIsomorphisms := inferInstance

中文:
实例 CommMonCat.forget₂_full
  签名: : (forget₂ CommMonCat MonCat).Full where
  定义体: ⟨ofHom f.hom, rfl⟩

example : (forget₂ CommMonCat MonCat).ReflectsIsomorphisms := inferInstance

Depends on / 依赖: f.hom
-/
instance CommMonCat.forget₂_full : (forget₂ CommMonCat MonCat).Full where
  map_surjective f := ⟨ofHom f.hom, rfl⟩

example : (forget₂ CommMonCat MonCat).ReflectsIsomorphisms := inferInstance

/-!
`@[simp]` lemmas for `MonoidHom.comp` and categorical identities.
-/

/-- The equivalence between `AddMonCat` and `MonCat`. -/
@[simps]
/--
Definition of `AddMonCat.equivalence` / `AddMonCat.equivalence` 的定义

English:
definition AddMonCat.equivalence
  signature: : AddMonCat ≌ MonCat where
  body: { obj X := .of (Multiplicative X), map f := MonCat.ofHom f.hom.toMultiplicative }
  inverse := { obj X := .of (Additive X), map f := ofHom f.hom.toAdditive }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 AddMonCat.equivalence
  签名: : AddMonCat ≌ MonCat where
  定义体: { obj X := .of (Multiplicative X), map f := MonCat.ofHom f.hom.toMultiplicative }
  inverse := { obj X := .of (Additive X), map f := ofHom f.hom.toAdditive }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: MonCat, MonCat.ofHom, Multiplicative, f.hom.toMultiplicative, toMultiplicative
-/
def AddMonCat.equivalence : AddMonCat ≌ MonCat where
  functor := { obj X := .of (Multiplicative X), map f := MonCat.ofHom f.hom.toMultiplicative }
  inverse := { obj X := .of (Additive X), map f := ofHom f.hom.toAdditive }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The equivalence between `AddCommMonCat` and `CommMonCat`. -/
@[simps]
/--
Definition of `AddCommMonCat.equivalence` / `AddCommMonCat.equivalence` 的定义

English:
definition AddCommMonCat.equivalence
  signature: : AddCommMonCat ≌ CommMonCat where
  body: { obj X := .of (Multiplicative X), map f := CommMonCat.ofHom f.hom.toMultiplicative }
  inverse := { obj X := .of (Additive X), map f := ofHom f.hom.toAdditive }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 AddCommMonCat.equivalence
  签名: : AddCommMonCat ≌ CommMonCat where
  定义体: { obj X := .of (Multiplicative X), map f := CommMonCat.ofHom f.hom.toMultiplicative }
  inverse := { obj X := .of (Additive X), map f := ofHom f.hom.toAdditive }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: CommMonCat, CommMonCat.ofHom, Multiplicative, f.hom.toMultiplicative, toMultiplicative
-/
def AddCommMonCat.equivalence : AddCommMonCat ≌ CommMonCat where
  functor := { obj X := .of (Multiplicative X), map f := CommMonCat.ofHom f.hom.toMultiplicative }
  inverse := { obj X := .of (Additive X), map f := ofHom f.hom.toAdditive }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
