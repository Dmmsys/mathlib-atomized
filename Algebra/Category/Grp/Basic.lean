/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Category instances for Group, AddGroup, CommGroup, and AddCommGroup.

We introduce the bundled categories:
* `GrpCat`
* `AddGrpCat`
* `CommGrpCat`
* `AddCommGrpCat`

along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/

@[expose] public section

universe u v

open CategoryTheory

/--
Definition of `AddGrpCat` / `AddGrpCat` 的定义

English:
structure AddGrpCat
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - (carrier : Type u)
    - [str : AddGroup carrier]

中文:
结构 AddGrpCat
  参数: : Type (u + 1) where
  公理与运算 (2 个):
    - (carrier : 类型u)
    - [str : AddGroup carrier]
-/
structure AddGrpCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddGroup carrier]

/-- The category of groups and group morphisms. -/
@[to_additive]
/--
Definition of `GrpCat` / `GrpCat` 的定义

English:
structure GrpCat
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - (carrier : Type u)
    - [str : Group carrier]

中文:
结构 GrpCat
  参数: : Type (u + 1) where
  公理与运算 (2 个):
    - (carrier : 类型u)
    - [str : Group carrier]
-/
structure GrpCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : Group carrier]

attribute [instance] AddGrpCat.str GrpCat.str

initialize_simps_projections AddGrpCat (carrier -> coe, -str)
initialize_simps_projections GrpCat (carrier -> coe, -str)

namespace GrpCat

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort GrpCat (Type u)
  body: ⟨GrpCat.carrier⟩

中文:
实例 :
  签名: CoeSort GrpCat (类型u)
  定义体: ⟨GrpCat.carrier⟩

Depends on / 依赖: GrpCat, GrpCat.carrier, carrier
-/
instance : CoeSort GrpCat (Type u) :=
  ⟨GrpCat.carrier⟩

attribute [coe] AddGrpCat.carrier GrpCat.carrier

/-- Construct a bundled `GrpCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddGrpCat` from the underlying type and typeclass. -/]
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (M : Type u) [Group M]
  body: ⟨M⟩

中文:
缩写 of
  签名: (M : 类型u) [Group M]
  定义体: ⟨M⟩
-/
abbrev of (M : Type u) [Group M] : GrpCat := ⟨M⟩

end GrpCat

/-- The type of morphisms in `AddGrpCat R`. -/
@[ext]
/--
Definition of `AddGrpCat.Hom` / `AddGrpCat.Hom` 的定义

English:
structure AddGrpCat.Hom
  parameters: (A B : AddGrpCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->+ B

中文:
结构 AddGrpCat.Hom
  参数: (A B : AddGrpCat.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->+ B
-/
structure AddGrpCat.Hom (A B : AddGrpCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A ->+ B

/-- The type of morphisms in `GrpCat R`. -/
@[to_additive, ext]
/--
Definition of `GrpCat.Hom` / `GrpCat.Hom` 的定义

English:
structure GrpCat.Hom
  parameters: (A B : GrpCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->* B

中文:
结构 GrpCat.Hom
  参数: (A B : GrpCat.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->* B
-/
structure GrpCat.Hom (A B : GrpCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A ->* B

namespace GrpCat

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category GrpCat.{u}
  body: Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category GrpCat.{u}
  定义体: Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category GrpCat.{u} where
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
  signature: ConcreteCategory GrpCat (· ->* ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: ConcreteCategory GrpCat (· ->* ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory GrpCat (· ->* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `GrpCat` back into a `MonoidHom`. -/
@[to_additive /-- Turn a morphism in `AddGrpCat` back into an `AddMonoidHom`. -/]
/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : GrpCat.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := GrpCat) f

中文:
缩写 Hom.hom
  签名: {X Y : GrpCat.{u}} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := GrpCat) f
-/
abbrev Hom.hom {X Y : GrpCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := GrpCat) f

/-- Typecheck a `MonoidHom` as a morphism in `GrpCat`. -/
@[to_additive /-- Typecheck an `AddMonoidHom` as a morphism in `AddGrpCat`. -/]
/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [Group X] [Group Y] (f : X ->* Y)
  body: ConcreteCategory.ofHom (C := GrpCat) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [Group X] [Group Y] (f : X ->* Y)
  定义体: ConcreteCategory.ofHom (C := GrpCat) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, GrpCat
-/
abbrev ofHom {X Y : Type u} [Group X] [Group Y] (f : X ->* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := GrpCat) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : GrpCat.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddGrpCat.Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (X Y : GrpCat.{u}) (f : Hom X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddGrpCat.Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : GrpCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddGrpCat.Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  given: {X : GrpCat}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coe_id
  条件: {X : GrpCat}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coe_id {X : GrpCat} : (𝟙 X : X -> X) = id := rfl

@[to_additive (attr := simp)]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : GrpCat} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]

中文:
引理 coe_comp
  条件: {X Y Z : GrpCat} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
-/
lemma coe_comp {X Y Z : GrpCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : GrpCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

@[to_additive]

中文:
引理 ext
  条件: {X Y : GrpCat} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

@[to_additive]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : GrpCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (R : Type u) [Group R]
  statement: ↑(GrpCat.of R) = R
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_of
  条件: (R : 类型u) [Group R]
  结论: ↑(GrpCat.of R) = R
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_of (R : Type u) [Group R] : ↑(GrpCat.of R) = R :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : GrpCat}
  statement: (𝟙 X : X ⟶ X).hom = MonoidHom.id X
  proof: rfl

中文:
引理 hom_id
  条件: {X : GrpCat}
  结论: (𝟙 X : X ⟶ X).hom = MonoidHom.id X
  证明: rfl
-/
lemma hom_id {X : GrpCat} : (𝟙 X : X ⟶ X).hom = MonoidHom.id X := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : GrpCat) (x : X)
  proof: by simp

@[to_additive (attr := simp)]

中文:
引理 id_apply
  条件: (X : GrpCat) (x : X)
  证明: by simp

@[to_additive (attr := simp)]
-/
lemma id_apply (X : GrpCat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[to_additive (attr := simp)]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y T : GrpCat} (f : X ⟶ Y) (g : Y ⟶ T)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y T : GrpCat} (f : X ⟶ Y) (g : Y ⟶ T)
  证明: rfl
-/
lemma hom_comp {X Y T : GrpCat} (f : X ⟶ Y) (g : Y ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y T : GrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X)
  proof: by simp

@[to_additive (attr := ext)]

中文:
引理 comp_apply
  条件: {X Y T : GrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X)
  证明: by simp

@[to_additive (attr := ext)]
-/
lemma comp_apply {X Y T : GrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : GrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[to_additive (attr := simp)]

中文:
引理 hom_ext
  条件: {X Y : GrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[to_additive (attr := simp)]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : GrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {R S : Type u} [Group R] [Group S] (f : R ->* S)
  statement: (ofHom f).hom = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 hom_ofHom
  条件: {R S : 类型u} [Group R] [Group S] (f : R ->* S)
  结论: (ofHom f).hom = f
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma hom_ofHom {R S : Type u} [Group R] [Group S] (f : R ->* S) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : GrpCat} (f : X ⟶ Y)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_hom
  条件: {X Y : GrpCat} (f : X ⟶ Y)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_hom {X Y : GrpCat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [Group X]
  statement: ofHom (MonoidHom.id X) = 𝟙 (of X)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_id
  条件: {X : 类型u} [Group X]
  结论: ofHom (MonoidHom.id X) = 𝟙 (of X)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_id {X : Type u} [Group X] : ofHom (MonoidHom.id X) = 𝟙 (of X) := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [Group X] [Group Y] [Group Z]
  proof: rfl

@[to_additive]

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [Group X] [Group Y] [Group Z]
  证明: rfl

@[to_additive]
-/
lemma ofHom_comp {X Y Z : Type u} [Group X] [Group Y] [Group Z]
    (f : X ->* Y) (g : Y ->* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} [Group X] [Group Y] (f : X ->* Y) (x : X)
  proof: rfl

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} [Group X] [Group Y] (f : X ->* Y) (x : X)
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} [Group X] [Group Y] (f : X ->* Y) (x : X) :
    (ofHom f) x = f x := rfl

-- This is essentially an alias for `Iso.hom_inv_id_apply`; consider deprecation?
@[to_additive]
/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {X Y : GrpCat} (e : X ≅ Y) (x : X)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {X Y : GrpCat} (e : X ≅ Y) (x : X)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {X Y : GrpCat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

-- This is essentially an alias for `Iso.inv_hom_id_apply`; consider deprecation?
@[to_additive]
/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {X Y : GrpCat} (e : X ≅ Y) (s : Y)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

@[to_additive]

中文:
引理 hom_inv_apply
  条件: {X Y : GrpCat} (e : X ≅ Y) (s : Y)
  结论: e.hom (e.inv s) = s
  证明: by
  simp

@[to_additive]
-/
lemma hom_inv_apply {X Y : GrpCat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited GrpCat
  body: ⟨GrpCat.of PUnit⟩

@[to_additive hasForgetToAddMonCat]

中文:
实例 :
  签名: Inhabited GrpCat
  定义体: ⟨GrpCat.of PUnit⟩

@[to_additive hasForgetToAddMonCat]

Depends on / 依赖: GrpCat, GrpCat.of
-/
instance : Inhabited GrpCat :=
  ⟨GrpCat.of PUnit⟩

@[to_additive hasForgetToAddMonCat]
/--
Instance `hasForgetToMonCat` / 实例 `hasForgetToMonCat`

English:
instance hasForgetToMonCat
  signature: : HasForget₂ GrpCat MonCat where
  body: MonCat.of X
  forget₂.map f := MonCat.ofHom f.hom

中文:
实例 hasForgetToMonCat
  签名: : HasForget₂ GrpCat MonCat where
  定义体: MonCat.of X
  forget₂.map f := MonCat.ofHom f.hom

Depends on / 依赖: MonCat, MonCat.of
-/
instance hasForgetToMonCat : HasForget₂ GrpCat MonCat where
  forget₂.obj X := MonCat.of X
  forget₂.map f := MonCat.ofHom f.hom

/--
lemma `forget₂_map_ofHom` / 引理 `forget₂_map_ofHom`

English:
lemma forget₂_map_ofHom
  statement: {X Y : Type u} [Group X] [Group Y]
  proof: rfl

中文:
引理 forget₂_map_ofHom
  结论: {X Y : 类型u} [Group X] [Group Y]
  证明: rfl
-/
@[to_additive (attr := simp)] lemma forget₂_map_ofHom {X Y : Type u} [Group X] [Group Y]
    (f : X ->* Y) :
    (forget₂ GrpCat MonCat).map (ofHom f) = MonCat.ofHom f := rfl

/--
lemma `forget₂_map` / 引理 `forget₂_map`

English:
lemma forget₂_map
  given: {R S : GrpCat} (f : R ⟶ S) (x)
  proof: rfl

@[to_additive]

中文:
引理 forget₂_map
  条件: {R S : GrpCat} (f : R ⟶ S) (x)
  证明: rfl

@[to_additive]
-/
@[to_additive (attr := simp)] lemma forget₂_map {R S : GrpCat} (f : R ⟶ S) (x) :
    (forget₂ GrpCat MonCat).map f x = f x := rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe GrpCat.{u} MonCat.{u}
  body: (forget₂ GrpCat MonCat).obj

@[to_additive]

中文:
实例 :
  签名: Coe GrpCat.{u} MonCat.{u}
  定义体: (forget₂ GrpCat MonCat).obj

@[to_additive]

Depends on / 依赖: GrpCat, MonCat
-/
instance : Coe GrpCat.{u} MonCat.{u} where coe := (forget₂ GrpCat MonCat).obj

@[to_additive]
instance (G H : GrpCat) : One (G ⟶ H) where
  one := ofHom 1

@[to_additive (attr := simp)]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (G H : GrpCat) (g : G)
  statement: ((1 : G ⟶ H) : G -> H) g = 1
  proof: rfl

@[to_additive]

中文:
定理 one_apply
  条件: (G H : GrpCat) (g : G)
  结论: ((1 : G ⟶ H) : G -> H) g = 1
  证明: rfl

@[to_additive]
-/
theorem one_apply (G H : GrpCat) (g : G) : ((1 : G ⟶ H) : G -> H) g = 1 :=
  rfl

@[to_additive]
/--
lemma `ofHom_injective` / 引理 `ofHom_injective`

English:
lemma ofHom_injective
  given: {X Y : Type u} [Group X] [Group Y]
  proof: by
  intro _ _ h
  ext
  apply ConcreteCategory.congr_hom h

中文:
引理 ofHom_injective
  条件: {X Y : 类型u} [Group X] [Group Y]
  证明: by
  intro _ _ h
  ext
  apply ConcreteCategory.congr_hom h

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom
-/
lemma ofHom_injective {X Y : Type u} [Group X] [Group Y] :
    Function.Injective (fun (f : X ->* Y) => ofHom f) := by
  intro _ _ h
  ext
  apply ConcreteCategory.congr_hom h

/-- The forgetful functor from groups to monoids is fully faithful. -/
@[to_additive fullyFaihtfulForget₂ToAddMonCat
  /-- The forgetful functor from additive groups to additive monoids is fully faithful. -/]
/--
Definition of `fullyFaithfulForget₂ToMonCat` / `fullyFaithfulForget₂ToMonCat` 的定义

English:
definition fullyFaithfulForget₂ToMonCat
  signature: : (forget₂ GrpCat.{u} MonCat).FullyFaithful where
  body: ofHom f.hom

@[to_additive]

中文:
定义 fullyFaithfulForget₂ToMonCat
  签名: : (forget₂ GrpCat.{u} MonCat).FullyFaithful where
  定义体: ofHom f.hom

@[to_additive]

Depends on / 依赖: f.hom
-/
def fullyFaithfulForget₂ToMonCat : (forget₂ GrpCat.{u} MonCat).FullyFaithful where
  preimage f := ofHom f.hom

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ GrpCat.{u} MonCat).Full
  body: fullyFaithfulForget₂ToMonCat.full

中文:
实例 :
  签名: (forget₂ GrpCat.{u} MonCat).Full
  定义体: fullyFaithfulForget₂ToMonCat.full

Depends on / 依赖: ToMonCat.full
-/
instance : (forget₂ GrpCat.{u} MonCat).Full :=
  fullyFaithfulForget₂ToMonCat.full

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : GrpCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

/-- Universe lift functor for groups. -/
@[to_additive (attr := simps obj map)
  /-- Universe lift functor for additive groups. -/]
/--
Definition of `uliftFunctor` / `uliftFunctor` 的定义

English:
definition uliftFunctor
  signature: : GrpCat.{v} ⥤ GrpCat.{max v u} where
  body: GrpCat.of (ULift.{u, v} X)
map {_ _} f := GrpCat.ofHom
MulEquiv.ulift.symm.toMonoidHom.comp f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

中文:
定义 uliftFunctor
  签名: : GrpCat.{v} ⥤ GrpCat.{max v u} where
  定义体: GrpCat.of (ULift.{u, v} X)
map {_ _} f := GrpCat.ofHom
MulEquiv.ulift.symm.toMonoidHom.comp f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

Depends on / 依赖: GrpCat, GrpCat.of
-/
def uliftFunctor : GrpCat.{v} ⥤ GrpCat.{max v u} where
  obj X := GrpCat.of (ULift.{u, v} X)
map {_ _} f := GrpCat.ofHom
MulEquiv.ulift.symm.toMonoidHom.comp f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end GrpCat

/--
Definition of `AddCommGrpCat` / `AddCommGrpCat` 的定义

English:
structure AddCommGrpCat
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - (carrier : Type u)
    - [str : AddCommGroup carrier]

中文:
结构 AddCommGrpCat
  参数: : Type (u + 1) where
  公理与运算 (2 个):
    - (carrier : 类型u)
    - [str : AddCommGroup carrier]
-/
structure AddCommGrpCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddCommGroup carrier]

/-- The category of groups and group morphisms. -/
@[to_additive]
/--
Definition of `CommGrpCat` / `CommGrpCat` 的定义

English:
structure CommGrpCat
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - (carrier : Type u)
    - [str : CommGroup carrier]

中文:
结构 CommGrpCat
  参数: : Type (u + 1) where
  公理与运算 (2 个):
    - (carrier : 类型u)
    - [str : CommGroup carrier]
-/
structure CommGrpCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : CommGroup carrier]

attribute [instance] AddCommGrpCat.str CommGrpCat.str

initialize_simps_projections AddCommGrpCat (carrier -> coe, -str)
initialize_simps_projections CommGrpCat (carrier -> coe, -str)

/--
Definition of `Ab` / `Ab` 的定义

English:
abbreviation Ab
  body: AddCommGrpCat

中文:
缩写 Ab
  定义体: AddCommGrpCat

Depends on / 依赖: AddCommGrpCat
-/
abbrev Ab := AddCommGrpCat

namespace CommGrpCat

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort CommGrpCat (Type u)
  body: ⟨CommGrpCat.carrier⟩

中文:
实例 :
  签名: CoeSort CommGrpCat (类型u)
  定义体: ⟨CommGrpCat.carrier⟩

Depends on / 依赖: CommGrpCat, CommGrpCat.carrier, carrier
-/
instance : CoeSort CommGrpCat (Type u) :=
  ⟨CommGrpCat.carrier⟩

attribute [coe] AddCommGrpCat.carrier CommGrpCat.carrier

/-- Construct a bundled `CommGrpCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddCommGrpCat` from the underlying type and typeclass. -/]
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (M : Type u) [CommGroup M]
  body: ⟨M⟩

中文:
缩写 of
  签名: (M : 类型u) [CommGroup M]
  定义体: ⟨M⟩
-/
abbrev of (M : Type u) [CommGroup M] : CommGrpCat := ⟨M⟩

end CommGrpCat

/-- The type of morphisms in `AddCommGrpCat R`. -/
@[ext]
/--
Definition of `AddCommGrpCat.Hom` / `AddCommGrpCat.Hom` 的定义

English:
structure AddCommGrpCat.Hom
  parameters: (A B : AddCommGrpCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->+ B

中文:
结构 AddCommGrpCat.Hom
  参数: (A B : AddCommGrpCat.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->+ B
-/
structure AddCommGrpCat.Hom (A B : AddCommGrpCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A ->+ B

/-- The type of morphisms in `CommGrpCat R`. -/
@[to_additive, ext]
/--
Definition of `CommGrpCat.Hom` / `CommGrpCat.Hom` 的定义

English:
structure CommGrpCat.Hom
  parameters: (A B : CommGrpCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->* B

中文:
结构 CommGrpCat.Hom
  参数: (A B : CommGrpCat.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->* B
-/
structure CommGrpCat.Hom (A B : CommGrpCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A ->* B

namespace CommGrpCat

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category CommGrpCat.{u}
  body: Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category CommGrpCat.{u}
  定义体: Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category CommGrpCat.{u} where
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
  signature: ConcreteCategory CommGrpCat (· ->* ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: ConcreteCategory CommGrpCat (· ->* ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory CommGrpCat (· ->* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommGrpCat` back into a `MonoidHom`. -/
@[to_additive /-- Turn a morphism in `AddCommGrpCat` back into an `AddMonoidHom`. -/]
/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : CommGrpCat.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := CommGrpCat) f

中文:
缩写 Hom.hom
  签名: {X Y : CommGrpCat.{u}} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := CommGrpCat) f
-/
abbrev Hom.hom {X Y : CommGrpCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := CommGrpCat) f

/-- Typecheck a `MonoidHom` as a morphism in `CommGrpCat`. -/
@[to_additive /-- Typecheck an `AddMonoidHom` as a morphism in `AddCommGrpCat`. -/]
/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X ->* Y)
  body: ConcreteCategory.ofHom (C := CommGrpCat) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [CommGroup X] [CommGroup Y] (f : X ->* Y)
  定义体: ConcreteCategory.ofHom (C := CommGrpCat) f

Depends on / 依赖: CommGrpCat, ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X ->* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := CommGrpCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
@[to_additive /-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/]
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : CommGrpCat.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddCommGrpCat.Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (X Y : CommGrpCat.{u}) (f : Hom X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddCommGrpCat.Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : CommGrpCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)
initialize_simps_projections AddCommGrpCat.Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  given: {X : CommGrpCat}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coe_id
  条件: {X : CommGrpCat}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coe_id {X : CommGrpCat} : (𝟙 X : X -> X) = id := rfl

@[to_additive (attr := simp)]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : CommGrpCat} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]

中文:
引理 coe_comp
  条件: {X Y Z : CommGrpCat} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
-/
lemma coe_comp {X Y Z : CommGrpCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : CommGrpCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

@[to_additive]

中文:
引理 ext
  条件: {X Y : CommGrpCat} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

@[to_additive]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : CommGrpCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited CommGrpCat
  body: ⟨CommGrpCat.of PUnit⟩

@[to_additive]

中文:
实例 :
  签名: Inhabited CommGrpCat
  定义体: ⟨CommGrpCat.of PUnit⟩

@[to_additive]

Depends on / 依赖: CommGrpCat, CommGrpCat.of
-/
instance : Inhabited CommGrpCat :=
  ⟨CommGrpCat.of PUnit⟩

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (R : Type u) [CommGroup R]
  statement: ↑(CommGrpCat.of R) = R
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_of
  条件: (R : 类型u) [CommGroup R]
  结论: ↑(CommGrpCat.of R) = R
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_of (R : Type u) [CommGroup R] : ↑(CommGrpCat.of R) = R :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : CommGrpCat}
  statement: (𝟙 X : X ⟶ X).hom = MonoidHom.id X
  proof: rfl

中文:
引理 hom_id
  条件: {X : CommGrpCat}
  结论: (𝟙 X : X ⟶ X).hom = MonoidHom.id X
  证明: rfl
-/
lemma hom_id {X : CommGrpCat} : (𝟙 X : X ⟶ X).hom = MonoidHom.id X := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : CommGrpCat) (x : X)
  proof: by simp

@[to_additive (attr := simp)]

中文:
引理 id_apply
  条件: (X : CommGrpCat) (x : X)
  证明: by simp

@[to_additive (attr := simp)]
-/
lemma id_apply (X : CommGrpCat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[to_additive (attr := simp)]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y T : CommGrpCat} (f : X ⟶ Y) (g : Y ⟶ T)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y T : CommGrpCat} (f : X ⟶ Y) (g : Y ⟶ T)
  证明: rfl
-/
lemma hom_comp {X Y T : CommGrpCat} (f : X ⟶ Y) (g : Y ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y T : CommGrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X)
  proof: by simp

@[to_additive (attr := ext)]

中文:
引理 comp_apply
  条件: {X Y T : CommGrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X)
  证明: by simp

@[to_additive (attr := ext)]
-/
lemma comp_apply {X Y T : CommGrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : CommGrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[to_additive (attr := simp)]

中文:
引理 hom_ext
  条件: {X Y : CommGrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[to_additive (attr := simp)]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : CommGrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X ->* Y)
  statement: (ofHom f).hom = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 hom_ofHom
  条件: {X Y : 类型u} [CommGroup X] [CommGroup Y] (f : X ->* Y)
  结论: (ofHom f).hom = f
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma hom_ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X ->* Y) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : CommGrpCat} (f : X ⟶ Y)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_hom
  条件: {X Y : CommGrpCat} (f : X ⟶ Y)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_hom {X Y : CommGrpCat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [CommGroup X]
  statement: ofHom (MonoidHom.id X) = 𝟙 (of X)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_id
  条件: {X : 类型u} [CommGroup X]
  结论: ofHom (MonoidHom.id X) = 𝟙 (of X)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_id {X : Type u} [CommGroup X] : ofHom (MonoidHom.id X) = 𝟙 (of X) := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [CommGroup X] [CommGroup Y] [CommGroup Z]
  proof: rfl

@[to_additive]

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [CommGroup X] [CommGroup Y] [CommGroup Z]
  证明: rfl

@[to_additive]
-/
lemma ofHom_comp {X Y Z : Type u} [CommGroup X] [CommGroup Y] [CommGroup Z]
    (f : X ->* Y) (g : Y ->* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X ->* Y) (x : X)
  proof: rfl

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} [CommGroup X] [CommGroup Y] (f : X ->* Y) (x : X)
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X ->* Y) (x : X) :
    (ofHom f) x = f x := rfl

-- This is essentially an alias for `Iso.hom_inv_id_apply`; consider deprecation?
@[to_additive]
/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {X Y : CommGrpCat} (e : X ≅ Y) (x : X)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {X Y : CommGrpCat} (e : X ≅ Y) (x : X)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {X Y : CommGrpCat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

-- This is essentially an alias for `Iso.inv_hom_id_apply`; consider deprecation?
@[to_additive]
/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {X Y : CommGrpCat} (e : X ≅ Y) (s : Y)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

@[to_additive]

中文:
引理 hom_inv_apply
  条件: {X Y : CommGrpCat} (e : X ≅ Y) (s : Y)
  结论: e.hom (e.inv s) = s
  证明: by
  simp

@[to_additive]
-/
lemma hom_inv_apply {X Y : CommGrpCat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

@[to_additive]
/--
Instance `hasForgetToGroup` / 实例 `hasForgetToGroup`

English:
instance hasForgetToGroup
  signature: : HasForget₂ CommGrpCat GrpCat where
  body: GrpCat.of X
  forget₂.map f := GrpCat.ofHom f.hom

中文:
实例 hasForgetToGroup
  签名: : HasForget₂ CommGrpCat GrpCat where
  定义体: GrpCat.of X
  forget₂.map f := GrpCat.ofHom f.hom

Depends on / 依赖: GrpCat, GrpCat.of
-/
instance hasForgetToGroup : HasForget₂ CommGrpCat GrpCat where
  forget₂.obj X := GrpCat.of X
  forget₂.map f := GrpCat.ofHom f.hom

/--
lemma `forget₂_grp_map_ofHom` / 引理 `forget₂_grp_map_ofHom`

English:
lemma forget₂_grp_map_ofHom
  statement: {X Y : Type u} [CommGroup X] [CommGroup Y]
  proof: rfl

中文:
引理 forget₂_grp_map_ofHom
  结论: {X Y : 类型u} [CommGroup X] [CommGroup Y]
  证明: rfl
-/
@[to_additive (attr := simp)] lemma forget₂_grp_map_ofHom {X Y : Type u} [CommGroup X] [CommGroup Y]
    (f : X ->* Y) :
    (forget₂ CommGrpCat GrpCat).map (ofHom f) = GrpCat.ofHom f := rfl

/--
lemma `forget₂_map` / 引理 `forget₂_map`

English:
lemma forget₂_map
  given: {R S : CommGrpCat} (f : R ⟶ S) (x)
  proof: rfl

@[to_additive]

中文:
引理 forget₂_map
  条件: {R S : CommGrpCat} (f : R ⟶ S) (x)
  证明: rfl

@[to_additive]
-/
@[to_additive (attr := simp)] lemma forget₂_map {R S : CommGrpCat} (f : R ⟶ S) (x) :
    (forget₂ CommGrpCat GrpCat).map f x = f x := rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe CommGrpCat.{u} GrpCat.{u}
  body: (forget₂ CommGrpCat GrpCat).obj

中文:
实例 :
  签名: Coe CommGrpCat.{u} GrpCat.{u}
  定义体: (forget₂ CommGrpCat GrpCat).obj

Depends on / 依赖: CommGrpCat, GrpCat
-/
instance : Coe CommGrpCat.{u} GrpCat.{u} where coe := (forget₂ CommGrpCat GrpCat).obj

/-- The forgetful functor from commutative groups to groups is fully faithful. -/
@[to_additive fullyFaihtfulForget₂ToAddGrp
/-- The forgetful functor from additive commutative groups to additive groups is fully faithful. -/]
/--
Definition of `fullyFaithfulForget₂ToGrp` / `fullyFaithfulForget₂ToGrp` 的定义

English:
definition fullyFaithfulForget₂ToGrp
  signature: : (forget₂ CommGrpCat.{u} GrpCat).FullyFaithful where
  body: ofHom f.hom

@[to_additive]

中文:
定义 fullyFaithfulForget₂ToGrp
  签名: : (forget₂ CommGrpCat.{u} GrpCat).FullyFaithful where
  定义体: ofHom f.hom

@[to_additive]

Depends on / 依赖: f.hom
-/
def fullyFaithfulForget₂ToGrp : (forget₂ CommGrpCat.{u} GrpCat).FullyFaithful where
  preimage f := ofHom f.hom

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ CommGrpCat.{u} GrpCat).Full
  body: fullyFaithfulForget₂ToGrp.full

@[to_additive hasForgetToAddCommMonCat]

中文:
实例 :
  签名: (forget₂ CommGrpCat.{u} GrpCat).Full
  定义体: fullyFaithfulForget₂ToGrp.full

@[to_additive hasForgetToAddCommMonCat]

Depends on / 依赖: ToGrp.full
-/
instance : (forget₂ CommGrpCat.{u} GrpCat).Full :=
  fullyFaithfulForget₂ToGrp.full

@[to_additive hasForgetToAddCommMonCat]
/--
Instance `hasForgetToCommMonCat` / 实例 `hasForgetToCommMonCat`

English:
instance hasForgetToCommMonCat
  signature: : HasForget₂ CommGrpCat CommMonCat where
  body: CommMonCat.of X
  forget₂.map f := CommMonCat.ofHom f.hom

中文:
实例 hasForgetToCommMonCat
  签名: : HasForget₂ CommGrpCat CommMonCat where
  定义体: CommMonCat.of X
  forget₂.map f := CommMonCat.ofHom f.hom

Depends on / 依赖: CommMonCat, CommMonCat.of
-/
instance hasForgetToCommMonCat : HasForget₂ CommGrpCat CommMonCat where
  forget₂.obj X := CommMonCat.of X
  forget₂.map f := CommMonCat.ofHom f.hom

/--
lemma `forget₂_commMonCat_map_ofHom` / 引理 `forget₂_commMonCat_map_ofHom`

English:
lemma forget₂_commMonCat_map_ofHom
  statement: {X Y : Type u}
  proof: rfl

@[to_additive]

中文:
引理 forget₂_commMonCat_map_ofHom
  结论: {X Y : 类型u}
  证明: rfl

@[to_additive]
-/
@[to_additive (attr := simp)] lemma forget₂_commMonCat_map_ofHom {X Y : Type u}
    [CommGroup X] [CommGroup Y] (f : X ->* Y) :
    (forget₂ CommGrpCat CommMonCat).map (ofHom f) = CommMonCat.ofHom f := rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe CommGrpCat.{u} CommMonCat.{u}
  body: (forget₂ CommGrpCat CommMonCat).obj

@[to_additive]

中文:
实例 :
  签名: Coe CommGrpCat.{u} CommMonCat.{u}
  定义体: (forget₂ CommGrpCat CommMonCat).obj

@[to_additive]

Depends on / 依赖: CommGrpCat, CommMonCat
-/
instance : Coe CommGrpCat.{u} CommMonCat.{u} where coe := (forget₂ CommGrpCat CommMonCat).obj

@[to_additive]
instance (G H : CommGrpCat) : One (G ⟶ H) where
  one := ofHom 1

@[to_additive (attr := simp)]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (G H : CommGrpCat) (g : G)
  statement: ((1 : G ⟶ H) : G -> H) g = 1
  proof: rfl

@[to_additive]

中文:
定理 one_apply
  条件: (G H : CommGrpCat) (g : G)
  结论: ((1 : G ⟶ H) : G -> H) g = 1
  证明: rfl

@[to_additive]
-/
theorem one_apply (G H : CommGrpCat) (g : G) : ((1 : G ⟶ H) : G -> H) g = 1 :=
  rfl

@[to_additive]
/--
lemma `ofHom_injective` / 引理 `ofHom_injective`

English:
lemma ofHom_injective
  given: {X Y : Type u} [CommGroup X] [CommGroup Y]
  proof: by
  intro _ _ h
  ext
  apply ConcreteCategory.congr_hom h

中文:
引理 ofHom_injective
  条件: {X Y : 类型u} [CommGroup X] [CommGroup Y]
  证明: by
  intro _ _ h
  ext
  apply ConcreteCategory.congr_hom h

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom
-/
lemma ofHom_injective {X Y : Type u} [CommGroup X] [CommGroup Y] :
    Function.Injective (fun (f : X ->* Y) => ofHom f) := by
  intro _ _ h
  ext
  apply ConcreteCategory.congr_hom h

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
example {R S : CommGrpCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

/-- Universe lift functor for commutative groups. -/
@[to_additive (attr := simps obj map)
  /-- Universe lift functor for additive commutative groups. -/]
/--
Definition of `uliftFunctor` / `uliftFunctor` 的定义

English:
definition uliftFunctor
  signature: : CommGrpCat.{v} ⥤ CommGrpCat.{max v u} where
  body: CommGrpCat.of (ULift.{u, v} X)
map {_ _} f := CommGrpCat.ofHom
MulEquiv.ulift.symm.toMonoidHom.comp f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

中文:
定义 uliftFunctor
  签名: : CommGrpCat.{v} ⥤ CommGrpCat.{max v u} where
  定义体: CommGrpCat.of (ULift.{u, v} X)
map {_ _} f := CommGrpCat.ofHom
MulEquiv.ulift.symm.toMonoidHom.comp f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

Depends on / 依赖: CommGrpCat, CommGrpCat.of
-/
def uliftFunctor : CommGrpCat.{v} ⥤ CommGrpCat.{max v u} where
  obj X := CommGrpCat.of (ULift.{u, v} X)
map {_ _} f := CommGrpCat.ofHom
MulEquiv.ulift.symm.toMonoidHom.comp f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end CommGrpCat

namespace AddCommGrpCat

-- Note that because `ℤ : Type 0`, this forces `G : AddCommGrpCat.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ULiftInstances.lean` file
/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
@[simps!]
/--
Definition of `asHom` / `asHom` 的定义

English:
definition asHom
  signature: {G : AddCommGrpCat.{0}} (g : G)
  body: ofHom (zmultiplesHom G g)

中文:
定义 asHom
  签名: {G : AddCommGrpCat.{0}} (g : G)
  定义体: ofHom (zmultiplesHom G g)

Depends on / 依赖: zmultiplesHom
-/
def asHom {G : AddCommGrpCat.{0}} (g : G) : AddCommGrpCat.of Int ⟶ G :=
  ofHom (zmultiplesHom G g)

/--
theorem `asHom_injective` / 定理 `asHom_injective`

English:
theorem asHom_injective
  given: {G : AddCommGrpCat.{0}}
  statement: Function.Injective (@asHom G)
  proof: fun h k w => by
  simpa using CategoryTheory.congr_fun w 1

@[ext]

中文:
定理 asHom_injective
  条件: {G : AddCommGrpCat.{0}}
  结论: Function.Injective (@asHom G)
  证明: fun h k w => by
  simpa using CategoryTheory.congr_fun w 1

@[ext]

Depends on / 依赖: CategoryTheory, CategoryTheory.congr_fun, congr_fun
-/
theorem asHom_injective {G : AddCommGrpCat.{0}} : Function.Injective (@asHom G) := fun h k w => by
  simpa using CategoryTheory.congr_fun w 1

@[ext]
/--
theorem `int_hom_ext` / 定理 `int_hom_ext`

English:
theorem int_hom_ext
  statement: {G : AddCommGrpCat.{0}} (f g : AddCommGrpCat.of Int ⟶ G)
  proof: hom_ext (AddMonoidHom.ext_int w)

中文:
定理 int_hom_ext
  结论: {G : AddCommGrpCat.{0}} (f g : AddCommGrpCat.of 整数 ⟶ G)
  证明: hom_ext (AddMonoidHom.ext_int w)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext_int, ext_int, hom_ext
-/
theorem int_hom_ext {G : AddCommGrpCat.{0}} (f g : AddCommGrpCat.of Int ⟶ G)
    (w : f (1 : Int) = g (1 : Int)) : f = g :=
  hom_ext (AddMonoidHom.ext_int w)

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
/--
theorem `injective_of_mono` / 定理 `injective_of_mono`

English:
theorem injective_of_mono
  given: {G H : AddCommGrpCat.{0}} (f : G ⟶ H) [Mono f]
  statement: Function.Injective f
  proof: fun g₁ g₂ h => by
  have t0 : asHom g₁ ≫ f = asHom g₂ ≫ f := by cat_disch
  have t1 : asHom g₁ = asHom g₂ := (cancel_mono _).1 t0
  apply asHom_injective t1

中文:
定理 injective_of_mono
  条件: {G H : AddCommGrpCat.{0}} (f : G ⟶ H) [Mono f]
  结论: Function.Injective f
  证明: fun g₁ g₂ h => by
  have t0 : asHom g₁ ≫ f = asHom g₂ ≫ f := by cat_disch
  have t1 : asHom g₁ = asHom g₂ := (cancel_mono _).1 t0
  apply asHom_injective t1

Depends on / 依赖: asHom_injective, cancel_mono, cat_disch
-/
theorem injective_of_mono {G H : AddCommGrpCat.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  fun g₁ g₂ h => by
  have t0 : asHom g₁ ≫ f = asHom g₂ ≫ f := by cat_disch
  have t1 : asHom g₁ = asHom g₂ := (cancel_mono _).1 t0
  apply asHom_injective t1

end AddCommGrpCat

/-- Build an isomorphism in the category `GrpCat` from a `MulEquiv` between `Group`s. -/
@[to_additive (attr := simps)]
/--
Definition of `MulEquiv.toGrpIso` / `MulEquiv.toGrpIso` 的定义

English:
definition MulEquiv.toGrpIso
  signature: {X Y : GrpCat} (e : X ≃* Y)
  body: GrpCat.ofHom e.toMonoidHom
  inv := GrpCat.ofHom e.symm.toMonoidHom

中文:
定义 MulEquiv.toGrpIso
  签名: {X Y : GrpCat} (e : X ≃* Y)
  定义体: GrpCat.ofHom e.toMonoidHom
  inv := GrpCat.ofHom e.symm.toMonoidHom

Depends on / 依赖: GrpCat, GrpCat.ofHom, e.toMonoidHom, toMonoidHom
-/
def MulEquiv.toGrpIso {X Y : GrpCat} (e : X ≃* Y) : X ≅ Y where
  hom := GrpCat.ofHom e.toMonoidHom
  inv := GrpCat.ofHom e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddGrpCat` from an `AddEquiv` between `AddGroup`s. -/
add_decl_doc AddEquiv.toAddGrpIso

/-- Build an isomorphism in the category `CommGrpCat` from a `MulEquiv`
between `CommGroup`s. -/
@[to_additive (attr := simps)]
/--
Definition of `MulEquiv.toCommGrpIso` / `MulEquiv.toCommGrpIso` 的定义

English:
definition MulEquiv.toCommGrpIso
  signature: {X Y : CommGrpCat} (e : X ≃* Y)
  body: CommGrpCat.ofHom e.toMonoidHom
  inv := CommGrpCat.ofHom e.symm.toMonoidHom

中文:
定义 MulEquiv.toCommGrpIso
  签名: {X Y : CommGrpCat} (e : X ≃* Y)
  定义体: CommGrpCat.ofHom e.toMonoidHom
  inv := CommGrpCat.ofHom e.symm.toMonoidHom

Depends on / 依赖: CommGrpCat, CommGrpCat.ofHom, e.toMonoidHom, toMonoidHom
-/
def MulEquiv.toCommGrpIso {X Y : CommGrpCat} (e : X ≃* Y) : X ≅ Y where
  hom := CommGrpCat.ofHom e.toMonoidHom
  inv := CommGrpCat.ofHom e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddCommGrpCat` from an `AddEquiv`
between `AddCommGroup`s. -/
add_decl_doc AddEquiv.toAddCommGrpIso

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `GrpCat`. -/
@[to_additive (attr := simp)]
/--
Definition of `groupIsoToMulEquiv` / `groupIsoToMulEquiv` 的定义

English:
definition groupIsoToMulEquiv
  signature: {X Y : GrpCat} (i : X ≅ Y)
  body: MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

中文:
定义 groupIsoToMulEquiv
  签名: {X Y : GrpCat} (i : X ≅ Y)
  定义体: MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

Depends on / 依赖: MonoidHom, MonoidHom.toMulEquiv, i.hom.hom, i.inv.hom, toMulEquiv
-/
def groupIsoToMulEquiv {X Y : GrpCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build an `addEquiv` from an isomorphism in the category `AddGrpCat` -/
add_decl_doc addGroupIsoToAddEquiv

/-- Build a `MulEquiv` from an isomorphism in the category `CommGrpCat`. -/
@[to_additive (attr := simps!)]
/--
Definition of `commGroupIsoToMulEquiv` / `commGroupIsoToMulEquiv` 的定义

English:
definition commGroupIsoToMulEquiv
  signature: {X Y : CommGrpCat} (i : X ≅ Y)
  body: MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

中文:
定义 commGroupIsoToMulEquiv
  签名: {X Y : CommGrpCat} (i : X ≅ Y)
  定义体: MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

Depends on / 依赖: MonoidHom, MonoidHom.toMulEquiv, i.hom.hom, i.inv.hom, toMulEquiv
-/
def commGroupIsoToMulEquiv {X Y : CommGrpCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build an `AddEquiv` from an isomorphism in the category `AddCommGrpCat`. -/
add_decl_doc addCommGroupIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `Group`s are the same as (isomorphic to) isomorphisms
in `GrpCat` -/
@[to_additive]
/--
Definition of `mulEquivIsoGroupIso` / `mulEquivIsoGroupIso` 的定义

English:
definition mulEquivIsoGroupIso
  signature: {X Y : GrpCat.{u}}
  body: ↾fun e => e.toGrpIso
  inv := ↾fun i => i.groupIsoToMulEquiv

中文:
定义 mulEquivIsoGroupIso
  签名: {X Y : GrpCat.{u}}
  定义体: ↾fun e => e.toGrpIso
  inv := ↾fun i => i.groupIsoToMulEquiv

Depends on / 依赖: e.toGrpIso, toGrpIso
-/
def mulEquivIsoGroupIso {X Y : GrpCat.{u}} : (X ≃* Y) ≅ (X ≅ Y) where
  hom := ↾fun e => e.toGrpIso
  inv := ↾fun i => i.groupIsoToMulEquiv

/-- Additive equivalences between `AddGroup`s are the same
as (isomorphic to) isomorphisms in `AddGrpCat`. -/
add_decl_doc addEquivIsoAddGroupIso

/-- Multiplicative equivalences between `CommGroup`s are the same as (isomorphic to) isomorphisms
in `CommGrpCat`. -/
@[to_additive]
/--
Definition of `mulEquivIsoCommGroupIso` / `mulEquivIsoCommGroupIso` 的定义

English:
definition mulEquivIsoCommGroupIso
  signature: {X Y : CommGrpCat.{u}}
  body: ↾fun e => e.toCommGrpIso
  inv := ↾fun i => i.commGroupIsoToMulEquiv

中文:
定义 mulEquivIsoCommGroupIso
  签名: {X Y : CommGrpCat.{u}}
  定义体: ↾fun e => e.toCommGrpIso
  inv := ↾fun i => i.commGroupIsoToMulEquiv

Depends on / 依赖: e.toCommGrpIso, toCommGrpIso
-/
def mulEquivIsoCommGroupIso {X Y : CommGrpCat.{u}} : (X ≃* Y) ≅ (X ≅ Y) where
  hom := ↾fun e => e.toCommGrpIso
  inv := ↾fun i => i.commGroupIsoToMulEquiv

/-- Additive equivalences between `AddCommGroup`s are
the same as (isomorphic to) isomorphisms in `AddCommGrpCat`. -/
add_decl_doc addEquivIsoAddCommGroupIso

namespace CategoryTheory.Aut

/--
Definition of `isoPerm` / `isoPerm` 的定义

English:
definition isoPerm
  signature: {α : Type u}
  body: GrpCat.ofHom
    { toFun := fun g => g.toEquiv
      map_one' := by aesop
      map_mul' := by aesop }
  inv := GrpCat.ofHom
    { toFun := fun g => g.toIso
      map_one' := by aesop
      map_mul' := by aesop }

中文:
定义 isoPerm
  签名: {α : 类型u}
  定义体: GrpCat.ofHom
    { toFun := fun g => g.toEquiv
      map_one' := by aesop
      map_mul' := by aesop }
  inv := GrpCat.ofHom
    { toFun := fun g => g.toIso
      map_one' := by aesop
      map_mul' := by aesop }

Depends on / 依赖: GrpCat, GrpCat.ofHom
-/
def isoPerm {α : Type u} : GrpCat.of (Aut α) ≅ GrpCat.of (Equiv.Perm α) where
  hom := GrpCat.ofHom
    { toFun := fun g => g.toEquiv
      map_one' := by aesop
      map_mul' := by aesop }
  inv := GrpCat.ofHom
    { toFun := fun g => g.toIso
      map_one' := by aesop
      map_mul' := by aesop }

/--
Definition of `mulEquivPerm` / `mulEquivPerm` 的定义

English:
definition mulEquivPerm
  signature: {α : Type u}
  body: isoPerm.groupIsoToMulEquiv

中文:
定义 mulEquivPerm
  签名: {α : 类型u}
  定义体: isoPerm.groupIsoToMulEquiv

Depends on / 依赖: groupIsoToMulEquiv, isoPerm, isoPerm.groupIsoToMulEquiv
-/
def mulEquivPerm {α : Type u} : Aut α ≃* Equiv.Perm α :=
  isoPerm.groupIsoToMulEquiv

end CategoryTheory.Aut

@[to_additive]
/--
Instance `GrpCat.forget_reflects_isos` / 实例 `GrpCat.forget_reflects_isos`

English:
instance GrpCat.forget_reflects_isos
  signature: : (forget GrpCat.{u}).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget GrpCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := by simp [Iso.toEquiv, i] }
    exact e.toGrpIso.isIso_hom

@[to_additive]

中文:
实例 GrpCat.forget_reflects_isos
  签名: : (forget GrpCat.{u}).ReflectsIsomorphisms where
  定义体: by
    let i := asIso ((forget GrpCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := by simp [Iso.toEquiv, i] }
    exact e.toGrpIso.isIso_hom

@[to_additive]

Depends on / 依赖: GrpCat, Iso.toEquiv, e.toGrpIso.isIso_hom, forget, i.toEquiv, isIso_hom, map_mul, toEquiv, toGrpIso
-/
instance GrpCat.forget_reflects_isos : (forget GrpCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget GrpCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := by simp [Iso.toEquiv, i] }
    exact e.toGrpIso.isIso_hom

@[to_additive]
/--
Instance `CommGrpCat.forget_reflects_isos` / 实例 `CommGrpCat.forget_reflects_isos`

English:
instance CommGrpCat.forget_reflects_isos
  signature: : (forget CommGrpCat.{u}).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget CommGrpCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := by simp [Iso.toEquiv, i] }
    exact e.toCommGrpIso.isIso_hom

中文:
实例 CommGrpCat.forget_reflects_isos
  签名: : (forget CommGrpCat.{u}).ReflectsIsomorphisms where
  定义体: by
    let i := asIso ((forget CommGrpCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := by simp [Iso.toEquiv, i] }
    exact e.toCommGrpIso.isIso_hom

Depends on / 依赖: CommGrpCat, Iso.toEquiv, e.toCommGrpIso.isIso_hom, forget, i.toEquiv, isIso_hom, map_mul, toCommGrpIso, toEquiv
-/
instance CommGrpCat.forget_reflects_isos : (forget CommGrpCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommGrpCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := by simp [Iso.toEquiv, i] }
    exact e.toCommGrpIso.isIso_hom

-- note: in the following definitions, there is a problem with `@[to_additive]`
-- as the `Category` instance is not found on the additive variant
-- this variant is then renamed with an `Aux` suffix
set_option linter.checkUnivs false in
/-- An alias for `GrpCat.{max u v}`, to deal around unification issues. -/
@[to_additive GrpMaxAux
  /-- An alias for `AddGrpCat.{max u v}`, to deal around unification issues. -/]
/--
Definition of `GrpMax.` / `GrpMax.` 的定义

English:
abbreviation GrpMax.{u1,
  signature: u2}
  body: GrpCat.{max u1 u2}

中文:
缩写 GrpMax.{u1,
  签名: u2}
  定义体: GrpCat.{max u1 u2}

Depends on / 依赖: GrpCat
-/
abbrev GrpMax.{u1, u2} := GrpCat.{max u1 u2}

set_option linter.checkUnivs false in
/--
Definition of `AddGrpMax.` / `AddGrpMax.` 的定义

English:
abbreviation AddGrpMax.{u1,
  signature: u2}
  body: AddGrpCat.{max u1 u2}

中文:
缩写 AddGrpMax.{u1,
  签名: u2}
  定义体: AddGrpCat.{max u1 u2}

Depends on / 依赖: AddGrpCat
-/
abbrev AddGrpMax.{u1, u2} := AddGrpCat.{max u1 u2}

set_option linter.checkUnivs false in
/-- An alias for `CommGrpCat.{max u v}`, to deal around unification issues. -/
@[to_additive AddCommGrpMaxAux
  /-- An alias for `AddCommGrpCat.{max u v}`, to deal around unification issues. -/]
/--
Definition of `CommGrpMax.` / `CommGrpMax.` 的定义

English:
abbreviation CommGrpMax.{u1,
  signature: u2}
  body: CommGrpCat.{max u1 u2}

中文:
缩写 CommGrpMax.{u1,
  签名: u2}
  定义体: CommGrpCat.{max u1 u2}

Depends on / 依赖: CommGrpCat
-/
abbrev CommGrpMax.{u1, u2} := CommGrpCat.{max u1 u2}

set_option linter.checkUnivs false in
/--
Definition of `AddCommGrpMax.` / `AddCommGrpMax.` 的定义

English:
abbreviation AddCommGrpMax.{u1,
  signature: u2}
  body: AddCommGrpCat.{max u1 u2}

中文:
缩写 AddCommGrpMax.{u1,
  签名: u2}
  定义体: AddCommGrpCat.{max u1 u2}

Depends on / 依赖: AddCommGrpCat
-/
abbrev AddCommGrpMax.{u1, u2} := AddCommGrpCat.{max u1 u2}
