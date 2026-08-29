/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.WithTerminal.Cone

/-!
# The category of commutative algebras over a commutative ring

This file defines the bundled category `CommAlgCat` of commutative algebras over a fixed commutative
ring `R` along with the forgetful functors to `CommRingCat` and `AlgCat`.
-/

@[expose] public section

open CategoryTheory Limits

universe w v u

variable {R : Type u} [CommRing R]

variable (R) in
/--
Definition of `CommAlgCat` / `CommAlgCat` 的定义

English:
structure CommAlgCat
  parameters: where
  axioms and operations (4):
    - private(mk) : :
    - carrier : Type v
    - [commRing : CommRing carrier]
    - [algebra : Algebra R carrier]

中文:
结构 CommAlgCat
  参数: where
  公理与运算 (4 个):
    - private(mk) : :
    - carrier : 类型v
    - [commRing : CommRing carrier]
    - [algebra : Algebra R carrier]
-/
structure CommAlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]

namespace CommAlgCat
variable {A B C : CommAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [Algebra R X]
  [CommRing Y] [Algebra R Y] [CommRing Z] [Algebra R Z]

attribute [instance] commRing algebra

initialize_simps_projections CommAlgCat (-commRing, -algebra)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (CommAlgCat R) (Type v)
  body: ⟨carrier⟩

中文:
实例 :
  签名: CoeSort (CommAlgCat R) (类型v)
  定义体: ⟨carrier⟩

Depends on / 依赖: carrier
-/
instance : CoeSort (CommAlgCat R) (Type v) := ⟨carrier⟩

attribute [coe] carrier

variable (R) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type v) [CommRing X] [Algebra R X]
  body: ⟨X⟩

中文:
缩写 of
  签名: (X : 类型v) [CommRing X] [Algebra R X]
  定义体: ⟨X⟩
-/
abbrev of (X : Type v) [CommRing X] [Algebra R X] : CommAlgCat.{v} R := ⟨X⟩

variable (R) in
/--
lemma `coe_of` / 引理 `coe_of`

English:
lemma coe_of
  given: (X : Type v) [CommRing X] [Algebra R X]
  statement: (of R X : Type v) = X
  proof: rfl

中文:
引理 coe_of
  条件: (X : 类型v) [CommRing X] [Algebra R X]
  结论: (of R X : 类型v) = X
  证明: rfl
-/
lemma coe_of (X : Type v) [CommRing X] [Algebra R X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `CommAlgCat R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (A B : CommAlgCat.{v} R)
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->ₐ[R] B

中文:
结构 Hom
  参数: (A B : CommAlgCat.{v} R)
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->ₐ[R] B
-/
structure Hom (A B : CommAlgCat.{v} R) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A ->ₐ[R] B

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (CommAlgCat.{v} R)
  body: Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category (CommAlgCat.{v} R)
  定义体: Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category (CommAlgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory (CommAlgCat.{v} R) (· ->ₐ[R] ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: ConcreteCategory (CommAlgCat.{v} R) (· ->ₐ[R] ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory (CommAlgCat.{v} R) (· ->ₐ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: (f : Hom A B)
  body: ConcreteCategory.hom (C := CommAlgCat R) f

中文:
缩写 Hom.hom
  签名: (f : Hom A B)
  定义体: ConcreteCategory.hom (C := CommAlgCat R) f
-/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := CommAlgCat R) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: (f : X ->ₐ[R] Y)
  body: ConcreteCategory.ofHom (C := CommAlgCat R) f

中文:
缩写 ofHom
  签名: (f : X ->ₐ[R] Y)
  定义体: ConcreteCategory.ofHom (C := CommAlgCat R) f

Depends on / 依赖: CommAlgCat, ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom (f : X ->ₐ[R] Y) : of R X ⟶ of R Y := ConcreteCategory.ofHom (C := CommAlgCat R) f

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (A B : CommAlgCat.{v} R) (f : Hom A B)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (A B : CommAlgCat.{v} R) (f : Hom A B)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (A B : CommAlgCat.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' -> hom)


/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  statement: (𝟙 A : A ⟶ A).hom = AlgHom.id R A
  proof: rfl

中文:
引理 hom_id
  结论: (𝟙 A : A ⟶ A).hom = AlgHom.id R A
  证明: rfl
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (A : CommAlgCat.{v} R) (a : A)
  statement: (𝟙 A : A ⟶ A) a = a
  proof: by simp

中文:
引理 id_apply
  条件: (A : CommAlgCat.{v} R) (a : A)
  结论: (𝟙 A : A ⟶ A) a = a
  证明: by simp
-/
lemma id_apply (A : CommAlgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: (f : A ⟶ B) (g : B ⟶ C)
  statement: (f ≫ g).hom = g.hom.comp f.hom
  proof: rfl

中文:
引理 hom_comp
  条件: (f : A ⟶ B) (g : B ⟶ C)
  结论: (f ≫ g).hom = g.hom.comp f.hom
  证明: rfl
-/
@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: (f : A ⟶ B) (g : B ⟶ C) (a : A)
  statement: (f ≫ g) a = g (f a)
  proof: by simp

中文:
引理 comp_apply
  条件: (f : A ⟶ B) (g : B ⟶ C) (a : A)
  结论: (f ≫ g) a = g (f a)
  证明: by simp
-/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {f g : A ⟶ B} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

中文:
引理 hom_ext
  条件: {f g : A ⟶ B} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf
-/
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: (f : X ->ₐ[R] Y)
  statement: (ofHom f).hom = f
  proof: rfl

中文:
引理 hom_ofHom
  条件: (f : X ->ₐ[R] Y)
  结论: (ofHom f).hom = f
  证明: rfl
-/
@[simp] lemma hom_ofHom (f : X ->ₐ[R] Y) : (ofHom f).hom = f := rfl
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: (f : A ⟶ B)
  statement: ofHom f.hom = f
  proof: rfl

中文:
引理 ofHom_hom
  条件: (f : A ⟶ B)
  结论: ofHom f.hom = f
  证明: rfl
-/
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  statement: ofHom (.id R X) = 𝟙 (of R X)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  结论: ofHom (.id R X) = 𝟙 (of R X)
  证明: rfl

@[simp]
-/
@[simp] lemma ofHom_id : ofHom (.id R X) = 𝟙 (of R X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  given: (f : X ->ₐ[R] Y) (g : Y ->ₐ[R] Z)
  statement: ofHom (g.comp f) = ofHom f ≫ ofHom g
  proof: rfl

中文:
引理 ofHom_comp
  条件: (f : X ->ₐ[R] Y) (g : Y ->ₐ[R] Z)
  结论: ofHom (g.comp f) = ofHom f ≫ ofHom g
  证明: rfl
-/
lemma ofHom_comp (f : X ->ₐ[R] Y) (g : Y ->ₐ[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: (f : X ->ₐ[R] Y) (x : X)
  statement: ofHom f x = f x
  proof: rfl

中文:
引理 ofHom_apply
  条件: (f : X ->ₐ[R] Y) (x : X)
  结论: ofHom f x = f x
  证明: rfl
-/
lemma ofHom_apply (f : X ->ₐ[R] Y) (x : X) : ofHom f x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: (e : A ≅ B) (x : A)
  statement: e.inv (e.hom x) = x
  proof: by simp

中文:
引理 inv_hom_apply
  条件: (e : A ≅ B) (x : A)
  结论: e.inv (e.hom x) = x
  证明: by simp
-/
lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp
/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: (e : A ≅ B) (x : B)
  statement: e.hom (e.inv x) = x
  proof: by simp

中文:
引理 hom_inv_apply
  条件: (e : A ≅ B) (x : B)
  结论: e.hom (e.inv x) = x
  证明: by simp
-/
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (CommAlgCat R)
  body: ⟨of R R⟩

中文:
实例 :
  签名: Inhabited (CommAlgCat R)
  定义体: ⟨of R R⟩
-/
instance : Inhabited (CommAlgCat R) := ⟨of R R⟩

/--
lemma `forget_obj` / 引理 `forget_obj`

English:
lemma forget_obj
  given: (A : CommAlgCat.{v} R)
  statement: (forget (CommAlgCat.{v} R)).obj A = A
  proof: rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-06")]

中文:
引理 forget_obj
  条件: (A : CommAlgCat.{v} R)
  结论: (forget (CommAlgCat.{v} R)).obj A = A
  证明: rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-06")]
-/
lemma forget_obj (A : CommAlgCat.{v} R) : (forget (CommAlgCat.{v} R)).obj A = A := rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-06")]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: (f : A ⟶ B)
  statement: (forget (CommAlgCat.{v} R)).map f = (f : _ -> _)
  proof: rfl

中文:
引理 forget_map
  条件: (f : A ⟶ B)
  结论: (forget (CommAlgCat.{v} R)).map f = (f : _ -> _)
  证明: rfl
-/
lemma forget_map (f : A ⟶ B) : (forget (CommAlgCat.{v} R)).map f = (f : _ -> _) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing ((forget (CommAlgCat R)).obj A)
  body: inferInstanceAs CommRing A

中文:
实例 :
  签名: CommRing ((forget (CommAlgCat R)).obj A)
  定义体: inferInstanceAs CommRing A

Depends on / 依赖: CommRing
-/
instance : CommRing ((forget (CommAlgCat R)).obj A) := inferInstanceAs CommRing A

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R ((forget (CommAlgCat R)).obj A)
  body: inferInstanceAs Algebra R A

中文:
实例 :
  签名: Algebra R ((forget (CommAlgCat R)).obj A)
  定义体: inferInstanceAs Algebra R A

Depends on / 依赖: Algebra
-/
instance : Algebra R ((forget (CommAlgCat R)).obj A) := inferInstanceAs Algebra R A

/--
Instance `hasForgetToCommRingCat` / 实例 `hasForgetToCommRingCat`

English:
instance hasForgetToCommRingCat
  signature: : HasForget₂ (CommAlgCat.{v} R) CommRingCat.{v} where
  body: .of A
  forget₂.map f := CommRingCat.ofHom f.hom.toRingHom

中文:
实例 hasForgetToCommRingCat
  签名: : HasForget₂ (CommAlgCat.{v} R) CommRingCat.{v} where
  定义体: .of A
  forget₂.map f := CommRingCat.ofHom f.hom.toRingHom
-/
instance hasForgetToCommRingCat : HasForget₂ (CommAlgCat.{v} R) CommRingCat.{v} where
  forget₂.obj A := .of A
  forget₂.map f := CommRingCat.ofHom f.hom.toRingHom

/--
Instance `hasForgetToAlgCat` / 实例 `hasForgetToAlgCat`

English:
instance hasForgetToAlgCat
  signature: : HasForget₂ (CommAlgCat.{v} R) (AlgCat.{v} R) where
  body: .of R A
  forget₂.map f := AlgCat.ofHom f.hom

中文:
实例 hasForgetToAlgCat
  签名: : HasForget₂ (CommAlgCat.{v} R) (AlgCat.{v} R) where
  定义体: .of R A
  forget₂.map f := AlgCat.ofHom f.hom
-/
instance hasForgetToAlgCat : HasForget₂ (CommAlgCat.{v} R) (AlgCat.{v} R) where
  forget₂.obj A := .of R A
  forget₂.map f := AlgCat.ofHom f.hom

/--
lemma `forget₂_commRingCat_obj` / 引理 `forget₂_commRingCat_obj`

English:
lemma forget₂_commRingCat_obj
  given: (A : CommAlgCat.{v} R)
  proof: rfl

中文:
引理 forget₂_commRingCat_obj
  条件: (A : CommAlgCat.{v} R)
  证明: rfl
-/
@[simp] lemma forget₂_commRingCat_obj (A : CommAlgCat.{v} R) :
    (forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).obj A = .of A := rfl

/--
lemma `forget₂_commRingCat_map` / 引理 `forget₂_commRingCat_map`

English:
lemma forget₂_commRingCat_map
  given: (f : A ⟶ B)
  proof: rfl

中文:
引理 forget₂_commRingCat_map
  条件: (f : A ⟶ B)
  证明: rfl
-/
@[simp] lemma forget₂_commRingCat_map (f : A ⟶ B) :
    (forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).map f = CommRingCat.ofHom f.hom := rfl

/--
lemma `forget₂_algCat_obj` / 引理 `forget₂_algCat_obj`

English:
lemma forget₂_algCat_obj
  given: (A : CommAlgCat.{v} R)
  proof: rfl

中文:
引理 forget₂_algCat_obj
  条件: (A : CommAlgCat.{v} R)
  证明: rfl
-/
@[simp] lemma forget₂_algCat_obj (A : CommAlgCat.{v} R) :
    (forget₂ (CommAlgCat.{v} R) (AlgCat.{v} R)).obj A = .of R A := rfl

/--
lemma `forget₂_algCat_map` / 引理 `forget₂_algCat_map`

English:
lemma forget₂_algCat_map
  given: (f : A ⟶ B)
  proof: rfl

中文:
引理 forget₂_algCat_map
  条件: (f : A ⟶ B)
  证明: rfl
-/
@[simp] lemma forget₂_algCat_map (f : A ⟶ B) :
    (forget₂ (CommAlgCat.{v} R) (AlgCat.{v} R)).map f = AlgCat.ofHom f.hom := rfl

/-- Build an isomorphism in the category `CommAlgCat R` from an `AlgEquiv` between commutative
`Algebra`s. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Algebra R X} {_ : Algebra R Y}
  body: ofHom (e : X ->ₐ[R] Y)
  inv := ofHom (e.symm : Y ->ₐ[R] X)

中文:
定义 isoMk
  签名: {X Y : 类型v} {_ : CommRing X} {_ : CommRing Y} {_ : Algebra R X} {_ : Algebra R Y}
  定义体: ofHom (e : X ->ₐ[R] Y)
  inv := ofHom (e.symm : Y ->ₐ[R] X)
-/
def isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Algebra R X} {_ : Algebra R Y}
    (e : X ≃ₐ[R] Y) : of R X ≅ of R Y where
  hom := ofHom (e : X ->ₐ[R] Y)
  inv := ofHom (e.symm : Y ->ₐ[R] X)

/-- Build an `AlgEquiv` from an isomorphism in the category `CommAlgCat R`. -/
@[simps]
/--
Definition of `algEquivOfIso` / `algEquivOfIso` 的定义

English:
definition algEquivOfIso
  signature: (i : A ≅ B)
  body: i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

中文:
定义 algEquivOfIso
  签名: (i : A ≅ B)
  定义体: i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

Depends on / 依赖: i.hom.hom
-/
def algEquivOfIso (i : A ≅ B) : A ≃ₐ[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/-- Algebra equivalences between `Algebra`s are the same as isomorphisms in `CommAlgCat`. -/
@[simps]
/--
Definition of `isoEquivAlgEquiv` / `isoEquivAlgEquiv` 的定义

English:
definition isoEquivAlgEquiv
  signature: : (of R X ≅ of R Y) ≃ (X ≃ₐ[R] Y) where
  body: algEquivOfIso
  invFun := isoMk

中文:
定义 isoEquivAlgEquiv
  签名: : (of R X ≅ of R Y) ≃ (X ≃ₐ[R] Y) where
  定义体: algEquivOfIso
  invFun := isoMk

Depends on / 依赖: algEquivOfIso
-/
def isoEquivAlgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐ[R] Y) where
  toFun := algEquivOfIso
  invFun := isoMk

/--
Instance `reflectsIsomorphisms_forget` / 实例 `reflectsIsomorphisms_forget`

English:
instance reflectsIsomorphisms_forget
  signature: : (forget (CommAlgCat.{u} R)).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget (CommAlgCat.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

中文:
实例 reflectsIsomorphisms_forget
  签名: : (forget (CommAlgCat.{u} R)).ReflectsIsomorphisms where
  定义体: by
    let i := asIso ((forget (CommAlgCat.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

Depends on / 依赖: CommAlgCat, f.hom, forget, i.toEquiv, isIso_hom, toEquiv
-/
instance reflectsIsomorphisms_forget : (forget (CommAlgCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommAlgCat.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

variable (R)

/--
Definition of `uliftFunctor` / `uliftFunctor` 的定义

English:
definition uliftFunctor
  signature: : CommAlgCat.{v} R ⥤ CommAlgCat.{max v w} R where
  body: .of R ULift A
map {A B} f := CommAlgCat.ofHom
ULift.algEquiv.symm.toAlgHom.comp f.hom.comp ULift.algEquiv.toAlgHom

中文:
定义 uliftFunctor
  签名: : CommAlgCat.{v} R ⥤ CommAlgCat.{max v w} R where
  定义体: .of R ULift A
map {A B} f := CommAlgCat.ofHom
ULift.algEquiv.symm.toAlgHom.comp f.hom.comp ULift.algEquiv.toAlgHom
-/
def uliftFunctor : CommAlgCat.{v} R ⥤ CommAlgCat.{max v w} R where
obj A := .of R ULift A
map {A B} f := CommAlgCat.ofHom
ULift.algEquiv.symm.toAlgHom.comp f.hom.comp ULift.algEquiv.toAlgHom

/--
Definition of `fullyFaithfulUliftFunctor` / `fullyFaithfulUliftFunctor` 的定义

English:
definition fullyFaithfulUliftFunctor
  signature: : (uliftFunctor R).FullyFaithful where
  body: CommAlgCat.ofHom ULift.algEquiv.toAlgHom.comp f.hom.comp ULift.algEquiv.symm.toAlgHom

中文:
定义 fullyFaithfulUliftFunctor
  签名: : (uliftFunctor R).FullyFaithful where
  定义体: CommAlgCat.ofHom ULift.algEquiv.toAlgHom.comp f.hom.comp ULift.algEquiv.symm.toAlgHom

Depends on / 依赖: CommAlgCat, CommAlgCat.ofHom, ULift.algEquiv.symm.toAlgHom, ULift.algEquiv.toAlgHom.comp, algEquiv, f.hom.comp, toAlgHom
-/
def fullyFaithfulUliftFunctor : (uliftFunctor R).FullyFaithful where
  preimage {A B} f :=
CommAlgCat.ofHom ULift.algEquiv.toAlgHom.comp f.hom.comp ULift.algEquiv.symm.toAlgHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uliftFunctor R).Full
  body: (fullyFaithfulUliftFunctor R).full

中文:
实例 :
  签名: (uliftFunctor R).Full
  定义体: (fullyFaithfulUliftFunctor R).full

Depends on / 依赖: fullyFaithfulUliftFunctor
-/
instance : (uliftFunctor R).Full :=
  (fullyFaithfulUliftFunctor R).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uliftFunctor R).Faithful
  body: (fullyFaithfulUliftFunctor R).faithful

中文:
实例 :
  签名: (uliftFunctor R).Faithful
  定义体: (fullyFaithfulUliftFunctor R).faithful

Depends on / 依赖: faithful, fullyFaithfulUliftFunctor
-/
instance : (uliftFunctor R).Faithful :=
  (fullyFaithfulUliftFunctor R).faithful

end CommAlgCat

/-- The category of commutative algebras over a commutative ring `R` is the same as commutative
rings under `R`. -/
@[simps]
/--
Definition of `commAlgCatEquivUnder` / `commAlgCatEquivUnder` 的定义

English:
definition commAlgCatEquivUnder
  signature: (R : CommRingCat)
  body: R.mkUnder A
  functor.map {A B} f := f.hom.toUnder
  inverse.obj A := .of _ A
inverse.map {A B} f := CommAlgCat.ofHom CommRingCat.toAlgHom f
  unitIso := NatIso.ofComponents fun A =>
    CommAlgCat.isoMk { toRingEquiv := .refl A, commutes' _ := rfl }
  counitIso := .refl _

中文:
定义 commAlgCatEquivUnder
  签名: (R : CommRingCat)
  定义体: R.mkUnder A
  functor.map {A B} f := f.hom.toUnder
  inverse.obj A := .of _ A
inverse.map {A B} f := CommAlgCat.ofHom CommRingCat.toAlgHom f
  unitIso := NatIso.ofComponents fun A =>
    CommAlgCat.isoMk { toRingEquiv := .refl A, commutes' _ := rfl }
  counitIso := .refl _

Depends on / 依赖: R.mkUnder, mkUnder
-/
def commAlgCatEquivUnder (R : CommRingCat) : CommAlgCat R ≌ Under R where
  functor.obj A := R.mkUnder A
  functor.map {A B} f := f.hom.toUnder
  inverse.obj A := .of _ A
inverse.map {A B} f := CommAlgCat.ofHom CommRingCat.toAlgHom f
  unitIso := NatIso.ofComponents fun A =>
    CommAlgCat.isoMk { toRingEquiv := .refl A, commutes' _ := rfl }
  counitIso := .refl _

-- TODO: Generalize to `UnivLE.{u, v}` once `commAlgCatEquivUnder` is generalized.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimits (CommAlgCat.{u} R)
  body: Adjunction.has_colimits_of_equivalence (commAlgCatEquivUnder (.of R)).functor

中文:
实例 :
  签名: HasColimits (CommAlgCat.{u} R)
  定义体: Adjunction.has_colimits_of_equivalence (commAlgCatEquivUnder (.of R)).functor

Depends on / 依赖: Adjunction, Adjunction.has_colimits_of_equivalence, commAlgCatEquivUnder, functor, has_colimits_of_equivalence
-/
instance : HasColimits (CommAlgCat.{u} R) :=
  Adjunction.has_colimits_of_equivalence (commAlgCatEquivUnder (.of R)).functor

-- TODO: Generalize to `UnivLE.{u, v}` once `commAlgCatEquivUnder` is generalized.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimits (CommAlgCat.{u} R)
  body: Adjunction.has_limits_of_equivalence (commAlgCatEquivUnder (.of R)).functor

中文:
实例 :
  签名: HasLimits (CommAlgCat.{u} R)
  定义体: Adjunction.has_limits_of_equivalence (commAlgCatEquivUnder (.of R)).functor

Depends on / 依赖: Adjunction, Adjunction.has_limits_of_equivalence, commAlgCatEquivUnder, functor, has_limits_of_equivalence
-/
instance : HasLimits (CommAlgCat.{u} R) :=
  Adjunction.has_limits_of_equivalence (commAlgCatEquivUnder (.of R)).functor
