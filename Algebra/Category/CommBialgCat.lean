/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# The category of commutative bialgebras over a commutative ring

This file defines the bundled category `CommBialgCat R` of commutative bialgebras over a fixed
commutative ring `R` along with the forgetful functor to `CommAlgCat`.
-/

@[expose] public section

noncomputable section

open Bialgebra Coalgebra Opposite CategoryTheory Limits MonObj
open scoped MonoidalCategory

universe v u
variable {R : Type u} [CommRing R]

variable (R) in
/--
Definition of `CommBialgCat` / `CommBialgCat` 的定义

English:
structure CommBialgCat
  parameters: where
  axioms and operations (4):
    - private(mk) : :
    - carrier : Type v
    - [commRing : CommRing carrier]
    - [bialgebra : Bialgebra R carrier]

中文:
结构 交换Bialg范畴
  参数: where
  公理与运算 (4 个):
    - private(mk) : :
    - carrier : 类型v
    - [commRing : 交换环 carrier]
    - [bialgebra : 双代数 R carrier]
-/
structure CommBialgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [bialgebra : Bialgebra R carrier]

namespace CommBialgCat
variable {A B C : CommBialgCat.{v} R} {X Y Z : Type v} [CommRing X] [Bialgebra R X]
  [CommRing Y] [Bialgebra R Y] [CommRing Z] [Bialgebra R Z]

attribute [instance] commRing bialgebra

initialize_simps_projections CommBialgCat (-commRing, -bialgebra)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (CommBialgCat R) (Type v)
  body: ⟨carrier⟩

中文:
实例 :
  签名: CoeSort (交换Bialg范畴 R) (类型v)
  定义体: ⟨carrier⟩

Depends on / 依赖: carrier
-/
instance : CoeSort (CommBialgCat R) (Type v) := ⟨carrier⟩

attribute [coe] CommBialgCat.carrier

variable (R) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type v) [CommRing X] [Bialgebra R X]
  body: ⟨X⟩

中文:
缩写 of
  签名: (X : 类型v) [交换环 X] [双代数 R X]
  定义体: ⟨X⟩
-/
abbrev of (X : Type v) [CommRing X] [Bialgebra R X] : CommBialgCat.{v} R := ⟨X⟩

variable (R) in
/--
lemma `coe_of` / 引理 `coe_of`

English:
lemma coe_of
  given: (X : Type v) [CommRing X] [Bialgebra R X]
  statement: (of R X : Type v) = X
  proof: rfl

中文:
引理 coe_of
  条件: (X : 类型v) [交换环 X] [双代数 R X]
  结论: (of R X : 类型v) = X
  证明: rfl
-/
lemma coe_of (X : Type v) [CommRing X] [Bialgebra R X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `CommBialgCat R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (A B : CommBialgCat.{v} R)
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->ₐc[R] B

中文:
结构 态射
  参数: (A B : 交换Bialg范畴.{v} R)
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->ₐc[R] B
-/
structure Hom (A B : CommBialgCat.{v} R) where
  private mk ::
  /-- The underlying bialgebra map. -/
  hom' : A ->ₐc[R] B

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (CommBialgCat.{v} R)
  body: Hom A B
  id A := ⟨.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 (交换Bialg范畴.{v} R)
  定义体: Hom A B
  id A := ⟨.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category (CommBialgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory (CommBialgCat.{v} R) (· ->ₐc[R] ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: 余ncrete范畴 (交换Bialg范畴.{v} R) (· ->ₐc[R] ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory (CommBialgCat.{v} R) (· ->ₐc[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: (f : Hom A B)
  body: ConcreteCategory.hom (C := CommBialgCat R) f

中文:
缩写 态射.hom
  签名: (f : 态射 A B)
  定义体: ConcreteCategory.hom (C := CommBialgCat R) f
-/
abbrev Hom.hom (f : Hom A B) : A ->ₐc[R] B := ConcreteCategory.hom (C := CommBialgCat R) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
  body: ConcreteCategory.ofHom (C := CommBialgCat R) f

中文:
缩写 ofHom
  签名: {X Y : 类型v} {_ : 交换环 X} {_ : 交换环 Y} {_ : 双代数 R X}
  定义体: ConcreteCategory.ofHom (C := CommBialgCat R) f

Depends on / 依赖: CommBialgCat, ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
    {_ : Bialgebra R Y} (f : X ->ₐc[R] Y) : of R X ⟶ of R Y :=
  ConcreteCategory.ofHom (C := CommBialgCat R) f

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (A B : CommBialgCat.{v} R) (f : Hom A B)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (A B : 交换Bialg范畴.{v} R) (f : 态射 A B)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)

Depends on / 依赖: f.hom
-/
def Hom.Simps.hom (A B : CommBialgCat.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' -> hom)


/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  statement: (𝟙 A : A ⟶ A).hom = .id R A
  proof: rfl

中文:
引理 hom_id
  结论: (𝟙 A : A ⟶ A).hom = .id R A
  证明: rfl
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = .id R A := rfl
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
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (A : CommBialgCat.{v} R) (a : A)
  statement: (𝟙 A : A ⟶ A) a = a
  proof: by simp

中文:
引理 id_apply
  条件: (A : 交换Bialg范畴.{v} R) (a : A)
  结论: (𝟙 A : A ⟶ A) a = a
  证明: by simp
-/
lemma id_apply (A : CommBialgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp
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
  given: (f : X ->ₐc[R] Y)
  statement: (ofHom f).hom = f
  proof: rfl

中文:
引理 hom_ofHom
  条件: (f : X ->ₐc[R] Y)
  结论: (ofHom f).hom = f
  证明: rfl
-/
@[simp] lemma hom_ofHom (f : X ->ₐc[R] Y) : (ofHom f).hom = f := rfl
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
  given: (f : X ->ₐc[R] Y) (g : Y ->ₐc[R] Z)
  statement: ofHom (g.comp f) = ofHom f ≫ ofHom g
  proof: rfl

中文:
引理 ofHom_comp
  条件: (f : X ->ₐc[R] Y) (g : Y ->ₐc[R] Z)
  结论: ofHom (g.comp f) = ofHom f ≫ ofHom g
  证明: rfl
-/
lemma ofHom_comp (f : X ->ₐc[R] Y) (g : Y ->ₐc[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: (f : X ->ₐc[R] Y) (x : X)
  statement: ofHom f x = f x
  proof: rfl

中文:
引理 ofHom_apply
  条件: (f : X ->ₐc[R] Y) (x : X)
  结论: ofHom f x = f x
  证明: rfl
-/
lemma ofHom_apply (f : X ->ₐc[R] Y) (x : X) : ofHom f x = f x := rfl

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
  signature: Inhabited (CommBialgCat R)
  body: ⟨of R R⟩

中文:
实例 :
  签名: 可居 (交换Bialg范畴 R)
  定义体: ⟨of R R⟩
-/
instance : Inhabited (CommBialgCat R) := ⟨of R R⟩

/--
lemma `forget_obj` / 引理 `forget_obj`

English:
lemma forget_obj
  given: (A : CommBialgCat.{v} R)
  statement: (forget (CommBialgCat.{v} R)).obj A = A
  proof: rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-06")]

中文:
引理 forget_obj
  条件: (A : 交换Bialg范畴.{v} R)
  结论: (forget (交换Bialg范畴.{v} R)).obj A = A
  证明: rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-06")]
-/
lemma forget_obj (A : CommBialgCat.{v} R) : (forget (CommBialgCat.{v} R)).obj A = A :=
  rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-06")]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: (f : A ⟶ B)
  statement: (forget (CommBialgCat.{v} R)).map f = (f : _ -> _)
  proof: rfl

中文:
引理 forget_map
  条件: (f : A ⟶ B)
  结论: (forget (交换Bialg范畴.{v} R)).map f = (f : _ -> _)
  证明: rfl
-/
lemma forget_map (f : A ⟶ B) : (forget (CommBialgCat.{v} R)).map f = (f : _ -> _) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing ((forget (CommBialgCat R)).obj A)
  body: inferInstanceAs CommRing A

中文:
实例 :
  签名: 交换环 ((forget (交换Bialg范畴 R)).obj A)
  定义体: inferInstanceAs CommRing A

Depends on / 依赖: CommRing
-/
instance : CommRing ((forget (CommBialgCat R)).obj A) := inferInstanceAs CommRing A

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bialgebra R ((forget (CommBialgCat R)).obj A)
  body: inferInstanceAs Bialgebra R A

中文:
实例 :
  签名: 双代数 R ((forget (交换Bialg范畴 R)).obj A)
  定义体: inferInstanceAs Bialgebra R A

Depends on / 依赖: Bialgebra
-/
instance : Bialgebra R ((forget (CommBialgCat R)).obj A) := inferInstanceAs Bialgebra R A

/--
Instance `hasForgetToCommAlgCat` / 实例 `hasForgetToCommAlgCat`

English:
instance hasForgetToCommAlgCat
  signature: : HasForget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R) where
  body: .of R M
  forget₂.map f := CommAlgCat.ofHom f.hom.toAlgHom

中文:
实例 hasForgetToCommAlgCat
  签名: : 有Forget₂ (交换Bialg范畴.{v} R) (交换Alg范畴.{v} R) where
  定义体: .of R M
  forget₂.map f := CommAlgCat.ofHom f.hom.toAlgHom
-/
instance hasForgetToCommAlgCat : HasForget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R) where
  forget₂.obj M := .of R M
  forget₂.map f := CommAlgCat.ofHom f.hom.toAlgHom

/--
lemma `forget₂_commAlgCat_obj` / 引理 `forget₂_commAlgCat_obj`

English:
lemma forget₂_commAlgCat_obj
  given: (A : CommBialgCat.{v} R)
  proof: rfl

中文:
引理 forget₂_commAlgCat_obj
  条件: (A : 交换Bialg范畴.{v} R)
  证明: rfl
-/
@[simp] lemma forget₂_commAlgCat_obj (A : CommBialgCat.{v} R) :
    (forget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R)).obj A = .of R A := rfl

/--
lemma `forget₂_commAlgCat_map` / 引理 `forget₂_commAlgCat_map`

English:
lemma forget₂_commAlgCat_map
  given: (f : A ⟶ B)
  proof: rfl

中文:
引理 forget₂_commAlgCat_map
  条件: (f : A ⟶ B)
  证明: rfl
-/
@[simp] lemma forget₂_commAlgCat_map (f : A ⟶ B) :
    (forget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R)).map f =
      CommAlgCat.ofHom f.hom.toAlgHom := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original
bialgebra. -/
@[simps]
/--
Definition of `ofIsoSelf` / `ofIsoSelf` 的定义

English:
definition ofIsoSelf
  signature: (M : CommBialgCat.{v} R)
  body: 𝟙 M
  inv := 𝟙 M

@[deprecated (since := "2026-06-09")] alias ofSelfIso := ofIsoSelf

中文:
定义 ofIsoSelf
  签名: (M : 交换Bialg范畴.{v} R)
  定义体: 𝟙 M
  inv := 𝟙 M

@[deprecated (since := "2026-06-09")] alias ofSelfIso := ofIsoSelf
-/
def ofIsoSelf (M : CommBialgCat.{v} R) : of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

@[deprecated (since := "2026-06-09")] alias ofSelfIso := ofIsoSelf

/-- Build an isomorphism in the category `CommBialgCat R` from a `BialgEquiv` between
`Bialgebra`s. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
  body: ofHom (e : X ->ₐc[R] Y)
  inv := ofHom (e.symm : Y ->ₐc[R] X)

中文:
定义 isoMk
  签名: {X Y : 类型v} {_ : 交换环 X} {_ : 交换环 Y} {_ : 双代数 R X}
  定义体: ofHom (e : X ->ₐc[R] Y)
  inv := ofHom (e.symm : Y ->ₐc[R] X)
-/
def isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
    {_ : Bialgebra R Y} (e : X ≃ₐc[R] Y) : of R X ≅ of R Y where
  hom := ofHom (e : X ->ₐc[R] Y)
  inv := ofHom (e.symm : Y ->ₐc[R] X)

/-- Build a `BialgEquiv` from an isomorphism in the category `CommBialgCat R`. -/
@[simps apply, simps -isSimp symm_apply]
/--
Definition of `bialgEquivOfIso` / `bialgEquivOfIso` 的定义

English:
definition bialgEquivOfIso
  signature: (i : A ≅ B)
  body: i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

中文:
定义 bialgEquivOfIso
  签名: (i : A ≅ B)
  定义体: i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

Depends on / 依赖: i.hom.hom
-/
def bialgEquivOfIso (i : A ≅ B) : A ≃ₐc[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/-- Bialgebra equivalences between `Bialgebra`s are the same as isomorphisms in `CommBialgCat`. -/
@[simps]
/--
Definition of `isoEquivBialgEquiv` / `isoEquivBialgEquiv` 的定义

English:
definition isoEquivBialgEquiv
  signature: : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where
  body: bialgEquivOfIso
  invFun := isoMk
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 isoEquivBialgEquiv
  签名: : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where
  定义体: bialgEquivOfIso
  invFun := isoMk
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: bialgEquivOfIso
-/
def isoEquivBialgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where
  toFun := bialgEquivOfIso
  invFun := isoMk
  left_inv _ := rfl
  right_inv _ := rfl

/--
Instance `reflectsIsomorphisms_forget` / 实例 `reflectsIsomorphisms_forget`

English:
instance reflectsIsomorphisms_forget
  signature: : (forget (CommBialgCat.{u} R)).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget (CommBialgCat.{u} R)).map f)
    let e : X ≃ₐc[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

中文:
实例 reflectsIsomorphisms_forget
  签名: : (forget (交换Bialg范畴.{u} R)).反映同构 where
  定义体: by
    let i := asIso ((forget (CommBialgCat.{u} R)).map f)
    let e : X ≃ₐc[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

Depends on / 依赖: CommBialgCat, f.hom, forget, i.toEquiv, isIso_hom, toEquiv
-/
instance reflectsIsomorphisms_forget : (forget (CommBialgCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommBialgCat.{u} R)).map f)
    let e : X ≃ₐc[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

end CommBialgCat

attribute [local ext] Quiver.Hom.unop_inj

/--
Instance `CommAlgCat.monObjOpOf` / 实例 `CommAlgCat.monObjOpOf`

English:
instance CommAlgCat.monObjOpOf
  signature: {A : Type u} [CommRing A] [Bialgebra R A]
  body: (CommAlgCat.ofHom <| counitAlgHom R A).op
  mul := (CommAlgCat.ofHom <| comulAlgHom R A).op
  one_mul := by ext; exact Coalgebra.rTensor_counit_comul _
  mul_one := by ext; exact Coalgebra.lTensor_counit_comul _
  mul_assoc := by ext; exact (Coalgebra.coassoc_symm_apply _).symm

@[simp]

中文:
实例 交换Alg范畴.monObjOpOf
  签名: {A : 类型u} [交换环 A] [双代数 R A]
  定义体: (CommAlgCat.ofHom <| counitAlgHom R A).op
  mul := (CommAlgCat.ofHom <| comulAlgHom R A).op
  one_mul := by ext; exact Coalgebra.rTensor_counit_comul _
  mul_one := by ext; exact Coalgebra.lTensor_counit_comul _
  mul_assoc := by ext; exact (Coalgebra.coassoc_symm_apply _).symm

@[simp]

Depends on / 依赖: CommAlgCat, CommAlgCat.ofHom, counitAlgHom
-/
instance CommAlgCat.monObjOpOf {A : Type u} [CommRing A] [Bialgebra R A] :
    MonObj (op <| CommAlgCat.of R A) where
  one := (CommAlgCat.ofHom <| counitAlgHom R A).op
  mul := (CommAlgCat.ofHom <| comulAlgHom R A).op
  one_mul := by ext; exact Coalgebra.rTensor_counit_comul _
  mul_one := by ext; exact Coalgebra.lTensor_counit_comul _
  mul_assoc := by ext; exact (Coalgebra.coassoc_symm_apply _).symm

@[simp]
/--
lemma `CommAlgCat.one_op_of_unop_hom` / 引理 `CommAlgCat.one_op_of_unop_hom`

English:
lemma CommAlgCat.one_op_of_unop_hom
  given: {A : Type u} [CommRing A] [Bialgebra R A]
  proof: rfl

@[simp]

中文:
引理 交换Alg范畴.one_op_of_unop_hom
  条件: {A : 类型u} [交换环 A] [双代数 R A]
  证明: rfl

@[simp]
-/
lemma CommAlgCat.one_op_of_unop_hom {A : Type u} [CommRing A] [Bialgebra R A] :
    η[op <| CommAlgCat.of R A].unop.hom = counitAlgHom R A := rfl

@[simp]
/--
lemma `CommAlgCat.mul_op_of_unop_hom` / 引理 `CommAlgCat.mul_op_of_unop_hom`

English:
lemma CommAlgCat.mul_op_of_unop_hom
  given: {A : Type u} [CommRing A] [Bialgebra R A]
  proof: rfl

中文:
引理 交换Alg范畴.mul_op_of_unop_hom
  条件: {A : 类型u} [交换环 A] [双代数 R A]
  证明: rfl
-/
lemma CommAlgCat.mul_op_of_unop_hom {A : Type u} [CommRing A] [Bialgebra R A] :
    μ[op <| CommAlgCat.of R A].unop.hom = comulAlgHom R A := rfl

instance {A : Type u} [CommRing A] [Bialgebra R A] [IsCocomm R A] :
    IsCommMonObj (Opposite.op <| CommAlgCat.of R A) where
  mul_comm := by ext; exact comm_comul R _

instance {A B : Type u} [CommRing A] [Bialgebra R A] [CommRing B] [Bialgebra R B]
    (f : A ->ₐc[R] B) : IsMonHom (CommAlgCat.ofHom f.toAlgHom).op where

instance (A : (CommAlgCat R)ᵒᵖ) [MonObj A] : Bialgebra R A.unop :=
  .ofAlgHom μ[A].unop.hom η[A].unop.hom
    congr(($((MonObj.mul_assoc_flip A).symm)).unop.hom)
    congr(($(MonObj.one_mul A)).unop.hom)
    congr(($(MonObj.mul_one A)).unop.hom)

variable (R) in
/-- Commutative bialgebras over a commutative ring `R` are the same thing as comonoid
`R`-algebras. -/
@[simps! functor_obj_unop_X inverse_obj unitIso_hom_app
  unitIso_inv_app counitIso_hom_app counitIso_inv_app]
/--
Definition of `commBialgCatEquivComonCommAlgCat` / `commBialgCatEquivComonCommAlgCat` 的定义

English:
definition commBialgCatEquivComonCommAlgCat
  signature: : CommBialgCat R ≌ (Mon (CommAlgCat R)ᵒᵖ)ᵒᵖ where
  body: .op .mk .op .of R A
functor.map {A B} f := .op .mk' .op CommAlgCat.ofHom f.hom.toAlgHom
  inverse.obj A := .of R A.unop.X.unop
inverse.map {A B} f := CommBialgCat.ofHom .ofAlgHom f.unop.hom.unop.hom
    congr(($(IsMonHom.one_hom (f := f.unop.hom))).unop.hom)
    congr(($((IsMonHom.mul_hom (f := f.unop.hom)).symm)).unop.hom)
  unitIso.hom := 𝟙 _
  unitIso.inv := 𝟙 _
  counitIso.hom := 𝟙 _
  counitIso.inv := 𝟙 _

@[simp]

中文:
定义 commBialgCatEquivComonCommAlgCat
  签名: : 交换Bialg范畴 R ≌ (幺半群 (交换Alg范畴 R)ᵒᵖ)ᵒᵖ where
  定义体: .op .mk .op .of R A
functor.map {A B} f := .op .mk' .op CommAlgCat.ofHom f.hom.toAlgHom
  inverse.obj A := .of R A.unop.X.unop
inverse.map {A B} f := CommBialgCat.ofHom .ofAlgHom f.unop.hom.unop.hom
    congr(($(IsMonHom.one_hom (f := f.unop.hom))).unop.hom)
    congr(($((IsMonHom.mul_hom (f := f.unop.hom)).symm)).unop.hom)
  unitIso.hom := 𝟙 _
  unitIso.inv := 𝟙 _
  counitIso.hom := 𝟙 _
  counitIso.inv := 𝟙 _

@[simp]
-/
def commBialgCatEquivComonCommAlgCat : CommBialgCat R ≌ (Mon (CommAlgCat R)ᵒᵖ)ᵒᵖ where
functor.obj A := .op .mk .op .of R A
functor.map {A B} f := .op .mk' .op CommAlgCat.ofHom f.hom.toAlgHom
  inverse.obj A := .of R A.unop.X.unop
inverse.map {A B} f := CommBialgCat.ofHom .ofAlgHom f.unop.hom.unop.hom
    congr(($(IsMonHom.one_hom (f := f.unop.hom))).unop.hom)
    congr(($((IsMonHom.mul_hom (f := f.unop.hom)).symm)).unop.hom)
  unitIso.hom := 𝟙 _
  unitIso.inv := 𝟙 _
  counitIso.hom := 𝟙 _
  counitIso.inv := 𝟙 _

@[simp]
/--
lemma `commBialgCatEquivComonCommAlgCat_functor_map_unop_hom` / 引理 `commBialgCatEquivComonCommAlgCat_functor_map_unop_hom`

English:
lemma commBialgCatEquivComonCommAlgCat_functor_map_unop_hom
  given: {A B : CommBialgCat R} (f : A ⟶ B)
  proof: rfl

@[simp]

中文:
引理 commBialgCatEquivComonCommAlgCat_functor_map_unop_hom
  条件: {A B : 交换Bialg范畴 R} (f : A ⟶ B)
  证明: rfl

@[simp]
-/
lemma commBialgCatEquivComonCommAlgCat_functor_map_unop_hom {A B : CommBialgCat R} (f : A ⟶ B) :
  ((commBialgCatEquivComonCommAlgCat R).functor.map f).unop.hom =
    (CommAlgCat.ofHom f.hom.toAlgHom).op := rfl

@[simp]
/--
lemma `commBialgCatEquivComonCommAlgCat_inverse_map_unop_hom` / 引理 `commBialgCatEquivComonCommAlgCat_inverse_map_unop_hom`

English:
lemma commBialgCatEquivComonCommAlgCat_inverse_map_unop_hom
  proof: rfl

中文:
引理 commBialgCatEquivComonCommAlgCat_inverse_map_unop_hom
  证明: rfl
-/
lemma commBialgCatEquivComonCommAlgCat_inverse_map_unop_hom
    {A B : (Mon (CommAlgCat R)ᵒᵖ)ᵒᵖ} (f : A ⟶ B) :
  ((commBialgCatEquivComonCommAlgCat R).inverse.map f).hom.toAlgHom =
    f.unop.hom.unop.hom := rfl

instance {A : CommBialgCat.{u} R} [IsCocomm R A] :
    IsCommMonObj ((commBialgCatEquivComonCommAlgCat R).functor.obj A).unop.X :=
inferInstanceAs IsCommMonObj op CommAlgCat.of R A
