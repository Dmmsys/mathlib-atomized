/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Category instance for algebras over a commutative ring

We introduce the bundled category `AlgCat` of algebras over a fixed commutative ring `R` along
with the forgetful functors to `RingCat` and `ModuleCat`. We furthermore show that the functor
associating to a type the free `R`-algebra on that type is left adjoint to the forgetful functor.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

variable (R : Type u) [CommRing R]

/--
Definition of `AlgCat` / `AlgCat` 的定义

English:
structure AlgCat
  parameters: where
  axioms and operations (4):
    - private(mk) : :
    - carrier : Type v
    - [isRing : Ring carrier]
    - [isAlgebra : Algebra R carrier]

中文:
结构 Alg范畴
  参数: where
  公理与运算 (4 个):
    - private(mk) : :
    - carrier : 类型v
    - [isRing : 环 carrier]
    - [isAlgebra : 代数 R carrier]
-/
structure AlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [isRing : Ring carrier]
  [isAlgebra : Algebra R carrier]

attribute [instance] AlgCat.isRing AlgCat.isAlgebra

initialize_simps_projections AlgCat (-isRing, -isAlgebra)

namespace AlgCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (AlgCat R) (Type v)
  body: ⟨AlgCat.carrier⟩

中文:
实例 :
  签名: CoeSort (Alg范畴 R) (类型v)
  定义体: ⟨AlgCat.carrier⟩

Depends on / 依赖: AlgCat, AlgCat.carrier, carrier
-/
instance : CoeSort (AlgCat R) (Type v) :=
  ⟨AlgCat.carrier⟩

attribute [coe] AlgCat.carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type v) [Ring X] [Algebra R X]
  body: ⟨X⟩

中文:
缩写 of
  签名: (X : 类型v) [环 X] [代数 R X]
  定义体: ⟨X⟩
-/
abbrev of (X : Type v) [Ring X] [Algebra R X] : AlgCat.{v} R :=
  ⟨X⟩

/--
lemma `coe_of` / 引理 `coe_of`

English:
lemma coe_of
  given: (X : Type v) [Ring X] [Algebra R X]
  statement: (of R X : Type v) = X
  proof: rfl

中文:
引理 coe_of
  条件: (X : 类型v) [环 X] [代数 R X]
  结论: (of R X : 类型v) = X
  证明: rfl
-/
lemma coe_of (X : Type v) [Ring X] [Algebra R X] : (of R X : Type v) = X :=
  rfl

variable {R} in
/-- The type of morphisms in `AlgCat R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (A B : AlgCat.{v} R)
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->ₐ[R] B

中文:
结构 态射
  参数: (A B : Alg范畴.{v} R)
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->ₐ[R] B
-/
structure Hom (A B : AlgCat.{v} R) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A ->ₐ[R] B

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (AlgCat.{v} R)
  body: Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 (Alg范畴.{v} R)
  定义体: Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category (AlgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory (AlgCat.{v} R) (· ->ₐ[R] ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: 余ncrete范畴 (Alg范畴.{v} R) (· ->ₐ[R] ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory (AlgCat.{v} R) (· ->ₐ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {R} in
/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {A B : AlgCat.{v} R} (f : Hom A B)
  body: ConcreteCategory.hom (C := AlgCat R) f

中文:
缩写 态射.hom
  签名: {A B : Alg范畴.{v} R} (f : 态射 A B)
  定义体: ConcreteCategory.hom (C := AlgCat R) f
-/
abbrev Hom.hom {A B : AlgCat.{v} R} (f : Hom A B) :=
  ConcreteCategory.hom (C := AlgCat R) f

variable {R} in
/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {A B : Type v} [Ring A] [Ring B] [Algebra R A] [Algebra R B] (f : A ->ₐ[R] B)
  body: ConcreteCategory.ofHom (C := AlgCat R) f

中文:
缩写 ofHom
  签名: {A B : 类型v} [环 A] [环 B] [代数 R A] [代数 R B] (f : A ->ₐ[R] B)
  定义体: ConcreteCategory.ofHom (C := AlgCat R) f

Depends on / 依赖: AlgCat, ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {A B : Type v} [Ring A] [Ring B] [Algebra R A] [Algebra R B] (f : A ->ₐ[R] B) :
    of R A ⟶ of R B :=
  ConcreteCategory.ofHom (C := AlgCat R) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (A B : AlgCat.{v} R) (f : Hom A B)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (A B : Alg范畴.{v} R) (f : 态射 A B)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (A B : AlgCat.{v} R) (f : Hom A B) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {A : AlgCat.{v} R}
  statement: (𝟙 A : A ⟶ A).hom = AlgHom.id R A
  proof: rfl

中文:
引理 hom_id
  条件: {A : Alg范畴.{v} R}
  结论: (𝟙 A : A ⟶ A).hom = 代数态射.id R A
  证明: rfl
-/
lemma hom_id {A : AlgCat.{v} R} : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (A : AlgCat.{v} R) (a : A)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (A : Alg范畴.{v} R) (a : A)
  证明: by simp

@[simp]
-/
lemma id_apply (A : AlgCat.{v} R) (a : A) :
    (𝟙 A : A ⟶ A) a = a := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C)
  proof: rfl

中文:
引理 hom_comp
  条件: {A B C : Alg范畴.{v} R} (f : A ⟶ B) (g : B ⟶ C)
  证明: rfl
-/
lemma hom_comp {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) (a : A)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {A B C : Alg范畴.{v} R} (f : A ⟶ B) (g : B ⟶ C) (a : A)
  证明: by simp

@[ext]
-/
lemma comp_apply {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {A B : AlgCat.{v} R} {f g : A ⟶ B} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {A B : Alg范畴.{v} R} {f g : A ⟶ B} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {A B : AlgCat.{v} R} {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  statement: {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  结论: {R : 类型u} [交换环 R] {X Y : 类型v} [环 X] [代数 R X] [环 Y]
  证明: rfl

@[simp]
-/
lemma hom_ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X ->ₐ[R] Y) : (ofHom f).hom = f := rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {A B : AlgCat.{v} R} (f : A ⟶ B)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {A B : Alg范畴.{v} R} (f : A ⟶ B)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {A B : AlgCat.{v} R} (f : A ⟶ B) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type v} [Ring X] [Algebra R X]
  statement: ofHom (AlgHom.id R X) = 𝟙 (of R X)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {X : 类型v} [环 X] [代数 R X]
  结论: ofHom (代数态射.id R X) = 𝟙 (of R X)
  证明: rfl

@[simp]
-/
lemma ofHom_id {X : Type v} [Ring X] [Algebra R X] : ofHom (AlgHom.id R X) = 𝟙 (of R X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type v} [Ring X] [Ring Y] [Ring Z] [Algebra R X] [Algebra R Y]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型v} [环 X] [环 Y] [环 Z] [代数 R X] [代数 R Y]
  证明: rfl
-/
lemma ofHom_comp {X Y Z : Type v} [Ring X] [Ring Y] [Ring Z] [Algebra R X] [Algebra R Y]
    [Algebra R Z] (f : X ->ₐ[R] Y) (g : Y ->ₐ[R] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  statement: {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
  proof: rfl

中文:
引理 ofHom_apply
  结论: {R : 类型u} [交换环 R] {X Y : 类型v} [环 X] [代数 R X] [环 Y]
  证明: rfl
-/
lemma ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X ->ₐ[R] Y) (x : X) : ofHom f x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {A B : AlgCat.{v} R} (e : A ≅ B) (x : A)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {A B : Alg范畴.{v} R} (e : A ≅ B) (x : A)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {A B : AlgCat.{v} R} (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {A B : AlgCat.{v} R} (e : A ≅ B) (x : B)
  statement: e.hom (e.inv x) = x
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {A B : Alg范畴.{v} R} (e : A ≅ B) (x : B)
  结论: e.hom (e.inv x) = x
  证明: by
  simp
-/
lemma hom_inv_apply {A B : AlgCat.{v} R} (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (AlgCat R)
  body: ⟨of R R⟩

中文:
实例 :
  签名: 可居 (Alg范畴 R)
  定义体: ⟨of R R⟩
-/
instance : Inhabited (AlgCat R) :=
  ⟨of R R⟩

/--
lemma `forget_obj` / 引理 `forget_obj`

English:
lemma forget_obj
  given: {A : AlgCat.{v} R}
  statement: (forget (AlgCat.{v} R)).obj A = A
  proof: rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-03")]

中文:
引理 forget_obj
  条件: {A : Alg范畴.{v} R}
  结论: (forget (Alg范畴.{v} R)).obj A = A
  证明: rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-03")]
-/
lemma forget_obj {A : AlgCat.{v} R} : (forget (AlgCat.{v} R)).obj A = A := rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-03")]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {A B : AlgCat.{v} R} (f : A ⟶ B)
  proof: rfl

中文:
引理 forget_map
  条件: {A B : Alg范畴.{v} R} (f : A ⟶ B)
  证明: rfl
-/
lemma forget_map {A B : AlgCat.{v} R} (f : A ⟶ B) :
    (forget (AlgCat.{v} R)).map f = (f : _ -> _) :=
  rfl

instance {S : AlgCat.{v} R} : Ring ((forget (AlgCat R)).obj S) :=
inferInstanceAs Ring S.carrier

instance {S : AlgCat.{v} R} : Algebra R ((forget (AlgCat R)).obj S) :=
inferInstanceAs Algebra R S.carrier

/--
Instance `hasForgetToRing` / 实例 `hasForgetToRing`

English:
instance hasForgetToRing
  signature: : HasForget₂ (AlgCat.{v} R) RingCat.{v} where
  body: { obj := fun A => RingCat.of A
      map := fun f => RingCat.ofHom f.hom.toRingHom }

@[simp]

中文:
实例 hasForgetToRing
  签名: : 有Forget₂ (Alg范畴.{v} R) 环范畴.{v} where
  定义体: { obj := fun A => RingCat.of A
      map := fun f => RingCat.ofHom f.hom.toRingHom }

@[simp]

Depends on / 依赖: RingCat, RingCat.of, RingCat.ofHom, f.hom.toRingHom, toRingHom
-/
instance hasForgetToRing : HasForget₂ (AlgCat.{v} R) RingCat.{v} where
  forget₂ :=
    { obj := fun A => RingCat.of A
      map := fun f => RingCat.ofHom f.hom.toRingHom }

@[simp]
/--
lemma `forget₂_ringCat_obj` / 引理 `forget₂_ringCat_obj`

English:
lemma forget₂_ringCat_obj
  given: (X : AlgCat.{v} R)
  proof: rfl

@[simp]

中文:
引理 forget₂_ringCat_obj
  条件: (X : Alg范畴.{v} R)
  证明: rfl

@[simp]
-/
lemma forget₂_ringCat_obj (X : AlgCat.{v} R) :
    (forget₂ (AlgCat.{v} R) RingCat.{v}).obj X = RingCat.of X :=
  rfl

@[simp]
/--
lemma `forget₂_ringCat_map` / 引理 `forget₂_ringCat_map`

English:
lemma forget₂_ringCat_map
  given: {X Y : AlgCat.{v} R} (f : X ⟶ Y)
  proof: rfl

中文:
引理 forget₂_ringCat_map
  条件: {X Y : Alg范畴.{v} R} (f : X ⟶ Y)
  证明: rfl
-/
lemma forget₂_ringCat_map {X Y : AlgCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (AlgCat.{v} R) RingCat.{v}).map f = RingCat.ofHom f.hom :=
  rfl

instance (A : AlgCat.{v} R) : Algebra R ((forget₂ (AlgCat.{v} R) RingCat).obj A) :=
inferInstanceAs Algebra R A

/--
Instance `hasForgetToModule` / 实例 `hasForgetToModule`

English:
instance hasForgetToModule
  signature: : HasForget₂ (AlgCat.{v} R) (ModuleCat.{v} R) where
  body: { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.hom.toLinearMap }

@[simp]

中文:
实例 hasForgetToModule
  签名: : 有Forget₂ (Alg范畴.{v} R) (模范畴.{v} R) where
  定义体: { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.hom.toLinearMap }

@[simp]

Depends on / 依赖: ModuleCat, ModuleCat.of, ModuleCat.ofHom, f.hom.toLinearMap, toLinearMap
-/
instance hasForgetToModule : HasForget₂ (AlgCat.{v} R) (ModuleCat.{v} R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.hom.toLinearMap }

@[simp]
/--
lemma `forget₂_module_obj` / 引理 `forget₂_module_obj`

English:
lemma forget₂_module_obj
  given: (X : AlgCat.{v} R)
  proof: rfl

@[simp]

中文:
引理 forget₂_module_obj
  条件: (X : Alg范畴.{v} R)
  证明: rfl

@[simp]
-/
lemma forget₂_module_obj (X : AlgCat.{v} R) :
    (forget₂ (AlgCat.{v} R) (ModuleCat.{v} R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
/--
lemma `forget₂_module_map` / 引理 `forget₂_module_map`

English:
lemma forget₂_module_map
  given: {X Y : AlgCat.{v} R} (f : X ⟶ Y)
  proof: rfl

中文:
引理 forget₂_module_map
  条件: {X Y : Alg范畴.{v} R} (f : X ⟶ Y)
  证明: rfl
-/
lemma forget₂_module_map {X Y : AlgCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (AlgCat.{v} R) (ModuleCat.{v} R)).map f = ModuleCat.ofHom f.hom.toLinearMap :=
  rfl

/-- The "free algebra" functor, sending a type `S` to the free algebra on `S`. -/
@[simps! obj map]
/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: : Type u ⥤ AlgCat.{u} R where
  body: of R (FreeAlgebra R S)
map f := ofHom FreeAlgebra.lift _ FreeAlgebra.ι _ ∘ f

中文:
定义 free
  签名: : 类型u ⥤ Alg范畴.{u} R where
  定义体: of R (FreeAlgebra R S)
map f := ofHom FreeAlgebra.lift _ FreeAlgebra.ι _ ∘ f

Depends on / 依赖: FreeAlgebra
-/
def free : Type u ⥤ AlgCat.{u} R where
  obj S := of R (FreeAlgebra R S)
map f := ofHom FreeAlgebra.lift _ FreeAlgebra.ι _ ∘ f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : free.{u} R ⊣ forget (AlgCat.{u} R)
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => ↾((FreeAlgebra.lift _).symm f.hom)
invFun := fun f => ofHom (FreeAlgebra.lift _) f
          left_inv := fun f => by aesop
          right_inv := fun f => by aesop } }

中文:
定义 adj
  签名: : free.{u} R ⊣ forget (Alg范畴.{u} R)
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => ↾((FreeAlgebra.lift _).symm f.hom)
invFun := fun f => ofHom (FreeAlgebra.lift _) f
          left_inv := fun f => by aesop
          right_inv := fun f => by aesop } }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, FreeAlgebra, FreeAlgebra.lift, f.hom, homEquiv, invFun, left_inv, mkOfHomEquiv, right_inv
-/
def adj : free.{u} R ⊣ forget (AlgCat.{u} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => ↾((FreeAlgebra.lift _).symm f.hom)
invFun := fun f => ofHom (FreeAlgebra.lift _) f
          left_inv := fun f => by aesop
          right_inv := fun f => by aesop } }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget (AlgCat.{u} R)).IsRightAdjoint
  body: (adj R).isRightAdjoint

中文:
实例 :
  签名: (forget (Alg范畴.{u} R)).是右伴随
  定义体: (adj R).isRightAdjoint

Depends on / 依赖: isRightAdjoint
-/
instance : (forget (AlgCat.{u} R)).IsRightAdjoint := (adj R).isRightAdjoint

end AlgCat

variable {R}
variable {X₁ X₂ : Type v}

/-- Build an isomorphism in the category `AlgCat R` from an `AlgEquiv` between `Algebra`s. -/
@[simps]
/--
Definition of `AlgEquiv.toAlgebraIso` / `AlgEquiv.toAlgebraIso` 的定义

English:
definition AlgEquiv.toAlgebraIso
  signature: {g₁ : Ring X₁} {g₂ : Ring X₂} {m₁ : Algebra R X₁} {m₂ : Algebra R X₂}
  body: AlgCat.ofHom (e : X₁ ->ₐ[R] X₂)
  inv := AlgCat.ofHom (e.symm : X₂ ->ₐ[R] X₁)

中文:
定义 代数等价.toAlgebraIso
  签名: {g₁ : 环 X₁} {g₂ : 环 X₂} {m₁ : 代数 R X₁} {m₂ : 代数 R X₂}
  定义体: AlgCat.ofHom (e : X₁ ->ₐ[R] X₂)
  inv := AlgCat.ofHom (e.symm : X₂ ->ₐ[R] X₁)

Depends on / 依赖: AlgCat, AlgCat.ofHom
-/
def AlgEquiv.toAlgebraIso {g₁ : Ring X₁} {g₂ : Ring X₂} {m₁ : Algebra R X₁} {m₂ : Algebra R X₂}
    (e : X₁ ≃ₐ[R] X₂) : AlgCat.of R X₁ ≅ AlgCat.of R X₂ where
  hom := AlgCat.ofHom (e : X₁ ->ₐ[R] X₂)
  inv := AlgCat.ofHom (e.symm : X₂ ->ₐ[R] X₁)

namespace CategoryTheory.Iso

/-- Build an `AlgEquiv` from an isomorphism in the category `AlgCat R`. -/
@[simps]
/--
Definition of `toAlgEquiv` / `toAlgEquiv` 的定义

English:
definition toAlgEquiv
  signature: {X Y : AlgCat.{v} R} (i : X ≅ Y)
  body: { i.hom.hom with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x => by simp
    right_inv := fun x => by simp }

中文:
定义 toAlgEquiv
  签名: {X Y : Alg范畴.{v} R} (i : X ≅ Y)
  定义体: { i.hom.hom with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x => by simp
    right_inv := fun x => by simp }

Depends on / 依赖: i.hom, i.hom.hom, i.inv, invFun, left_inv, right_inv
-/
def toAlgEquiv {X Y : AlgCat.{v} R} (i : X ≅ Y) : X ≃ₐ[R] Y :=
  { i.hom.hom with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x => by simp
    right_inv := fun x => by simp }

end CategoryTheory.Iso

/-- Algebra equivalences between `Algebra`s are the same as (isomorphic to) isomorphisms in
`AlgCat`. -/
@[simps]
/--
Definition of `algEquivIsoAlgebraIso` / `algEquivIsoAlgebraIso` 的定义

English:
definition algEquivIsoAlgebraIso
  signature: {X Y : Type v} [Ring X] [Ring Y] [Algebra R X] [Algebra R Y]
  body: ↾fun e => e.toAlgebraIso
  inv := ↾fun i => i.toAlgEquiv

中文:
定义 algEquivIsoAlgebraIso
  签名: {X Y : 类型v} [环 X] [环 Y] [代数 R X] [代数 R Y]
  定义体: ↾fun e => e.toAlgebraIso
  inv := ↾fun i => i.toAlgEquiv

Depends on / 依赖: e.toAlgebraIso, toAlgebraIso
-/
def algEquivIsoAlgebraIso {X Y : Type v} [Ring X] [Ring Y] [Algebra R X] [Algebra R Y] :
    (X ≃ₐ[R] Y) ≅ (AlgCat.of R X ≅ AlgCat.of R Y) where
  hom := ↾fun e => e.toAlgebraIso
  inv := ↾fun i => i.toAlgEquiv

/--
Instance `AlgCat.forget_reflects_isos` / 实例 `AlgCat.forget_reflects_isos`

English:
instance AlgCat.forget_reflects_isos
  signature: : (forget (AlgCat.{v} R)).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget (AlgCat.{v} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact e.toAlgebraIso.isIso_hom

中文:
实例 Alg范畴.forget_reflects_isos
  签名: : (forget (Alg范畴.{v} R)).反映同构 where
  定义体: by
    let i := asIso ((forget (AlgCat.{v} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact e.toAlgebraIso.isIso_hom

Depends on / 依赖: AlgCat, e.toAlgebraIso.isIso_hom, f.hom, forget, i.toEquiv, isIso_hom, toAlgebraIso, toEquiv
-/
instance AlgCat.forget_reflects_isos : (forget (AlgCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (AlgCat.{v} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact e.toAlgebraIso.isIso_hom

namespace AlgCat

/-- The restriction of scalars functor `AlgCat S ⥤ AlgCat R` induced by a ring homomorphism
`R →+* S`. -/
@[simps]
/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S)
  body: letI : Algebra R A := Algebra.compHom _ f
    AlgCat.of R A
  map {A B} g :=
    letI : Algebra R A := Algebra.compHom _ f
    letI : Algebra R B := Algebra.compHom _ f
    letI : Algebra R S := f.toAlgebra
    haveI : IsScalarTower R S A := .of_algebraMap_eq' rfl
    haveI : IsScalarTower R S B := 

中文:
定义 restrictScalars
  签名: {R S : 类型} [交换环 R] [交换环 S] (f : R ->+* S)
  定义体: letI : Algebra R A := Algebra.compHom _ f
    AlgCat.of R A
  map {A B} g :=
    letI : Algebra R A := Algebra.compHom _ f
    letI : Algebra R B := Algebra.compHom _ f
    letI : Algebra R S := f.toAlgebra
    haveI : IsScalarTower R S A := .of_algebraMap_eq' rfl
    haveI : IsScalarTower R S B := 

Depends on / 依赖: AlgCat, AlgCat.of, AlgCat.ofHom, Algebra, Algebra.compHom, IsScalarTower, compHom, f.toAlgebra, g.hom.restrictScalars, of_algebraMap_eq, restrictScalars, toAlgebra
-/
def restrictScalars {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) :
    AlgCat.{v} S ⥤ AlgCat.{v} R where
  obj A :=
    letI : Algebra R A := Algebra.compHom _ f
    AlgCat.of R A
  map {A B} g :=
    letI : Algebra R A := Algebra.compHom _ f
    letI : Algebra R B := Algebra.compHom _ f
    letI : Algebra R S := f.toAlgebra
    haveI : IsScalarTower R S A := .of_algebraMap_eq' rfl
    haveI : IsScalarTower R S B := .of_algebraMap_eq' rfl
    AlgCat.ofHom (g.hom.restrictScalars _)

-- The option makes `simps` produce the correct lemmas
set_option backward.isDefEq.respectTransparency false in
/-- Restricting scalars along the identity is isomorphic to the identity. -/
@[simps!]
/--
Definition of `restrictScalarsId'` / `restrictScalarsId'` 的定义

English:
definition restrictScalarsId'
  signature: {R : Type*} [CommRing R] (f : R ->+* R) (hf : f = .id R)
  body: NatIso.ofComponents
fun A => AlgEquiv.toAlgebraIso
      @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _
        ((restrictScalars f).obj A).isAlgebra _ fun _ => by subst hf; rfl

中文:
定义 restrictScalarsId'
  签名: {R : 类型} [交换环 R] (f : R ->+* R) (hf : f = .id R)
  定义体: NatIso.ofComponents
fun A => AlgEquiv.toAlgebraIso
      @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _
        ((restrictScalars f).obj A).isAlgebra _ fun _ => by subst hf; rfl

Depends on / 依赖: AlgEquiv, AlgEquiv.ofRingEquiv, AlgEquiv.toAlgebraIso, NatIso, NatIso.ofComponents, RingEquiv, RingEquiv.refl, isAlgebra, ofComponents, ofRingEquiv, restrictScalars, toAlgebraIso
-/
def restrictScalarsId' {R : Type*} [CommRing R] (f : R ->+* R) (hf : f = .id R) :
    AlgCat.restrictScalars.{v} f ≅ 𝟭 _ :=
  NatIso.ofComponents
fun A => AlgEquiv.toAlgebraIso
      @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _
        ((restrictScalars f).obj A).isAlgebra _ fun _ => by subst hf; rfl

-- The option makes `simps` produce the correct lemmas
set_option backward.isDefEq.respectTransparency false in
/-- Restricting scalars along a composition is isomorphic to the composition
of restriction of scalars. -/
@[simps!]
/--
Definition of `restrictScalarsComp'` / `restrictScalarsComp'` 的定义

English:
definition restrictScalarsComp'
  signature: {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R ->+* S)
  body: NatIso.ofComponents
fun A => AlgEquiv.toAlgebraIso
      @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _
        ((restrictScalars gf).obj A).isAlgebra
        ((restrictScalars f).obj ((restrictScalars g).obj A)).isAlgebra
        fun _ => by subst hfg; rfl

中文:
定义 restrictScalarsComp'
  签名: {R S T : 类型} [交换环 R] [交换环 S] [交换环 T] (f : R ->+* S)
  定义体: NatIso.ofComponents
fun A => AlgEquiv.toAlgebraIso
      @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _
        ((restrictScalars gf).obj A).isAlgebra
        ((restrictScalars f).obj ((restrictScalars g).obj A)).isAlgebra
        fun _ => by subst hfg; rfl

Depends on / 依赖: AlgEquiv, AlgEquiv.ofRingEquiv, AlgEquiv.toAlgebraIso, NatIso, NatIso.ofComponents, RingEquiv, RingEquiv.refl, isAlgebra, ofComponents, ofRingEquiv, restrictScalars, toAlgebraIso
-/
def restrictScalarsComp' {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R ->+* S)
      (g : S ->+* T) (gf : R ->+* T) (hfg : gf = g.comp f) :
    AlgCat.restrictScalars.{v} gf ≅
      AlgCat.restrictScalars.{v} g ⋙ AlgCat.restrictScalars.{v} f :=
  NatIso.ofComponents
fun A => AlgEquiv.toAlgebraIso
      @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _
        ((restrictScalars gf).obj A).isAlgebra
        ((restrictScalars f).obj ((restrictScalars g).obj A)).isAlgebra
        fun _ => by subst hfg; rfl

/-- A ring isomorphism induces an equivalence of categories of algebras. -/
@[simps]
/--
Definition of `restrictScalarsEquivalenceOfRingEquiv` / `restrictScalarsEquivalenceOfRingEquiv` 的定义

English:
definition restrictScalarsEquivalenceOfRingEquiv
  signature: {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
  body: restrictScalars e.toRingHom
  inverse := restrictScalars e.symm.toRingHom
  unitIso := (restrictScalarsId' _ rfl).symm ≪≫
    restrictScalarsComp' _ _ _ e.toRingHom_comp_symm_toRingHom.symm
  counitIso := (restrictScalarsComp' _ _ _ e.symm_toRingHom_comp_toRingHom.symm).symm ≪≫
    restrictScalarsId

中文:
定义 restrictScalarsEquivalenceOfRingEquiv
  签名: {R S : 类型} [交换环 R] [交换环 S] (e : R ≃+* S)
  定义体: restrictScalars e.toRingHom
  inverse := restrictScalars e.symm.toRingHom
  unitIso := (restrictScalarsId' _ rfl).symm ≪≫
    restrictScalarsComp' _ _ _ e.toRingHom_comp_symm_toRingHom.symm
  counitIso := (restrictScalarsComp' _ _ _ e.symm_toRingHom_comp_toRingHom.symm).symm ≪≫
    restrictScalarsId

Depends on / 依赖: e.toRingHom, restrictScalars, toRingHom
-/
def restrictScalarsEquivalenceOfRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    AlgCat.{u} S ≌ AlgCat.{u} R where
  functor := restrictScalars e.toRingHom
  inverse := restrictScalars e.symm.toRingHom
  unitIso := (restrictScalarsId' _ rfl).symm ≪≫
    restrictScalarsComp' _ _ _ e.toRingHom_comp_symm_toRingHom.symm
  counitIso := (restrictScalarsComp' _ _ _ e.symm_toRingHom_comp_toRingHom.symm).symm ≪≫
    restrictScalarsId' _ rfl

instance {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (restrictScalars e.toRingHom).IsEquivalence :=
inferInstanceAs (restrictScalarsEquivalenceOfRingEquiv e).functor.IsEquivalence

instance {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (restrictScalars e.symm.toRingHom).IsEquivalence :=
inferInstanceAs (restrictScalarsEquivalenceOfRingEquiv e).inverse.IsEquivalence

/-- The equivalence of categories of `ℤ`-algebras and rings. -/
@[simps! (dsimpLhs := true) functor inverse_obj inverse_map_hom unitIso_hom_app_hom_apply counitIso]
/--
Definition of `intEquivalence` / `intEquivalence` 的定义

English:
definition intEquivalence
  signature: : AlgCat.{u} Int ≌ RingCat.{u} where
  body: forget₂ _ _
  inverse.obj A := AlgCat.of Int A
  inverse.map f := AlgCat.ofHom f.hom.toIntAlgHom
  unitIso := NatIso.ofComponents
    fun A => AlgEquiv.toAlgebraIso (@.ofRingEquiv (f := RingEquiv.refl _)
      _ _ _ _ _ _ _ (Ring.toIntAlgebra _) fun _ => by simp)
  counitIso := Iso.refl _

中文:
定义 intEquivalence
  签名: : Alg范畴.{u} 整数 ≌ 环范畴.{u} where
  定义体: forget₂ _ _
  inverse.obj A := AlgCat.of Int A
  inverse.map f := AlgCat.ofHom f.hom.toIntAlgHom
  unitIso := NatIso.ofComponents
    fun A => AlgEquiv.toAlgebraIso (@.ofRingEquiv (f := RingEquiv.refl _)
      _ _ _ _ _ _ _ (Ring.toIntAlgebra _) fun _ => by simp)
  counitIso := Iso.refl _
-/
def intEquivalence : AlgCat.{u} Int ≌ RingCat.{u} where
  functor := forget₂ _ _
  inverse.obj A := AlgCat.of Int A
  inverse.map f := AlgCat.ofHom f.hom.toIntAlgHom
  unitIso := NatIso.ofComponents
    fun A => AlgEquiv.toAlgebraIso (@.ofRingEquiv (f := RingEquiv.refl _)
      _ _ _ _ _ _ _ (Ring.toIntAlgebra _) fun _ => by simp)
  counitIso := Iso.refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (AlgCat.{u} Int) RingCat.{u}).IsEquivalence
  body: inferInstanceAs intEquivalence.functor.IsEquivalence

中文:
实例 :
  签名: (forget₂ (Alg范畴.{u} 整数) 环范畴.{u}).是等价
  定义体: inferInstanceAs intEquivalence.functor.IsEquivalence

Depends on / 依赖: IsEquivalence, functor, intEquivalence, intEquivalence.functor.IsEquivalence
-/
instance : (forget₂ (AlgCat.{u} Int) RingCat.{u}).IsEquivalence :=
inferInstanceAs intEquivalence.functor.IsEquivalence

end AlgCat
