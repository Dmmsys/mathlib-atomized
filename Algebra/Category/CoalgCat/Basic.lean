/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Coalgebra.Equiv

/-!
# The category of coalgebras over a commutative ring

We introduce the bundled category `CoalgCat` of coalgebras over a fixed commutative ring `R`
along with the forgetful functor to `ModuleCat`.

This file mimics `Mathlib/LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean`.

-/

@[expose] public section

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/--
Definition of `CoalgCat` / `CoalgCat` 的定义

English:
structure CoalgCat
  parameters: extends ModuleCat.{v} R
  extends: ModuleCat.{v} R
  axioms and operations (1):
    - instCoalgebra : Coalgebra R carrier

中文:
结构 CoalgCat
  参数: extends ModuleCat.{v} R
  继承: ModuleCat.{v} R
  公理与运算 (1 个):
    - instCoalgebra : Coalgebra R carrier
-/
structure CoalgCat extends ModuleCat.{v} R where
  instCoalgebra : Coalgebra R carrier

attribute [instance] CoalgCat.instCoalgebra

variable {R}

namespace CoalgCat

open Coalgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (CoalgCat.{v} R) (Type v)
  body: ⟨(·.carrier)⟩

中文:
实例 :
  签名: CoeSort (CoalgCat.{v} R) (类型v)
  定义体: ⟨(·.carrier)⟩

Depends on / 依赖: carrier
-/
instance : CoeSort (CoalgCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

/--
theorem `moduleCat_of_toModuleCat` / 定理 `moduleCat_of_toModuleCat`

English:
theorem moduleCat_of_toModuleCat
  given: (X : CoalgCat.{v} R)
  proof: rfl

中文:
定理 moduleCat_of_toModuleCat
  条件: (X : CoalgCat.{v} R)
  证明: rfl
-/
@[simp] theorem moduleCat_of_toModuleCat (X : CoalgCat.{v} R) :
    ModuleCat.of R X.toModuleCat = X.toModuleCat :=
  rfl

variable (R) in
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type v) [AddCommGroup X] [Module R X] [Coalgebra R X]
  body: { ModuleCat.of R X with
    instCoalgebra := (inferInstance : Coalgebra R X) }

@[simp]

中文:
缩写 of
  签名: (X : 类型v) [AddCommGroup X] [Module R X] [Coalgebra R X]
  定义体: { ModuleCat.of R X with
    instCoalgebra := (inferInstance : Coalgebra R X) }

@[simp]

Depends on / 依赖: Coalgebra, ModuleCat, ModuleCat.of, instCoalgebra
-/
abbrev of (X : Type v) [AddCommGroup X] [Module R X] [Coalgebra R X] :
    CoalgCat R :=
  { ModuleCat.of R X with
    instCoalgebra := (inferInstance : Coalgebra R X) }

@[simp]
/--
lemma `of_comul` / 引理 `of_comul`

English:
lemma of_comul
  given: {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X]
  proof: rfl

@[simp]

中文:
引理 of_comul
  条件: {X : 类型v} [AddCommGroup X] [Module R X] [Coalgebra R X]
  证明: rfl

@[simp]

Depends on / 依赖: Coalgebra, Coalgebra.comul
-/
lemma of_comul {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

@[simp]
/--
lemma `of_counit` / 引理 `of_counit`

English:
lemma of_counit
  given: {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X]
  proof: rfl

中文:
引理 of_counit
  条件: {X : 类型v} [AddCommGroup X] [Module R X] [Coalgebra R X]
  证明: rfl

Depends on / 依赖: Coalgebra, Coalgebra.counit, counit
-/
lemma of_counit {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `CoalgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (V W : CoalgCat.{v} R)
  axioms and operations (1):
    - toCoalgHom' : V ->ₗc[R] W

中文:
结构 Hom
  参数: (V W : CoalgCat.{v} R)
  公理与运算 (1 个):
    - toCoalgHom' : V ->ₗc[R] W
-/
structure Hom (V W : CoalgCat.{v} R) where
  /-- The underlying `CoalgHom` -/
  toCoalgHom' : V ->ₗc[R] W

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (CoalgCat.{v} R) where
  body: Hom M N
  id M := ⟨CoalgHom.id R M⟩
  comp f g := ⟨CoalgHom.comp g.toCoalgHom' f.toCoalgHom'⟩

中文:
实例 category
  签名: : Category (CoalgCat.{v} R) where
  定义体: Hom M N
  id M := ⟨CoalgHom.id R M⟩
  comp f g := ⟨CoalgHom.comp g.toCoalgHom' f.toCoalgHom'⟩
-/
instance category : Category (CoalgCat.{v} R) where
  Hom M N := Hom M N
  id M := ⟨CoalgHom.id R M⟩
  comp f g := ⟨CoalgHom.comp g.toCoalgHom' f.toCoalgHom'⟩

/--
Instance `concreteCategory` / 实例 `concreteCategory`

English:
instance concreteCategory
  signature: : ConcreteCategory (CoalgCat.{v} R) (· ->ₗc[R] ·) where
  body: f.toCoalgHom'
  ofHom f := ⟨f⟩

中文:
实例 concreteCategory
  签名: : ConcreteCategory (CoalgCat.{v} R) (· ->ₗc[R] ·) where
  定义体: f.toCoalgHom'
  ofHom f := ⟨f⟩

Depends on / 依赖: f.toCoalgHom, toCoalgHom
-/
instance concreteCategory : ConcreteCategory (CoalgCat.{v} R) (· ->ₗc[R] ·) where
  hom f := f.toCoalgHom'
  ofHom f := ⟨f⟩

/--
Definition of `Hom.toCoalgHom` / `Hom.toCoalgHom` 的定义

English:
abbreviation Hom.toCoalgHom
  signature: {X Y : CoalgCat.{v} R} (f : Hom X Y)
  body: ConcreteCategory.hom (C := CoalgCat.{v} R) f

中文:
缩写 Hom.toCoalgHom
  签名: {X Y : CoalgCat.{v} R} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := CoalgCat.{v} R) f

Depends on / 依赖: CoalgCat, ConcreteCategory, ConcreteCategory.hom
-/
abbrev Hom.toCoalgHom {X Y : CoalgCat.{v} R} (f : Hom X Y) : X ->ₗc[R] Y :=
  ConcreteCategory.hom (C := CoalgCat.{v} R) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  body: ConcreteCategory.ofHom f

中文:
缩写 ofHom
  签名: {X Y : 类型v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  定义体: ConcreteCategory.ofHom f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [Coalgebra R X] [Coalgebra R Y] (f : X ->ₗc[R] Y) :
    of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f

/--
lemma `Hom.toCoalgHom_injective` / 引理 `Hom.toCoalgHom_injective`

English:
lemma Hom.toCoalgHom_injective
  given: (V W : CoalgCat.{v} R)
  proof: fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]

中文:
引理 Hom.toCoalgHom_injective
  条件: (V W : CoalgCat.{v} R)
  证明: fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]
-/
lemma Hom.toCoalgHom_injective (V W : CoalgCat.{v} R) :
    Function.Injective (Hom.toCoalgHom' : Hom V W -> _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {M N : CoalgCat.{v} R} (f g : M ⟶ N) (h : f.toCoalgHom = g.toCoalgHom)
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {M N : CoalgCat.{v} R} (f g : M ⟶ N) (h : f.toCoalgHom = g.toCoalgHom)
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {M N : CoalgCat.{v} R} (f g : M ⟶ N) (h : f.toCoalgHom = g.toCoalgHom) :
    f = g :=
  Hom.ext h

/--
theorem `toCoalgHom_comp` / 定理 `toCoalgHom_comp`

English:
theorem toCoalgHom_comp
  given: {M N U : CoalgCat.{v} R} (f : M ⟶ N) (g : N ⟶ U)
  proof: rfl

中文:
定理 toCoalgHom_comp
  条件: {M N U : CoalgCat.{v} R} (f : M ⟶ N) (g : N ⟶ U)
  证明: rfl
-/
@[simp] theorem toCoalgHom_comp {M N U : CoalgCat.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
    (f ≫ g).toCoalgHom = g.toCoalgHom.comp f.toCoalgHom :=
  rfl

/--
theorem `toCoalgHom_id` / 定理 `toCoalgHom_id`

English:
theorem toCoalgHom_id
  given: {M : CoalgCat.{v} R}
  proof: rfl

中文:
定理 toCoalgHom_id
  条件: {M : CoalgCat.{v} R}
  证明: rfl
-/
@[simp] theorem toCoalgHom_id {M : CoalgCat.{v} R} :
    Hom.toCoalgHom (𝟙 M) = CoalgHom.id _ _ :=
  rfl

/--
Instance `hasForgetToModule` / 实例 `hasForgetToModule`

English:
instance hasForgetToModule
  signature: : HasForget₂ (CoalgCat R) (ModuleCat R) where
  body: { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toCoalgHom.toLinearMap }

@[simp]

中文:
实例 hasForgetToModule
  签名: : HasForget₂ (CoalgCat R) (ModuleCat R) where
  定义体: { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toCoalgHom.toLinearMap }

@[simp]

Depends on / 依赖: ModuleCat, ModuleCat.of, ModuleCat.ofHom, f.toCoalgHom.toLinearMap, toCoalgHom, toLinearMap
-/
instance hasForgetToModule : HasForget₂ (CoalgCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toCoalgHom.toLinearMap }

@[simp]
/--
theorem `forget₂_obj` / 定理 `forget₂_obj`

English:
theorem forget₂_obj
  given: (X : CoalgCat R)
  proof: rfl

@[simp]

中文:
定理 forget₂_obj
  条件: (X : CoalgCat R)
  证明: rfl

@[simp]
-/
theorem forget₂_obj (X : CoalgCat R) :
    (forget₂ (CoalgCat R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
/--
theorem `forget₂_map` / 定理 `forget₂_map`

English:
theorem forget₂_map
  given: (X Y : CoalgCat R) (f : X ⟶ Y)
  proof: rfl

中文:
定理 forget₂_map
  条件: (X Y : CoalgCat R) (f : X ⟶ Y)
  证明: rfl
-/
theorem forget₂_map (X Y : CoalgCat R) (f : X ⟶ Y) :
    (forget₂ (CoalgCat R) (ModuleCat R)).map f = ModuleCat.ofHom (f.toCoalgHom : X ->ₗ[R] Y) :=
  rfl

end CoalgCat

namespace CoalgEquiv

open CoalgCat

variable {X Y Z : Type v}
variable [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
variable [Coalgebra R X] [Coalgebra R Y] [Coalgebra R Z]

/-- Build an isomorphism in the category `CoalgCat R` from a
`CoalgEquiv`. -/
@[simps]
/--
Definition of `toCoalgIso` / `toCoalgIso` 的定义

English:
definition toCoalgIso
  signature: (e : X ≃ₗc[R] Y)
  body: CoalgCat.ofHom e
  inv := CoalgCat.ofHom e.symm
hom_inv_id := Hom.ext DFunLike.ext _ _ e.left_inv
inv_hom_id := Hom.ext DFunLike.ext _ _ e.right_inv

中文:
定义 toCoalgIso
  签名: (e : X ≃ₗc[R] Y)
  定义体: CoalgCat.ofHom e
  inv := CoalgCat.ofHom e.symm
hom_inv_id := Hom.ext DFunLike.ext _ _ e.left_inv
inv_hom_id := Hom.ext DFunLike.ext _ _ e.right_inv

Depends on / 依赖: CoalgCat, CoalgCat.ofHom
-/
def toCoalgIso (e : X ≃ₗc[R] Y) : CoalgCat.of R X ≅ CoalgCat.of R Y where
  hom := CoalgCat.ofHom e
  inv := CoalgCat.ofHom e.symm
hom_inv_id := Hom.ext DFunLike.ext _ _ e.left_inv
inv_hom_id := Hom.ext DFunLike.ext _ _ e.right_inv

/--
theorem `toCoalgIso_refl` / 定理 `toCoalgIso_refl`

English:
theorem toCoalgIso_refl
  proof: rfl

中文:
定理 toCoalgIso_refl
  证明: rfl
-/
@[simp] theorem toCoalgIso_refl :
    toCoalgIso (CoalgEquiv.refl R X) = .refl _ :=
  rfl

/--
theorem `toCoalgIso_symm` / 定理 `toCoalgIso_symm`

English:
theorem toCoalgIso_symm
  given: (e : X ≃ₗc[R] Y)
  proof: rfl

中文:
定理 toCoalgIso_symm
  条件: (e : X ≃ₗc[R] Y)
  证明: rfl
-/
@[simp] theorem toCoalgIso_symm (e : X ≃ₗc[R] Y) :
    toCoalgIso e.symm = (toCoalgIso e).symm :=
  rfl

/--
theorem `toCoalgIso_trans` / 定理 `toCoalgIso_trans`

English:
theorem toCoalgIso_trans
  given: (e : X ≃ₗc[R] Y) (f : Y ≃ₗc[R] Z)
  proof: rfl

中文:
定理 toCoalgIso_trans
  条件: (e : X ≃ₗc[R] Y) (f : Y ≃ₗc[R] Z)
  证明: rfl
-/
@[simp] theorem toCoalgIso_trans (e : X ≃ₗc[R] Y) (f : Y ≃ₗc[R] Z) :
    toCoalgIso (e.trans f) = toCoalgIso e ≪≫ toCoalgIso f :=
  rfl

end CoalgEquiv

namespace CategoryTheory.Iso

open Coalgebra

variable {X Y Z : CoalgCat.{v} R}

/--
Definition of `toCoalgEquiv` / `toCoalgEquiv` 的定义

English:
definition toCoalgEquiv
  signature: (i : X ≅ Y)
  body: { i.hom.toCoalgHom with
    invFun := i.inv.toCoalgHom
    left_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgCat.Hom.toCoalgHom i.3) x
    right_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgCat.Hom.toCoalgHom i.4) x }

中文:
定义 toCoalgEquiv
  签名: (i : X ≅ Y)
  定义体: { i.hom.toCoalgHom with
    invFun := i.inv.toCoalgHom
    left_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgCat.Hom.toCoalgHom i.3) x
    right_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgCat.Hom.toCoalgHom i.4) x }

Depends on / 依赖: CoalgCat, CoalgCat.Hom.toCoalgHom, CoalgHom, CoalgHom.congr_fun, congr_arg, congr_fun, i.hom.toCoalgHom, i.inv.toCoalgHom, invFun, left_inv, right_inv, toCoalgHom
-/
def toCoalgEquiv (i : X ≅ Y) : X ≃ₗc[R] Y :=
  { i.hom.toCoalgHom with
    invFun := i.inv.toCoalgHom
    left_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgCat.Hom.toCoalgHom i.3) x
    right_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgCat.Hom.toCoalgHom i.4) x }

/--
theorem `toCoalgEquiv_toCoalgHom` / 定理 `toCoalgEquiv_toCoalgHom`

English:
theorem toCoalgEquiv_toCoalgHom
  given: (i : X ≅ Y)
  proof: rfl

中文:
定理 toCoalgEquiv_toCoalgHom
  条件: (i : X ≅ Y)
  证明: rfl
-/
@[simp] theorem toCoalgEquiv_toCoalgHom (i : X ≅ Y) :
    i.toCoalgEquiv = i.hom.toCoalgHom := rfl

/--
theorem `toCoalgEquiv_refl` / 定理 `toCoalgEquiv_refl`

English:
theorem toCoalgEquiv_refl
  statement: toCoalgEquiv (.refl X) = .refl _ _
  proof: rfl

中文:
定理 toCoalgEquiv_refl
  结论: toCoalgEquiv (.refl X) = .refl _ _
  证明: rfl
-/
@[simp] theorem toCoalgEquiv_refl : toCoalgEquiv (.refl X) = .refl _ _ :=
  rfl

/--
theorem `toCoalgEquiv_symm` / 定理 `toCoalgEquiv_symm`

English:
theorem toCoalgEquiv_symm
  given: (e : X ≅ Y)
  proof: rfl

中文:
定理 toCoalgEquiv_symm
  条件: (e : X ≅ Y)
  证明: rfl
-/
@[simp] theorem toCoalgEquiv_symm (e : X ≅ Y) :
    toCoalgEquiv e.symm = (toCoalgEquiv e).symm :=
  rfl

/--
theorem `toCoalgEquiv_trans` / 定理 `toCoalgEquiv_trans`

English:
theorem toCoalgEquiv_trans
  given: (e : X ≅ Y) (f : Y ≅ Z)
  proof: rfl

中文:
定理 toCoalgEquiv_trans
  条件: (e : X ≅ Y) (f : Y ≅ Z)
  证明: rfl
-/
@[simp] theorem toCoalgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toCoalgEquiv (e ≪≫ f) = e.toCoalgEquiv.trans f.toCoalgEquiv :=
  rfl

end CategoryTheory.Iso

/--
Instance `CoalgCat.forget_reflects_isos` / 实例 `CoalgCat.forget_reflects_isos`

English:
instance CoalgCat.forget_reflects_isos
  signature: :
  body: by
    let i := asIso ((forget (CoalgCat.{v} R)).map f)
    let e : X ≃ₗc[R] Y := { f.toCoalgHom, i.toEquiv with }
    exact ⟨e.toCoalgIso.isIso_hom.1⟩

中文:
实例 CoalgCat.forget_reflects_isos
  签名: :
  定义体: by
    let i := asIso ((forget (CoalgCat.{v} R)).map f)
    let e : X ≃ₗc[R] Y := { f.toCoalgHom, i.toEquiv with }
    exact ⟨e.toCoalgIso.isIso_hom.1⟩

Depends on / 依赖: CoalgCat, e.toCoalgIso.isIso_hom, f.toCoalgHom, forget, i.toEquiv, isIso_hom, toCoalgHom, toCoalgIso, toEquiv
-/
instance CoalgCat.forget_reflects_isos :
    (forget (CoalgCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CoalgCat.{v} R)).map f)
    let e : X ≃ₗc[R] Y := { f.toCoalgHom, i.toEquiv with }
    exact ⟨e.toCoalgIso.isIso_hom.1⟩
