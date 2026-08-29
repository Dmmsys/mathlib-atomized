/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.BialgCat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The category of Hopf algebras over a commutative ring

We introduce the bundled category `HopfAlgCat` of Hopf algebras over a fixed commutative ring
`R` along with the forgetful functor to `BialgCat`.

This file mimics `Mathlib/LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean`.

-/

@[expose] public section

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

set_option backward.privateInPublic true in
/--
Definition of `HopfAlgCat` / `HopfAlgCat` 的定义

English:
structure HopfAlgCat
  parameters: where
  axioms and operations (4):
    - private(mk) : :
    - carrier : Type v
    - [instRing : Ring carrier]
    - [instHopfAlgebra : HopfAlgebra R carrier]

中文:
结构 HopfAlgCat
  参数: where
  公理与运算 (4 个):
    - private(mk) : :
    - carrier : 类型v
    - [instRing : Ring carrier]
    - [instHopfAlgebra : HopfAlgebra R carrier]
-/
structure HopfAlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [instRing : Ring carrier]
  [instHopfAlgebra : HopfAlgebra R carrier]

initialize_simps_projections HopfAlgCat (-instRing, -instHopfAlgebra)
attribute [instance] HopfAlgCat.instHopfAlgebra HopfAlgCat.instRing

variable {R}

namespace HopfAlgCat

open HopfAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (HopfAlgCat.{v} R) (Type v)
  body: ⟨(·.carrier)⟩

中文:
实例 :
  签名: CoeSort (HopfAlgCat.{v} R) (类型v)
  定义体: ⟨(·.carrier)⟩

Depends on / 依赖: carrier
-/
instance : CoeSort (HopfAlgCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

variable (R) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type v) [Ring X] [HopfAlgebra R X]
  body: X

@[simp]

中文:
缩写 of
  签名: (X : 类型v) [Ring X] [HopfAlgebra R X]
  定义体: X

@[simp]
-/
abbrev of (X : Type v) [Ring X] [HopfAlgebra R X] :
    HopfAlgCat R where
  carrier := X

@[simp]
/--
lemma `of_comul` / 引理 `of_comul`

English:
lemma of_comul
  given: {X : Type v} [Ring X] [HopfAlgebra R X]
  proof: rfl

@[simp]

中文:
引理 of_comul
  条件: {X : 类型v} [Ring X] [HopfAlgebra R X]
  证明: rfl

@[simp]

Depends on / 依赖: Coalgebra, Coalgebra.comul
-/
lemma of_comul {X : Type v} [Ring X] [HopfAlgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

@[simp]
/--
lemma `of_counit` / 引理 `of_counit`

English:
lemma of_counit
  given: {X : Type v} [Ring X] [HopfAlgebra R X]
  proof: rfl

中文:
引理 of_counit
  条件: {X : 类型v} [Ring X] [HopfAlgebra R X]
  证明: rfl

Depends on / 依赖: Coalgebra, Coalgebra.counit, IsEquivalence, counit, functor, functor.IsEquivalence, restrictScalarsEquivalenceOfRingEquiv
-/
lemma of_counit {X : Type v} [Ring X] [HopfAlgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `BialgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (V W : HopfAlgCat.{v} R)
  axioms and operations (1):
    - toBialgHom' : V ->ₐc[R] W

中文:
结构 Hom
  参数: (V W : HopfAlgCat.{v} R)
  公理与运算 (1 个):
    - toBialgHom' : V ->ₐc[R] W

Depends on / 依赖: IsEquivalence, inverse, inverse.IsEquivalence, restrictScalarsEquivalenceOfRingEquiv
-/
structure Hom (V W : HopfAlgCat.{v} R) where
  /-- The underlying `BialgHom`. -/
  toBialgHom' : V ->ₐc[R] W

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (HopfAlgCat.{v} R) where
  body: Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom' f.toBialgHom'⟩

中文:
实例 category
  签名: : Category (HopfAlgCat.{v} R) where
  定义体: Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom' f.toBialgHom'⟩
-/
instance category : Category (HopfAlgCat.{v} R) where
  Hom X Y := Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom' f.toBialgHom'⟩

/--
Instance `concreteCategory` / 实例 `concreteCategory`

English:
instance concreteCategory
  signature: : ConcreteCategory (HopfAlgCat.{v} R) (· ->ₐc[R] ·) where
  body: f.toBialgHom'
  ofHom f := ⟨f⟩

中文:
实例 concreteCategory
  签名: : ConcreteCategory (HopfAlgCat.{v} R) (· ->ₐc[R] ·) where
  定义体: f.toBialgHom'
  ofHom f := ⟨f⟩

Depends on / 依赖: f.toBialgHom, toBialgHom
-/
instance concreteCategory : ConcreteCategory (HopfAlgCat.{v} R) (· ->ₐc[R] ·) where
  hom f := f.toBialgHom'
  ofHom f := ⟨f⟩

/--
Definition of `Hom.toBialgHom` / `Hom.toBialgHom` 的定义

English:
abbreviation Hom.toBialgHom
  signature: {X Y : HopfAlgCat R} (f : Hom X Y)
  body: ConcreteCategory.hom (C := HopfAlgCat R) f

中文:
缩写 Hom.toBialgHom
  签名: {X Y : HopfAlgCat R} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := HopfAlgCat R) f
-/
abbrev Hom.toBialgHom {X Y : HopfAlgCat R} (f : Hom X Y) :=
  ConcreteCategory.hom (C := HopfAlgCat R) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type v} [Ring X] [Ring Y]
  body: ConcreteCategory.ofHom f

中文:
缩写 ofHom
  签名: {X Y : 类型v} [Ring X] [Ring Y]
  定义体: ConcreteCategory.ofHom f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type v} [Ring X] [Ring Y]
    [HopfAlgebra R X] [HopfAlgebra R Y] (f : X ->ₐc[R] Y) :
    of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f

/--
lemma `Hom.toBialgHom_injective` / 引理 `Hom.toBialgHom_injective`

English:
lemma Hom.toBialgHom_injective
  given: (V W : HopfAlgCat.{v} R)
  proof: fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]

中文:
引理 Hom.toBialgHom_injective
  条件: (V W : HopfAlgCat.{v} R)
  证明: fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]
-/
lemma Hom.toBialgHom_injective (V W : HopfAlgCat.{v} R) :
    Function.Injective (Hom.toBialgHom : Hom V W -> _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : HopfAlgCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom)
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {X Y : HopfAlgCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom)
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : HopfAlgCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom) :
    f = g :=
  Hom.ext h

/--
theorem `toBialgHom_comp` / 定理 `toBialgHom_comp`

English:
theorem toBialgHom_comp
  given: {X Y Z : HopfAlgCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 toBialgHom_comp
  条件: {X Y Z : HopfAlgCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
@[simp] theorem toBialgHom_comp {X Y Z : HopfAlgCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toBialgHom = g.toBialgHom.comp f.toBialgHom :=
  rfl

/--
theorem `toBialgHom_id` / 定理 `toBialgHom_id`

English:
theorem toBialgHom_id
  given: {M : HopfAlgCat.{v} R}
  proof: rfl

中文:
定理 toBialgHom_id
  条件: {M : HopfAlgCat.{v} R}
  证明: rfl
-/
@[simp] theorem toBialgHom_id {M : HopfAlgCat.{v} R} :
    Hom.toBialgHom (𝟙 M) = BialgHom.id _ _ :=
  rfl

/--
Instance `hasForgetToBialgebra` / 实例 `hasForgetToBialgebra`

English:
instance hasForgetToBialgebra
  signature: : HasForget₂ (HopfAlgCat R) (BialgCat R) where
  body: { obj := fun X => BialgCat.of R X
      map := fun {_ _} f => BialgCat.ofHom f.toBialgHom }

@[simp]

中文:
实例 hasForgetToBialgebra
  签名: : HasForget₂ (HopfAlgCat R) (BialgCat R) where
  定义体: { obj := fun X => BialgCat.of R X
      map := fun {_ _} f => BialgCat.ofHom f.toBialgHom }

@[simp]

Depends on / 依赖: BialgCat, BialgCat.of, BialgCat.ofHom, f.toBialgHom, sectionsSubalgebra, toBialgHom
-/
instance hasForgetToBialgebra : HasForget₂ (HopfAlgCat R) (BialgCat R) where
  forget₂ :=
    { obj := fun X => BialgCat.of R X
      map := fun {_ _} f => BialgCat.ofHom f.toBialgHom }

@[simp]
/--
theorem `forget₂_bialgebra_obj` / 定理 `forget₂_bialgebra_obj`

English:
theorem forget₂_bialgebra_obj
  given: (X : HopfAlgCat R)
  proof: rfl

@[simp]

中文:
定理 forget₂_bialgebra_obj
  条件: (X : HopfAlgCat R)
  证明: rfl

@[simp]

Depends on / 依赖: Algebra, sectionsSubalgebra
-/
theorem forget₂_bialgebra_obj (X : HopfAlgCat R) :
    (forget₂ (HopfAlgCat R) (BialgCat R)).obj X = BialgCat.of R X :=
  rfl

@[simp]
/--
theorem `forget₂_bialgebra_map` / 定理 `forget₂_bialgebra_map`

English:
theorem forget₂_bialgebra_map
  given: (X Y : HopfAlgCat R) (f : X ⟶ Y)
  proof: rfl

中文:
定理 forget₂_bialgebra_map
  条件: (X Y : HopfAlgCat R) (f : X ⟶ Y)
  证明: rfl
-/
theorem forget₂_bialgebra_map (X Y : HopfAlgCat R) (f : X ⟶ Y) :
    (forget₂ (HopfAlgCat R) (BialgCat R)).map f = BialgCat.ofHom f.toBialgHom :=
  rfl

end HopfAlgCat

namespace BialgEquiv

open HopfAlgCat

variable {X Y Z : Type v}
variable [Ring X] [Ring Y] [Ring Z]
variable [HopfAlgebra R X] [HopfAlgebra R Y] [HopfAlgebra R Z]

/-- Build an isomorphism in the category `HopfAlgCat R` from a
`BialgEquiv`. -/
@[simps]
/--
Definition of `toHopfAlgIso` / `toHopfAlgIso` 的定义

English:
definition toHopfAlgIso
  signature: (e : X ≃ₐc[R] Y)
  body: HopfAlgCat.ofHom e
  inv := HopfAlgCat.ofHom e.symm
hom_inv_id := Hom.ext DFunLike.ext _ _ e.left_inv
inv_hom_id := Hom.ext DFunLike.ext _ _ e.right_inv

中文:
定义 toHopfAlgIso
  签名: (e : X ≃ₐc[R] Y)
  定义体: HopfAlgCat.ofHom e
  inv := HopfAlgCat.ofHom e.symm
hom_inv_id := Hom.ext DFunLike.ext _ _ e.left_inv
inv_hom_id := Hom.ext DFunLike.ext _ _ e.right_inv

Depends on / 依赖: HopfAlgCat, HopfAlgCat.ofHom
-/
def toHopfAlgIso (e : X ≃ₐc[R] Y) : HopfAlgCat.of R X ≅ HopfAlgCat.of R Y where
  hom := HopfAlgCat.ofHom e
  inv := HopfAlgCat.ofHom e.symm
hom_inv_id := Hom.ext DFunLike.ext _ _ e.left_inv
inv_hom_id := Hom.ext DFunLike.ext _ _ e.right_inv

/--
theorem `toHopfAlgIso_refl` / 定理 `toHopfAlgIso_refl`

English:
theorem toHopfAlgIso_refl
  proof: rfl

中文:
定理 toHopfAlgIso_refl
  证明: rfl
-/
@[simp] theorem toHopfAlgIso_refl :
    toHopfAlgIso (BialgEquiv.refl R X) = .refl _ :=
  rfl

/--
theorem `toHopfAlgIso_symm` / 定理 `toHopfAlgIso_symm`

English:
theorem toHopfAlgIso_symm
  given: (e : X ≃ₐc[R] Y)
  proof: rfl

中文:
定理 toHopfAlgIso_symm
  条件: (e : X ≃ₐc[R] Y)
  证明: rfl
-/
@[simp] theorem toHopfAlgIso_symm (e : X ≃ₐc[R] Y) :
    toHopfAlgIso e.symm = (toHopfAlgIso e).symm :=
  rfl

/--
theorem `toHopfAlgIso_trans` / 定理 `toHopfAlgIso_trans`

English:
theorem toHopfAlgIso_trans
  given: (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z)
  proof: rfl

中文:
定理 toHopfAlgIso_trans
  条件: (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z)
  证明: rfl
-/
@[simp] theorem toHopfAlgIso_trans (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z) :
    toHopfAlgIso (e.trans f) = toHopfAlgIso e ≪≫ toHopfAlgIso f :=
  rfl

end BialgEquiv

namespace CategoryTheory.Iso

open HopfAlgebra

variable {X Y Z : HopfAlgCat.{v} R}

/--
Definition of `toHopfAlgEquiv` / `toHopfAlgEquiv` 的定义

English:
definition toHopfAlgEquiv
  signature: (i : X ≅ Y)
  body: { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgCat.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgCat.Hom.toBialgHom i.4) x }

中文:
定义 toHopfAlgEquiv
  签名: (i : X ≅ Y)
  定义体: { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgCat.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgCat.Hom.toBialgHom i.4) x }

Depends on / 依赖: BialgHom, BialgHom.congr_fun, HopfAlgCat, HopfAlgCat.Hom.toBialgHom, congr_arg, congr_fun, i.hom.toBialgHom, i.inv.toBialgHom, invFun, left_inv, right_inv, toBialgHom
-/
def toHopfAlgEquiv (i : X ≅ Y) : X ≃ₐc[R] Y :=
  { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgCat.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgCat.Hom.toBialgHom i.4) x }

/--
theorem `toHopfAlgEquiv_toBialgHom` / 定理 `toHopfAlgEquiv_toBialgHom`

English:
theorem toHopfAlgEquiv_toBialgHom
  given: (i : X ≅ Y)
  proof: rfl

中文:
定理 toHopfAlgEquiv_toBialgHom
  条件: (i : X ≅ Y)
  证明: rfl
-/
@[simp] theorem toHopfAlgEquiv_toBialgHom (i : X ≅ Y) :
    (i.toHopfAlgEquiv : X ->ₐc[R] Y) = i.hom.1 := rfl

/--
theorem `toHopfAlgEquiv_refl` / 定理 `toHopfAlgEquiv_refl`

English:
theorem toHopfAlgEquiv_refl
  statement: toHopfAlgEquiv (.refl X) = .refl _ _
  proof: rfl

中文:
定理 toHopfAlgEquiv_refl
  结论: toHopfAlgEquiv (.refl X) = .refl _ _
  证明: rfl
-/
@[simp] theorem toHopfAlgEquiv_refl : toHopfAlgEquiv (.refl X) = .refl _ _ :=
  rfl

/--
theorem `toHopfAlgEquiv_symm` / 定理 `toHopfAlgEquiv_symm`

English:
theorem toHopfAlgEquiv_symm
  given: (e : X ≅ Y)
  proof: rfl

中文:
定理 toHopfAlgEquiv_symm
  条件: (e : X ≅ Y)
  证明: rfl
-/
@[simp] theorem toHopfAlgEquiv_symm (e : X ≅ Y) :
    toHopfAlgEquiv e.symm = (toHopfAlgEquiv e).symm :=
  rfl

/--
theorem `toHopfAlgEquiv_trans` / 定理 `toHopfAlgEquiv_trans`

English:
theorem toHopfAlgEquiv_trans
  given: (e : X ≅ Y) (f : Y ≅ Z)
  proof: rfl

中文:
定理 toHopfAlgEquiv_trans
  条件: (e : X ≅ Y) (f : Y ≅ Z)
  证明: rfl
-/
@[simp] theorem toHopfAlgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toHopfAlgEquiv (e ≪≫ f) = e.toHopfAlgEquiv.trans f.toHopfAlgEquiv :=
  rfl

end CategoryTheory.Iso

/--
Instance `HopfAlgCat.forget_reflects_isos` / 实例 `HopfAlgCat.forget_reflects_isos`

English:
instance HopfAlgCat.forget_reflects_isos
  signature: :
  body: by
    let i := asIso ((forget (HopfAlgCat.{v} R)).map f)
    let e : X ≃ₐc[R] Y := { f.toBialgHom, i.toEquiv with }
    exact ⟨e.toHopfAlgIso.isIso_hom.1⟩

中文:
实例 HopfAlgCat.forget_reflects_isos
  签名: :
  定义体: by
    let i := asIso ((forget (HopfAlgCat.{v} R)).map f)
    let e : X ≃ₐc[R] Y := { f.toBialgHom, i.toEquiv with }
    exact ⟨e.toHopfAlgIso.isIso_hom.1⟩

Depends on / 依赖: HopfAlgCat, e.toHopfAlgIso.isIso_hom, f.toBialgHom, forget, i.toEquiv, isIso_hom, toBialgHom, toEquiv, toHopfAlgIso
-/
instance HopfAlgCat.forget_reflects_isos :
    (forget (HopfAlgCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (HopfAlgCat.{v} R)).map f)
    let e : X ≃ₐc[R] Y := { f.toBialgHom, i.toEquiv with }
    exact ⟨e.toHopfAlgIso.isIso_hom.1⟩
