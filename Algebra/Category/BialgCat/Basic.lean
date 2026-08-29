/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.CoalgCat.Basic
public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# The category of bialgebras over a commutative ring

We introduce the bundled category `BialgCat` of bialgebras over a fixed commutative ring `R`
along with the forgetful functors to `CoalgCat` and `AlgCat`.

This file mimics `Mathlib/LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean`.

-/

@[expose] public section

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/--
Definition of `BialgCat` / `BialgCat` 的定义

English:
structure BialgCat
  parameters: where
  axioms and operations (3):
    - carrier : Type v
    - [instRing : Ring carrier]
    - [instBialgebra : Bialgebra R carrier]

中文:
结构 BialgCat
  参数: where
  公理与运算 (3 个):
    - carrier : 类型v
    - [instRing : Ring carrier]
    - [instBialgebra : Bialgebra R carrier]
-/
structure BialgCat where
  /-- The underlying type. -/
  carrier : Type v
  [instRing : Ring carrier]
  [instBialgebra : Bialgebra R carrier]

initialize_simps_projections BialgCat (-instRing, -instBialgebra)
attribute [instance] BialgCat.instBialgebra BialgCat.instRing

variable {R}

namespace BialgCat

open Bialgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (BialgCat.{v} R) (Type v)
  body: ⟨(·.carrier)⟩

中文:
实例 :
  签名: CoeSort (BialgCat.{v} R) (类型v)
  定义体: ⟨(·.carrier)⟩

Depends on / 依赖: carrier
-/
instance : CoeSort (BialgCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

variable (R) in
/-- The object in the category of `R`-bialgebras associated to an `R`-bialgebra. -/
@[simps]
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (X : Type v) [Ring X] [Bialgebra R X]
  body: X

中文:
定义 of
  签名: (X : 类型v) [Ring X] [Bialgebra R X]
  定义体: X
-/
def of (X : Type v) [Ring X] [Bialgebra R X] :
    BialgCat R where
  carrier := X

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `of_comul` / 引理 `of_comul`

English:
lemma of_comul
  given: {X : Type v} [Ring X] [Bialgebra R X]
  proof: rfl

中文:
引理 of_comul
  条件: {X : 类型v} [Ring X] [Bialgebra R X]
  证明: rfl

Depends on / 依赖: Coalgebra, Coalgebra.comul
-/
lemma of_comul {X : Type v} [Ring X] [Bialgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `of_counit` / 引理 `of_counit`

English:
lemma of_counit
  given: {X : Type v} [Ring X] [Bialgebra R X]
  proof: rfl

中文:
引理 of_counit
  条件: {X : 类型v} [Ring X] [Bialgebra R X]
  证明: rfl

Depends on / 依赖: Coalgebra, Coalgebra.counit, counit
-/
lemma of_counit {X : Type v} [Ring X] [Bialgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `BialgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (V W : BialgCat.{v} R)
  axioms and operations (1):
    - toBialgHom' : V ->ₐc[R] W

中文:
结构 Hom
  参数: (V W : BialgCat.{v} R)
  公理与运算 (1 个):
    - toBialgHom' : V ->ₐc[R] W
-/
structure Hom (V W : BialgCat.{v} R) where
  /-- The underlying `BialgHom` -/
  toBialgHom' : V ->ₐc[R] W

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (BialgCat.{v} R) where
  body: Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom' f.toBialgHom'⟩

中文:
实例 category
  签名: : Category (BialgCat.{v} R) where
  定义体: Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom' f.toBialgHom'⟩
-/
instance category : Category (BialgCat.{v} R) where
  Hom X Y := Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom' f.toBialgHom'⟩

/--
Instance `concreteCategory` / 实例 `concreteCategory`

English:
instance concreteCategory
  signature: : ConcreteCategory (BialgCat.{v} R) (· ->ₐc[R] ·) where
  body: f.toBialgHom'
  ofHom f := ⟨f⟩

中文:
实例 concreteCategory
  签名: : ConcreteCategory (BialgCat.{v} R) (· ->ₐc[R] ·) where
  定义体: f.toBialgHom'
  ofHom f := ⟨f⟩

Depends on / 依赖: f.toBialgHom, toBialgHom
-/
instance concreteCategory : ConcreteCategory (BialgCat.{v} R) (· ->ₐc[R] ·) where
  hom f := f.toBialgHom'
  ofHom f := ⟨f⟩

/--
Definition of `Hom.toBialgHom` / `Hom.toBialgHom` 的定义

English:
abbreviation Hom.toBialgHom
  signature: {X Y : BialgCat R} (f : Hom X Y)
  body: ConcreteCategory.hom (C := BialgCat R) f

中文:
缩写 Hom.toBialgHom
  签名: {X Y : BialgCat R} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := BialgCat R) f

Depends on / 依赖: BialgCat, ConcreteCategory, ConcreteCategory.hom
-/
abbrev Hom.toBialgHom {X Y : BialgCat R} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BialgCat R) f

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
    [Bialgebra R X] [Bialgebra R Y] (f : X ->ₐc[R] Y) :
    of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f

/--
lemma `Hom.toBialgHom_injective` / 引理 `Hom.toBialgHom_injective`

English:
lemma Hom.toBialgHom_injective
  given: (V W : BialgCat.{v} R)
  proof: fun ⟨f⟩ ⟨g⟩ _ => by congr

中文:
引理 Hom.toBialgHom_injective
  条件: (V W : BialgCat.{v} R)
  证明: fun ⟨f⟩ ⟨g⟩ _ => by congr
-/
lemma Hom.toBialgHom_injective (V W : BialgCat.{v} R) :
    Function.Injective (Hom.toBialgHom : Hom V W -> _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

-- TODO: if `Quiver.Hom` and the instance above were `reducible`, this wouldn't be needed.
@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : BialgCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom)
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {X Y : BialgCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom)
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : BialgCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom) :
    f = g :=
  Hom.ext h

/--
theorem `toBialgHom_comp` / 定理 `toBialgHom_comp`

English:
theorem toBialgHom_comp
  given: {X Y Z : BialgCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 toBialgHom_comp
  条件: {X Y Z : BialgCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
@[simp] theorem toBialgHom_comp {X Y Z : BialgCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toBialgHom = g.toBialgHom.comp f.toBialgHom :=
  rfl

/--
theorem `toBialgHom_id` / 定理 `toBialgHom_id`

English:
theorem toBialgHom_id
  given: {M : BialgCat.{v} R}
  proof: rfl

中文:
定理 toBialgHom_id
  条件: {M : BialgCat.{v} R}
  证明: rfl
-/
@[simp] theorem toBialgHom_id {M : BialgCat.{v} R} :
    Hom.toBialgHom (𝟙 M) = BialgHom.id _ _ :=
  rfl

/--
Instance `hasForgetToAlgebra` / 实例 `hasForgetToAlgebra`

English:
instance hasForgetToAlgebra
  signature: : HasForget₂ (BialgCat R) (AlgCat R) where
  body: { obj := fun X => AlgCat.of R X
      map := fun {X Y} f => AlgCat.ofHom f.toBialgHom }

@[simp]

中文:
实例 hasForgetToAlgebra
  签名: : HasForget₂ (BialgCat R) (AlgCat R) where
  定义体: { obj := fun X => AlgCat.of R X
      map := fun {X Y} f => AlgCat.ofHom f.toBialgHom }

@[simp]

Depends on / 依赖: AlgCat, AlgCat.of, AlgCat.ofHom, f.toBialgHom, toBialgHom
-/
instance hasForgetToAlgebra : HasForget₂ (BialgCat R) (AlgCat R) where
  forget₂ :=
    { obj := fun X => AlgCat.of R X
      map := fun {X Y} f => AlgCat.ofHom f.toBialgHom }

@[simp]
/--
theorem `forget₂_algebra_obj` / 定理 `forget₂_algebra_obj`

English:
theorem forget₂_algebra_obj
  given: (X : BialgCat R)
  proof: rfl

@[simp]

中文:
定理 forget₂_algebra_obj
  条件: (X : BialgCat R)
  证明: rfl

@[simp]
-/
theorem forget₂_algebra_obj (X : BialgCat R) :
    (forget₂ (BialgCat R) (AlgCat R)).obj X = AlgCat.of R X :=
  rfl

@[simp]
/--
theorem `forget₂_algebra_map` / 定理 `forget₂_algebra_map`

English:
theorem forget₂_algebra_map
  given: (X Y : BialgCat R) (f : X ⟶ Y)
  proof: rfl

中文:
定理 forget₂_algebra_map
  条件: (X Y : BialgCat R) (f : X ⟶ Y)
  证明: rfl
-/
theorem forget₂_algebra_map (X Y : BialgCat R) (f : X ⟶ Y) :
    (forget₂ (BialgCat R) (AlgCat R)).map f = AlgCat.ofHom f.toBialgHom :=
  rfl

/--
Instance `hasForgetToCoalgebra` / 实例 `hasForgetToCoalgebra`

English:
instance hasForgetToCoalgebra
  signature: : HasForget₂ (BialgCat R) (CoalgCat R) where
  body: { obj := fun X => CoalgCat.of R X
      map := fun {_ _} f => CoalgCat.ofHom f.toBialgHom }

@[simp]

中文:
实例 hasForgetToCoalgebra
  签名: : HasForget₂ (BialgCat R) (CoalgCat R) where
  定义体: { obj := fun X => CoalgCat.of R X
      map := fun {_ _} f => CoalgCat.ofHom f.toBialgHom }

@[simp]

Depends on / 依赖: CoalgCat, CoalgCat.of, CoalgCat.ofHom, f.toBialgHom, toBialgHom
-/
instance hasForgetToCoalgebra : HasForget₂ (BialgCat R) (CoalgCat R) where
  forget₂ :=
    { obj := fun X => CoalgCat.of R X
      map := fun {_ _} f => CoalgCat.ofHom f.toBialgHom }

@[simp]
/--
theorem `forget₂_coalgebra_obj` / 定理 `forget₂_coalgebra_obj`

English:
theorem forget₂_coalgebra_obj
  given: (X : BialgCat R)
  proof: rfl

@[simp]

中文:
定理 forget₂_coalgebra_obj
  条件: (X : BialgCat R)
  证明: rfl

@[simp]
-/
theorem forget₂_coalgebra_obj (X : BialgCat R) :
    (forget₂ (BialgCat R) (CoalgCat R)).obj X = CoalgCat.of R X :=
  rfl

@[simp]
/--
theorem `forget₂_coalgebra_map` / 定理 `forget₂_coalgebra_map`

English:
theorem forget₂_coalgebra_map
  given: (X Y : BialgCat R) (f : X ⟶ Y)
  proof: rfl

中文:
定理 forget₂_coalgebra_map
  条件: (X Y : BialgCat R) (f : X ⟶ Y)
  证明: rfl
-/
theorem forget₂_coalgebra_map (X Y : BialgCat R) (f : X ⟶ Y) :
    (forget₂ (BialgCat R) (CoalgCat R)).map f = CoalgCat.ofHom f.toBialgHom :=
  rfl

end BialgCat

namespace BialgEquiv

open BialgCat

variable {X Y Z : Type v}
variable [Ring X] [Ring Y] [Ring Z]
variable [Bialgebra R X] [Bialgebra R Y] [Bialgebra R Z]

/-- Build an isomorphism in the category `BialgCat R` from a
`BialgEquiv`. -/
@[simps]
/--
Definition of `toBialgIso` / `toBialgIso` 的定义

English:
definition toBialgIso
  signature: (e : X ≃ₐc[R] Y)
  body: BialgCat.ofHom e
  inv := BialgCat.ofHom e.symm
hom_inv_id := Hom.ext DFunLike.ext _ _ e.left_inv
inv_hom_id := Hom.ext DFunLike.ext _ _ e.right_inv

中文:
定义 toBialgIso
  签名: (e : X ≃ₐc[R] Y)
  定义体: BialgCat.ofHom e
  inv := BialgCat.ofHom e.symm
hom_inv_id := Hom.ext DFunLike.ext _ _ e.left_inv
inv_hom_id := Hom.ext DFunLike.ext _ _ e.right_inv

Depends on / 依赖: BialgCat, BialgCat.ofHom
-/
def toBialgIso (e : X ≃ₐc[R] Y) : BialgCat.of R X ≅ BialgCat.of R Y where
  hom := BialgCat.ofHom e
  inv := BialgCat.ofHom e.symm
hom_inv_id := Hom.ext DFunLike.ext _ _ e.left_inv
inv_hom_id := Hom.ext DFunLike.ext _ _ e.right_inv

/--
theorem `toBialgIso_refl` / 定理 `toBialgIso_refl`

English:
theorem toBialgIso_refl
  statement: toBialgIso (BialgEquiv.refl R X) = .refl _
  proof: rfl

中文:
定理 toBialgIso_refl
  结论: toBialgIso (BialgEquiv.refl R X) = .refl _
  证明: rfl
-/
@[simp] theorem toBialgIso_refl : toBialgIso (BialgEquiv.refl R X) = .refl _ :=
  rfl

/--
theorem `toBialgIso_symm` / 定理 `toBialgIso_symm`

English:
theorem toBialgIso_symm
  given: (e : X ≃ₐc[R] Y)
  proof: rfl

中文:
定理 toBialgIso_symm
  条件: (e : X ≃ₐc[R] Y)
  证明: rfl
-/
@[simp] theorem toBialgIso_symm (e : X ≃ₐc[R] Y) :
    toBialgIso e.symm = (toBialgIso e).symm :=
  rfl

/--
theorem `toBialgIso_trans` / 定理 `toBialgIso_trans`

English:
theorem toBialgIso_trans
  given: (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z)
  proof: rfl

中文:
定理 toBialgIso_trans
  条件: (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z)
  证明: rfl
-/
@[simp] theorem toBialgIso_trans (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z) :
    toBialgIso (e.trans f) = toBialgIso e ≪≫ toBialgIso f :=
  rfl

end BialgEquiv

namespace CategoryTheory.Iso

open Bialgebra

variable {X Y Z : BialgCat.{v} R}

/--
Definition of `toBialgEquiv` / `toBialgEquiv` 的定义

English:
definition toBialgEquiv
  signature: (i : X ≅ Y)
  body: { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg BialgCat.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg BialgCat.Hom.toBialgHom i.4) x }

中文:
定义 toBialgEquiv
  签名: (i : X ≅ Y)
  定义体: { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg BialgCat.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg BialgCat.Hom.toBialgHom i.4) x }

Depends on / 依赖: BialgCat, BialgCat.Hom.toBialgHom, BialgHom, BialgHom.congr_fun, congr_arg, congr_fun, i.hom.toBialgHom, i.inv.toBialgHom, invFun, left_inv, right_inv, toBialgHom
-/
def toBialgEquiv (i : X ≅ Y) : X ≃ₐc[R] Y :=
  { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg BialgCat.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg BialgCat.Hom.toBialgHom i.4) x }

/--
theorem `toBialgEquiv_toBialgHom` / 定理 `toBialgEquiv_toBialgHom`

English:
theorem toBialgEquiv_toBialgHom
  given: (i : X ≅ Y)
  proof: rfl

中文:
定理 toBialgEquiv_toBialgHom
  条件: (i : X ≅ Y)
  证明: rfl
-/
@[simp] theorem toBialgEquiv_toBialgHom (i : X ≅ Y) :
    (i.toBialgEquiv : X ->ₐc[R] Y) = i.hom.1 := rfl

/--
theorem `toBialgEquiv_refl` / 定理 `toBialgEquiv_refl`

English:
theorem toBialgEquiv_refl
  statement: toBialgEquiv (.refl X) = .refl _ _
  proof: rfl

中文:
定理 toBialgEquiv_refl
  结论: toBialgEquiv (.refl X) = .refl _ _
  证明: rfl
-/
@[simp] theorem toBialgEquiv_refl : toBialgEquiv (.refl X) = .refl _ _ :=
  rfl

/--
theorem `toBialgEquiv_symm` / 定理 `toBialgEquiv_symm`

English:
theorem toBialgEquiv_symm
  given: (e : X ≅ Y)
  proof: rfl

中文:
定理 toBialgEquiv_symm
  条件: (e : X ≅ Y)
  证明: rfl
-/
@[simp] theorem toBialgEquiv_symm (e : X ≅ Y) :
    toBialgEquiv e.symm = (toBialgEquiv e).symm :=
  rfl

/--
theorem `toBialgEquiv_trans` / 定理 `toBialgEquiv_trans`

English:
theorem toBialgEquiv_trans
  given: (e : X ≅ Y) (f : Y ≅ Z)
  proof: rfl

中文:
定理 toBialgEquiv_trans
  条件: (e : X ≅ Y) (f : Y ≅ Z)
  证明: rfl
-/
@[simp] theorem toBialgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toBialgEquiv (e ≪≫ f) = e.toBialgEquiv.trans f.toBialgEquiv :=
  rfl

end CategoryTheory.Iso

/--
Instance `BialgCat.forget_reflects_isos` / 实例 `BialgCat.forget_reflects_isos`

English:
instance BialgCat.forget_reflects_isos
  signature: :
  body: by
    let i := asIso ((forget (BialgCat.{v} R)).map f)
    let e : X ≃ₐc[R] Y := { f.toBialgHom, i.toEquiv with }
    exact ⟨e.toBialgIso.isIso_hom.1⟩

中文:
实例 BialgCat.forget_reflects_isos
  签名: :
  定义体: by
    let i := asIso ((forget (BialgCat.{v} R)).map f)
    let e : X ≃ₐc[R] Y := { f.toBialgHom, i.toEquiv with }
    exact ⟨e.toBialgIso.isIso_hom.1⟩

Depends on / 依赖: BialgCat, e.toBialgIso.isIso_hom, f.toBialgHom, forget, i.toEquiv, isIso_hom, toBialgHom, toBialgIso, toEquiv
-/
instance BialgCat.forget_reflects_isos :
    (forget (BialgCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (BialgCat.{v} R)).map f)
    let e : X ≃ₐc[R] Y := { f.toBialgHom, i.toEquiv with }
    exact ⟨e.toBialgIso.isIso_hom.1⟩
