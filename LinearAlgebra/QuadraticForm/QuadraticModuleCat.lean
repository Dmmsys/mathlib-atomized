/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The category of quadratic modules
-/

@[expose] public section

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/--
Definition of `QuadraticModuleCat` / `QuadraticModuleCat` 的定义

English:
structure QuadraticModuleCat
  parameters: extends ModuleCat.{v} R
  extends: ModuleCat.{v} R
  axioms and operations (1):
    - form : QuadraticForm R carrier

中文:
结构 QuadraticModuleCat
  参数: extends ModuleCat.{v} R
  继承: ModuleCat.{v} R
  公理与运算 (1 个):
    - form : QuadraticForm R carrier
-/
structure QuadraticModuleCat extends ModuleCat.{v} R where
  /-- The quadratic form associated with the module. -/
  form : QuadraticForm R carrier

variable {R}

namespace QuadraticModuleCat

open QuadraticForm QuadraticMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (QuadraticModuleCat.{v} R) (Type v)
  body: ⟨(·.carrier)⟩

中文:
实例 :
  签名: CoeSort (QuadraticModuleCat.{v} R) (类型v)
  定义体: ⟨(·.carrier)⟩

Depends on / 依赖: carrier
-/
instance : CoeSort (QuadraticModuleCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

/--
theorem `moduleCat_of_toModuleCat` / 定理 `moduleCat_of_toModuleCat`

English:
theorem moduleCat_of_toModuleCat
  given: (X : QuadraticModuleCat.{v} R)
  proof: rfl

中文:
定理 moduleCat_of_toModuleCat
  条件: (X : QuadraticModuleCat.{v} R)
  证明: rfl
-/
@[simp] theorem moduleCat_of_toModuleCat (X : QuadraticModuleCat.{v} R) :
    ModuleCat.of R X.toModuleCat = X.toModuleCat :=
  rfl

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: {X : Type v} [AddCommGroup X] [Module R X] (Q : QuadraticForm R X)
  body: { ModuleCat.of R X with
    form := Q }

中文:
缩写 of
  签名: {X : 类型v} [AddCommGroup X] [Module R X] (Q : QuadraticForm R X)
  定义体: { ModuleCat.of R X with
    form := Q }

Depends on / 依赖: ModuleCat, ModuleCat.of
-/
abbrev of {X : Type v} [AddCommGroup X] [Module R X] (Q : QuadraticForm R X) :
    QuadraticModuleCat R :=
  { ModuleCat.of R X with
    form := Q }

/-- A type alias for `QuadraticForm.LinearIsometry` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (V W : QuadraticModuleCat.{v} R)
  axioms and operations (1):
    - toIsometry' : V.form ->qᵢ W.form

中文:
结构 Hom
  参数: (V W : QuadraticModuleCat.{v} R)
  公理与运算 (1 个):
    - toIsometry' : V.form ->qᵢ W.form
-/
structure Hom (V W : QuadraticModuleCat.{v} R) where
  /-- The underlying isometry -/
  toIsometry' : V.form ->qᵢ W.form

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (QuadraticModuleCat.{v} R) where
  body: Hom M N
  id M := ⟨Isometry.id M.form⟩
  comp f g := ⟨Isometry.comp g.toIsometry' f.toIsometry'⟩

中文:
实例 category
  签名: : Category (QuadraticModuleCat.{v} R) where
  定义体: Hom M N
  id M := ⟨Isometry.id M.form⟩
  comp f g := ⟨Isometry.comp g.toIsometry' f.toIsometry'⟩
-/
instance category : Category (QuadraticModuleCat.{v} R) where
  Hom M N := Hom M N
  id M := ⟨Isometry.id M.form⟩
  comp f g := ⟨Isometry.comp g.toIsometry' f.toIsometry'⟩

/--
Instance `concreteCategory` / 实例 `concreteCategory`

English:
instance concreteCategory
  signature: : ConcreteCategory (QuadraticModuleCat.{v} R)
  body: f.toIsometry'
  ofHom f := ⟨f⟩

中文:
实例 concreteCategory
  签名: : ConcreteCategory (QuadraticModuleCat.{v} R)
  定义体: f.toIsometry'
  ofHom f := ⟨f⟩

Depends on / 依赖: f.toIsometry, toIsometry
-/
instance concreteCategory : ConcreteCategory (QuadraticModuleCat.{v} R)
    fun V W => V.form ->qᵢ W.form where
  hom f := f.toIsometry'
  ofHom f := ⟨f⟩

/--
Definition of `Hom.toIsometry` / `Hom.toIsometry` 的定义

English:
abbreviation Hom.toIsometry
  signature: {X Y : QuadraticModuleCat R} (f : Hom X Y)
  body: ConcreteCategory.hom (C := QuadraticModuleCat R) f

中文:
缩写 Hom.toIsometry
  签名: {X Y : QuadraticModuleCat R} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := QuadraticModuleCat R) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, QuadraticModuleCat
-/
abbrev Hom.toIsometry {X Y : QuadraticModuleCat R} (f : Hom X Y) :=
  ConcreteCategory.hom (C := QuadraticModuleCat R) f

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
    {Q₁ : QuadraticForm R X} {Q₂ : QuadraticForm R Y} (f : Q₁ ->qᵢ Q₂) :
    of Q₁ ⟶ of Q₂ :=
  ConcreteCategory.ofHom f

/--
lemma `Hom.toIsometry_injective` / 引理 `Hom.toIsometry_injective`

English:
lemma Hom.toIsometry_injective
  given: (V W : QuadraticModuleCat.{v} R)
  proof: fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]

中文:
引理 Hom.toIsometry_injective
  条件: (V W : QuadraticModuleCat.{v} R)
  证明: fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]
-/
lemma Hom.toIsometry_injective (V W : QuadraticModuleCat.{v} R) :
    Function.Injective (Hom.toIsometry : Hom V W -> _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {M N : QuadraticModuleCat.{v} R} (f g : M ⟶ N) (h : f.toIsometry = g.toIsometry)
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {M N : QuadraticModuleCat.{v} R} (f g : M ⟶ N) (h : f.toIsometry = g.toIsometry)
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {M N : QuadraticModuleCat.{v} R} (f g : M ⟶ N) (h : f.toIsometry = g.toIsometry) :
    f = g :=
  Hom.ext h

/--
theorem `toIsometry_comp` / 定理 `toIsometry_comp`

English:
theorem toIsometry_comp
  given: {M N U : QuadraticModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ U)
  proof: rfl

中文:
定理 toIsometry_comp
  条件: {M N U : QuadraticModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ U)
  证明: rfl
-/
@[simp] theorem toIsometry_comp {M N U : QuadraticModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
    (f ≫ g).toIsometry = g.toIsometry.comp f.toIsometry :=
  rfl

/--
theorem `toIsometry_id` / 定理 `toIsometry_id`

English:
theorem toIsometry_id
  given: {M : QuadraticModuleCat.{v} R}
  proof: rfl

中文:
定理 toIsometry_id
  条件: {M : QuadraticModuleCat.{v} R}
  证明: rfl
-/
@[simp] theorem toIsometry_id {M : QuadraticModuleCat.{v} R} :
    Hom.toIsometry (𝟙 M) = Isometry.id _ :=
  rfl

/--
Instance `hasForgetToModule` / 实例 `hasForgetToModule`

English:
instance hasForgetToModule
  signature: : HasForget₂ (QuadraticModuleCat R) (ModuleCat R) where
  body: { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toIsometry.toLinearMap }

@[simp]

中文:
实例 hasForgetToModule
  签名: : HasForget₂ (QuadraticModuleCat R) (ModuleCat R) where
  定义体: { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toIsometry.toLinearMap }

@[simp]

Depends on / 依赖: ModuleCat, ModuleCat.of, ModuleCat.ofHom, f.toIsometry.toLinearMap, toIsometry, toLinearMap
-/
instance hasForgetToModule : HasForget₂ (QuadraticModuleCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toIsometry.toLinearMap }

@[simp]
/--
theorem `forget₂_obj` / 定理 `forget₂_obj`

English:
theorem forget₂_obj
  given: (X : QuadraticModuleCat R)
  proof: rfl

@[simp]

中文:
定理 forget₂_obj
  条件: (X : QuadraticModuleCat R)
  证明: rfl

@[simp]
-/
theorem forget₂_obj (X : QuadraticModuleCat R) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
/--
theorem `forget₂_map` / 定理 `forget₂_map`

English:
theorem forget₂_map
  given: (X Y : QuadraticModuleCat R) (f : X ⟶ Y)
  proof: rfl

中文:
定理 forget₂_map
  条件: (X Y : QuadraticModuleCat R) (f : X ⟶ Y)
  证明: rfl
-/
theorem forget₂_map (X Y : QuadraticModuleCat R) (f : X ⟶ Y) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).map f =
      ModuleCat.ofHom f.toIsometry.toLinearMap :=
  rfl

variable {X Y Z : Type v}
variable [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
variable {Q₁ : QuadraticForm R X} {Q₂ : QuadraticForm R Y} {Q₃ : QuadraticForm R Z}

/-- Build an isomorphism in the category `QuadraticModuleCat R` from a
`QuadraticForm.IsometryEquiv`. -/
@[simps]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: (e : Q₁.IsometryEquiv Q₂)
  body: ofHom e.toIsometry
  inv := ofHom e.symm.toIsometry
hom_inv_id := Hom.ext DFunLike.ext _ _ e.left_inv
inv_hom_id := Hom.ext DFunLike.ext _ _ e.right_inv

中文:
定义 ofIso
  签名: (e : Q₁.IsometryEquiv Q₂)
  定义体: ofHom e.toIsometry
  inv := ofHom e.symm.toIsometry
hom_inv_id := Hom.ext DFunLike.ext _ _ e.left_inv
inv_hom_id := Hom.ext DFunLike.ext _ _ e.right_inv

Depends on / 依赖: e.toIsometry, toIsometry
-/
def ofIso (e : Q₁.IsometryEquiv Q₂) : QuadraticModuleCat.of Q₁ ≅ QuadraticModuleCat.of Q₂ where
  hom := ofHom e.toIsometry
  inv := ofHom e.symm.toIsometry
hom_inv_id := Hom.ext DFunLike.ext _ _ e.left_inv
inv_hom_id := Hom.ext DFunLike.ext _ _ e.right_inv

/--
theorem `ofIso_refl` / 定理 `ofIso_refl`

English:
theorem ofIso_refl
  statement: ofIso (IsometryEquiv.refl Q₁) = .refl _
  proof: rfl

中文:
定理 ofIso_refl
  结论: ofIso (IsometryEquiv.refl Q₁) = .refl _
  证明: rfl
-/
@[simp] theorem ofIso_refl : ofIso (IsometryEquiv.refl Q₁) = .refl _ :=
  rfl

/--
theorem `ofIso_symm` / 定理 `ofIso_symm`

English:
theorem ofIso_symm
  given: (e : Q₁.IsometryEquiv Q₂)
  statement: ofIso e.symm = (ofIso e).symm
  proof: rfl

中文:
定理 ofIso_symm
  条件: (e : Q₁.IsometryEquiv Q₂)
  结论: ofIso e.symm = (ofIso e).symm
  证明: rfl
-/
@[simp] theorem ofIso_symm (e : Q₁.IsometryEquiv Q₂) : ofIso e.symm = (ofIso e).symm :=
  rfl

/--
theorem `ofIso_trans` / 定理 `ofIso_trans`

English:
theorem ofIso_trans
  given: (e : Q₁.IsometryEquiv Q₂) (f : Q₂.IsometryEquiv Q₃)
  proof: rfl

中文:
定理 ofIso_trans
  条件: (e : Q₁.IsometryEquiv Q₂) (f : Q₂.IsometryEquiv Q₃)
  证明: rfl
-/
@[simp] theorem ofIso_trans (e : Q₁.IsometryEquiv Q₂) (f : Q₂.IsometryEquiv Q₃) :
    ofIso (e.trans f) = ofIso e ≪≫ ofIso f :=
  rfl

end QuadraticModuleCat

namespace CategoryTheory.Iso

open QuadraticForm

variable {X Y Z : QuadraticModuleCat.{v} R}

/-- Build a `QuadraticForm.IsometryEquiv` from an isomorphism in the category
`QuadraticModuleCat R`. -/
@[simps]
/--
Definition of `toIsometryEquiv` / `toIsometryEquiv` 的定义

English:
definition toIsometryEquiv
  signature: (i : X ≅ Y)
  body: i.hom.toIsometry
  invFun := i.inv.toIsometry
  left_inv x := by
    change (i.hom ≫ i.inv).toIsometry x = x
    simp
  right_inv x := by
    change (i.inv ≫ i.hom).toIsometry x = x
    simp
  map_add' := map_add _
  map_smul' := map_smul _
  map_app' := QuadraticMap.Isometry.map_app _

中文:
定义 toIsometryEquiv
  签名: (i : X ≅ Y)
  定义体: i.hom.toIsometry
  invFun := i.inv.toIsometry
  left_inv x := by
    change (i.hom ≫ i.inv).toIsometry x = x
    simp
  right_inv x := by
    change (i.inv ≫ i.hom).toIsometry x = x
    simp
  map_add' := map_add _
  map_smul' := map_smul _
  map_app' := QuadraticMap.Isometry.map_app _

Depends on / 依赖: i.hom.toIsometry, toIsometry
-/
def toIsometryEquiv (i : X ≅ Y) : X.form.IsometryEquiv Y.form where
  toFun := i.hom.toIsometry
  invFun := i.inv.toIsometry
  left_inv x := by
    change (i.hom ≫ i.inv).toIsometry x = x
    simp
  right_inv x := by
    change (i.inv ≫ i.hom).toIsometry x = x
    simp
  map_add' := map_add _
  map_smul' := map_smul _
  map_app' := QuadraticMap.Isometry.map_app _

/--
theorem `toIsometryEquiv_refl` / 定理 `toIsometryEquiv_refl`

English:
theorem toIsometryEquiv_refl
  statement: toIsometryEquiv (.refl X) = .refl _
  proof: rfl

中文:
定理 toIsometryEquiv_refl
  结论: toIsometryEquiv (.refl X) = .refl _
  证明: rfl
-/
@[simp] theorem toIsometryEquiv_refl : toIsometryEquiv (.refl X) = .refl _ :=
  rfl

/--
theorem `toIsometryEquiv_symm` / 定理 `toIsometryEquiv_symm`

English:
theorem toIsometryEquiv_symm
  given: (e : X ≅ Y)
  proof: rfl

中文:
定理 toIsometryEquiv_symm
  条件: (e : X ≅ Y)
  证明: rfl
-/
@[simp] theorem toIsometryEquiv_symm (e : X ≅ Y) :
    toIsometryEquiv e.symm = (toIsometryEquiv e).symm :=
  rfl

/--
theorem `toIsometryEquiv_trans` / 定理 `toIsometryEquiv_trans`

English:
theorem toIsometryEquiv_trans
  given: (e : X ≅ Y) (f : Y ≅ Z)
  proof: rfl

中文:
定理 toIsometryEquiv_trans
  条件: (e : X ≅ Y) (f : Y ≅ Z)
  证明: rfl
-/
@[simp] theorem toIsometryEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toIsometryEquiv (e ≪≫ f) = e.toIsometryEquiv.trans f.toIsometryEquiv :=
  rfl

end CategoryTheory.Iso
