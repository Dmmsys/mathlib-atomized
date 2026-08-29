/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Linear categories

An `R`-linear category is a category in which `X ⟶ Y` is an `R`-module in such a way that
composition of morphisms is `R`-linear in both variables.

Note that sometimes in the literature a "linear category" is further required to be abelian.

## Implementation

Corresponding to the fact that we need to have an `AddCommGroup X` structure in place
to talk about a `Module R X` structure,
we need `Preadditive C` as a prerequisite typeclass for `Linear R C`.
This makes for longer signatures than would be ideal.

## Future work

It would be nice to have a usable framework of enriched categories in which this would just be
a category enriched in `Module R`.

-/

@[expose] public section

universe w v u

open CategoryTheory.Limits

open LinearMap

namespace CategoryTheory

/--
Definition of `Linear` / `Linear` 的定义

English:
class Linear
  parameters: (R : Type w) [Semiring R] (C : Type u) [Category.{v} C] [Preadditive C]
  axioms and operations (3):
    - homModule : forall X Y : C, Module R (X ⟶ Y)  [default: by infer_instance]
    - smul_comp : forall (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g  [default: by cat_disch]
    - comp_smul : forall (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g  [default: by cat_disch]

中文:
类 线性
  参数: (R : 类型 w) [半环 R] (C : 类型u) [范畴.{v} C] [预加性 C]
  公理与运算 (3 个):
    - homModule : 对任意 X Y : C, 模 R (X ⟶ Y)  [默认: by infer_instance]
    - smul_comp : 对任意 (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g  [默认: by cat_disch]
    - comp_smul : 对任意 (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g  [默认: by cat_disch]

Depends on / 依赖: infer_instance
-/
class Linear (R : Type w) [Semiring R] (C : Type u) [Category.{v} C] [Preadditive C] where
  homModule : forall X Y : C, Module R (X ⟶ Y) := by infer_instance
  /-- compatibility of the scalar multiplication with the post-composition -/
  smul_comp : forall (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g := by
    cat_disch
  /-- compatibility of the scalar multiplication with the pre-composition -/
  comp_smul : forall (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g := by
    cat_disch

attribute [instance_reducible, instance] Linear.homModule

attribute [simp] Linear.smul_comp Linear.comp_smul

-- (the linter doesn't like `simp` on the `_assoc` lemma)
end CategoryTheory

open CategoryTheory

namespace CategoryTheory.Linear

variable {C : Type u} [Category.{v} C] [Preadditive C]

/--
Instance `preadditiveNatLinear` / 实例 `preadditiveNatLinear`

English:
instance preadditiveNatLinear
  signature: : Linear Nat C where
  body: by exact (Preadditive.rightComp X g).map_nsmul r f
  comp_smul _X _Y Z f r g := by exact (Preadditive.leftComp Z f).map_nsmul r g

中文:
实例 preadditive自然数Linear
  签名: : 线性 自然数 C where
  定义体: by exact (Preadditive.rightComp X g).map_nsmul r f
  comp_smul _X _Y Z f r g := by exact (Preadditive.leftComp Z f).map_nsmul r g

Depends on / 依赖: Preadditive, Preadditive.leftComp, Preadditive.rightComp, comp_smul, leftComp, map_nsmul, rightComp
-/
instance preadditiveNatLinear : Linear Nat C where
  smul_comp X _Y _Z r f g := by exact (Preadditive.rightComp X g).map_nsmul r f
  comp_smul _X _Y Z f r g := by exact (Preadditive.leftComp Z f).map_nsmul r g

/--
Instance `preadditiveIntLinear` / 实例 `preadditiveIntLinear`

English:
instance preadditiveIntLinear
  signature: : Linear Int C where
  body: by exact (Preadditive.rightComp X g).map_zsmul r f
  comp_smul _X _Y Z f r g := by exact (Preadditive.leftComp Z f).map_zsmul r g

中文:
实例 preadditive整数Linear
  签名: : 线性 整数 C where
  定义体: by exact (Preadditive.rightComp X g).map_zsmul r f
  comp_smul _X _Y Z f r g := by exact (Preadditive.leftComp Z f).map_zsmul r g

Depends on / 依赖: Preadditive, Preadditive.leftComp, Preadditive.rightComp, comp_smul, leftComp, map_zsmul, rightComp
-/
instance preadditiveIntLinear : Linear Int C where
  smul_comp X _Y _Z r f g := by exact (Preadditive.rightComp X g).map_zsmul r f
  comp_smul _X _Y Z f r g := by exact (Preadditive.leftComp Z f).map_zsmul r g

section End

variable {R : Type w}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [Linear R C] (X
  body: inferInstanceAs Module R (X ⟶ X)

中文:
实例 [半环
  签名: R] [线性 R C] (X
  定义体: inferInstanceAs Module R (X ⟶ X)

Depends on / 依赖: Module
-/
instance [Semiring R] [Linear R C] (X : C) : Module R (End X) :=
inferInstanceAs Module R (X ⟶ X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: R] [Linear R C] (X
  body: Algebra.ofModule (fun _ _ _ => comp_smul _ _ _ _ _ _) fun _ _ _ => smul_comp _ _ _ _ _ _

中文:
实例 [交换半环
  签名: R] [线性 R C] (X
  定义体: Algebra.ofModule (fun _ _ _ => comp_smul _ _ _ _ _ _) fun _ _ _ => smul_comp _ _ _ _ _ _

Depends on / 依赖: Algebra, Algebra.ofModule, comp_smul, ofModule, smul_comp
-/
instance [CommSemiring R] [Linear R C] (X : C) : Algebra R (End X) :=
  Algebra.ofModule (fun _ _ _ => comp_smul _ _ _ _ _ _) fun _ _ _ => smul_comp _ _ _ _ _ _

end End

section

variable {R : Type w} [Semiring R] [Linear R C]

section InducedCategory

universe u'

variable {D : Type u'} (F : D -> C)

/--
Instance `inducedCategory` / 实例 `inducedCategory`

English:
instance inducedCategory
  signature: : Linear.{w, v} R (InducedCategory C F) where
  body: Equiv.module _ InducedCategory.homEquiv
  smul_comp _ _ _ _ _ _ := by ext; apply smul_comp
  comp_smul _ _ _ _ _ _ := by ext; apply comp_smul

中文:
实例 inducedCategory
  签名: : 线性.{w, v} R (InducedCategory C F) where
  定义体: Equiv.module _ InducedCategory.homEquiv
  smul_comp _ _ _ _ _ _ := by ext; apply smul_comp
  comp_smul _ _ _ _ _ _ := by ext; apply comp_smul

Depends on / 依赖: Equiv.module, HasCardinalFilteredGenerator, HasCardinalFilteredGenerator.exists_generator, InducedCategory, InducedCategory.homEquiv, essentiallySmall_isPresentable, exists_generator, hP.essentiallySmall_isPresentable, homEquiv, module
-/
instance inducedCategory : Linear.{w, v} R (InducedCategory C F) where
  homModule X Y := Equiv.module _ InducedCategory.homEquiv
  smul_comp _ _ _ _ _ _ := by ext; apply smul_comp
  comp_smul _ _ _ _ _ _ := by ext; apply comp_smul

variable {F} in
/-- The linear equivalence `(X ⟶ Y) ≃+ (F X ⟶ F Y)` when `F : D → C` and
`C` is a `R`-linear category. -/
@[simps!]
/--
Definition of `_root_.CategoryTheory.InducedCategory.homLinearEquiv` / `_root_.CategoryTheory.InducedCategory.homLinearEquiv` 的定义

English:
definition _root_.CategoryTheory.InducedCategory.homLinearEquiv
  body: InducedCategory.homAddEquiv
  map_smul' := by cat_disch

中文:
定义 _root_.范畴论.InducedCategory.homLinearEquiv
  定义体: InducedCategory.homAddEquiv
  map_smul' := by cat_disch

Depends on / 依赖: InducedCategory, InducedCategory.homAddEquiv, homAddEquiv
-/
def _root_.CategoryTheory.InducedCategory.homLinearEquiv
    {X Y : InducedCategory C F} :
    (X ⟶ Y) ≃ₗ[R] (F X ⟶ F Y) where
  toAddEquiv := InducedCategory.homAddEquiv
  map_smul' := by cat_disch

end InducedCategory

/--
Instance `fullSubcategory` / 实例 `fullSubcategory`

English:
instance fullSubcategory
  signature: (Z : ObjectProperty C)
  body: inducedCategory _

中文:
实例 fullSubcategory
  签名: (Z : ObjectProperty C)
  定义体: inducedCategory _

Depends on / 依赖: inducedCategory
-/
instance fullSubcategory (Z : ObjectProperty C) : Linear.{w, v} R Z.FullSubcategory :=
  inducedCategory _

variable (R)

/-- Composition by a fixed left argument as an `R`-linear map. -/
@[simps]
/--
Definition of `leftComp` / `leftComp` 的定义

English:
definition leftComp
  signature: {X Y : C} (Z : C) (f : X ⟶ Y)
  body: f ≫ g
  map_add' := by simp
  map_smul' := by simp

中文:
定义 leftComp
  签名: {X Y : C} (Z : C) (f : X ⟶ Y)
  定义体: f ≫ g
  map_add' := by simp
  map_smul' := by simp
-/
def leftComp {X Y : C} (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) ->ₗ[R] X ⟶ Z where
  toFun g := f ≫ g
  map_add' := by simp
  map_smul' := by simp

/-- Composition by a fixed right argument as an `R`-linear map. -/
@[simps]
/--
Definition of `rightComp` / `rightComp` 的定义

English:
definition rightComp
  signature: (X : C) {Y Z : C} (g : Y ⟶ Z)
  body: f ≫ g
  map_add' := by simp
  map_smul' := by simp

中文:
定义 rightComp
  签名: (X : C) {Y Z : C} (g : Y ⟶ Z)
  定义体: f ≫ g
  map_add' := by simp
  map_smul' := by simp
-/
def rightComp (X : C) {Y Z : C} (g : Y ⟶ Z) : (X ⟶ Y) ->ₗ[R] X ⟶ Z where
  toFun f := f ≫ g
  map_add' := by simp
  map_smul' := by simp

instance {X Y : C} (f : X ⟶ Y) [Epi f] (r : R) [Invertible r] : Epi (r • f) :=
  ⟨fun g g' H => by
    rw [smul_comp]; rw [smul_comp]; rw [← comp_smul]; rw [← comp_smul]; rw [cancel_epi] at H
    simpa [smul_smul] using congr_arg (fun f => ⅟r • f) H⟩

instance {X Y : C} (f : X ⟶ Y) [Mono f] (r : R) [Invertible r] : Mono (r • f) :=
  ⟨fun g g' H => by
    rw [comp_smul]; rw [comp_smul]; rw [← smul_comp]; rw [← smul_comp]; rw [cancel_mono] at H
    simpa [smul_smul] using congr_arg (fun f => ⅟r • f) H⟩

/--
Definition of `homCongr` / `homCongr` 的定义

English:
definition homCongr
  signature: (k : Type*) {C : Type*} [Category* C] [Semiring k] [Preadditive C] [Linear k C]
  body: {
    (rightComp k Y f₂.hom).comp
      (leftComp k W
        f₁.symm.hom) with
    invFun := (leftComp k W f₁.hom).comp (rightComp k Y f₂.symm.hom)
    left_inv := fun x => by
      simp only [Iso.symm_hom, LinearMap.toFun_eq_coe, LinearMap.coe_comp, Function.comp_apply,
        leftComp_apply, rig

中文:
定义 homCongr
  签名: (k : 类型) {C : 类型} [范畴* C] [半环 k] [预加性 C] [线性 k C]
  定义体: {
    (rightComp k Y f₂.hom).comp
      (leftComp k W
        f₁.symm.hom) with
    invFun := (leftComp k W f₁.hom).comp (rightComp k Y f₂.symm.hom)
    left_inv := fun x => by
      simp only [Iso.symm_hom, LinearMap.toFun_eq_coe, LinearMap.coe_comp, Function.comp_apply,
        leftComp_apply, rig

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Function, Function.comp_apply, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Iso.in, Iso.symm_hom, LinearMap, LinearMap.coe_comp, LinearMap.toFun_eq_coe, coe_comp, comp_apply, comp_id, hom_inv_id, hom_inv_id_assoc, invFun, leftComp, leftComp_apply
-/
def homCongr (k : Type*) {C : Type*} [Category* C] [Semiring k] [Preadditive C] [Linear k C]
    {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) : (X ⟶ W) ≃ₗ[k] Y ⟶ Z :=
  {
    (rightComp k Y f₂.hom).comp
      (leftComp k W
        f₁.symm.hom) with
    invFun := (leftComp k W f₁.hom).comp (rightComp k Y f₂.symm.hom)
    left_inv := fun x => by
      simp only [Iso.symm_hom, LinearMap.toFun_eq_coe, LinearMap.coe_comp, Function.comp_apply,
        leftComp_apply, rightComp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Iso.hom_inv_id_assoc]
    right_inv := fun x => by
      simp only [Iso.symm_hom, LinearMap.coe_comp, Function.comp_apply, rightComp_apply,
        leftComp_apply, LinearMap.toFun_eq_coe, Iso.inv_hom_id_assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id] }

/--
theorem `homCongr_apply` / 定理 `homCongr_apply`

English:
theorem homCongr_apply
  statement: (k : Type*) {C : Type*} [Category* C] [Semiring k] [Preadditive C]
  proof: rfl

中文:
定理 homCongr_apply
  结论: (k : 类型) {C : 类型} [范畴* C] [半环 k] [预加性 C]
  证明: rfl
-/
theorem homCongr_apply (k : Type*) {C : Type*} [Category* C] [Semiring k] [Preadditive C]
    [Linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : X ⟶ W) :
    homCongr k f₁ f₂ f = (f₁.inv ≫ f) ≫ f₂.hom :=
  rfl

/--
theorem `homCongr_symm_apply` / 定理 `homCongr_symm_apply`

English:
theorem homCongr_symm_apply
  statement: (k : Type*) {C : Type*} [Category* C] [Semiring k] [Preadditive C]
  proof: rfl

中文:
定理 homCongr_symm_apply
  结论: (k : 类型) {C : 类型} [范畴* C] [半环 k] [预加性 C]
  证明: rfl
-/
theorem homCongr_symm_apply (k : Type*) {C : Type*} [Category* C] [Semiring k] [Preadditive C]
    [Linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : Y ⟶ Z) :
    (homCongr k f₁ f₂).symm f = f₁.hom ≫ f ≫ f₂.inv :=
  rfl

variable {R}

@[simp]
/--
lemma `units_smul_comp` / 引理 `units_smul_comp`

English:
lemma units_smul_comp
  given: {X Y Z : C} (r : Rˣ) (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  apply Linear.smul_comp

@[simp]

中文:
引理 units_smul_comp
  条件: {X Y Z : C} (r : Rˣ) (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  apply Linear.smul_comp

@[simp]

Depends on / 依赖: Linear, Linear.smul_comp, smul_comp
-/
lemma units_smul_comp {X Y Z : C} (r : Rˣ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (r • f) ≫ g = r • f ≫ g := by
  apply Linear.smul_comp

@[simp]
/--
lemma `comp_units_smul` / 引理 `comp_units_smul`

English:
lemma comp_units_smul
  given: {X Y Z : C} (f : X ⟶ Y) (r : Rˣ) (g : Y ⟶ Z)
  proof: by
  apply Linear.comp_smul

中文:
引理 comp_units_smul
  条件: {X Y Z : C} (f : X ⟶ Y) (r : Rˣ) (g : Y ⟶ Z)
  证明: by
  apply Linear.comp_smul

Depends on / 依赖: Linear, Linear.comp_smul, comp_smul
-/
lemma comp_units_smul {X Y Z : C} (f : X ⟶ Y) (r : Rˣ) (g : Y ⟶ Z) :
    f ≫ (r • g) = r • f ≫ g := by
  apply Linear.comp_smul

end

section

variable {S : Type w} [CommSemiring S] [Linear S C]

/-- Composition as a bilinear map. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (X Y Z : C)
  body: leftComp S Z f
  map_add' := by
    intros
    ext
    simp
  map_smul' := by
    intros
    ext
    simp

中文:
定义 comp
  签名: (X Y Z : C)
  定义体: leftComp S Z f
  map_add' := by
    intros
    ext
    simp
  map_smul' := by
    intros
    ext
    simp

Depends on / 依赖: leftComp
-/
def comp (X Y Z : C) : (X ⟶ Y) ->ₗ[S] (Y ⟶ Z) ->ₗ[S] X ⟶ Z where
  toFun f := leftComp S Z f
  map_add' := by
    intros
    ext
    simp
  map_smul' := by
    intros
    ext
    simp

end

end CategoryTheory.Linear
