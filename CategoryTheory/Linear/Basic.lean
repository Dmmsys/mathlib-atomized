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

/-- A category is called `R`-linear if `P ⟶ Q` is an `R`-module such that composition is
`R`-linear in both variables. -/
/-
**CategoryTheory.Linear** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：Linear (R : Type w) [Semiring R] (C : Type u) [Category.{v} C] [Preadditiv
e C] where homModule : forall X Y : C, Module R (X ⟶ Y)
参数：R : Type w；C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is called `R`-linear if `P ⟶ Q` is an `R`-module such that compositio
n is
`R`-linear in both variables.
-/
class Linear (R : Type w) [Semiring R] (C : Type u) [Category.{v} C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y) := by infer_instance
  /-- compatibility of the scalar multiplication with the post-composition -/
  smul_comp : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g := by
    cat_disch
  /-- compatibility of the scalar multiplication with the pre-composition -/
  comp_smul : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g := by
    cat_disch

attribute [instance_reducible, instance] Linear.homModule

attribute [simp] Linear.smul_comp Linear.comp_smul

-- (the linter doesn't like `simp` on the `_assoc` lemma)
end CategoryTheory

open CategoryTheory

namespace CategoryTheory.Linear

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-
**CategoryTheory.Linear.preadditiveNatLinear** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Linear`。
形式化陈述：preadditiveNatLinear : Linear Nat C where smul_comp X _Y _Z r f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preadditiveNatLinear : Linear ℕ C where
  smul_comp X _Y _Z r f g := by exact (Preadditive.rightComp X g).map_nsmul r f
  comp_smul _X _Y Z f r g := by exact (Preadditive.leftComp Z f).map_nsmul r g
/-
**CategoryTheory.Linear.preadditiveIntLinear** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Linear`。
形式化陈述：preadditiveIntLinear : Linear Int C where smul_comp X _Y _Z r f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preadditiveIntLinear : Linear ℤ C where
  smul_comp X _Y _Z r f g := by exact (Preadditive.rightComp X g).map_zsmul r f
  comp_smul _X _Y Z f r g := by exact (Preadditive.leftComp Z f).map_zsmul r g

section End

variable {R : Type w}

/-
**CategoryTheory.Linear.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Linear`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [Linear R C] (X : C) : Module R (End X) :=
  inferInstanceAs <| Module R (X ⟶ X)
/-
**CategoryTheory.Linear.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Linear`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring R] [Linear R C] (X : C) : Algebra R (End X) :=
  Algebra.ofModule (fun _ _ _ => comp_smul _ _ _ _ _ _) fun _ _ _ => smul_comp _ _ _ _ _ _

end End

section

variable {R : Type w} [Semiring R] [Linear R C]

section InducedCategory

universe u'

variable {D : Type u'} (F : D → C)

/-
**CategoryTheory.Linear.inducedCategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Linear`。
形式化陈述：inducedCategory : Linear.{w, v} R (InducedCategory C F) where homModule X 
Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inducedCategory : Linear.{w, v} R (InducedCategory C F) where
  homModule X Y := Equiv.module _ InducedCategory.homEquiv
  smul_comp _ _ _ _ _ _ := by ext; apply smul_comp
  comp_smul _ _ _ _ _ _ := by ext; apply comp_smul

variable {F} in
/-- The linear equivalence `(X ⟶ Y) ≃+ (F X ⟶ F Y)` when `F : D → C` and
`C` is a `R`-linear category. -/
@[simps!]
/-
**CategoryTheory.Linear._root_.CategoryTheory.InducedCategory.homLinearEquiv** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Linear`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence `(X ⟶ Y) ≃+ (F X ⟶ F Y)` when `F : D → C` and
`C` is a `R`-linear category.
-/
def _root_.CategoryTheory.InducedCategory.homLinearEquiv
    {X Y : InducedCategory C F} :
    (X ⟶ Y) ≃ₗ[R] (F X ⟶ F Y) where
  toAddEquiv := InducedCategory.homAddEquiv
  map_smul' := by cat_disch

end InducedCategory

/-
**CategoryTheory.Linear.fullSubcategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Linear`。
形式化陈述：fullSubcategory (Z : ObjectProperty C) : Linear.{w, v} R Z.FullSubcategory
参数：Z : ObjectProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fullSubcategory (Z : ObjectProperty C) : Linear.{w, v} R Z.FullSubcategory :=
  inducedCategory _

variable (R)

/-- Composition by a fixed left argument as an `R`-linear map. -/
@[simps]
/-
**CategoryTheory.Linear.leftComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Linea
r`。
形式化陈述：leftComp {X Y : C} (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) ->ₗ[R] X ⟶ Z where toFun 
g
参数：Z : C；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition by a fixed left argument as an `R`-linear map.
-/
def leftComp {X Y : C} (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →ₗ[R] X ⟶ Z where
  toFun g := f ≫ g
  map_add' := by simp
  map_smul' := by simp

/-- Composition by a fixed right argument as an `R`-linear map. -/
@[simps]
/-
**CategoryTheory.Linear.rightComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Line
ar`。
形式化陈述：rightComp (X : C) {Y Z : C} (g : Y ⟶ Z) : (X ⟶ Y) ->ₗ[R] X ⟶ Z where toFun
 f
参数：X : C；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition by a fixed right argument as an `R`-linear map.
-/
def rightComp (X : C) {Y Z : C} (g : Y ⟶ Z) : (X ⟶ Y) →ₗ[R] X ⟶ Z where
  toFun f := f ≫ g
  map_add' := by simp
  map_smul' := by simp
/-
**CategoryTheory.Linear.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Linear`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) [Epi f] (r : R) [Invertible r] : Epi (r • f) :=
  ⟨fun g g' H => by
    rw [smul_comp, smul_comp, ← comp_smul, ← comp_smul, cancel_epi] at H
    simpa [smul_smul] using congr_arg (fun f => ⅟r • f) H⟩
/-
**CategoryTheory.Linear.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Linear`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) [Mono f] (r : R) [Invertible r] : Mono (r • f) :=
  ⟨fun g g' H => by
    rw [comp_smul, comp_smul, ← smul_comp, ← smul_comp, cancel_mono] at H
    simpa [smul_smul] using congr_arg (fun f => ⅟r • f) H⟩

/-- Given isomorphic objects `X ≅ Y, W ≅ Z` in a `k`-linear category, we have a `k`-linear
isomorphism between `Hom(X, W)` and `Hom(Y, Z).` -/
/-
**CategoryTheory.Linear.homCongr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Linea
r`。
形式化陈述：homCongr (k : Type*) {C : Type*} [Category* C] [Semiring k] [Preadditive C
] [Linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) : (X ⟶ W) ≃ₗ[k] Y ⟶ Z
参数：k : Type*；f₁ : X ≅ Y；f₂ : W ≅ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given isomorphic objects `X ≅ Y, W ≅ Z` in a `k`-linear category, we have a `k`-
linear
isomorphism between `Hom(X, W)` and `Hom(Y, Z).`
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
/-
**CategoryTheory.Linear.homCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Linear`。
形式化陈述：homCongr_apply (k : Type*) {C : Type*} [Category* C] [Semiring k] [Preaddi
tive C] [Linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : X ⟶ W) : homCo
ngr k f₁ f₂ f = (f₁.inv ≫ f) ≫ f₂.hom
参数：k : Type*；f₁ : X ≅ Y；f₂ : W ≅ Z；f : X ⟶ W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homCongr_apply (k : Type*) {C : Type*} [Category* C] [Semiring k] [Preadditive C]
    [Linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : X ⟶ W) :
    homCongr k f₁ f₂ f = (f₁.inv ≫ f) ≫ f₂.hom :=
  rfl
/-
**CategoryTheory.Linear.homCongr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Linear`。
形式化陈述：homCongr_symm_apply (k : Type*) {C : Type*} [Category* C] [Semiring k] [Pr
eadditive C] [Linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : Y ⟶ Z) : 
(homCongr k f₁ f₂).symm f = f₁.hom ≫ f ≫ f₂.inv
参数：k : Type*；f₁ : X ≅ Y；f₂ : W ≅ Z；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homCongr_symm_apply (k : Type*) {C : Type*} [Category* C] [Semiring k] [Preadditive C]
    [Linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : Y ⟶ Z) :
    (homCongr k f₁ f₂).symm f = f₁.hom ≫ f ≫ f₂.inv :=
  rfl

variable {R}

@[simp]
/-
**CategoryTheory.Linear.units_smul_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Linear`。
形式化陈述：units_smul_comp {X Y Z : C} (r : Rˣ) (f : X ⟶ Y) (g : Y ⟶ Z) : (r • f) ≫ g
 = r • f ≫ g
参数：r : Rˣ；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
-/
lemma units_smul_comp {X Y Z : C} (r : Rˣ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (r • f) ≫ g = r • f ≫ g := by
  apply Linear.smul_comp

@[simp]
/-
**CategoryTheory.Linear.comp_units_smul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Linear`。
形式化陈述：comp_units_smul {X Y Z : C} (f : X ⟶ Y) (r : Rˣ) (g : Y ⟶ Z) : f ≫ (r • g)
 = r • f ≫ g
参数：f : X ⟶ Y；r : Rˣ；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Linear.comp_smul`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
-/
lemma comp_units_smul {X Y Z : C} (f : X ⟶ Y) (r : Rˣ) (g : Y ⟶ Z) :
    f ≫ (r • g) = r • f ≫ g := by
  apply Linear.comp_smul

end

section

variable {S : Type w} [CommSemiring S] [Linear S C]

/-- Composition as a bilinear map. -/
@[simps]
/-
**CategoryTheory.Linear.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Linear`。
形式化陈述：comp (X Y Z : C) : (X ⟶ Y) ->ₗ[S] (Y ⟶ Z) ->ₗ[S] X ⟶ Z where toFun f
参数：X Y Z : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition as a bilinear map.
-/
def comp (X Y Z : C) : (X ⟶ Y) →ₗ[S] (Y ⟶ Z) →ₗ[S] X ⟶ Z where
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

