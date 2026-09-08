/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!

# `CartesianMonoidalCategory` for `Over X`

We provide a `CartesianMonoidalCategory (Over X)` instance via pullbacks, and provide simp lemmas
for the induced `MonoidalCategory (Over X)` instance.

-/

public noncomputable section

namespace CategoryTheory.Over

open CategoryTheory.Functor Limits CartesianMonoidalCategory

variable {C : Type*} [Category* C] [HasPullbacks C]

/-- A choice of finite products of `Over X` given by `Limits.pullback`. -/
/-
**CategoryTheory.Over.cartesianMonoidalCategory** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：cartesianMonoidalCategory (X : C) : CartesianMonoidalCategory (Over X)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of finite products of `Over X` given by `Limits.pullback`.
-/
abbrev cartesianMonoidalCategory (X : C) : CartesianMonoidalCategory (Over X) :=
  .ofChosenFiniteProducts
    ⟨asEmptyCone (Over.mk (𝟙 X)), IsTerminal.ofUniqueHom (fun Y ↦ Over.homMk Y.hom)
      fun Y m ↦ Over.OverMorphism.ext (by simpa using m.w)⟩
    fun Y Z ↦ ⟨pullbackConeEquivBinaryFan.functor.obj (pullback.cone Y.hom Z.hom),
    (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor⟩

attribute [local instance] cartesianMonoidalCategory

/-- `Over X` is braided w.r.t. the Cartesian monoidal structure given by `Limits.pullback`. -/
/-
**CategoryTheory.Over.braidedCategory** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Over`。
形式化陈述：braidedCategory (X : C) : BraidedCategory (Over X)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Over X` is braided w.r.t. the Cartesian monoidal structure given by `Limits.pul
lback`.
-/
abbrev braidedCategory (X : C) : BraidedCategory (Over X) :=
  .ofCartesianMonoidalCategory

attribute [local instance] braidedCategory

open MonoidalCategory

variable {X : C}

@[ext]
/-
**CategoryTheory.Over.tensorObj_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Ov
er`。
形式化陈述：tensorObj_ext {R : C} {S T : Over X} (f₁ f₂ : R ⟶ (S otimes T).left) (e₁ :
 f₁ ≫ pullback.fst _ _ = f₂ ≫ pullback.fst _ _) (e₂ : f₁ ≫ pullback.snd _ _ = f₂
 ≫ pullback.snd _ _) : f₁ = f₂
参数：f₁ f₂ : R ⟶ (S otimes T).left；e₁ : f₁ ≫ pullback.fst _ _ = f₂ ≫ pullback.fst 
_ _；e₂ : f₁ ≫ pullback.snd _ _ = f₂ ≫ pullback.snd _ _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
-/
lemma tensorObj_ext {R : C} {S T : Over X} (f₁ f₂ : R ⟶ (S ⊗ T).left)
    (e₁ : f₁ ≫ pullback.fst _ _ = f₂ ≫ pullback.fst _ _)
    (e₂ : f₁ ≫ pullback.snd _ _ = f₂ ≫ pullback.snd _ _) : f₁ = f₂ :=
  pullback.hom_ext e₁ e₂

@[simp]
/-
**CategoryTheory.Over.tensorObj_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.O
ver`。
形式化陈述：tensorObj_left (R S : Over X) : (R otimes S).left = Limits.pullback R.hom 
S.hom
参数：R S : Over X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj_left (R S : Over X) : (R ⊗ S).left = Limits.pullback R.hom S.hom := rfl

@[simp]
/-
**CategoryTheory.Over.tensorObj_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Ov
er`。
形式化陈述：tensorObj_hom (R S : Over X) : (R otimes S).hom = pullback.fst R.hom S.hom
 ≫ R.hom
参数：R S : Over X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj_hom (R S : Over X) : (R ⊗ S).hom = pullback.fst R.hom S.hom ≫ R.hom := rfl

@[simp]
/-
**CategoryTheory.Over.tensorUnit_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Over`。
形式化陈述：tensorUnit_left : (𝟙_ (Over X)).left = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit_left : (𝟙_ (Over X)).left = X := rfl

@[simp]
/-
**CategoryTheory.Over.tensorUnit_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.O
ver`。
形式化陈述：tensorUnit_hom : (𝟙_ (Over X)).hom = 𝟙 X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit_hom : (𝟙_ (Over X)).hom = 𝟙 X := rfl

@[simp]
/-
**CategoryTheory.Over.lift_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：lift_left {R S T : Over X} (f : R ⟶ S) (g : R ⟶ T) : (lift f g).left = pul
lback.lift f.left g.left (f.w.trans g.w.symm)
参数：f : R ⟶ S；g : R ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_left {R S T : Over X} (f : R ⟶ S) (g : R ⟶ T) :
    (lift f g).left = pullback.lift f.left g.left (f.w.trans g.w.symm) := rfl

@[simp]
/-
**CategoryTheory.Over.fst_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：fst_left {R S : Over X} : (fst R S).left = pullback.fst _ _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fst_left {R S : Over X} : (fst R S).left = pullback.fst _ _ := rfl

@[simp]
/-
**CategoryTheory.Over.snd_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：snd_left {R S : Over X} : (snd R S).left = pullback.snd _ _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma snd_left {R S : Over X} : (snd R S).left = pullback.snd _ _ := rfl

@[simp]
/-
**CategoryTheory.Over.toUnit_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over
`。
形式化陈述：toUnit_left {R : Over X} : (toUnit R).left = R.hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toUnit_left {R : Over X} : (toUnit R).left = R.hom := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.associator_hom_left_fst** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Over`。
形式化陈述：associator_hom_left_fst (R S T : Over X) : (α_ R S T).hom.left ≫ pullback.
fst _ (pullback.fst _ _ ≫ _) = pullback.fst _ _ ≫ pullback.fst _ _
参数：R S T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma associator_hom_left_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.fst _ (pullback.fst _ _ ≫ _) =
      pullback.fst _ _ ≫ pullback.fst _ _ :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.associator_hom_left_snd_fst** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：associator_hom_left_snd_fst (R S T : Over X) : (α_ R S T).hom.left ≫ pullb
ack.snd _ (pullback.fst _ _ ≫ _) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullbac
k.snd _ _
参数：R S T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma associator_hom_left_snd_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.snd _ (pullback.fst _ _ ≫ _) ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.associator_hom_left_snd_snd** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：associator_hom_left_snd_snd (R S T : Over X) : (α_ R S T).hom.left ≫ pullb
ack.snd _ (pullback.fst _ _ ≫ _) ≫ pullback.snd _ _ = pullback.snd _ _
参数：R S T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma associator_hom_left_snd_snd (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.snd _ (pullback.fst _ _ ≫ _) ≫ pullback.snd _ _ =
      pullback.snd _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.associator_inv_left_fst_fst** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：associator_inv_left_fst_fst (R S T : Over X) : (α_ R S T).inv.left ≫ pullb
ack.fst (pullback.fst _ _ ≫ _) _ ≫ pullback.fst _ _ = pullback.fst _ _
参数：R S T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma associator_inv_left_fst_fst (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.fst (pullback.fst _ _ ≫ _) _ ≫ pullback.fst _ _ =
      pullback.fst _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.associator_inv_left_fst_snd** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：associator_inv_left_fst_snd (R S T : Over X) : (α_ R S T).inv.left ≫ pullb
ack.fst (pullback.fst _ _ ≫ _) _ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullbac
k.fst _ _
参数：R S T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma associator_inv_left_fst_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.fst (pullback.fst _ _ ≫ _) _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.associator_inv_left_snd** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Over`。
形式化陈述：associator_inv_left_snd (R S T : Over X) : (α_ R S T).inv.left ≫ pullback.
snd (pullback.fst _ _ ≫ _) _ = pullback.snd _ _ ≫ pullback.snd _ _
参数：R S T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma associator_inv_left_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.snd (pullback.fst _ _ ≫ _) _ =
      pullback.snd _ _ ≫ pullback.snd _ _ :=
  limit.lift_π _ _

@[simp]
/-
**CategoryTheory.Over.leftUnitor_hom_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Over`。
形式化陈述：leftUnitor_hom_left (Y : Over X) : (fun_ Y).hom.left = pullback.snd _ _
参数：Y : Over X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_hom_left (Y : Over X) :
    (λ_ Y).hom.left = pullback.snd _ _ := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.leftUnitor_inv_left_fst** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Over`。
形式化陈述：leftUnitor_inv_left_fst (Y : Over X) : (fun_ Y).inv.left ≫ pullback.fst (𝟙
 X) _ = Y.hom
参数：Y : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma leftUnitor_inv_left_fst (Y : Over X) :
    (λ_ Y).inv.left ≫ pullback.fst (𝟙 X) _ = Y.hom :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.leftUnitor_inv_left_snd** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Over`。
形式化陈述：leftUnitor_inv_left_snd (Y : Over X) : (fun_ Y).inv.left ≫ pullback.snd (𝟙
 X) _ = 𝟙 Y.left
参数：Y : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma leftUnitor_inv_left_snd (Y : Over X) :
    (λ_ Y).inv.left ≫ pullback.snd (𝟙 X) _ = 𝟙 Y.left :=
  limit.lift_π _ _

@[simp]
/-
**CategoryTheory.Over.rightUnitor_hom_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Over`。
形式化陈述：rightUnitor_hom_left (Y : Over X) : (ρ_ Y).hom.left = pullback.fst _ (𝟙 X)
参数：Y : Over X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_hom_left (Y : Over X) :
    (ρ_ Y).hom.left = pullback.fst _ (𝟙 X) := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.rightUnitor_inv_left_fst** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Over`。
形式化陈述：rightUnitor_inv_left_fst (Y : Over X) : (ρ_ Y).inv.left ≫ pullback.fst _ (
𝟙 X) = 𝟙 _
参数：Y : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma rightUnitor_inv_left_fst (Y : Over X) :
    (ρ_ Y).inv.left ≫ pullback.fst _ (𝟙 X) = 𝟙 _ :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.rightUnitor_inv_left_snd** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Over`。
形式化陈述：rightUnitor_inv_left_snd (Y : Over X) : (ρ_ Y).inv.left ≫ pullback.snd _ (
𝟙 X) = Y.hom
参数：Y : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma rightUnitor_inv_left_snd (Y : Over X) :
    (ρ_ Y).inv.left ≫ pullback.snd _ (𝟙 X) = Y.hom :=
  limit.lift_π _ _
/-
**CategoryTheory.Over.whiskerLeft_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Over`。
形式化陈述：whiskerLeft_left {R S T : Over X} (f : S ⟶ T) : (R ◁ f).left = pullback.ma
p _ _ _ _ (𝟙 _) f.left (𝟙 _) (by simp) (by simp)
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_left {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left = pullback.map _ _ _ _ (𝟙 _) f.left (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.whiskerLeft_left_fst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Over`。
形式化陈述：whiskerLeft_left_fst {R S T : Over X} (f : S ⟶ T) : (R ◁ f).left ≫ pullbac
k.fst _ _ = pullback.fst _ _
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma whiskerLeft_left_fst {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (limit.lift_π _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.whiskerLeft_left_snd** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Over`。
形式化陈述：whiskerLeft_left_snd {R S T : Over X} (f : S ⟶ T) : (R ◁ f).left ≫ pullbac
k.snd _ _ = pullback.snd _ _ ≫ f.left
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma whiskerLeft_left_snd {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ pullback.snd _ _ = pullback.snd _ _ ≫ f.left :=
  limit.lift_π _ _
/-
**CategoryTheory.Over.whiskerRight_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Over`。
形式化陈述：whiskerRight_left {R S T : Over X} (f : S ⟶ T) : (f ▷ R).left = pullback.m
ap _ _ _ _ f.left (𝟙 _) (𝟙 _) (by simp) (by simp)
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRight_left {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left = pullback.map _ _ _ _ f.left (𝟙 _) (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.whiskerRight_left_fst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Over`。
形式化陈述：whiskerRight_left_fst {R S T : Over X} (f : S ⟶ T) : (f ▷ R).left ≫ pullba
ck.fst _ _ = pullback.fst _ _ ≫ f.left
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma whiskerRight_left_fst {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.left :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.whiskerRight_left_snd** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Over`。
形式化陈述：whiskerRight_left_snd {R S T : Over X} (f : S ⟶ T) : (f ▷ R).left ≫ pullba
ck.snd _ _ = pullback.snd _ _
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma whiskerRight_left_snd {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (limit.lift_π _ _).trans (Category.comp_id _)
/-
**CategoryTheory.Over.tensorHom_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.O
ver`。
形式化陈述：tensorHom_left {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) : (f otimesₘ g).
left = pullback.map _ _ _ _ f.left g.left (𝟙 _) (by simp) (by simp)
参数：f : R ⟶ S；g : T ⟶ U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorHom_left {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ₘ g).left = pullback.map _ _ _ _ f.left g.left (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.tensorHom_left_fst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Over`。
形式化陈述：tensorHom_left_fst {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X) (f :
 R ⟶ mk fS) (g : T ⟶ mk fU) : (f otimesₘ g).left ≫ pullback.fst fS fU = pullback
.fst R.hom T.hom ≫ f.left
参数：fS : S ⟶ X；fU : U ⟶ X；f : R ⟶ mk fS；g : T ⟶ mk fU。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma tensorHom_left_fst {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X)
    (f : R ⟶ mk fS) (g : T ⟶ mk fU) :
    (f ⊗ₘ g).left ≫ pullback.fst fS fU = pullback.fst R.hom T.hom ≫ f.left :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.tensorHom_left_snd** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Over`。
形式化陈述：tensorHom_left_snd {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X) (f :
 R ⟶ mk fS) (g : T ⟶ mk fU) : (f otimesₘ g).left ≫ pullback.snd fS fU = pullback
.snd R.hom T.hom ≫ g.left
参数：fS : S ⟶ X；fU : U ⟶ X；f : R ⟶ mk fS；g : T ⟶ mk fU。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma tensorHom_left_snd {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X)
    (f : R ⟶ mk fS) (g : T ⟶ mk fU) :
    (f ⊗ₘ g).left ≫ pullback.snd fS fU = pullback.snd R.hom T.hom ≫ g.left :=
  limit.lift_π _ _

@[simp]
/-
**CategoryTheory.Over.braiding_hom_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Over`。
形式化陈述：braiding_hom_left {R S : Over X} : (β_ R S).hom.left = (pullbackSymmetry _
 _).hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma braiding_hom_left {R S : Over X} :
    (β_ R S).hom.left = (pullbackSymmetry _ _).hom := rfl

@[simp]
/-
**CategoryTheory.Over.braiding_inv_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Over`。
形式化陈述：braiding_inv_left {R S : Over X} : (β_ R S).inv.left = (pullbackSymmetry _
 _).hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma braiding_inv_left {R S : Over X} :
    (β_ R S).inv.left = (pullbackSymmetry _ _).hom := rfl

variable {A B R S Y Z : C} {f : R ⟶ X} {g : S ⟶ X}
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Over.pullback f).Braided := .ofChosenFiniteProducts _

@[simp]
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma η_pullback_left : (OplaxMonoidal.η (Over.pullback f)).left = (pullback.snd (𝟙 _) f) := rfl

@[simp]
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ε_pullback_left : (LaxMonoidal.ε (Over.pullback f)).left = inv (pullback.snd (𝟙 _) f) := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← η_pullback_left, ← Over.comp_left, Monoidal.η_ε, Over.id_left]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_pullback_left_fst_fst (R S : Over X) :
    (LaxMonoidal.μ (Over.pullback f) R S).left ≫
      pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  rw [Monoidal.μ_of_cartesianMonoidalCategory,
    ← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left, ← Over.comp_left_assoc,
    Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison, fst]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_pullback_left_fst_snd (R S : Over X) :
    (LaxMonoidal.μ (Over.pullback f) R S).left ≫
      pullback.fst _ _ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst _ _ := by
  rw [Monoidal.μ_of_cartesianMonoidalCategory,
    ← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left,
    ← Over.comp_left_assoc, Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison, snd]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_pullback_left_snd (R S : Over X) :
    (LaxMonoidal.μ (Over.pullback f) R S).left ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [Monoidal.μ_of_cartesianMonoidalCategory,
    ← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left,
    ← Over.comp_left_assoc, Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison]

@[simp]
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_pullback_left_fst_fst' (g₁ : Y ⟶ X) (g₂ : Z ⟶ X) :
    (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).left ≫
      pullback.fst (pullback.fst g₁ g₂ ≫ g₁) f ≫ pullback.fst g₁ g₂ =
        pullback.fst _ _ ≫ pullback.fst _ _ :=
  μ_pullback_left_fst_fst ..

@[simp]
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_pullback_left_fst_snd' (g₁ : Y ⟶ X) (g₂ : Z ⟶ X) :
    (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).left ≫
      pullback.fst (pullback.fst g₁ g₂ ≫ g₁) f ≫ pullback.snd g₁ g₂ =
        pullback.snd _ _ ≫ pullback.fst _ _ :=
  μ_pullback_left_fst_snd ..

@[simp]
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_pullback_left_snd' (g₁ : Y ⟶ X) (g₂ : Z ⟶ X) :
    (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).left ≫
      pullback.snd (pullback.fst g₁ g₂ ≫ g₁) f =
        pullback.snd _ _ ≫ pullback.snd _ _ := μ_pullback_left_snd ..

@[simp]
/-
**CategoryTheory.Over.preservesTerminalIso_pullback** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Over`。
形式化陈述：preservesTerminalIso_pullback (f : R ⟶ S) : preservesTerminalIso (Over.pul
lback f) = Over.isoMk (asIso (pullback.snd (𝟙 _) f)) (by simp)
参数：f : R ⟶ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
-/
lemma preservesTerminalIso_pullback (f : R ⟶ S) :
    preservesTerminalIso (Over.pullback f) =
      Over.isoMk (asIso (pullback.snd (𝟙 _) f)) (by simp) := by
  ext1; exact toUnit_unique _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Over.prodComparisonIso_pullback_inv_left_fst_fst** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：prodComparisonIso_pullback_inv_left_fst_fst (f : X ⟶ Y) (A B : Over Y) : (
prodComparisonIso (Over.pullback f) A B).inv.left ≫ pullback.fst (pullback.fst A
.hom B.hom ≫ A.hom) f ≫ pullback.fst _ _ = pullback.fst (pullback.snd A.hom f) (
pullback.snd B.hom f) ≫ pullback.fst _ _
参数：f : X ⟶ Y；A B : Over Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Comma.instIsIsoLeft`：∀ {A : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 B]   {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Over.hom_left_inv_left_assoc`：∀ {T : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Over X} (e : f ≅ 
g) {Z : T}   (h : f.left ⟶ Z),   …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Over.homMk_left`：∀ {T : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} (f : U.left ⟶ V.left) 
  (w : autoParam (Ca…
· 使用定理 `CategoryTheory.Over.Hom.w`：∀ {T : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Over X} (φ : f ⟶ g),   CategoryTheo
ry.CategoryStru…
· 使用定理 `CategoryTheory.Over.pullback_map_left`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.
HasPullbacksAlong f] (g : C…
· 使用定理 `CategoryTheory.Limits.pullback.lift.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1
 : CategoryTheory.Limits.HasPullback…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodComparisonIso_pullback_inv_left_fst_fst (f : X ⟶ Y) (A B : Over Y) :
    (prodComparisonIso (Over.pullback f) A B).inv.left ≫
      pullback.fst (pullback.fst A.hom B.hom ≫ A.hom) f ≫ pullback.fst _ _ =
        pullback.fst (pullback.snd A.hom f) (pullback.snd B.hom f) ≫ pullback.fst _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) A B).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison, fst]

@[simp]
/-
**CategoryTheory.Over.prodComparisonIso_pullback_Spec_inv_left_fst_fst'** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：prodComparisonIso_pullback_Spec_inv_left_fst_fst' (f : X ⟶ Y) (gA : A ⟶ Y)
 (gB : B ⟶ Y) : (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left
 ≫ pullback.fst (pullback.fst gA gB ≫ gA) f ≫ pullback.fst _ _ = pullback.fst (p
ullback.snd gA f) (pullback.snd gB f) ≫ pullback.fst _ _
参数：f : X ⟶ Y；gA : A ⟶ Y；gB : B ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Over.prodComparisonIso_pullback_inv_left_fst_fst`：prodCom
parisonIso_pullback_inv_left_fst_fst (f : X ⟶ Y) (A B : Over Y) : (prodCompariso
nIso (Over.pullback f) A B).inv.left ≫ pullback.fst (…
-/
lemma prodComparisonIso_pullback_Spec_inv_left_fst_fst' (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y) :
    (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫
      pullback.fst (pullback.fst gA gB ≫ gA) f ≫ pullback.fst _ _ =
        pullback.fst (pullback.snd gA f) (pullback.snd gB f) ≫ pullback.fst _ _ :=
  prodComparisonIso_pullback_inv_left_fst_fst ..

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Over.prodComparisonIso_pullback_inv_left_fst_snd'** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：prodComparisonIso_pullback_inv_left_fst_snd' (f : X ⟶ Y) (gA : A ⟶ Y) (gB 
: B ⟶ Y) : (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫ pu
llback.fst (pullback.fst gA gB ≫ gA) f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ p
ullback.fst _ _
参数：f : X ⟶ Y；gA : A ⟶ Y；gB : B ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Comma.instIsIsoLeft`：∀ {A : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 B]   {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Over.hom_left_inv_left_assoc`：∀ {T : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Over X} (e : f ≅ 
g) {Z : T}   (h : f.left ⟶ Z),   …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Over.homMk_left`：∀ {T : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} (f : U.left ⟶ V.left) 
  (w : autoParam (Ca…
· 使用定理 `CategoryTheory.Over.Hom.w`：∀ {T : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Over X} (φ : f ⟶ g),   CategoryTheo
ry.CategoryStru…
· 使用定理 `CategoryTheory.Over.pullback_map_left`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.
HasPullbacksAlong f] (g : C…
· 使用定理 `CategoryTheory.Limits.pullback.lift.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1
 : CategoryTheory.Limits.HasPullback…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodComparisonIso_pullback_inv_left_fst_snd' (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y) :
    (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫
      pullback.fst (pullback.fst gA gB ≫ gA) f ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ pullback.fst _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) _ _).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison, snd]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Over.prodComparisonIso_pullback_inv_left_snd'** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：prodComparisonIso_pullback_inv_left_snd' (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B 
⟶ Y) : (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫ pullba
ck.snd (pullback.fst gA gB ≫ gA) f = pullback.snd _ _ ≫ pullback.snd _ _
参数：f : X ⟶ Y；gA : A ⟶ Y；gB : B ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Comma.instIsIsoLeft`：∀ {A : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 B]   {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Over.hom_left_inv_left_assoc`：∀ {T : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Over X} (e : f ≅ 
g) {Z : T}   (h : f.left ⟶ Z),   …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Over.Hom.w`：∀ {T : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Over X} (φ : f ⟶ g),   CategoryTheo
ry.CategoryStru…
· 使用定理 `CategoryTheory.Over.pullback_map_left`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.
HasPullbacksAlong f] (g : C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullback.lift.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1
 : CategoryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodComparisonIso_pullback_inv_left_snd' (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y) :
    (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫
      pullback.snd (pullback.fst gA gB ≫ gA) f = pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) _ _).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison]

/-- The pullback of a monoid object is a monoid object. -/
@[simps! -isSimp mul one]
/-
**CategoryTheory.Over.monObjMkPullbackSnd** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Over`。
形式化陈述：monObjMkPullbackSnd [MonObj (Over.mk f)] : MonObj (Over.mk <| pullback.snd
 f g)
参数：Over.mk f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a monoid object is a monoid object.
-/
abbrev monObjMkPullbackSnd [MonObj (Over.mk f)] : MonObj (Over.mk <| pullback.snd f g) :=
  ((Over.pullback g).mapMon.obj <| .mk <| .mk f).mon

attribute [local instance] monObjMkPullbackSnd
/-
**CategoryTheory.Over.isCommMonObj_mk_pullbackSnd** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：isCommMonObj_mk_pullbackSnd [MonObj (Over.mk f)] [IsCommMonObj (Over.mk f)
] : IsCommMonObj (Over.mk <| pullback.snd f g)
参数：Over.mk f；Over.mk f。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommMon.comm`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]   [inst_2 : Catego
ryTheory.BraidedC…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance isCommMonObj_mk_pullbackSnd [MonObj (Over.mk f)] [IsCommMonObj (Over.mk f)] :
    IsCommMonObj (Over.mk <| pullback.snd f g) :=
  ((Over.pullback g).mapCommMon.obj <| .mk <| .mk f).comm

/-- The pullback of a monoid object is a monoid object. -/
@[simps! -isSimp mul one]
/-
**CategoryTheory.Over.grpObjMkPullbackSnd** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Over`。
形式化陈述：grpObjMkPullbackSnd [GrpObj (Over.mk f)] : GrpObj (Over.mk (pullback.snd f
 g))
参数：Over.mk f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a monoid object is a monoid object.
-/
abbrev grpObjMkPullbackSnd [GrpObj (Over.mk f)] : GrpObj (Over.mk (pullback.snd f g)) :=
  ((Over.pullback g).mapGrp.obj <| .mk <| .mk f).grp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] monObjMkPullbackSnd_one in
/-
**CategoryTheory.Over.isMonHom_pullbackFst_id_right** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Over`。
形式化陈述：isMonHom_pullbackFst_id_right [MonObj (Over.mk f)] : IsMonHom Over.homMk (
U
参数：Over.mk f。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Over.ε_pullback_left`：ε_pullback_left : (LaxMonoidal.ε (O
ver.pullback f)).left = inv (pullback.snd (𝟙 _) f)
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullback_inv_snd_fst_of_left_isIso_assoc`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y 
⟶ Z)   [inst_1 : CategoryTheory.IsIso f] {Z_1 : C} (…
· 使用定理 `CategoryTheory.IsIso.inv_id`：inv_id : inv (𝟙 X) = 𝟙 X
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用引理 `CategoryTheory.Over.μ_pullback_left_fst_fst'`：μ_pullback_left_fst_fst' (
g₁ : Y ⟶ X) (g₂ : Z ⟶ X) : (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).l
eft ≫ pullback.fst (pullback.fst g…
· 使用引理 `CategoryTheory.Over.tensorHom_left_fst`：tensorHom_left_fst {S U : C} {R 
T : Over X} (fS : S ⟶ X) (fU : U ⟶ X) (f : R ⟶ mk fS) (g : T ⟶ mk fU) : (f otime
sₘ g).left ≫ pullback.fst fS…
· 使用引理 `CategoryTheory.Over.μ_pullback_left_fst_snd'`：μ_pullback_left_fst_snd' (
g₁ : Y ⟶ X) (g₂ : Z ⟶ X) : (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).l
eft ≫ pullback.fst (pullback.fst g…
· 使用引理 `CategoryTheory.Over.tensorHom_left_snd`：tensorHom_left_snd {S U : C} {R 
T : Over X} (fS : S ⟶ X) (fU : U ⟶ X) (f : R ⟶ mk fS) (g : T ⟶ mk fU) : (f otime
sₘ g).left ≫ pullback.snd fS…
-/
instance isMonHom_pullbackFst_id_right [MonObj (Over.mk f)] :
    IsMonHom <| Over.homMk (U := Over.mk <| pullback.snd f (𝟙 X)) (V := Over.mk f)
      (pullback.fst f (𝟙 X)) (pullback.condition.trans <| by simp) where
  mul_hom := by
    ext
    dsimp [monObjMkPullbackSnd_mul]
    simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    simp only [← Category.assoc]
    congr 1
    ext <;> simp

end CategoryTheory.Over

