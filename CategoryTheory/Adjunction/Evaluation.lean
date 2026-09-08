/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!

# Adjunctions involving evaluation

We show that evaluation of functors has adjoints, given the existence of (co)products.

-/

@[expose] public section


namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

noncomputable section

section

variable [∀ a b : C, HasCoproductsOfShape (a ⟶ b) D]

set_option backward.isDefEq.respectTransparency false in
/-- The left adjoint of evaluation. -/
@[simps]
/-
**CategoryTheory.evaluationLeftAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：evaluationLeftAdjoint (c : C) : D ⥤ C ⥤ D where obj d
参数：c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left adjoint of evaluation.
-/
def evaluationLeftAdjoint (c : C) : D ⥤ C ⥤ D where
  obj d :=
    { obj := fun t => ∐ fun _ : c ⟶ t => d
      map := fun f => Sigma.desc fun g => (Sigma.ι fun _ => d) <| g ≫ f }
  map {_ d₂} f :=
    { app := fun _ => Sigma.desc fun h => f ≫ Sigma.ι (fun _ => d₂) h
      naturality := by
        intros
        dsimp
        ext
        simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction showing that evaluation is a right adjoint. -/
@[simps! unit_app counit_app_app]
/-
**CategoryTheory.evaluationAdjunctionRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：evaluationAdjunctionRight (c : C) : evaluationLeftAdjoint D c ⊣ (evaluatio
n _ _).obj c
参数：c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction showing that evaluation is a right adjoint.
-/
def evaluationAdjunctionRight (c : C) : evaluationLeftAdjoint D c ⊣ (evaluation _ _).obj c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun d F =>
        { toFun := fun f => Sigma.ι (fun _ => d) (𝟙 _) ≫ f.app c
          invFun := fun f => { app := fun _ => Sigma.desc fun h => f ≫ F.map h }
          left_inv := by
            intro f
            ext x
            dsimp
            ext g
            simp only [colimit.ι_desc, Cofan.mk_ι_app, Category.assoc, ← f.naturality,
              evaluationLeftAdjoint_obj_map, colimit.ι_desc_assoc,
              Discrete.functor_obj, Cofan.mk_pt, Category.id_comp]
          right_inv := fun f => by simp } }
/-
**CategoryTheory.evaluationIsRightAdjoint** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory`。
形式化陈述：evaluationIsRightAdjoint (c : C) : ((evaluation _ D).obj c).IsRightAdjoint
参数：c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance evaluationIsRightAdjoint (c : C) : ((evaluation _ D).obj c).IsRightAdjoint :=
  ⟨_, ⟨evaluationAdjunctionRight _ _⟩⟩

/-- See also the file `Mathlib/CategoryTheory/Limits/FunctorCategory/EpiMono.lean`
for a similar result under a `HasPullbacks` assumption. -/
/-
**CategoryTheory.NatTrans.mono_iff_mono_app'** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.NatTrans`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [∀ (a b : C), CategoryTheory.Lim
its.HasCoproductsOfShape (a ⟶ b) D] {F G : CategoryTheory.Functor C D} (η : F ⟶ 
G),   CategoryTheory.Mono η ↔ ∀ (c : C), CategoryTheory.Mono (η.app c)
参数：D : Type u₂；a b : C；a ⟶ b；η : F ⟶ G；c : C；η.app c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.preservesMonomorphisms_of_isRightAdjoint`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.NatTrans.mono_of_mono_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…

--- 原说明 ---
See also the file `Mathlib/CategoryTheory/Limits/FunctorCategory/EpiMono.lean`
for a similar result under a `HasPullbacks` assumption.
-/
theorem NatTrans.mono_iff_mono_app' {F G : C ⥤ D} (η : F ⟶ G) : Mono η ↔ ∀ c, Mono (η.app c) := by
  constructor
  · intro h c
    exact (inferInstance : Mono (((evaluation _ _).obj c).map η))
  · intro _
    apply NatTrans.mono_of_mono_app

end

section

variable [∀ a b : C, HasProductsOfShape (a ⟶ b) D]

set_option backward.isDefEq.respectTransparency false in
/-- The right adjoint of evaluation. -/
@[simps]
/-
**CategoryTheory.evaluationRightAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：evaluationRightAdjoint (c : C) : D ⥤ C ⥤ D where obj d
参数：c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right adjoint of evaluation.
-/
def evaluationRightAdjoint (c : C) : D ⥤ C ⥤ D where
  obj d :=
    { obj := fun t => ∏ᶜ fun _ : t ⟶ c => d
      map := fun f => Pi.lift fun g => Pi.π _ <| f ≫ g }
  map f := { app := fun _ => Pi.lift fun g => Pi.π _ g ≫ f }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction showing that evaluation is a left adjoint. -/
@[simps! unit_app_app counit_app]
/-
**CategoryTheory.evaluationAdjunctionLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory`。
形式化陈述：evaluationAdjunctionLeft (c : C) : (evaluation _ _).obj c ⊣ evaluationRigh
tAdjoint D c
参数：c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction showing that evaluation is a left adjoint.
-/
def evaluationAdjunctionLeft (c : C) : (evaluation _ _).obj c ⊣ evaluationRightAdjoint D c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F d =>
        { toFun := fun f => { app := fun _ => Pi.lift fun g => F.map g ≫ f }
          invFun := fun f => f.app _ ≫ Pi.π _ (𝟙 _)
          left_inv := fun f => by simp
          right_inv := by
            intro f
            ext x
            dsimp
            ext g
            simp only [NatTrans.naturality_assoc,
              evaluationRightAdjoint_obj_obj, evaluationRightAdjoint_obj_map, limit.lift_π,
              Fan.mk_pt, Fan.mk_π_app, Category.comp_id] } }
/-
**CategoryTheory.evaluationIsLeftAdjoint** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry`。
形式化陈述：evaluationIsLeftAdjoint (c : C) : ((evaluation _ D).obj c).IsLeftAdjoint
参数：c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance evaluationIsLeftAdjoint (c : C) : ((evaluation _ D).obj c).IsLeftAdjoint :=
  ⟨_, ⟨evaluationAdjunctionLeft _ _⟩⟩

/-- See also the file `Mathlib/CategoryTheory/Limits/FunctorCategory/EpiMono.lean`
for a similar result under a `HasPushouts` assumption. -/
/-
**CategoryTheory.NatTrans.epi_iff_epi_app'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.NatTrans`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [∀ (a b : C), CategoryTheory.Lim
its.HasProductsOfShape (a ⟶ b) D] {F G : CategoryTheory.Functor C D} (η : F ⟶ G)
,   CategoryTheory.Epi η ↔ ∀ (c : C), CategoryTheory.Epi (η.app c)
参数：D : Type u₂；a b : C；a ⟶ b；η : F ⟶ G；c : C；η.app c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_of_isLeftAdjoint`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.NatTrans.epi_of_epi_app`：epi_of_epi_app (α : F ⟶ G) [fora
ll X : C, Epi (α.app X)] : Epi α

--- 原说明 ---
See also the file `Mathlib/CategoryTheory/Limits/FunctorCategory/EpiMono.lean`
for a similar result under a `HasPushouts` assumption.
-/
theorem NatTrans.epi_iff_epi_app' {F G : C ⥤ D} (η : F ⟶ G) : Epi η ↔ ∀ c, Epi (η.app c) := by
  constructor
  · intro h c
    exact (inferInstance : Epi (((evaluation _ _).obj c).map η))
  · intros
    apply NatTrans.epi_of_epi_app

end

end

end CategoryTheory

