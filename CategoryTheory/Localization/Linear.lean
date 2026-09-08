/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.HasLocalization
public import Mathlib.CategoryTheory.Center.Localization
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Localization of linear categories

If `L : C ⥤ D` is an additive localization functor between preadditive categories,
and `C` is `R`-linear, we show that `D` can also be equipped with an `R`-linear
structure such that `L` is an `R`-linear functor.

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Localization

variable (R : Type w) [Ring R] {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  [L.Additive] [Linear R C]

/-- If `L : C ⥤ D` is a localization functor and `C` is `R`-linear, then `D` is
`R`-linear if we already know that `D` is preadditive and `L` is additive. -/
@[instance_reducible]
/-
**CategoryTheory.Localization.linear** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
ocalization`。
形式化陈述：linear : Linear R D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L : C ⥤ D` is a localization functor and `C` is `R`-linear, then `D` is
`R`-linear if we already know that `D` is preadditive and `L` is additive.
-/
noncomputable def linear : Linear R D := Linear.ofRingMorphism
  ((CatCenter.localizationRingHom L W).comp (Linear.toCatCenter R C))
/-
**CategoryTheory.Localization.functor_linear** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Localization`。
形式化陈述：functor_linear : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.CatCenter.localization_app`：localization_app (X : C) : (r
.localization L W).app (L.obj X) = L.map (r.app X)
· 使用定理 `CategoryTheory.Linear.toCatCenter_apply_app`：∀ (R : Type w) [inst : Ring
 R] (C : Type u) [inst_1 : CategoryTheory.Category.{v, u} C]   [inst_2 : Categor
yTheory.Preadditive C] [inst_3 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functor_linear :
    letI := linear R L W
    Functor.Linear R L := by
  let := linear R L W
  constructor
  intro X Y f r
  change L.map (r • f) = ((Linear.toCatCenter R C r).localization L W).app (L.obj X) ≫ L.map f
  simp [← L.map_comp]

section

variable [Preadditive W.Localization] [W.Q.Additive]

/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Linear R W.Localization := Localization.linear R W.Q W
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Functor.Linear R W.Q := Localization.functor_linear R W.Q W

end

section

variable [W.HasLocalization] [Preadditive W.Localization'] [W.Q'.Additive]

/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Linear R W.Localization' := Localization.linear R W.Q' W
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Functor.Linear R W.Q' := Localization.functor_linear R W.Q' W

end

section

variable {E : Type*} [Category* E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [Preadditive E]
  (R : Type*) [Ring R]
  [Linear R C] [Linear R D] [Linear R E] [L.Linear R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.functor_linear_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Localization`。
形式化陈述：functor_linear_iff (F : C ⥤ E) (G : D ⥤ E) [Lifting L W F G] : F.Linear R 
↔ G.Linear R
参数：F : C ⥤ E；G : D ⥤ E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.linear_of_iso`：linear_of_iso {G : C ⥤ D} (e : F ≅
 G) [F.Linear R] : G.Linear R
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.linear_iff`：∀ (R : Type u_1) [inst : Semiring R] 
{C : Type u_2} {D : Type u_3} [inst_1 : CategoryTheory.Category.{v_1, u_2} C]   
[inst_2 : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Linear.comp_smul`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_smul`：map_smul {X Y : C} (r : R) (f : X ⟶ Y) 
: F.map (r • f) = r • F.map f
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `CategoryTheory.Functor.instLinearComp`：∀ {R : Type u_1} [inst : Semiring
 R] {C : Type u_2} {D : Type u_3} [inst_1 : CategoryTheory.Category.{v_1, u_2} C
]   [inst_2 : CategoryTheor…
-/
lemma functor_linear_iff (F : C ⥤ E) (G : D ⥤ E) [Lifting L W F G] :
    F.Linear R ↔ G.Linear R := by
  constructor
  · intro
    have : (L ⋙ G).Linear R := Functor.linear_of_iso _ (Lifting.iso L W F G).symm
    have := Localization.essSurj L W
    rw [Functor.linear_iff]
    intro X r
    have e := L.objObjPreimageIso X
    have : r • 𝟙 X = e.inv ≫ (r • 𝟙 _) ≫ e.hom := by simp
    rw [this, G.map_comp, G.map_comp, ← L.map_id, ← L.map_smul, ← Functor.comp_map,
      (L ⋙ G).map_smul, Functor.map_id, Linear.smul_comp, Linear.comp_smul]
    dsimp
    rw [Category.id_comp, ← G.map_comp, e.inv_hom_id, G.map_id]
  · intro
    exact Functor.linear_of_iso _ (Lifting.iso L W F G)

end

end Localization

end CategoryTheory

