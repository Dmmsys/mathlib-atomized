/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.GradedObject.Bifunctor

/-!
# The action of a bifunctor on homological complexes

Given a bifunctor `F : C₁ ⥤ C₂ ⥤ D` and complexes shapes `c₁ : ComplexShape I₁` and
`c₂ : ComplexShape I₂`, we define a bifunctor `mapBifunctorHomologicalComplex F c₁ c₂`
of type `HomologicalComplex C₁ c₁ ⥤ HomologicalComplex C₂ c₂ ⥤ HomologicalComplex₂ D c₁ c₂`.

Then, when `K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂` and
`c : ComplexShape J` are such that we have `TotalComplexShape c₁ c₂ c`, we introduce
a typeclass `HasMapBifunctor K₁ K₂ F c` which allows to define
`mapBifunctor K₁ K₂ F c : HomologicalComplex D c` as the total complex of the
bicomplex `(((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂)`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Limits

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

namespace CategoryTheory

namespace Functor

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms D]
  (F : C₁ ⥤ C₂ ⥤ D) {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {c₁} in
/-- Auxiliary definition for `mapBifunctorHomologicalComplex`. -/
@[simps!]
/-
**CategoryTheory.Functor.mapBifunctorHomologicalComplexObj** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：mapBifunctorHomologicalComplexObj (K₁ : HomologicalComplex C₁ c₁) : Homolo
gicalComplex C₂ c₂ ⥤ HomologicalComplex₂ D c₁ c₂ where obj K₂
参数：K₁ : HomologicalComplex C₁ c₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `mapBifunctorHomologicalComplex`.
-/
def mapBifunctorHomologicalComplexObj (K₁ : HomologicalComplex C₁ c₁) :
    HomologicalComplex C₂ c₂ ⥤ HomologicalComplex₂ D c₁ c₂ where
  obj K₂ := HomologicalComplex₂.ofGradedObject c₁ c₂
      (((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).obj K₂.X)
      (fun i₁ i₁' i₂ => (F.map (K₁.d i₁ i₁')).app (K₂.X i₂))
      (fun i₁ i₂ i₂' => (F.obj (K₁.X i₁)).map (K₂.d i₂ i₂'))
      (fun i₁ i₁' h₁ i₂ => by
        dsimp
        rw [K₁.shape _ _ h₁, Functor.map_zero, zero_app])
      (fun i₁ i₂ i₂' h₂ => by
        dsimp
        rw [K₂.shape _ _ h₂, Functor.map_zero])
      (fun i₁ i₁' i₁'' i₂ => by
        dsimp
        rw [← NatTrans.comp_app, ← Functor.map_comp, HomologicalComplex.d_comp_d,
          Functor.map_zero, zero_app])
      (fun i₁ i₂ i₂' i₂'' => by
        dsimp
        rw [← Functor.map_comp, HomologicalComplex.d_comp_d, Functor.map_zero])
      (fun i₁ i₁' i₂ i₂' => by
        dsimp
        rw [NatTrans.naturality])
  map {K₂ K₂' φ} := HomologicalComplex₂.homMk
      (((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).map φ.f)
        (by dsimp; intros; rw [NatTrans.naturality]) (by
          dsimp
          intros
          simp only [← Functor.map_comp, φ.comm])
  map_id K₂ := by dsimp; ext; dsimp; rw [Functor.map_id]
  map_comp f g := by dsimp; ext; dsimp; rw [Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a functor `F : C₁ ⥤ C₂ ⥤ D`, this is the bifunctor which sends
`K₁ : HomologicalComplex C₁ c₁` and `K₂ : HomologicalComplex C₂ c₂` to the bicomplex
which is degree `(i₁, i₂)` consists of `(F.obj (K₁.X i₁)).obj (K₂.X i₂)`. -/
@[simps! obj_obj_X_X obj_obj_X_d obj_obj_d_f obj_map_f_f map_app_f_f]
/-
**CategoryTheory.Functor.mapBifunctorHomologicalComplex** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：mapBifunctorHomologicalComplex : HomologicalComplex C₁ c₁ ⥤ HomologicalCom
plex C₂ c₂ ⥤ HomologicalComplex₂ D c₁ c₂ where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C₁ ⥤ C₂ ⥤ D`, this is the bifunctor which sends
`K₁ : HomologicalComplex C₁ c₁` and `K₂ : HomologicalComplex C₂ c₂` to the bicom
plex
which is degree `(i₁, i₂)` consists of `(F.obj (K₁.X i₁)).obj (K₂.X i₂)`.
-/
def mapBifunctorHomologicalComplex :
    HomologicalComplex C₁ c₁ ⥤ HomologicalComplex C₂ c₂ ⥤ HomologicalComplex₂ D c₁ c₂ where
  obj := mapBifunctorHomologicalComplexObj F c₂
  map {K₁ K₁'} f :=
    { app := fun K₂ => HomologicalComplex₂.homMk
        (((GradedObject.mapBifunctor F I₁ I₂).map f.f).app K₂.X) (by
          intros
          dsimp
          simp only [← NatTrans.comp_app, ← F.map_comp, f.comm]) (by simp) }

variable {c₁ c₂}

@[simp]
/-
**CategoryTheory.Functor.mapBifunctorHomologicalComplex_obj_obj_toGradedObject**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mapBifunctorHomologicalComplex_obj_obj_toGradedObject (K₁ : HomologicalCom
plex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂) : (((mapBifunctorHomologicalComplex 
F c₁ c₂).obj K₁).obj K₂).toGradedObject = ((GradedObject.mapBifunctor F I₁ I₂).o
bj K₁.X).obj K₂.X
参数：K₁ : HomologicalComplex C₁ c₁；K₂ : HomologicalComplex C₂ c₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapBifunctorHomologicalComplex_obj_obj_toGradedObject
    (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂) :
    (((mapBifunctorHomologicalComplex F c₁ c₂).obj K₁).obj K₂).toGradedObject =
      ((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).obj K₂.X := rfl

end Functor

end CategoryTheory

namespace HomologicalComplex

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

/-- The condition that `((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂` has
a total complex. -/
/-
**HomologicalComplex.HasMapBifunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalCom
plex`。
形式化陈述：HasMapBifunctor
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that `((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂` ha
s
a total complex.
-/
abbrev HasMapBifunctor := (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).HasTotal c

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

/-- Given `K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂`,
a bifunctor `F : C₁ ⥤ C₂ ⥤ D` and a complex shape `ComplexShape J` such that we have
`[TotalComplexShape c₁ c₂ c]`, this `mapBifunctor K₁ K₂ F c : HomologicalComplex D c`
is the total complex of the bicomplex obtained by applying `F` to `K₁` and `K₂`. -/
/-
**HomologicalComplex.mapBifunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComple
x`。
形式化陈述：mapBifunctor : HomologicalComplex D c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂`,
a bifunctor `F : C₁ ⥤ C₂ ⥤ D` and a complex shape `ComplexShape J` such that we 
have
`[TotalComplexShape c₁ c₂ c]`, this `mapBifunctor K₁ K₂ F c : HomologicalComplex
 D c`
is the total complex of the bicomplex obtained by applying `F` to `K₁` and `K₂`.
-/
noncomputable abbrev mapBifunctor : HomologicalComplex D c :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).total c

/-- The inclusion of a summand of `(mapBifunctor K₁ K₂ F c).X j`. -/
/-
**HomologicalComplex.** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a summand of `(mapBifunctor K₁ K₂ F c).X j`.
-/
noncomputable abbrev ιMapBifunctor
    (i₁ : I₁) (i₂ : I₂) (j : J) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (mapBifunctor K₁ K₂ F c).X j :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).ιTotal c i₁ i₂ j h

/-- The inclusion of a summand of `(mapBifunctor K₁ K₂ F c).X j`, or zero. -/
/-
**HomologicalComplex.** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a summand of `(mapBifunctor K₁ K₂ F c).X j`, or zero.
-/
noncomputable abbrev ιMapBifunctorOrZero (i₁ : I₁) (i₂ : I₂) (j : J) :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (mapBifunctor K₁ K₂ F c).X j :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).ιTotalOrZero c i₁ i₂ j
/-
**HomologicalComplex.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιMapBifunctorOrZero_eq (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctorOrZero K₁ K₂ F c i₁ i₂ j = ιMapBifunctor K₁ K₂ F c i₁ i₂ j h := dif_pos h
/-
**HomologicalComplex.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιMapBifunctorOrZero_eq_zero (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) ≠ j) :
    ιMapBifunctorOrZero K₁ K₂ F c i₁ i₂ j = 0 := dif_neg h

section

variable {K₁ K₂ F c}
variable {A : D} {j : J}
  (f : ∀ (i₁ : I₁) (i₂ : I₂) (_ : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j),
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ A)

/-- Constructor for morphisms from `(mapBifunctor K₁ K₂ F c).X j`. -/
/-
**HomologicalComplex.mapBifunctorDesc** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComp
lex`。
形式化陈述：mapBifunctorDesc : (mapBifunctor K₁ K₂ F c).X j ⟶ A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms from `(mapBifunctor K₁ K₂ F c).X j`.
-/
noncomputable def mapBifunctorDesc : (mapBifunctor K₁ K₂ F c).X j ⟶ A :=
  HomologicalComplex₂.totalDesc _ f

@[reassoc (attr := simp)]
/-
**HomologicalComplex.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_mapBifunctorDesc (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ mapBifunctorDesc f = f i₁ i₂ h := by
  apply HomologicalComplex₂.ι_totalDesc

end

namespace mapBifunctor

variable {K₁ K₂ F c} in
@[ext]
/-
**HomologicalComplex.mapBifunctor.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Homological
Complex.mapBifunctor`。
形式化陈述：hom_ext {Y : D} {j : J} {f g : (mapBifunctor K₁ K₂ F c).X j ⟶ Y} (h : fora
ll (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j), ιMapBifunctor 
K₁ K₂ F c i₁ i₂ j h ≫ f = ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ g) : f = g
参数：mapBifunctor K₁ K₂ F c；h : forall (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ 
c₂ c ⟨i₁, i₂⟩ = j), ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ f = ιMapBifunctor K₁ K₂ 
F c i₁ i₂ j h ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex₂.total.hom_ext`：hom_ext {A : C} {i₁₂ : I₁₂} {f g : (K
.total c₁₂).X i₁₂ ⟶ A} (h : forall (i₁ : I₁) (i₂ : I₂) (hi : ComplexShape.π c₁ c
₂ c₁₂ (i₁, i₂) = i₁₂), …
-/
lemma hom_ext {Y : D} {j : J} {f g : (mapBifunctor K₁ K₂ F c).X j ⟶ Y}
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j),
      ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ f = ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ g) :
    f = g :=
  HomologicalComplex₂.total.hom_ext _ h

section

variable (j j' : J)

/-- The first differential on `mapBifunctor K₁ K₂ F c` -/
/-
**HomologicalComplex.mapBifunctor.D** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first differential on `mapBifunctor K₁ K₂ F c`
-/
noncomputable def D₁ :
    (mapBifunctor K₁ K₂ F c).X j ⟶ (mapBifunctor K₁ K₂ F c).X j' :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).D₁ c j j'

/-- The second differential on `mapBifunctor K₁ K₂ F c` -/
/-
**HomologicalComplex.mapBifunctor.D** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second differential on `mapBifunctor K₁ K₂ F c`
-/
noncomputable def D₂ :
    (mapBifunctor K₁ K₂ F c).X j ⟶ (mapBifunctor K₁ K₂ F c).X j' :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).D₂ c j j'
/-
**HomologicalComplex.mapBifunctor.d_eq** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex.mapBifunctor`。
形式化陈述：d_eq : (mapBifunctor K₁ K₂ F c).d j j' = D₁ K₁ K₂ F c j j' + D₂ K₁ K₂ F c 
j j'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d_eq :
    (mapBifunctor K₁ K₂ F c).d j j' = D₁ K₁ K₂ F c j j' + D₂ K₁ K₂ F c j j' := rfl

end

section

variable (i₁ : I₁) (i₂ : I₂) (j : J)

/-- The first differential on a summand of `mapBifunctor K₁ K₂ F c` -/
/-
**HomologicalComplex.mapBifunctor.d** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first differential on a summand of `mapBifunctor K₁ K₂ F c`
-/
noncomputable def d₁ :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (mapBifunctor K₁ K₂ F c).X j :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).d₁ c i₁ i₂ j

/-- The second differential on a summand of `mapBifunctor K₁ K₂ F c` -/
/-
**HomologicalComplex.mapBifunctor.d** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second differential on a summand of `mapBifunctor K₁ K₂ F c`
-/
noncomputable def d₂ :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (mapBifunctor K₁ K₂ F c).X j :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).d₂ c i₁ i₂ j
/-
**HomologicalComplex.mapBifunctor.d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₁_eq_zero (h : ¬ c₁.Rel i₁ (c₁.next i₁)) :
    d₁ K₁ K₂ F c i₁ i₂ j = 0 :=
  HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h
/-
**HomologicalComplex.mapBifunctor.d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₂_eq_zero (h : ¬ c₂.Rel i₂ (c₂.next i₂)) :
    d₂ K₁ K₂ F c i₁ i₂ j = 0 :=
  HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h
/-
**HomologicalComplex.mapBifunctor.d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₁_eq_zero' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁', i₂⟩ ≠ j) :
    d₁ K₁ K₂ F c i₁ i₂ j = 0 :=
  HomologicalComplex₂.d₁_eq_zero' _ _ h _ _ h'
/-
**HomologicalComplex.mapBifunctor.d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₂_eq_zero' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁, i₂'⟩ ≠ j) :
    d₂ K₁ K₂ F c i₁ i₂ j = 0 :=
  HomologicalComplex₂.d₂_eq_zero' _ _ _ h _ h'
/-
**HomologicalComplex.mapBifunctor.d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₁_eq' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J) :
    d₁ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₁ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.map (K₁.d i₁ i₁')).app (K₂.X i₂) ≫ ιMapBifunctorOrZero K₁ K₂ F c i₁' i₂ j) :=
  HomologicalComplex₂.d₁_eq' _ _ h _ _
/-
**HomologicalComplex.mapBifunctor.d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₂_eq' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J) :
    d₂ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₂ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.obj (K₁.X i₁)).map (K₂.d i₂ i₂') ≫ ιMapBifunctorOrZero K₁ K₂ F c i₁ i₂' j) :=
  HomologicalComplex₂.d₂_eq' _ _ _ h _
/-
**HomologicalComplex.mapBifunctor.d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₁_eq {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁', i₂⟩ = j) :
    d₁ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₁ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.map (K₁.d i₁ i₁')).app (K₂.X i₂) ≫ ιMapBifunctor K₁ K₂ F c i₁' i₂ j h') :=
  HomologicalComplex₂.d₁_eq _ _ h _ _ h'
/-
**HomologicalComplex.mapBifunctor.d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₂_eq (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁, i₂'⟩ = j) :
    d₂ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₂ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.obj (K₁.X i₁)).map (K₂.d i₂ i₂') ≫ ιMapBifunctor K₁ K₂ F c i₁ i₂' j h') :=
  HomologicalComplex₂.d₂_eq _ _ _ h _ h'

end

section

variable (j j' : J) (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j)

@[reassoc (attr := simp)]
/-
**HomologicalComplex.mapBifunctor.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_D₁ :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ D₁ K₁ K₂ F c j j' = d₁ K₁ K₂ F c i₁ i₂ j' := by
  apply HomologicalComplex₂.ι_D₁

@[reassoc (attr := simp)]
/-
**HomologicalComplex.mapBifunctor.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
.mapBifunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_D₂ :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ D₂ K₁ K₂ F c j j' = d₂ K₁ K₂ F c i₁ i₂ j' := by
  apply HomologicalComplex₂.ι_D₂

end

end mapBifunctor

section

variable {K₁ K₂ L₁ L₂}

/-- The morphism `mapBifunctor K₁ K₂ F c ⟶ mapBifunctor L₁ L₂ F c` induced by
morphisms of complexes `K₁ ⟶ L₁` and `K₂ ⟶ L₂`. -/
/-
**HomologicalComplex.mapBifunctorMap** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：mapBifunctorMap : mapBifunctor K₁ K₂ F c ⟶ mapBifunctor L₁ L₂ F c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `mapBifunctor K₁ K₂ F c ⟶ mapBifunctor L₁ L₂ F c` induced by
morphisms of complexes `K₁ ⟶ L₁` and `K₂ ⟶ L₂`.
-/
noncomputable def mapBifunctorMap : mapBifunctor K₁ K₂ F c ⟶ mapBifunctor L₁ L₂ F c :=
  HomologicalComplex₂.total.map (((F.mapBifunctorHomologicalComplex c₁ c₂).map f₁).app K₂ ≫
    ((F.mapBifunctorHomologicalComplex c₁ c₂).obj L₁).map f₂) c

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_mapBifunctorMap (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ (mapBifunctorMap f₁ f₂ F c).f j =
      (F.map (f₁.f i₁)).app (K₂.X i₂) ≫ (F.obj (L₁.X i₁)).map (f₂.f i₂) ≫
        ιMapBifunctor L₁ L₂ F c i₁ i₂ j h := by
  simp [mapBifunctorMap]

end

end HomologicalComplex

namespace CategoryTheory.Functor

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c : ComplexShape J)
  [DecidableEq J] [TotalComplexShape c₁ c₂ c]

open HomologicalComplex

/-- The bifunctor on homological complexes that is induced by a bifunctor. -/
@[simps]
/-
**CategoryTheory.Functor.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (self : 
CategoryTheory.Functor C D) → {X Y : C} → (X ⟶ Y) → (self.obj X ⟶ self.obj Y)
参数：self : CategoryTheory.Functor C D；X ⟶ Y；self.obj X ⟶ self.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bifunctor on homological complexes that is induced by a bifunctor.
-/
noncomputable def map₂HomologicalComplex
    [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂),
      HasMapBifunctor K₁ K₂ F c] :
    HomologicalComplex C₁ c₁ ⥤ HomologicalComplex C₂ c₂ ⥤ HomologicalComplex D c where
  obj K₁ :=
    { obj K₂ := mapBifunctor K₁ K₂ F c
      map g := mapBifunctorMap (𝟙 K₁) g _ _ }
  map f := { app K₂ := mapBifunctorMap f (𝟙 K₂) _ _ }

/-- The bifunctor on cochain complexes that is induced by a bifunctor. -/
/-
**CategoryTheory.Functor.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (self : 
CategoryTheory.Functor C D) → {X Y : C} → (X ⟶ Y) → (self.obj X ⟶ self.obj Y)
参数：self : CategoryTheory.Functor C D；X ⟶ Y；self.obj X ⟶ self.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bifunctor on cochain complexes that is induced by a bifunctor.
-/
noncomputable abbrev map₂CochainComplex
    [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F (.up ℤ)] :
    CochainComplex C₁ ℤ ⥤ CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ :=
  F.map₂HomologicalComplex _ _ _

end CategoryTheory.Functor

