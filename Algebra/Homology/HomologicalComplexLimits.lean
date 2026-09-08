/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Limits and colimits in the category of homological complexes

In this file, it is shown that if a category `C` has (co)limits of shape `J`,
then it is also the case of the categories `HomologicalComplex C c`,
and the evaluation functors `eval C c i : HomologicalComplex C c ⥤ C`
commute to these.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C ι J : Type*} [Category* C] [Category* J] {c : ComplexShape ι} [HasZeroMorphisms C]

section

variable (F : J ⥤ HomologicalComplex C c)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A cone in `HomologicalComplex C c` is limit if the induced cones obtained
by applying `eval C c i : HomologicalComplex C c ⥤ C` for all `i` are limit. -/
/-
**HomologicalComplex.isLimitOfEval** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex
`。
形式化陈述：isLimitOfEval (s : Cone F) (hs : forall (i : ι), IsLimit ((eval C c i).map
Cone s)) : IsLimit s where lift t
参数：s : Cone F；hs : forall (i : ι), IsLimit ((eval C c i).mapCone s)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone in `HomologicalComplex C c` is limit if the induced cones obtained
by applying `eval C c i : HomologicalComplex C c ⥤ C` for all `i` are limit.
-/
def isLimitOfEval (s : Cone F)
    (hs : ∀ (i : ι), IsLimit ((eval C c i).mapCone s)) : IsLimit s where
  lift t :=
    { f := fun i => (hs i).lift ((eval C c i).mapCone t)
      comm' := fun i i' _ => by
        apply IsLimit.hom_ext (hs i')
        intro j
        have eq := fun k => (hs k).fac ((eval C c k).mapCone t)
        simp only [Functor.mapCone_π_app, eval_map] at eq
        simp only [Functor.mapCone_π_app, eval_map, assoc]
        rw [eq i', ← Hom.comm, reassoc_of% (eq i), Hom.comm] }
  fac t j := by
    ext i
    apply (hs i).fac
  uniq t m hm := by
    ext i
    apply (hs i).uniq ((eval C c i).mapCone t)
    intro j
    dsimp
    simp only [← comp_f, hm]

variable [∀ (n : ι), HasLimit (F ⋙ eval C c n)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A cone for a functor `F : J ⥤ HomologicalComplex C c` which is given in degree `n` by
the limit `F ⋙ eval C c n`. -/
@[simps]
/-
**HomologicalComplex.coneOfHasLimitEval** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：coneOfHasLimitEval : Cone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone for a functor `F : J ⥤ HomologicalComplex C c` which is given in degree `
n` by
the limit `F ⋙ eval C c n`.
-/
noncomputable def coneOfHasLimitEval : Cone F where
  pt :=
    { X := fun n => limit (F ⋙ eval C c n)
      d := fun n m => limMap { app := fun j => (F.obj j).d n m }
      shape := fun {n m} h => by
        ext j
        rw [limMap_π]
        dsimp
        rw [(F.obj j).shape _ _ h, comp_zero, zero_comp] }
  π :=
    { app := fun j => { f := fun _ => limit.π _ j }
      naturality := fun i j φ => by
        ext n
        dsimp
        simp only [Category.id_comp]
        rw [← eval_map, ← Functor.comp_map, limit.w] }

/-- The cone `coneOfHasLimitEval F` is limit. -/
/-
**HomologicalComplex.isLimitConeOfHasLimitEval** 是 Mathlib 中的一个定义，位于命名空间 `Homolo
gicalComplex`。
形式化陈述：isLimitConeOfHasLimitEval : IsLimit (coneOfHasLimitEval F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone `coneOfHasLimitEval F` is limit.
-/
noncomputable def isLimitConeOfHasLimitEval : IsLimit (coneOfHasLimitEval F) :=
  isLimitOfEval _ _ (fun _ => limit.isLimit _)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLimit F := ⟨⟨⟨_, isLimitConeOfHasLimitEval F⟩⟩⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (n : ι) : PreservesLimit F (eval C c n) :=
  preservesLimit_of_preserves_limit_cone (isLimitConeOfHasLimitEval F) (limit.isLimit _)

end

/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimitsOfShape J C] : HasLimitsOfShape J (HomologicalComplex C c) := ⟨inferInstance⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [HasLimitsOfShape J C] (n : ι) :
    PreservesLimitsOfShape J (eval C c n) := ⟨inferInstance⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteLimits C] : HasFiniteLimits (HomologicalComplex C c) :=
  ⟨fun _ _ => inferInstance⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [HasFiniteLimits C] (n : ι) : PreservesFiniteLimits (eval C c n) :=
  ⟨fun _ _ _ => inferInstance⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteLimits C] {K L : HomologicalComplex C c} (φ : K ⟶ L) [Mono φ] (n : ι) :
    Mono (φ.f n) := by
  change Mono ((HomologicalComplex.eval C c n).map φ)
  infer_instance

section

variable (F : J ⥤ HomologicalComplex C c)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A cocone in `HomologicalComplex C c` is colimit if the induced cocones obtained
by applying `eval C c i : HomologicalComplex C c ⥤ C` for all `i` are colimit. -/
/-
**HomologicalComplex.isColimitOfEval** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：isColimitOfEval (s : Cocone F) (hs : forall (i : ι), IsColimit ((eval C c 
i).mapCocone s)) : IsColimit s where desc t
参数：s : Cocone F；hs : forall (i : ι), IsColimit ((eval C c i).mapCocone s)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cocone in `HomologicalComplex C c` is colimit if the induced cocones obtained
by applying `eval C c i : HomologicalComplex C c ⥤ C` for all `i` are colimit.
-/
def isColimitOfEval (s : Cocone F)
    (hs : ∀ (i : ι), IsColimit ((eval C c i).mapCocone s)) : IsColimit s where
  desc t :=
    { f := fun i => (hs i).desc ((eval C c i).mapCocone t)
      comm' := fun i i' _ => by
        apply IsColimit.hom_ext (hs i)
        intro j
        have eq := fun k => (hs k).fac ((eval C c k).mapCocone t)
        simp only [Functor.mapCocone_ι_app, eval_map] at eq
        simp only [Functor.mapCocone_ι_app, eval_map]
        rw [reassoc_of% (eq i), Hom.comm_assoc, eq i', Hom.comm] }
  fac t j := by
    ext i
    apply (hs i).fac
  uniq t m hm := by
    ext i
    apply (hs i).uniq ((eval C c i).mapCocone t)
    intro j
    dsimp
    simp only [← comp_f, hm]


variable [∀ (n : ι), HasColimit (F ⋙ HomologicalComplex.eval C c n)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A cocone for a functor `F : J ⥤ HomologicalComplex C c` which is given in degree `n` by
the colimit of `F ⋙ eval C c n`. -/
@[simps]
/-
**HomologicalComplex.coconeOfHasColimitEval** 是 Mathlib 中的一个定义，位于命名空间 `Homologic
alComplex`。
形式化陈述：coconeOfHasColimitEval : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cocone for a functor `F : J ⥤ HomologicalComplex C c` which is given in degree
 `n` by
the colimit of `F ⋙ eval C c n`.
-/
noncomputable def coconeOfHasColimitEval : Cocone F where
  pt :=
    { X := fun n => colimit (F ⋙ eval C c n)
      d := fun n m => colimMap { app := fun j => (F.obj j).d n m }
      shape := fun {n m} h => by
        ext j
        rw [ι_colimMap]
        dsimp
        rw [(F.obj j).shape _ _ h, zero_comp, comp_zero] }
  ι :=
    { app := fun j => { f := fun n => colimit.ι (F ⋙ eval C c n) j }
      naturality := fun i j φ => by
        ext n
        dsimp
        simp only [Category.comp_id]
        rw [← eval_map, ← Functor.comp_map, colimit.w] }

/-- The cocone `coconeOfHasLimitEval F` is colimit. -/
/-
**HomologicalComplex.isColimitCoconeOfHasColimitEval** 是 Mathlib 中的一个定义，位于命名空间 `
HomologicalComplex`。
形式化陈述：isColimitCoconeOfHasColimitEval : IsColimit (coconeOfHasColimitEval F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone `coconeOfHasLimitEval F` is colimit.
-/
noncomputable def isColimitCoconeOfHasColimitEval : IsColimit (coconeOfHasColimitEval F) :=
  isColimitOfEval _ _ (fun _ => colimit.isColimit _)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasColimit F := ⟨⟨⟨_, isColimitCoconeOfHasColimitEval F⟩⟩⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (n : ι) : PreservesColimit F (eval C c n) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitCoconeOfHasColimitEval F)
    (colimit.isColimit _)

end

/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimitsOfShape J C] : HasColimitsOfShape J (HomologicalComplex C c) := ⟨inferInstance⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [HasColimitsOfShape J C] (n : ι) :
    PreservesColimitsOfShape J (eval C c n) := ⟨inferInstance⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteColimits C] : HasFiniteColimits (HomologicalComplex C c) :=
  ⟨fun _ _ => inferInstance⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [HasFiniteColimits C] (n : ι) :
    PreservesFiniteColimits (eval C c n) := ⟨fun _ _ _ => inferInstance⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteColimits C] {K L : HomologicalComplex C c} (φ : K ⟶ L) [Epi φ] (n : ι) :
    Epi (φ.f n) := by
  change Epi ((HomologicalComplex.eval C c n).map φ)
  infer_instance

/-- A functor `D ⥤ HomologicalComplex C c` preserves limits of shape `J`
if for any `i`, `G ⋙ eval C c i` does. -/
/-
**HomologicalComplex.preservesLimitsOfShape_of_eval** 是 Mathlib 中的一个引理，位于命名空间 `H
omologicalComplex`。
形式化陈述：preservesLimitsOfShape_of_eval {D : Type*} [Category* D] (G : D ⥤ Homologi
calComplex C c) (_ : forall (i : ι), PreservesLimitsOfShape J (G ⋙ eval C c i)) 
: PreservesLimitsOfShape J G
参数：G : D ⥤ HomologicalComplex C c；_ : forall (i : ι), PreservesLimitsOfShape J (
G ⋙ eval C c i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A functor `D ⥤ HomologicalComplex C c` preserves limits of shape `J`
if for any `i`, `G ⋙ eval C c i` does.
-/
lemma preservesLimitsOfShape_of_eval {D : Type*} [Category* D]
    (G : D ⥤ HomologicalComplex C c)
    (_ : ∀ (i : ι), PreservesLimitsOfShape J (G ⋙ eval C c i)) :
    PreservesLimitsOfShape J G :=
  ⟨fun {_} => ⟨fun hs ↦ ⟨isLimitOfEval _ _
    (fun i => isLimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩⟩

/-- A functor `D ⥤ HomologicalComplex C c` preserves colimits of shape `J`
if for any `i`, `G ⋙ eval C c i` does. -/
/-
**HomologicalComplex.preservesColimitsOfShape_of_eval** 是 Mathlib 中的一个引理，位于命名空间 
`HomologicalComplex`。
形式化陈述：preservesColimitsOfShape_of_eval {D : Type*} [Category* D] (G : D ⥤ Homolo
gicalComplex C c) (_ : forall (i : ι), PreservesColimitsOfShape J (G ⋙ eval C c 
i)) : PreservesColimitsOfShape J G
参数：G : D ⥤ HomologicalComplex C c；_ : forall (i : ι), PreservesColimitsOfShape J
 (G ⋙ eval C c i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A functor `D ⥤ HomologicalComplex C c` preserves colimits of shape `J`
if for any `i`, `G ⋙ eval C c i` does.
-/
lemma preservesColimitsOfShape_of_eval {D : Type*} [Category* D]
    (G : D ⥤ HomologicalComplex C c)
    (_ : ∀ (i : ι), PreservesColimitsOfShape J (G ⋙ eval C c i)) :
    PreservesColimitsOfShape J G :=
  ⟨fun {_} => ⟨fun hs ↦ ⟨isColimitOfEval _ _
    (fun i => isColimitOfPreserves (G ⋙ eval C c i) hs)⟩⟩⟩

section

variable [HasZeroObject C] [DecidableEq ι] (i : ι)

/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesLimitsOfShape J (single C c i) :=
  preservesLimitsOfShape_of_eval _ (fun j => by
    by_cases h : j = i
    · subst h
      exact preservesLimitsOfShape_of_natIso (singleCompEvalIsoSelf C c j).symm
    · exact Functor.preservesLimitsOfShape_of_isZero _ (isZero_single_comp_eval C c _ _ h) _)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesColimitsOfShape J (single C c i) :=
  preservesColimitsOfShape_of_eval _ (fun j => by
    by_cases h : j = i
    · subst h
      exact preservesColimitsOfShape_of_natIso (singleCompEvalIsoSelf C c j).symm
    · exact Functor.preservesColimitsOfShape_of_isZero _ (isZero_single_comp_eval C c _ _ h) _)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteLimits (single C c i) := ⟨by intros; infer_instance⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteColimits (single C c i) := ⟨by intros; infer_instance⟩

end

end HomologicalComplex

