/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
/-!

# Functors preserving effective epimorphisms

This file concerns functors which preserve and/or reflect effective epimorphisms and effective
epimorphic families.

## TODO
- Find nice sufficient conditions in terms of preserving/reflecting (co)limits, to preserve/reflect
  effective epis, similar to `CategoryTheory.preserves_epi_of_preservesColimit`.
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

noncomputable section Equivalence

variable {D : Type*} [Category* D] (e : C ≌ D) {B : C}

variable {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))

/-
**CategoryTheory.effectiveEpiFamilyStructOfEquivalence_aux** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory`。
形式化陈述：effectiveEpiFamilyStructOfEquivalence_aux {W : D} (ε : (a : α) -> e.functo
r.obj (X a) ⟶ W) (h : forall {Z : D} (a₁ a₂ : α) (g₁ : Z ⟶ e.functor.obj (X a₁))
 (g₂ : Z ⟶ e.functor.obj (X a₂)), g₁ ≫ e.functor.map (π a₁) = g₂ ≫ e.functor.map
 (π a₂) -> g₁ ≫ ε a₁ = g₂ ≫ ε a₂) {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ 
X a₂) (hg : g₁ ≫ π a₁ = g₂ ≫ π a₂) : g₁ ≫ (fun a => e.unit.app (X a) ≫ e.inverse
.map (ε a)) a₁ = g₂ ≫ (fun a => e.unit.app (X a) ≫ e.inverse.map (ε a)) a₂
参数：ε : (a : α) -> e.functor.obj (X a) ⟶ W；h : forall {Z : D} (a₁ a₂ : α) (g₁ : Z
 ⟶ e.functor.obj (X a₁)) (g₂ : Z ⟶ e.functor.obj (X a₂)), g₁ ≫ e.functor.map (π 
a₁) = g₂ ≫ e.functor.map (π a₂) -> g₁ ≫ ε a₁ = g₂ ≫ ε a₂；a₁ a₂ : α；g₁ : Z ⟶ X a₁
；g₂ : Z ⟶ X a₂；hg : g₁ ≫ π a₁ = g₂ ≫ π a₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Equivalence.inv_fun_map`：inv_fun_map (e : C ≌ D) (X Y : C
) (f : X ⟶ Y) : e.inverse.map (e.functor.map f) = e.unitInv.app X ≫ f ≫ e.unit.a
pp Y
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem effectiveEpiFamilyStructOfEquivalence_aux {W : D} (ε : (a : α) → e.functor.obj (X a) ⟶ W)
    (h : ∀ {Z : D} (a₁ a₂ : α) (g₁ : Z ⟶ e.functor.obj (X a₁)) (g₂ : Z ⟶ e.functor.obj (X a₂)),
      g₁ ≫ e.functor.map (π a₁) = g₂ ≫ e.functor.map (π a₂) → g₁ ≫ ε a₁ = g₂ ≫ ε a₂)
    {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂) (hg : g₁ ≫ π a₁ = g₂ ≫ π a₂) :
    g₁ ≫ (fun a ↦ e.unit.app (X a) ≫ e.inverse.map (ε a)) a₁ =
    g₂ ≫ (fun a ↦ e.unit.app (X a) ≫ e.inverse.map (ε a)) a₂ := by
  have := h a₁ a₂ (e.functor.map g₁) (e.functor.map g₂)
  simp only [← Functor.map_comp, hg] at this
  simpa using congrArg e.inverse.map (this (by trivial))

variable [EffectiveEpiFamily X π]

/-- Equivalences preserve effective epimorphic families -/
/-
**CategoryTheory.effectiveEpiFamilyStructOfEquivalence** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory`。
形式化陈述：effectiveEpiFamilyStructOfEquivalence : EffectiveEpiFamilyStruct (fun a =>
 e.functor.obj (X a)) (fun a => e.functor.map (π a)) where desc ε h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Equivalences preserve effective epimorphic families
-/
def effectiveEpiFamilyStructOfEquivalence : EffectiveEpiFamilyStruct (fun a ↦ e.functor.obj (X a))
    (fun a ↦ e.functor.map (π a)) where
  desc ε h := (e.toAdjunction.homEquiv _ _).symm
      (EffectiveEpiFamily.desc X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h))
  fac ε h a := by
    simp only [Adjunction.homEquiv_counit,
      Equivalence.toAdjunction_counit]
    have := congrArg ((fun f ↦ f ≫ e.counit.app _) ∘ e.functor.map)
      (EffectiveEpiFamily.fac X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h) a)
    simp only [Functor.id_obj, Function.comp_apply, Functor.map_comp,
        Category.assoc, Equivalence.fun_inv_map,
        Equivalence.counitIso_inv_hom_id_app, Category.comp_id,
        Equivalence.functor_unit_comp_assoc] at this
    simp [this]
  uniq ε h m hm := by
    simp only [Adjunction.homEquiv_counit,
      Equivalence.toAdjunction_counit]
    have := EffectiveEpiFamily.uniq X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h)
    specialize this (e.unit.app _ ≫ e.inverse.map m) fun a ↦ ?_
    · rw [← congrArg e.inverse.map (hm a)]
      simp
    · simp [← this]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [F.IsEquivalence] :
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a ↦ F.map (π a)) :=
  ⟨⟨effectiveEpiFamilyStructOfEquivalence F.asEquivalence _ _⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {X B : C} (π : X ⟶ B) (F : C ⥤ D) [F.IsEquivalence] [EffectiveEpi π] :
    EffectiveEpi <| F.map π := inferInstance

end Equivalence

namespace Functor

variable {D : Type*} [Category* D]

section Preserves

/--
A class describing the property of preserving effective epimorphisms.
-/
/-
**CategoryTheory.Functor.PreservesEffectiveEpis** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} → [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class describing the property of preserving effective epimorphisms.
-/
class PreservesEffectiveEpis (F : C ⥤ D) : Prop where
  /--
  A functor preserves effective epimorphisms if it maps effective
  epimorphisms to effective epimorphisms.
  -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [EffectiveEpi f], EffectiveEpi (F.map f)
/-
**CategoryTheory.Functor.map_effectiveEpi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：map_effectiveEpi (F : C ⥤ D) [F.PreservesEffectiveEpis] {X Y : C} (f : X ⟶
 Y) [EffectiveEpi f] : EffectiveEpi (F.map f)
参数：F : C ⥤ D；f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesEffectiveEpis.preserves`：∀ {C : Type u_1
} {inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : Categ
oryTheory.Category.{v_2, u_2} D} {F : Categor…
-/
instance map_effectiveEpi (F : C ⥤ D) [F.PreservesEffectiveEpis] {X Y : C} (f : X ⟶ Y)
    [EffectiveEpi f] : EffectiveEpi (F.map f) :=
  PreservesEffectiveEpis.preserves f
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsRegularEpiCategory D] (F : C ⥤ D) [F.PreservesEpimorphisms] [Limits.HasPullbacks D] :
    F.PreservesEffectiveEpis where
  preserves _ _ := by
    rw [← isRegularEpi_iff_effectiveEpi]
    apply IsRegularEpiCategory.regularEpiOfEpi

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Applying a functor which preserves pullbacks and effective epimorphisms to a regular epi diagram
of the form `X ×_Y X ⇉ X → Y` gives a regular epi diagram.
-/
@[simps]
/-
**CategoryTheory.Functor.regularEpiOfPreserves** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：regularEpiOfPreserves {C D : Type*} [Category* C] [Category* D] {X Y : C} 
(f : X ⟶ Y) [EffectiveEpi f] (F : C ⥤ D) [PreservesEffectiveEpis F] [PreservesLi
mitsOfShape WalkingCospan F] (c : PullbackCone f f) (hc : IsLimit c) : RegularEp
i (F.map f) where W
参数：f : X ⟶ Y；F : C ⥤ D；c : PullbackCone f f；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying a functor which preserves pullbacks and effective epimorphisms to a reg
ular epi diagram
of the form `X ×_Y X ⇉ X → Y` gives a regular epi diagram.
-/
noncomputable def regularEpiOfPreserves {C D : Type*} [Category* C] [Category* D] {X Y : C}
    (f : X ⟶ Y) [EffectiveEpi f] (F : C ⥤ D) [PreservesEffectiveEpis F]
    [PreservesLimitsOfShape WalkingCospan F] (c : PullbackCone f f) (hc : IsLimit c) :
    RegularEpi (F.map f) where
  W := F.obj c.pt
  left := F.map c.fst
  right := F.map c.snd
  w := by rw [← F.map_comp, c.condition]; simp
  isColimit := by
    refine isColimitCoforkOfEffectiveEpi (F.map f) (.mk (F.map c.fst) (F.map c.snd) ?_) ?_
    · simp [← Functor.map_comp, c.condition]
    · refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (isLimitOfPreserves F hc)
      · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      · exact Cone.ext (Iso.refl _) <| by rintro (_ | _ | _) <;> cat_disch

/--
A class describing the property of preserving effective epimorphic families.
-/
/-
**CategoryTheory.Functor.PreservesEffectiveEpiFamilies** 是 Mathlib 中的一个归纳类型，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} → [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class describing the property of preserving effective epimorphic families.
-/
class PreservesEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor preserves effective epimorphic families if it maps effective epimorphic families to
  effective epimorphic families.
  -/
  preserves : ∀ {α : Type u} {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π],
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a ↦ F.map (π a))
/-
**CategoryTheory.Functor.map_effectiveEpiFamily** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：map_effectiveEpiFamily (F : C ⥤ D) [PreservesEffectiveEpiFamilies.{u} F] {
α : Type u} {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) [EffectiveEpiFamily 
X π] : EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a))
参数：F : C ⥤ D；X : α -> C；π : (a : α) -> (X a ⟶ B)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesEffectiveEpiFamilies.preserves`：∀ {C : T
ype u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 
: CategoryTheory.Category.{v_2, u_2} D} {F : Categor…
-/
instance map_effectiveEpiFamily (F : C ⥤ D) [PreservesEffectiveEpiFamilies.{u} F]
    {α : Type u} {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π] :
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a ↦ F.map (π a)) :=
  PreservesEffectiveEpiFamilies.preserves X π

/--
A class describing the property of preserving finite effective epimorphic families.
-/
/-
**CategoryTheory.Functor.PreservesFiniteEffectiveEpiFamilies** 是 Mathlib 中的一个归纳类
型，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} → [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class describing the property of preserving finite effective epimorphic famili
es.
-/
class PreservesFiniteEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor preserves finite effective epimorphic families if it maps finite effective epimorphic
  families to effective epimorphic families.
  -/
  preserves : ∀ {α : Type} [Finite α] {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π],
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a ↦ F.map (π a))
/-
**CategoryTheory.Functor.map_finite_effectiveEpiFamily** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：map_finite_effectiveEpiFamily (F : C ⥤ D) [F.PreservesFiniteEffectiveEpiFa
milies] {α : Type} [Finite α] {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) [E
ffectiveEpiFamily X π] : EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.m
ap (π a))
参数：F : C ⥤ D；X : α -> C；π : (a : α) -> (X a ⟶ B)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesFiniteEffectiveEpiFamilies.preserves`：∀ 
{C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {F : Categor…
-/
instance map_finite_effectiveEpiFamily (F : C ⥤ D) [F.PreservesFiniteEffectiveEpiFamilies]
    {α : Type} [Finite α] {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π] :
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a ↦ F.map (π a)) :=
  PreservesFiniteEffectiveEpiFamilies.preserves X π
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [PreservesEffectiveEpiFamilies.{0} F] :
    PreservesFiniteEffectiveEpiFamilies F where
  preserves _ _ := inferInstance
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [PreservesFiniteEffectiveEpiFamilies F] : PreservesEffectiveEpis F where
  preserves _ := inferInstance
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [IsEquivalence F] : F.PreservesEffectiveEpiFamilies where
  preserves _ _ := inferInstance

section Composition

variable {E : Type*} [Category* E]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) (G : D ⥤ E) [PreservesEffectiveEpis F] [PreservesEffectiveEpis G] :
    PreservesEffectiveEpis (F ⋙ G) where
  preserves _ _ := by dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteEffectiveEpiFamilies F]
    [PreservesFiniteEffectiveEpiFamilies G] :
    PreservesFiniteEffectiveEpiFamilies (F ⋙ G) where
  preserves _ _ _ := by dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) (G : D ⥤ E) [PreservesEffectiveEpiFamilies.{u} F]
    [PreservesEffectiveEpiFamilies.{u} G] :
    PreservesEffectiveEpiFamilies.{u} (F ⋙ G) where
  preserves _ _ _ := by dsimp; infer_instance

end Composition

end Preserves

section Reflects

/--
A class describing the property of reflecting effective epimorphisms.
-/
/-
**CategoryTheory.Functor.ReflectsEffectiveEpis** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} → [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class describing the property of reflecting effective epimorphisms.
-/
class ReflectsEffectiveEpis (F : C ⥤ D) : Prop where
  /--
  A functor reflects effective epimorphisms if morphisms that are mapped to epimorphisms are
  themselves effective epimorphisms.
  -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y), EffectiveEpi (F.map f) → EffectiveEpi f
/-
**CategoryTheory.Functor.effectiveEpi_of_map** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：effectiveEpi_of_map (F : C ⥤ D) [F.ReflectsEffectiveEpis] {X Y : C} (f : X
 ⟶ Y) (h : EffectiveEpi (F.map f)) : EffectiveEpi f
参数：F : C ⥤ D；f : X ⟶ Y；h : EffectiveEpi (F.map f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ReflectsEffectiveEpis.reflects`：∀ {C : Type u_1} 
{inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : Categor
yTheory.Category.{v_2, u_2} D} {F : Categor…
-/
lemma effectiveEpi_of_map (F : C ⥤ D) [F.ReflectsEffectiveEpis] {X Y : C} (f : X ⟶ Y)
    (h : EffectiveEpi (F.map f)) : EffectiveEpi f :=
  ReflectsEffectiveEpis.reflects f h

/--
A class describing the property of reflecting effective epimorphic families.
-/
/-
**CategoryTheory.Functor.ReflectsEffectiveEpiFamilies** 是 Mathlib 中的一个归纳类型，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} → [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class describing the property of reflecting effective epimorphic families.
-/
class ReflectsEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor reflects effective epimorphic families if families that are mapped to effective
  epimorphic families are themselves effective epimorphic families.
  -/
  reflects : ∀ {α : Type u} {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B)),
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a ↦ F.map (π a)) →
    EffectiveEpiFamily X π
/-
**CategoryTheory.Functor.effectiveEpiFamily_of_map** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：effectiveEpiFamily_of_map (F : C ⥤ D) [ReflectsEffectiveEpiFamilies.{u} F]
 {α : Type u} {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) (h : EffectiveEpiF
amily (fun a => F.obj (X a)) (fun a => F.map (π a))) : EffectiveEpiFamily X π
参数：F : C ⥤ D；X : α -> C；π : (a : α) -> (X a ⟶ B)；h : EffectiveEpiFamily (fun a =
> F.obj (X a)) (fun a => F.map (π a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ReflectsEffectiveEpiFamilies.reflects`：∀ {C : Typ
e u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : 
CategoryTheory.Category.{v_2, u_2} D} {F : Categor…
-/
lemma effectiveEpiFamily_of_map (F : C ⥤ D) [ReflectsEffectiveEpiFamilies.{u} F]
    {α : Type u} {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B))
    (h : EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a ↦ F.map (π a))) :
    EffectiveEpiFamily X π :=
  ReflectsEffectiveEpiFamilies.reflects X π h

/--
A class describing the property of reflecting finite effective epimorphic families.
-/
/-
**CategoryTheory.Functor.ReflectsFiniteEffectiveEpiFamilies** 是 Mathlib 中的一个归纳类型
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} → [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class describing the property of reflecting finite effective epimorphic famili
es.
-/
class ReflectsFiniteEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor reflects finite effective epimorphic families if finite families that are
  mapped to effective epimorphic families are themselves effective epimorphic families.
  -/
  reflects : ∀ {α : Type} [Finite α] {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B)),
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a ↦ F.map (π a)) →
    EffectiveEpiFamily X π
/-
**CategoryTheory.Functor.finite_effectiveEpiFamily_of_map** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：finite_effectiveEpiFamily_of_map (F : C ⥤ D) [ReflectsFiniteEffectiveEpiFa
milies F] {α : Type} [Finite α] {B : C} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) 
(h : EffectiveEpiFamily (fun a => F.obj (X a)) (fun a => F.map (π a))) : Effecti
veEpiFamily X π
参数：F : C ⥤ D；X : α -> C；π : (a : α) -> (X a ⟶ B)；h : EffectiveEpiFamily (fun a =
> F.obj (X a)) (fun a => F.map (π a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ReflectsFiniteEffectiveEpiFamilies.reflects`：∀ {C
 : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {ins
t_1 : CategoryTheory.Category.{v_2, u_2} D} {F : Categor…
-/
lemma finite_effectiveEpiFamily_of_map (F : C ⥤ D) [ReflectsFiniteEffectiveEpiFamilies F]
    {α : Type} [Finite α] {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B))
    (h : EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a ↦ F.map (π a))) :
    EffectiveEpiFamily X π :=
  ReflectsFiniteEffectiveEpiFamilies.reflects X π h
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [ReflectsEffectiveEpiFamilies.{0} F] :
    ReflectsFiniteEffectiveEpiFamilies F where
  reflects _ _ h := by
    have := F.effectiveEpiFamily_of_map _ _ h
    infer_instance
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [ReflectsFiniteEffectiveEpiFamilies F] : ReflectsEffectiveEpis F where
  reflects _ h := by
    rw [effectiveEpi_iff_effectiveEpiFamily] at h
    have := F.finite_effectiveEpiFamily_of_map _ _ h
    infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [IsEquivalence F] : F.ReflectsEffectiveEpiFamilies where
  reflects {α B} X π _ := by
    let i : (a : α) → X a ⟶ (inv F).obj (F.obj (X a)) := fun a ↦ (asEquivalence F).unit.app _
    have : EffectiveEpiFamily X (fun a ↦ (i a) ≫ (inv F).map (F.map (π a))) := inferInstance
    simp only [inv_fun_map, Iso.hom_inv_id_app_assoc, i] at this
    have : EffectiveEpiFamily X (fun a ↦ (π a ≫ (asEquivalence F).unit.app B) ≫
        (asEquivalence F).unitInv.app _) := inferInstance
    simpa

section Composition

variable {E : Type*} [Category* E]

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) (G : D ⥤ E) [ReflectsEffectiveEpis F] [ReflectsEffectiveEpis G] :
    ReflectsEffectiveEpis (F ⋙ G) where
  reflects _ h := F.effectiveEpi_of_map _ (G.effectiveEpi_of_map _ h)
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) (G : D ⥤ E) [ReflectsFiniteEffectiveEpiFamilies F]
    [ReflectsFiniteEffectiveEpiFamilies G] :
    ReflectsFiniteEffectiveEpiFamilies (F ⋙ G) where
  reflects _ _ h :=
    F.finite_effectiveEpiFamily_of_map _ _ (G.finite_effectiveEpiFamily_of_map _ _ h)
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) (G : D ⥤ E) [ReflectsEffectiveEpiFamilies.{u} F]
    [ReflectsEffectiveEpiFamilies.{u} G] :
    ReflectsEffectiveEpiFamilies.{u} (F ⋙ G) where
  reflects _ _ h := F.effectiveEpiFamily_of_map _ _ (G.effectiveEpiFamily_of_map _ _ h)

end Composition

end Reflects

end Functor

end CategoryTheory

