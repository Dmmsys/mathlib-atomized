/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin
-/
module

public import Mathlib.CategoryTheory.Limits.Creates

/-!
# Adjunctions and limits

A left adjoint preserves colimits (`CategoryTheory.Adjunction.leftAdjoint_preservesColimits`),
and a right adjoint preserves limits (`CategoryTheory.Adjunction.rightAdjoint_preservesLimits`).

Equivalences create and reflect (co)limits.
(`CategoryTheory.Functor.createsLimitsOfIsEquivalence`,
`CategoryTheory.Functor.createsColimitsOfIsEquivalence`,
`CategoryTheory.Functor.reflectsLimits_of_isEquivalence`,
`CategoryTheory.Functor.reflectsColimits_of_isEquivalence`.)

In `CategoryTheory.Adjunction.coconesIso` we show that
when `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/

@[expose] public section


open Opposite

namespace CategoryTheory

open CategoryTheory.Functor Limits

universe v u v₁ v₂ v₀ u₁ u₂

namespace Adjunction

section ArbitraryUniverse

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

section PreservationColimits

variable {J : Type u} [Category.{v} J] (K : J ⥤ C)

/-- The right adjoint of `Cocone.functoriality K F : Cocone K ⥤ Cocone (K ⋙ F)`.

Auxiliary definition for `functorialityAdjunction`.
-/
/-
**CategoryTheory.Adjunction.functorialityRightAdjoint** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：functorialityRightAdjoint : Cocone (K ⋙ F) ⥤ Cocone K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right adjoint of `Cocone.functoriality K F : Cocone K ⥤ Cocone (K ⋙ F)`.

Auxiliary definition for `functorialityAdjunction`.
-/
def functorialityRightAdjoint : Cocone (K ⋙ F) ⥤ Cocone K :=
  Cocone.functoriality _ G ⋙
    Cocone.precompose (K.rightUnitor.inv ≫ whiskerLeft K adj.unit ≫ (associator _ _ _).inv)

attribute [local simp] functorialityRightAdjoint

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit for the adjunction for `Cocone.functoriality K F : Cocone K ⥤ Cocone (K ⋙ F)`.

Auxiliary definition for `functorialityAdjunction`.
-/
@[simps]
/-
**CategoryTheory.Adjunction.functorialityUnit** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Adjunction`。
形式化陈述：functorialityUnit : 𝟭 (Cocone K) ⟶ Cocone.functoriality _ F ⋙ functorialit
yRightAdjoint adj K where app c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit for the adjunction for `Cocone.functoriality K F : Cocone K ⥤ Cocone (K
 ⋙ F)`.

Auxiliary definition for `functorialityAdjunction`.
-/
def functorialityUnit :
    𝟭 (Cocone K) ⟶ Cocone.functoriality _ F ⋙ functorialityRightAdjoint adj K where
  app c := { hom := adj.unit.app c.pt }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The counit for the adjunction for `Cocone.functoriality K F : Cocone K ⥤ Cocone (K ⋙ F)`.

Auxiliary definition for `functorialityAdjunction`.
-/
@[simps]
/-
**CategoryTheory.Adjunction.functorialityCounit** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Adjunction`。
形式化陈述：functorialityCounit : functorialityRightAdjoint adj K ⋙ Cocone.functoriali
ty _ F ⟶ 𝟭 (Cocone (K ⋙ F)) where app c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit for the adjunction for `Cocone.functoriality K F : Cocone K ⥤ Cocone 
(K ⋙ F)`.

Auxiliary definition for `functorialityAdjunction`.
-/
def functorialityCounit :
    functorialityRightAdjoint adj K ⋙ Cocone.functoriality _ F ⟶ 𝟭 (Cocone (K ⋙ F)) where
  app c := { hom := adj.counit.app c.pt }

set_option backward.defeqAttrib.useBackward true in
/-- The functor `Cocone.functoriality K F : Cocone K ⥤ Cocone (K ⋙ F)` is a left adjoint. -/
/-
**CategoryTheory.Adjunction.functorialityAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Adjunction`。
形式化陈述：functorialityAdjunction : Cocone.functoriality K F ⊣ functorialityRightAdj
oint adj K where unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Cocone.functoriality K F : Cocone K ⥤ Cocone (K ⋙ F)` is a left adj
oint.
-/
def functorialityAdjunction : Cocone.functoriality K F ⊣ functorialityRightAdjoint adj K where
  unit := functorialityUnit adj K
  counit := functorialityCounit adj K

include adj in
/-- A left adjoint preserves colimits. -/
@[stacks 0038]
/-
**CategoryTheory.Adjunction.leftAdjoint_preservesColimits** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Adjunction`。
形式化陈述：leftAdjoint_preservesColimits : PreservesColimitsOfSize.{v, u} F where pre
servesColimitsOfShape
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left adjoint preserves colimits.
-/
lemma leftAdjoint_preservesColimits : PreservesColimitsOfSize.{v, u} F where
  preservesColimitsOfShape :=
    { preservesColimit :=
        { preserves := fun hc =>
            ⟨IsColimit.isoUniqueCoconeMorphism.inv fun _ =>
              @Equiv.unique _ _ (IsColimit.isoUniqueCoconeMorphism.hom hc _)
                ((adj.functorialityAdjunction _).homEquiv _ _)⟩ } }

noncomputable
/-
**CategoryTheory.Adjunction.colim_preservesColimits** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Adjunction`。
形式化陈述：colim_preservesColimits [HasColimitsOfShape J C] : PreservesColimits (coli
m (J
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`：leftAdjoint_pre
servesColimits : PreservesColimitsOfSize.{v, u} F where preservesColimitsOfShape
-/
instance colim_preservesColimits [HasColimitsOfShape J C] :
    PreservesColimits (colim (J := J) (C := C)) :=
  colimConstAdj.leftAdjoint_preservesColimits

-- see Note [lower instance priority]
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (priority := 100) isEquivalence_preservesColimits
    (E : C ⥤ D) [E.IsEquivalence] :
    PreservesColimitsOfSize.{v, u} E :=
  leftAdjoint_preservesColimits E.adjunction

-- see Note [lower instance priority]
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (priority := 100)
    _root_.CategoryTheory.Functor.reflectsColimits_of_isEquivalence
    (E : D ⥤ C) [E.IsEquivalence] :
    ReflectsColimitsOfSize.{v, u} E where
  reflectsColimitsOfShape :=
    { reflectsColimit :=
        { reflects := fun t =>
          ⟨(isColimitOfPreserves E.inv t).mapCoconeEquiv E.asEquivalence.unitIso.symm⟩ } }

-- see Note [lower instance priority]
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (priority := 100)
    _root_.CategoryTheory.Functor.createsColimitsOfIsEquivalence (H : D ⥤ C)
    [H.IsEquivalence] :
    CreatesColimitsOfSize.{v, u} H where
  CreatesColimitsOfShape :=
    { CreatesColimit :=
        { lifts := fun c _ =>
            { liftedCocone := mapCoconeInv H c
              validLift := mapCoconeMapCoconeInv H c } } }


-- verify the preserve_colimits instance works as expected:
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example (E : C ⥤ D) [E.IsEquivalence] (c : Cocone K) (h : IsColimit c) :
    IsColimit (E.mapCocone c) :=
  isColimitOfPreserves E h
/-
**CategoryTheory.Adjunction.hasColimit_comp_equivalence** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Adjunction`。
形式化陈述：hasColimit_comp_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimit K] :
 HasColimit (K ⋙ E)
参数：E : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.isEquivalence_preservesColimits`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   (E : CategoryTheor…
-/
theorem hasColimit_comp_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimit K] :
    HasColimit (K ⋙ E) :=
  HasColimit.mk
    { cocone := E.mapCocone (colimit.cocone K)
      isColimit := isColimitOfPreserves _ (colimit.isColimit K) }
/-
**CategoryTheory.Adjunction.hasColimit_of_comp_equivalence** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Adjunction`。
形式化陈述：hasColimit_of_comp_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimit (
K ⋙ E)] : HasColimit K
参数：E : C ⥤ D；K ⋙ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.hasColimit_iff_of_iso`：∀ {J : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.
{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Adjunction.hasColimit_comp_equivalence`：hasColimit_comp_e
quivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimit K] : HasColimit (K ⋙ E)
-/
theorem hasColimit_of_comp_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimit (K ⋙ E)] :
    HasColimit K := by
  rw [hasColimit_iff_of_iso
    ((Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft K E.asEquivalence.unitIso)]
  exact hasColimit_comp_equivalence (K ⋙ E) E.inv

/-- Transport a `HasColimitsOfShape` instance across an equivalence. -/
/-
**CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：hasColimitsOfShape_of_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimi
tsOfShape J D] : HasColimitsOfShape J C
参数：E : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.hasColimit_of_comp_equivalence`：hasColimit_of_
comp_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimit (K ⋙ E)] : HasColimit
 K
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
Transport a `HasColimitsOfShape` instance across an equivalence.
-/
theorem hasColimitsOfShape_of_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfShape J D] :
    HasColimitsOfShape J C :=
  ⟨fun F => hasColimit_of_comp_equivalence F E⟩

/-- Transport a `HasColimitsOfSize` instance across an equivalence. -/
/-
**CategoryTheory.Adjunction.has_colimits_of_equivalence** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Adjunction`。
形式化陈述：has_colimits_of_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfSi
ze.{v, u} D] : HasColimitsOfSize.{v, u} C
参数：E : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence`：hasColimits
OfShape_of_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfShape J D] : 
HasColimitsOfShape J C
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
Transport a `HasColimitsOfSize` instance across an equivalence.
-/
theorem has_colimits_of_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfSize.{v, u} D] :
    HasColimitsOfSize.{v, u} C :=
  ⟨fun _ _ => hasColimitsOfShape_of_equivalence E⟩

end PreservationColimits

section PreservationLimits

variable {J : Type u} [Category.{v} J] (K : J ⥤ D)

/-- The left adjoint of `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G)`.

Auxiliary definition for `functorialityAdjunction'`.
-/
/-
**CategoryTheory.Adjunction.functorialityLeftAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Adjunction`。
形式化陈述：functorialityLeftAdjoint : Cone (K ⋙ G) ⥤ Cone K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left adjoint of `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G)`.

Auxiliary definition for `functorialityAdjunction'`.
-/
def functorialityLeftAdjoint : Cone (K ⋙ G) ⥤ Cone K :=
  Cone.functoriality _ F ⋙
    Cone.postcompose ((associator _ _ _).hom ≫ whiskerLeft K adj.counit ≫ K.rightUnitor.hom)

attribute [local simp] functorialityLeftAdjoint

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit for the adjunction for `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G)`.

Auxiliary definition for `functorialityAdjunction'`.
-/
@[simps]
/-
**CategoryTheory.Adjunction.functorialityUnit'** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Adjunction`。
形式化陈述：functorialityUnit' : 𝟭 (Cone (K ⋙ G)) ⟶ functorialityLeftAdjoint adj K ⋙ C
one.functoriality _ G where app c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit for the adjunction for `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G)`
.

Auxiliary definition for `functorialityAdjunction'`.
-/
def functorialityUnit' :
    𝟭 (Cone (K ⋙ G)) ⟶ functorialityLeftAdjoint adj K ⋙ Cone.functoriality _ G where
  app c := { hom := adj.unit.app c.pt }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The counit for the adjunction for `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G)`.

Auxiliary definition for `functorialityAdjunction'`.
-/
@[simps]
/-
**CategoryTheory.Adjunction.functorialityCounit'** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Adjunction`。
形式化陈述：functorialityCounit' : Cone.functoriality _ G ⋙ functorialityLeftAdjoint a
dj K ⟶ 𝟭 (Cone K) where app c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit for the adjunction for `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G
)`.

Auxiliary definition for `functorialityAdjunction'`.
-/
def functorialityCounit' :
    Cone.functoriality _ G ⋙ functorialityLeftAdjoint adj K ⟶ 𝟭 (Cone K) where
  app c := { hom := adj.counit.app c.pt }

set_option backward.defeqAttrib.useBackward true in
/-- The functor `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G)` is a right adjoint. -/
/-
**CategoryTheory.Adjunction.functorialityAdjunction'** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Adjunction`。
形式化陈述：functorialityAdjunction' : functorialityLeftAdjoint adj K ⊣ Cone.functoria
lity K G where unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G)` is a right adjoint.
-/
def functorialityAdjunction' : functorialityLeftAdjoint adj K ⊣ Cone.functoriality K G where
  unit := functorialityUnit' adj K
  counit := functorialityCounit' adj K

include adj in
/-- A right adjoint preserves limits. -/
@[stacks 0038]
/-
**CategoryTheory.Adjunction.rightAdjoint_preservesLimits** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Adjunction`。
形式化陈述：rightAdjoint_preservesLimits : PreservesLimitsOfSize.{v, u} G where preser
vesLimitsOfShape
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A right adjoint preserves limits.
-/
lemma rightAdjoint_preservesLimits : PreservesLimitsOfSize.{v, u} G where
  preservesLimitsOfShape :=
    { preservesLimit :=
        { preserves := fun hc =>
            ⟨IsLimit.isoUniqueConeMorphism.inv fun _ =>
              @Equiv.unique _ _ (IsLimit.isoUniqueConeMorphism.hom hc _)
                ((adj.functorialityAdjunction' _).homEquiv _ _).symm⟩ } }
/-
**CategoryTheory.Adjunction.lim_preservesLimits** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Adjunction`。
形式化陈述：lim_preservesLimits [HasLimitsOfShape J C] : PreservesLimits (lim (J
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`：rightAdjoint_pre
servesLimits : PreservesLimitsOfSize.{v, u} G where preservesLimitsOfShape
-/
instance lim_preservesLimits [HasLimitsOfShape J C] :
    PreservesLimits (lim (J := J) (C := C)) :=
  constLimAdj.rightAdjoint_preservesLimits

-- see Note [lower instance priority]
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isEquivalencePreservesLimits
    (E : D ⥤ C) [E.IsEquivalence] :
    PreservesLimitsOfSize.{v, u} E :=
  rightAdjoint_preservesLimits E.asEquivalence.symm.toAdjunction

-- see Note [lower instance priority]
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (priority := 100)
    _root_.CategoryTheory.Functor.reflectsLimits_of_isEquivalence
    (E : D ⥤ C) [E.IsEquivalence] :
    ReflectsLimitsOfSize.{v, u} E where
  reflectsLimitsOfShape :=
    { reflectsLimit :=
        { reflects := fun t =>
            ⟨(isLimitOfPreserves E.inv t).mapConeEquiv E.asEquivalence.unitIso.symm⟩ } }

-- see Note [lower instance priority]
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (priority := 100)
    _root_.CategoryTheory.Functor.createsLimitsOfIsEquivalence (H : D ⥤ C) [H.IsEquivalence] :
    CreatesLimitsOfSize.{v, u} H where
  CreatesLimitsOfShape :=
    { CreatesLimit :=
        { lifts := fun c _ =>
            { liftedCone := mapConeInv H c
              validLift := mapConeMapConeInv H c } } }


-- verify the preserve_limits instance works as expected:
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example (E : D ⥤ C) [E.IsEquivalence] (c : Cone K) (h : IsLimit c) :
    IsLimit (E.mapCone c) :=
  isLimitOfPreserves E h
/-
**CategoryTheory.Adjunction.hasLimit_comp_equivalence** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：hasLimit_comp_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimit K] : Has
Limit (K ⋙ E)
参数：E : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.isEquivalencePreservesLimits`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   (E : CategoryTheor…
-/
theorem hasLimit_comp_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimit K] : HasLimit (K ⋙ E) :=
  HasLimit.mk
    { cone := E.mapCone (limit.cone K)
      isLimit := isLimitOfPreserves _ (limit.isLimit K) }
/-
**CategoryTheory.Adjunction.hasLimit_of_comp_equivalence** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Adjunction`。
形式化陈述：hasLimit_of_comp_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimit (K ⋙ 
E)] : HasLimit K
参数：E : D ⥤ C；K ⋙ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.hasLimit_iff_of_iso`：hasLimit_iff_of_iso {F G : J 
⥤ C} (α : F ≅ G) : HasLimit F ↔ HasLimit G
· 使用定理 `CategoryTheory.Adjunction.hasLimit_comp_equivalence`：hasLimit_comp_equiv
alence (E : D ⥤ C) [E.IsEquivalence] [HasLimit K] : HasLimit (K ⋙ E)
-/
theorem hasLimit_of_comp_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimit (K ⋙ E)] :
    HasLimit K := by
  rw [← hasLimit_iff_of_iso
    (isoWhiskerLeft K E.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor _)]
  exact hasLimit_comp_equivalence (K ⋙ E) E.inv

/-- Transport a `HasLimitsOfShape` instance across an equivalence. -/
/-
**CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：hasLimitsOfShape_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOf
Shape J C] : HasLimitsOfShape J D
参数：E : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.hasLimit_of_comp_equivalence`：hasLimit_of_comp
_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimit (K ⋙ E)] : HasLimit K
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
Transport a `HasLimitsOfShape` instance across an equivalence.
-/
theorem hasLimitsOfShape_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfShape J C] :
    HasLimitsOfShape J D :=
  ⟨fun F => hasLimit_of_comp_equivalence F E⟩

/-- Transport a `HasLimitsOfSize` instance across an equivalence. -/
/-
**CategoryTheory.Adjunction.has_limits_of_equivalence** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：has_limits_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfSize.{
v, u} C] : HasLimitsOfSize.{v, u} D
参数：E : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence`：hasLimitsOfSh
ape_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfShape J C] : HasLim
itsOfShape J D
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
Transport a `HasLimitsOfSize` instance across an equivalence.
-/
theorem has_limits_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfSize.{v, u} C] :
    HasLimitsOfSize.{v, u} D :=
  ⟨fun _ _ => hasLimitsOfShape_of_equivalence E⟩

end PreservationLimits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- auxiliary construction for `coconesIso` -/
@[simp]
/-
**CategoryTheory.Adjunction.coconesIsoComponentHom** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Adjunction`。
形式化陈述：coconesIsoComponentHom {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D) (
t : ((cocones J D).obj (op (K ⋙ F))).obj Y) : (G ⋙ (cocones J C).obj (op K)).obj
 Y where app j
参数：Y : D；t : ((cocones J D).obj (op (K ⋙ F))).obj Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
auxiliary construction for `coconesIso`
-/
def coconesIsoComponentHom {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D)
    (t : ((cocones J D).obj (op (K ⋙ F))).obj Y) : (G ⋙ (cocones J C).obj (op K)).obj Y where
  app j := (adj.homEquiv (K.obj j) Y) (t.app j)
  naturality j j' f := by
    rw [← adj.homEquiv_naturality_left, ← Functor.comp_map, t.naturality]
    simp

set_option backward.defeqAttrib.useBackward true in
/-- auxiliary construction for `coconesIso` -/
@[simp]
/-
**CategoryTheory.Adjunction.coconesIsoComponentInv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Adjunction`。
形式化陈述：coconesIsoComponentInv {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D) (
t : (G ⋙ (cocones J C).obj (op K)).obj Y) : ((cocones J D).obj (op (K ⋙ F))).obj
 Y where app j
参数：Y : D；t : (G ⋙ (cocones J C).obj (op K)).obj Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
auxiliary construction for `coconesIso`
-/
def coconesIsoComponentInv {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D)
    (t : (G ⋙ (cocones J C).obj (op K)).obj Y) : ((cocones J D).obj (op (K ⋙ F))).obj Y where
  app j := (adj.homEquiv (K.obj j) Y).symm (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm, t.naturality]
    simp

/-- auxiliary construction for `conesIso` -/
@[simp]
/-
**CategoryTheory.Adjunction.conesIsoComponentHom** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Adjunction`。
形式化陈述：conesIsoComponentHom {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ) (
t : (Functor.op F ⋙ (cones J D).obj K).obj X) : ((cones J C).obj (K ⋙ G)).obj X 
where app j
参数：X : Cᵒᵖ；t : (Functor.op F ⋙ (cones J D).obj K).obj X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
auxiliary construction for `conesIso`
-/
def conesIsoComponentHom {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
    (t : (Functor.op F ⋙ (cones J D).obj K).obj X) : ((cones J C).obj (K ⋙ G)).obj X where
  app j := (adj.homEquiv (unop X) (K.obj j)) (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_right, ← t.naturality, Category.id_comp, Category.id_comp]
    rfl

/-- auxiliary construction for `conesIso` -/
@[simp]
/-
**CategoryTheory.Adjunction.conesIsoComponentInv** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Adjunction`。
形式化陈述：conesIsoComponentInv {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ) (
t : ((cones J C).obj (K ⋙ G)).obj X) : (Functor.op F ⋙ (cones J D).obj K).obj X 
where app j
参数：X : Cᵒᵖ；t : ((cones J C).obj (K ⋙ G)).obj X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
auxiliary construction for `conesIso`
-/
def conesIsoComponentInv {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
    (t : ((cones J C).obj (K ⋙ G)).obj X) : (Functor.op F ⋙ (cones J D).obj K).obj X where
  app j := (adj.homEquiv (unop X) (K.obj j)).symm (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_right_symm, ← t.naturality, Category.id_comp, Category.id_comp]

end ArbitraryUniverse

variable {C : Type u₁} [Category.{v₀} C] {D : Type u₂} [Category.{v₀} D] {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G)

attribute [local simp] homEquiv_unit homEquiv_counit

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- Note: this is natural in K, but we do not yet have the tools to formulate that.
/-- When `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/
/-
**CategoryTheory.Adjunction.coconesIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Adjunction`。
形式化陈述：coconesIso {J : Type u} [Category.{v} J] {K : J ⥤ C} : (cocones J D).obj (
op (K ⋙ F)) ≅ G ⋙ (cocones J C).obj (op K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj 
Y`.
-/
def coconesIso {J : Type u} [Category.{v} J] {K : J ⥤ C} :
    (cocones J D).obj (op (K ⋙ F)) ≅ G ⋙ (cocones J C).obj (op K) :=
  NatIso.ofComponents fun Y =>
    { hom := ↾(coconesIsoComponentHom adj Y)
      inv := ↾(coconesIsoComponentInv adj Y) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- Note: this is natural in K, but we do not yet have the tools to formulate that.
/-- When `F ⊣ G`,
the functor associating to each `X` the cones over `K` with cone point `F.op.obj X`
is naturally isomorphic to
the functor associating to each `X` the cones over `K ⋙ G` with cone point `X`.
-/
/-
**CategoryTheory.Adjunction.conesIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.A
djunction`。
形式化陈述：conesIso {J : Type u} [Category.{v} J] {K : J ⥤ D} : F.op ⋙ (cones J D).ob
j K ≅ (cones J C).obj (K ⋙ G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F ⊣ G`,
the functor associating to each `X` the cones over `K` with cone point `F.op.obj
 X`
is naturally isomorphic to
the functor associating to each `X` the cones over `K ⋙ G` with cone point `X`.
-/
def conesIso {J : Type u} [Category.{v} J] {K : J ⥤ D} :
    F.op ⋙ (cones J D).obj K ≅ (cones J C).obj (K ⋙ G) :=
  NatIso.ofComponents fun X =>
    { hom := ↾(conesIsoComponentHom adj X)
      inv := ↾(conesIsoComponentInv adj X) }

end Adjunction

namespace Functor

variable {J C D : Type*} [Category* J] [Category* C] [Category* D]
  (F : C ⥤ D)

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [IsLeftAdjoint F] : PreservesColimitsOfShape J F :=
  (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits.preservesColimitsOfShape
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [IsLeftAdjoint F] : PreservesColimitsOfSize.{v, u} F where
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [IsRightAdjoint F] : PreservesLimitsOfShape J F :=
  (Adjunction.ofIsRightAdjoint F).rightAdjoint_preservesLimits.preservesLimitsOfShape
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [IsRightAdjoint F] : PreservesLimitsOfSize.{v, u} F where

end Functor

end CategoryTheory

