/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Presentable objects and adjunctions

If `adj : F ⊣ G` and `G` is `κ`-accessible for a regular cardinal `κ`,
then `F` preserves `κ`-presentable objects.

Moreover, if `G : D ⥤ C` is fully faithful, then `D` is locally `κ`-presentable
(resp `κ`-accessible) if `C` is.

In particular, if `e : C ≌ D` is an equivalence of categories and
`C` is locally presentable (resp. accessible), then so is `D`.

-/

public section

universe w v v' u u'

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (κ : Cardinal.{w}) [Fact κ.IsRegular]

include adj

/-
**CategoryTheory.Adjunction.isCardinalPresentable_leftAdjoint_obj** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：isCardinalPresentable_leftAdjoint_obj (X : C) [IsCardinalPresentable X κ] 
[G.IsCardinalAccessible κ] : IsCardinalPresentable (F.obj X) κ
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isCardinalPresentable_iff_isCardinalAccessible_uliftCoyon
eda_obj`：isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj : IsCa
rdinalPresentable X κ ↔ (uliftCoyoneda.{t}.obj (op X)).IsCardinalAcce…
· 使用引理 `CategoryTheory.Functor.isCardinalAccessible_of_natIso`：isCardinalAccessi
ble_of_natIso [F.IsCardinalAccessible κ] : G.IsCardinalAccessible κ where preser
vesColimitOfShape J _ hκ
· 使用定理 `CategoryTheory.Functor.instIsCardinalAccessibleComp`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (κ : Cardinal.{w})…
· 使用定理 `CategoryTheory.instIsCardinalAccessibleObjOppositeFunctorTypeUliftCoyone
daOpOfIsCardinalPresentable`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁
, u₁} C] (X : C) (κ : Cardinal.{w}) [inst_1 : Fact κ.IsRegular]   [CategoryTheor
y.IsCardi…
-/
lemma isCardinalPresentable_leftAdjoint_obj (X : C) [IsCardinalPresentable X κ]
    [G.IsCardinalAccessible κ] :
    IsCardinalPresentable (F.obj X) κ := by
  rw [isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{v}]
  exact Functor.isCardinalAccessible_of_natIso
    (show G ⋙ _ ≅ _ from (Adjunction.compUliftCoyonedaIso.{0} adj).symm.app (op X)) κ

variable {κ} in
/-
**CategoryTheory.Adjunction.isCardinalFilteredGenerator** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Adjunction`。
形式化陈述：isCardinalFilteredGenerator {P : ObjectProperty C} (hP : P.IsCardinalFilte
redGenerator κ) [G.IsCardinalAccessible κ] [G.Full] [G.Faithful] : (P.map F).IsC
ardinalFilteredGenerator κ where le_isCardinalPresentable
参数：hP : P.IsCardinalFilteredGenerator κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.le_isCardinalP
resentable`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Catego
ryTheory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isCardinalPresentable_iff`：isCardinalPresentable_iff (X :
 C) : isCardinalPresentable C κ X ↔ IsCardinalPresentable X κ
· 使用引理 `CategoryTheory.Adjunction.isCardinalPresentable_leftAdjoint_obj`：isCardi
nalPresentable_leftAdjoint_obj (X : C) [IsCardinalPresentable X κ] [G.IsCardinal
Accessible κ] : IsCardinalPresentable (F.obj X) κ
· 使用引理 `CategoryTheory.isCardinalPresentable_of_iso`：isCardinalPresentable_of_is
o [IsCardinalPresentable X κ] : IsCardinalPresentable Y κ
· 使用引理 `CategoryTheory.Adjunction.isLeftAdjoint`：isLeftAdjoint (adj : F ⊣ G) : F
.IsLeftAdjoint
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.exists_colimit
sOfShape`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Category
Theory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_isIso`：prop_of_isIso [IsClosedUnde
rIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f] (hX : P X) : P Y
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsColimitsOfSha
pe`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : Category
Theory.ObjectProperty C) (J : Type u')   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用引理 `CategoryTheory.ObjectProperty.prop_map_obj`：prop_map_obj (P : ObjectProp
erty C) (F : C ⥤ D) {X : C} (hX : P X) : P.map F (F.obj X)
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
-/
lemma isCardinalFilteredGenerator
    {P : ObjectProperty C} (hP : P.IsCardinalFilteredGenerator κ)
    [G.IsCardinalAccessible κ] [G.Full] [G.Faithful] :
    (P.map F).IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := by
    rintro Y ⟨X, hX, ⟨e⟩⟩
    have hX' := hP.le_isCardinalPresentable X hX
    rw [isCardinalPresentable_iff] at hX' ⊢
    have := adj.isCardinalPresentable_leftAdjoint_obj κ X
    exact isCardinalPresentable_of_iso e κ
  exists_colimitsOfShape Y := by
    have := adj.isLeftAdjoint
    obtain ⟨J, _, _, ⟨hY⟩⟩ := hP.exists_colimitsOfShape (G.obj Y)
    exact ⟨J, inferInstance, inferInstance,
      ObjectProperty.prop_of_isIso _ (adj.counit.app Y) ⟨{
        diag := _
        ι := _
        isColimit := isColimitOfPreserves F hY.isColimit
        prop_diag_obj j := P.prop_map_obj _ (hY.prop_diag_obj j) }⟩⟩
/-
**CategoryTheory.Adjunction.hasCardinalFilteredGenerator** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Adjunction`。
形式化陈述：hasCardinalFilteredGenerator [HasCardinalFilteredGenerator C κ] [G.IsCardi
nalAccessible κ] [G.Full] [G.Faithful] : HasCardinalFilteredGenerator D κ where 
toLocallySmall
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_faithful`：locallySmall_of_faithful {C : T
ype u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Faithful]
 [LocallySmall.{w} D] : Local…
· 使用定理 `CategoryTheory.HasCardinalFilteredGenerator.toLocallySmall`：∀ {C : Type 
u} {hC : CategoryTheory.Category.{v, u} C} (κ : Cardinal.{w}) {hκ : Fact κ.IsReg
ular}   [self : CategoryTheory.HasCardinalFilter…
· 使用定理 `CategoryTheory.HasCardinalFilteredGenerator.exists_generator`：∀ (C : Typ
e u) [hC : CategoryTheory.Category.{v, u} C] (κ : Cardinal.{w}) [hκ : Fact κ.IsR
egular]   [self : CategoryTheory.HasCardinalFilter…
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallMap`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.C
ategory.{v', u'} D]   (P : CategoryTheory.O…
· 使用引理 `CategoryTheory.Adjunction.isCardinalFilteredGenerator`：isCardinalFiltere
dGenerator {P : ObjectProperty C} (hP : P.IsCardinalFilteredGenerator κ) [G.IsCa
rdinalAccessible κ] [G.Full] [G.Faithful] :…
-/
lemma hasCardinalFilteredGenerator [HasCardinalFilteredGenerator C κ]
    [G.IsCardinalAccessible κ] [G.Full] [G.Faithful] :
    HasCardinalFilteredGenerator D κ where
  toLocallySmall := locallySmall_of_faithful G
  exists_generator := by
    obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
    exact ⟨P.map F, inferInstance, adj.isCardinalFilteredGenerator hP⟩
/-
**CategoryTheory.Adjunction.isCardinalLocallyPresentable** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Adjunction`。
形式化陈述：isCardinalLocallyPresentable [IsCardinalLocallyPresentable C κ] [G.IsCardi
nalAccessible κ] [G.Full] [G.Faithful] : IsCardinalLocallyPresentable D κ where 
toHasColimitsOfSize
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.hasCardinalFilteredGenerator`：hasCardinalFilte
redGenerator [HasCardinalFilteredGenerator C κ] [G.IsCardinalAccessible κ] [G.Fu
ll] [G.Faithful] : HasCardinalFilteredGenera…
· 使用定理 `CategoryTheory.IsCardinalAccessibleCategory.toHasCardinalFilteredGenerat
or`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {κ : Cardinal.{w}} 
{inst_1 : Fact κ.IsRegular}   [self : CategoryTheory.IsCardinalA…
· 使用定理 `CategoryTheory.instIsCardinalAccessibleCategoryOfIsCardinalLocallyPresen
table`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (κ : Cardinal.{w
}) [inst_1 : Fact κ.IsRegular]   [CategoryTheory.IsCardinalLocallyP…
· 使用定理 `CategoryTheory.hasColimits_of_reflective`：hasColimits_of_reflective (R :
 D ⥤ C) [Reflective R] [HasColimitsOfSize.{v, u} C] : HasColimitsOfSize.{v, u} D
· 使用定理 `CategoryTheory.IsCardinalLocallyPresentable.toHasColimitsOfSize`：∀ {C : 
Type u} {inst : CategoryTheory.Category.{v, u} C} (κ : Cardinal.{w}) {inst_1 : F
act κ.IsRegular}   [self : CategoryTheory.IsCardinalL…
-/
lemma isCardinalLocallyPresentable [IsCardinalLocallyPresentable C κ]
    [G.IsCardinalAccessible κ] [G.Full] [G.Faithful] :
    IsCardinalLocallyPresentable D κ where
  toHasColimitsOfSize :=
    letI : Reflective G := ⟨_, adj⟩
    hasColimits_of_reflective G
  toHasCardinalFilteredGenerator := adj.hasCardinalFilteredGenerator κ
/-
**CategoryTheory.Adjunction.isCardinalAccessibleCategory** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Adjunction`。
形式化陈述：isCardinalAccessibleCategory [IsCardinalAccessibleCategory C κ] [G.IsCardi
nalAccessible κ] [G.Full] [G.Faithful] : IsCardinalAccessibleCategory D κ where 
toHasCardinalFilteredColimits
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.hasCardinalFilteredGenerator`：hasCardinalFilte
redGenerator [HasCardinalFilteredGenerator C κ] [G.IsCardinalAccessible κ] [G.Fu
ll] [G.Faithful] : HasCardinalFilteredGenera…
· 使用定理 `CategoryTheory.IsCardinalAccessibleCategory.toHasCardinalFilteredGenerat
or`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {κ : Cardinal.{w}} 
{inst_1 : Fact κ.IsRegular}   [self : CategoryTheory.IsCardinalA…
· 使用定理 `CategoryTheory.HasCardinalFilteredColimits.hasColimitsOfShape`：∀ (C : Ty
pe u₁) {inst : CategoryTheory.Category.{v₁, u₁} C} (κ : Cardinal.{w}) {inst_1 : 
Fact κ.IsRegular}   [self : CategoryTheory.HasCardi…
· 使用定理 `CategoryTheory.IsCardinalAccessibleCategory.toHasCardinalFilteredColimit
s`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {κ : Cardinal.{w}} {
inst_1 : Fact κ.IsRegular}   [self : CategoryTheory.IsCardinalA…
· 使用定理 `CategoryTheory.hasColimitsOfShape_of_reflective`：hasColimitsOfShape_of_r
eflective (R : D ⥤ C) [Reflective R] [HasColimitsOfShape J C] : HasColimitsOfSha
pe J D where has_colimit
-/
lemma isCardinalAccessibleCategory [IsCardinalAccessibleCategory C κ]
    [G.IsCardinalAccessible κ] [G.Full] [G.Faithful] :
    IsCardinalAccessibleCategory D κ where
  toHasCardinalFilteredColimits := ⟨fun J _ _ ↦
    let : Reflective G := ⟨_, adj⟩
    have := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    hasColimitsOfShape_of_reflective G⟩
  toHasCardinalFilteredGenerator := adj.hasCardinalFilteredGenerator κ

end Adjunction

namespace Equivalence

variable (e : C ≌ D)

include e

section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-
**CategoryTheory.Equivalence.hasCardinalFilteredGenerator** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Equivalence`。
形式化陈述：hasCardinalFilteredGenerator [HasCardinalFilteredGenerator C κ] : HasCardi
nalFilteredGenerator D κ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.hasCardinalFilteredGenerator`：hasCardinalFilte
redGenerator [HasCardinalFilteredGenerator C κ] [G.IsCardinalAccessible κ] [G.Fu
ll] [G.Faithful] : HasCardinalFilteredGenera…
· 使用定理 `CategoryTheory.Functor.instIsCardinalAccessibleOfPreservesColimitsOfSize
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
lemma hasCardinalFilteredGenerator [HasCardinalFilteredGenerator C κ] :
    HasCardinalFilteredGenerator D κ :=
  e.toAdjunction.hasCardinalFilteredGenerator κ
/-
**CategoryTheory.Equivalence.isCardinalLocallyPresentable** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Equivalence`。
形式化陈述：isCardinalLocallyPresentable [IsCardinalLocallyPresentable C κ] : IsCardin
alLocallyPresentable D κ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isCardinalLocallyPresentable`：isCardinalLocall
yPresentable [IsCardinalLocallyPresentable C κ] [G.IsCardinalAccessible κ] [G.Fu
ll] [G.Faithful] : IsCardinalLocallyPresenta…
· 使用定理 `CategoryTheory.Functor.instIsCardinalAccessibleOfPreservesColimitsOfSize
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
lemma isCardinalLocallyPresentable [IsCardinalLocallyPresentable C κ] :
    IsCardinalLocallyPresentable D κ :=
  e.toAdjunction.isCardinalLocallyPresentable κ
/-
**CategoryTheory.Equivalence.isCardinalAccessibleCategory** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Equivalence`。
形式化陈述：isCardinalAccessibleCategory [IsCardinalAccessibleCategory C κ] : IsCardin
alAccessibleCategory D κ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isCardinalAccessibleCategory`：isCardinalAccess
ibleCategory [IsCardinalAccessibleCategory C κ] [G.IsCardinalAccessible κ] [G.Fu
ll] [G.Faithful] : IsCardinalAccessibleCateg…
· 使用定理 `CategoryTheory.Functor.instIsCardinalAccessibleOfPreservesColimitsOfSize
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
lemma isCardinalAccessibleCategory [IsCardinalAccessibleCategory C κ] :
    IsCardinalAccessibleCategory D κ :=
  e.toAdjunction.isCardinalAccessibleCategory κ

end

/-
**CategoryTheory.Equivalence.isLocallyPresentable** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Equivalence`。
形式化陈述：isLocallyPresentable [IsLocallyPresentable.{w} C] : IsLocallyPresentable.{
w} D
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsLocallyPresentable.exists_cardinal`：∀ (C : Type u) [hC 
: CategoryTheory.Category.{v, u} C] [self : CategoryTheory.IsLocallyPresentable.
{w, v, u} C],   ∃ κ, ∃ (x : Fact κ.IsRegu…
· 使用引理 `CategoryTheory.Equivalence.isCardinalLocallyPresentable`：isCardinalLocal
lyPresentable [IsCardinalLocallyPresentable C κ] : IsCardinalLocallyPresentable 
D κ
-/
lemma isLocallyPresentable [IsLocallyPresentable.{w} C] :
    IsLocallyPresentable.{w} D := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  exact ⟨κ, inferInstance, e.isCardinalLocallyPresentable κ⟩
/-
**CategoryTheory.Equivalence.isAccessibleCategory** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Equivalence`。
形式化陈述：isAccessibleCategory [IsAccessibleCategory.{w} C] : IsAccessibleCategory.{
w} D
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsAccessibleCategory.exists_cardinal`：∀ (C : Type u) [hC 
: CategoryTheory.Category.{v, u} C] [self : CategoryTheory.IsAccessibleCategory.
{w, v, u} C],   ∃ κ, ∃ (x : Fact κ.IsRegu…
· 使用引理 `CategoryTheory.Equivalence.isCardinalAccessibleCategory`：isCardinalAcces
sibleCategory [IsCardinalAccessibleCategory C κ] : IsCardinalAccessibleCategory 
D κ
-/
lemma isAccessibleCategory [IsAccessibleCategory.{w} C] :
    IsAccessibleCategory.{w} D := by
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  exact ⟨κ, inferInstance, e.isCardinalAccessibleCategory κ⟩

end Equivalence

end CategoryTheory

