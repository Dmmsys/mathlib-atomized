/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Constructions.WeaklyInitial
public import Mathlib.CategoryTheory.Subobject.Comma

/-!
# Adjoint functor theorem

This file proves the (general) adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` has limits, and satisfies the solution set condition,
  then it has a left adjoint: `isRightAdjoint_of_preservesLimits_of_solutionSetCondition`.

We show that the converse holds, i.e. that if `G` has a left adjoint then it satisfies the solution
set condition, see `solutionSetCondition_of_isRightAdjoint`
(the file `CategoryTheory/Adjunction/Limits` already shows it preserves limits).

We define the *solution set condition* for the functor `G : D ⥤ C` to mean, for every object
`A : C`, there is a set-indexed family ${f_i : A ⟶ G (B_i)}$ such that any morphism `A ⟶ G X`
factors through one of the `f_i`.

This file also proves the special adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` is complete, well-powered and has a small coseparating
  set, then `G` has a left adjoint: `isRightAdjoint_of_preservesLimits_of_isCoseparating`

Finally, we prove the following corollaries of the special adjoint functor theorem:
* If `C` is complete, well-powered and has a small coseparating set, then it is cocomplete:
  `hasColimits_of_hasLimits_of_isCoseparating`, `hasColimits_of_hasLimits_of_hasCoseparator`
* If `C` is cocomplete, co-well-powered and has a small separating set, then it is complete:
  `hasLimits_of_hasColimits_of_isSeparating`, `hasLimits_of_hasColimits_of_hasSeparator`

-/

@[expose] public section


universe w v v₁ u u₁ u'

namespace CategoryTheory

open Limits

variable {J : Type v}
variable {C : Type u} [Category.{v} C]

/-- The functor `G : D ⥤ C` satisfies the *solution set condition* if for every `A : C`, there is a
family of morphisms `{f_i : A ⟶ G (B_i) // i ∈ ι}` such that given any morphism `h : A ⟶ G X`,
there is some `i ∈ ι` such that `h` factors through `f_i`.

The key part of this definition is that the indexing set `ι` lives in `Type v`, where `v` is the
universe of morphisms of the category: this is the "smallness" condition which allows the general
adjoint functor theorem to go through.
-/
/-
**CategoryTheory.SolutionSetCondition** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：SolutionSetCondition {D : Type u₁} [Category.{v₁} D] (G : D ⥤ C) : Prop
参数：G : D ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `G : D ⥤ C` satisfies the *solution set condition* if for every `A :
 C`, there is a
family of morphisms `{f_i : A ⟶ G (B_i) // i ∈ ι}` such that given any morphism 
`h : A ⟶ G X`,
there is some `i ∈ ι` such that `h` factors through `f_i`.

The key part of this definition is that the indexing set `ι` lives in `Type v`, 
where `v` is the
universe of morphisms of the category: this is the "smallness" condition which a
llows the general
adjoint functor theorem to go through.
-/
def SolutionSetCondition {D : Type u₁} [Category.{v₁} D] (G : D ⥤ C) : Prop :=
  ∀ A : C,
    ∃ (ι : Type w) (B : ι → D) (f : ∀ i : ι, A ⟶ G.obj (B i)),
      ∀ (X) (h : A ⟶ G.obj X), ∃ (i : ι) (g : B i ⟶ X), f i ≫ G.map g = h

section GeneralAdjointFunctorTheorem

variable {D : Type u₁} [Category.{v₁} D]
variable (G : D ⥤ C)

/-- If `G : D ⥤ C` is a right adjoint it satisfies the solution set condition. -/
/-
**CategoryTheory.solutionSetCondition_of_isRightAdjoint** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory`。
形式化陈述：solutionSetCondition_of_isRightAdjoint [G.IsRightAdjoint] : SolutionSetCon
dition.{w} G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x

--- 原说明 ---
If `G : D ⥤ C` is a right adjoint it satisfies the solution set condition.
-/
theorem solutionSetCondition_of_isRightAdjoint [G.IsRightAdjoint] : SolutionSetCondition.{w} G := by
  intro A
  refine
    ⟨PUnit, fun _ => G.leftAdjoint.obj A, fun _ => (Adjunction.ofIsRightAdjoint G).unit.app A, ?_⟩
  intro B h
  refine ⟨PUnit.unit, ((Adjunction.ofIsRightAdjoint G).homEquiv _ _).symm h, ?_⟩
  rw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

/-- The general adjoint functor theorem says that if `G : D ⥤ C` preserves limits and `D` has them,
if `G` satisfies the solution set condition then `G` is a right adjoint.
-/
/-
**CategoryTheory.isRightAdjoint_of_preservesLimits_of_solutionSetCondition** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isRightAdjoint_of_preservesLimits_of_solutionSetCondition [HasLimits D] [P
reservesLimitsOfSize.{v₁, v₁} G] (hG : SolutionSetCondition.{v₁} G) : G.IsRightA
djoint
参数：hG : SolutionSetCondition.{v₁} G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isRightAdjointOfStructuredArrowInitials`：isRightAdjointOf
StructuredArrowInitials : G.IsRightAdjoint where exists_leftAdjoint
· 使用定理 `CategoryTheory.has_weakly_initial_of_weakly_initial_set_and_hasProducts`
：has_weakly_initial_of_weakly_initial_set_and_hasProducts [HasProducts.{v} C] {ι
 : Type v} {B : ι -> C} (hB : forall A : C, exists i, Nonempt…
· 使用定理 `CategoryTheory.StructuredArrow.hasLimitsOfShape`：∀ {J : Type w} [inst : 
CategoryTheory.Category.{w', w} J] {A : Type u₁} [inst_1 : CategoryTheory.Catego
ry.{v₁, u₁} A]   {T : Type u₃} [inst_…
· 使用定理 `CategoryTheory.Limits.hasProductsOfShape_of_hasProducts`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasProducts C] 
(J : Type w),   CategoryTheory.Limits.HasProd…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.hasInitial_of_weakly_initial_and_hasWideEqualizers`：hasIn
itial_of_weakly_initial_and_hasWideEqualizers [HasWideEqualizers.{v} C] {T : C} 
(hT : forall X, Nonempty (T ⟶ X)) : HasInitial C
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
The general adjoint functor theorem says that if `G : D ⥤ C` preserves limits an
d `D` has them,
if `G` satisfies the solution set condition then `G` is a right adjoint.
-/
lemma isRightAdjoint_of_preservesLimits_of_solutionSetCondition [HasLimits D]
    [PreservesLimitsOfSize.{v₁, v₁} G] (hG : SolutionSetCondition.{v₁} G) : G.IsRightAdjoint := by
  refine @isRightAdjointOfStructuredArrowInitials _ _ _ _ G ?_
  intro A
  specialize hG A
  choose ι B f g using hG
  let B' : ι → StructuredArrow A G := fun i => StructuredArrow.mk (f i)
  have hB' : ∀ A' : StructuredArrow A G, ∃ i, Nonempty (B' i ⟶ A') := by
    intro A'
    obtain ⟨i, _, t⟩ := g _ A'.hom
    exact ⟨i, ⟨StructuredArrow.homMk _ t⟩⟩
  obtain ⟨T, hT⟩ := has_weakly_initial_of_weakly_initial_set_and_hasProducts hB'
  apply hasInitial_of_weakly_initial_and_hasWideEqualizers hT

end GeneralAdjointFunctorTheorem

section SpecialAdjointFunctorTheorem

variable {D : Type u'} [Category.{v} D]

/-- The special adjoint functor theorem: if `G : D ⥤ C` preserves limits and `D` is complete,
well-powered and has a small coseparating set, then `G` has a left adjoint.
-/
/-
**CategoryTheory.isRightAdjoint_of_preservesLimits_of_isCoseparating** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isRightAdjoint_of_preservesLimits_of_isCoseparating [HasLimits D] [WellPow
ered.{v} D] {P : ObjectProperty D} [ObjectProperty.Small.{v} P] (hP : P.IsCosepa
rating) (G : D ⥤ C) [PreservesLimits G] : G.IsRightAdjoint
参数：hP : P.IsCoseparating；G : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.hasInitial_of_isCoseparating`：hasInitial_of_isCoseparatin
g [LocallySmall.{w} C] [WellPowered.{w} C] [HasLimitsOfSize.{w, w} C] {P : Objec
tProperty C} [ObjectProperty.Smal…
· 使用定理 `CategoryTheory.StructuredArrow.locallySmall`：∀ {B : Type u₂} {T : Type u
₃} [inst : CategoryTheory.Category.{v₂, u₂} B] [inst_1 : CategoryTheory.Category
.{v₃, u₃} T]   (S : T) (T_1 : Cat…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.StructuredArrow.isCoseparating_inverseImage_proj`：isCosep
arating_inverseImage_proj {P : ObjectProperty C} (hP : P.IsCoseparating) : (P.in
verseImage (proj S T)).IsCoseparating
· 使用引理 `CategoryTheory.isRightAdjointOfStructuredArrowInitials`：isRightAdjointOf
StructuredArrowInitials : G.IsRightAdjoint where exists_leftAdjoint

--- 原说明 ---
The special adjoint functor theorem: if `G : D ⥤ C` preserves limits and `D` is 
complete,
well-powered and has a small coseparating set, then `G` has a left adjoint.
-/
lemma isRightAdjoint_of_preservesLimits_of_isCoseparating [HasLimits D] [WellPowered.{v} D]
    {P : ObjectProperty D} [ObjectProperty.Small.{v} P]
    (hP : P.IsCoseparating) (G : D ⥤ C) [PreservesLimits G] :
    G.IsRightAdjoint := by
  have : ∀ A, HasInitial (StructuredArrow A G) := fun A ↦
    hasInitial_of_isCoseparating.{v} (StructuredArrow.isCoseparating_inverseImage_proj A G hP)
  exact isRightAdjointOfStructuredArrowInitials _

/-- The special adjoint functor theorem: if `F : C ⥤ D` preserves colimits and `C` is cocomplete,
well-copowered and has a small separating set, then `F` has a right adjoint.
-/
/-
**CategoryTheory.isLeftAdjoint_of_preservesColimits_of_isSeparating** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isLeftAdjoint_of_preservesColimits_of_isSeparating [HasColimits C] [WellPo
wered.{v} Cᵒᵖ] {P : ObjectProperty C} [ObjectProperty.Small.{v} P] (h𝒢 : P.IsSep
arating) (F : C ⥤ D) [PreservesColimits F] : F.IsLeftAdjoint
参数：h𝒢 : P.IsSeparating；F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instLocallySmallOpposite`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C],   CategoryT
heory.LocallySmall.{w, v, u} …
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.hasTerminal_of_isSeparating`：hasTerminal_of_isSeparating 
[LocallySmall.{w} Cᵒᵖ] [WellPowered.{w} Cᵒᵖ] [HasColimitsOfSize.{w, w} C] {P : O
bjectProperty C} [ObjectProperty…
· 使用定理 `CategoryTheory.CostructuredArrow.locallySmall`：∀ {A : Type u₁} {T : Type
 u₃} [inst : CategoryTheory.Category.{v₁, u₁} A] [inst_1 : CategoryTheory.Catego
ry.{v₃, u₃} T]   (S : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.CostructuredArrow.isSeparating_inverseImage_proj`：isSepar
ating_inverseImage_proj {P : ObjectProperty C} (hP : P.IsSeparating) : (P.invers
eImage (proj S T)).IsSeparating
· 使用引理 `CategoryTheory.isLeftAdjoint_of_costructuredArrowTerminals`：isLeftAdjoin
t_of_costructuredArrowTerminals : G.IsLeftAdjoint where exists_rightAdjoint

--- 原说明 ---
The special adjoint functor theorem: if `F : C ⥤ D` preserves colimits and `C` i
s cocomplete,
well-copowered and has a small separating set, then `F` has a right adjoint.
-/
lemma isLeftAdjoint_of_preservesColimits_of_isSeparating [HasColimits C] [WellPowered.{v} Cᵒᵖ]
    {P : ObjectProperty C} [ObjectProperty.Small.{v} P]
    (h𝒢 : P.IsSeparating) (F : C ⥤ D) [PreservesColimits F] :
    F.IsLeftAdjoint :=
  have : ∀ A, HasTerminal (CostructuredArrow F A) := fun A =>
    hasTerminal_of_isSeparating.{v} (CostructuredArrow.isSeparating_inverseImage_proj F A h𝒢)
  isLeftAdjoint_of_costructuredArrowTerminals _

end SpecialAdjointFunctorTheorem

namespace Limits

/-- A consequence of the special adjoint functor theorem: if `C` is complete, well-powered and
    has a small coseparating set, then it is cocomplete. -/
/-
**CategoryTheory.Limits.hasColimits_of_hasLimits_of_isCoseparating** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimits_of_hasLimits_of_isCoseparating [HasLimits C] [WellPowered.{v} 
C] {P : ObjectProperty C} [ObjectProperty.Small.{v} P] (hP : P.IsCoseparating) :
 HasColimits C
参数：hP : P.IsCoseparating。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_iff_isRightAdjoint_const`：hasCo
limitsOfShape_iff_isRightAdjoint_const : HasColimitsOfShape J C ↔ IsRightAdjoint
 (const J : C ⥤ _)
· 使用引理 `CategoryTheory.isRightAdjoint_of_preservesLimits_of_isCoseparating`：isRi
ghtAdjoint_of_preservesLimits_of_isCoseparating [HasLimits D] [WellPowered.{v} D
] {P : ObjectProperty D} [ObjectProperty.Small.{v} P] (h…

--- 原说明 ---
A consequence of the special adjoint functor theorem: if `C` is complete, well-p
owered and
    has a small coseparating set, then it is cocomplete.
-/
theorem hasColimits_of_hasLimits_of_isCoseparating [HasLimits C] [WellPowered.{v} C]
    {P : ObjectProperty C} [ObjectProperty.Small.{v} P] (hP : P.IsCoseparating) : HasColimits C :=
  { has_colimits_of_shape := fun _ _ =>
      hasColimitsOfShape_iff_isRightAdjoint_const.2
        (isRightAdjoint_of_preservesLimits_of_isCoseparating hP _) }

/-- A consequence of the special adjoint functor theorem: if `C` is cocomplete, well-copowered and
    has a small separating set, then it is complete. -/
/-
**CategoryTheory.Limits.hasLimits_of_hasColimits_of_isSeparating** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasLimits_of_hasColimits_of_isSeparating [HasColimits C] [WellPowered.{v} 
Cᵒᵖ] {P : ObjectProperty C} [ObjectProperty.Small.{v} P] (hP : P.IsSeparating) :
 HasLimits C
参数：hP : P.IsSeparating。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instLocallySmallOpposite`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C],   CategoryT
heory.LocallySmall.{w, v, u} …
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_iff_isLeftAdjoint_const`：hasLimit
sOfShape_iff_isLeftAdjoint_const : HasLimitsOfShape J C ↔ IsLeftAdjoint (const J
 : C ⥤ _)
· 使用引理 `CategoryTheory.isLeftAdjoint_of_preservesColimits_of_isSeparating`：isLef
tAdjoint_of_preservesColimits_of_isSeparating [HasColimits C] [WellPowered.{v} C
ᵒᵖ] {P : ObjectProperty C} [ObjectProperty.Small.{v} P]…

--- 原说明 ---
A consequence of the special adjoint functor theorem: if `C` is cocomplete, well
-copowered and
    has a small separating set, then it is complete.
-/
theorem hasLimits_of_hasColimits_of_isSeparating [HasColimits C] [WellPowered.{v} Cᵒᵖ]
    {P : ObjectProperty C} [ObjectProperty.Small.{v} P] (hP : P.IsSeparating) : HasLimits C :=
  { has_limits_of_shape := fun _ _ =>
      hasLimitsOfShape_iff_isLeftAdjoint_const.2
        (isLeftAdjoint_of_preservesColimits_of_isSeparating hP _) }

/-- A consequence of the special adjoint functor theorem: if `C` is complete, well-powered and
    has a separator, then it is complete. -/
/-
**CategoryTheory.Limits.hasLimits_of_hasColimits_of_hasSeparator** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasLimits_of_hasColimits_of_hasSeparator [HasColimits C] [HasSeparator C] 
[WellPowered.{v} Cᵒᵖ] : HasLimits C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instLocallySmallOpposite`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C],   CategoryT
heory.LocallySmall.{w, v, u} …
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.Limits.hasLimits_of_hasColimits_of_isSeparating`：hasLimit
s_of_hasColimits_of_isSeparating [HasColimits C] [WellPowered.{v} Cᵒᵖ] {P : Obje
ctProperty C} [ObjectProperty.Small.{v} P] (hP : P.I…
· 使用定理 `CategoryTheory.ObjectProperty.instSmallOfObjOfSmall`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {ι : Type u_1} (X : ι → C) [Small.{w, u_1}
 ι],   CategoryTheory.ObjectProperty.Smal…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.isSeparator_separator`：isSeparator_separator [HasSeparato
r C] : IsSeparator (separator C)

--- 原说明 ---
A consequence of the special adjoint functor theorem: if `C` is complete, well-p
owered and
    has a separator, then it is complete.
-/
theorem hasLimits_of_hasColimits_of_hasSeparator [HasColimits C] [HasSeparator C]
    [WellPowered.{v} Cᵒᵖ] : HasLimits C :=
  hasLimits_of_hasColimits_of_isSeparating <| isSeparator_separator C

/-- A consequence of the special adjoint functor theorem: if `C` is complete, well-powered and
    has a coseparator, then it is cocomplete. -/
/-
**CategoryTheory.Limits.hasColimits_of_hasLimits_of_hasCoseparator** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimits_of_hasLimits_of_hasCoseparator [HasLimits C] [HasCoseparator C
] [WellPowered.{v} C] : HasColimits C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.Limits.hasColimits_of_hasLimits_of_isCoseparating`：hasCol
imits_of_hasLimits_of_isCoseparating [HasLimits C] [WellPowered.{v} C] {P : Obje
ctProperty C} [ObjectProperty.Small.{v} P] (hP : P.IsC…
· 使用定理 `CategoryTheory.ObjectProperty.instSmallOfObjOfSmall`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {ι : Type u_1} (X : ι → C) [Small.{w, u_1}
 ι],   CategoryTheory.ObjectProperty.Smal…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.isCoseparator_coseparator`：isCoseparator_coseparator [Has
Coseparator C] : IsCoseparator (coseparator C)

--- 原说明 ---
A consequence of the special adjoint functor theorem: if `C` is complete, well-p
owered and
    has a coseparator, then it is cocomplete.
-/
theorem hasColimits_of_hasLimits_of_hasCoseparator [HasLimits C] [HasCoseparator C]
    [WellPowered.{v} C] : HasColimits C :=
  hasColimits_of_hasLimits_of_isCoseparating <| isCoseparator_coseparator C

end Limits

end CategoryTheory

