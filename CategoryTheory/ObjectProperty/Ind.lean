/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Presentable.ColimitPresentation
public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct

/-!
# Ind and pro-properties

Given an object property `P`, we define an object property `ind P` that is satisfied for
`X` if `X` is a filtered colimit of `Xᵢ` and `Xᵢ` satisfies `P`.

## Main definitions

- `CategoryTheory.ObjectProperty.ind`: `X` satisfies `ind P` if `X` is a filtered colimit of `Xᵢ`
  for `Xᵢ` in `P`.

## Main results

- `CategoryTheory.ObjectProperty.ind_ind`: If `P` implies finitely presentable, then
  `P.ind.ind = P.ind`.

## TODOs:

- Dualise to obtain `CategoryTheory.ObjectProperty.pro`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.ObjectProperty

open Limits Opposite

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

/-- `X` satisfies `ind P` if `X` is a filtered colimit of `Xᵢ` for `Xᵢ` in `P`. -/
/-
**CategoryTheory.ObjectProperty.ind** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ob
jectProperty`。
形式化陈述：ind (P : ObjectProperty C) : ObjectProperty C
参数：P : ObjectProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X` satisfies `ind P` if `X` is a filtered colimit of `Xᵢ` for `Xᵢ` in `P`.
-/
def ind (P : ObjectProperty C) : ObjectProperty C :=
  fun X ↦ ∃ (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J)
    (pres : ColimitPresentation J X), ∀ i, P (pres.diag.obj i)

variable (P) in
/-
**CategoryTheory.ObjectProperty.le_ind** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ObjectProperty`。
形式化陈述：le_ind : P <= ind.{w} P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isFiltered_of_directed_le_nonempty`：∀ (α : Type u) [inst 
: Preorder α] [IsDirectedOrder α] [Nonempty α], CategoryTheory.IsFiltered α
· 使用定理 `OrderTop.instIsDirectedOrder`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.ColimitPresentation.self_diag`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] (X : C),   (CategoryTheory.Limits.ColimitP
resentation.self X).diag = (CategoryTheor…
-/
lemma le_ind : P ≤ ind.{w} P := by
  intro X hX
  exact ⟨PUnit, inferInstance, inferInstance, .self X, by simpa⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.Nonempty] : (ind.{w} P).Nonempty := .mono P.le_ind
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.ind.IsClosedUnderIsomorphisms where
  of_iso {X Y} e := fun ⟨J, _, _, pres, h⟩ ↦ ⟨J, ‹_›, ‹_›, pres.ofIso e, h⟩

/-- `ind` is idempotent if `P` implies finitely presentable. -/
/-
**CategoryTheory.ObjectProperty.ind_ind** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ObjectProperty`。
形式化陈述：ind_ind (h : P <= isFinitelyPresentable.{w} C) [LocallySmall.{w} C] : ind.
{w} (ind.{w} P) = ind.{w} P
参数：h : P <= isFinitelyPresentable.{w} C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.Limits.ColimitPresentation.instLocallySmallTotal`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u_1} {I : J → Type u
_2}   [inst_1 : CategoryTheory.Category.{v_1, u_1} J]…
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
· 使用定理 `CategoryTheory.Limits.ColimitPresentation.instIsFilteredTotalOfIsFinitel
yPresentableObjDiag`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J
 : Type w} {I : J → Type w}   [inst_1 : CategoryTheory.SmallCategory J] [inst_2 
:…
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ShrinkHoms.equivalence_inverse`：∀ (C : Type u) [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.LocallySmall.{w, v, u} 
C],   (CategoryTheory.ShrinkHoms.eq…
· 使用定理 `CategoryTheory.Limits.ColimitPresentation.reindex.congr_simp`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : CategoryTh
eory.Category.{t, w} J]   {X : C} (P P_1 : Categor…
· 使用定理 `CategoryTheory.Limits.ColimitPresentation.reindex_diag`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : CategoryTheory.C
ategory.{t, w} J]   {X : C} (P : CategoryThe…
· 使用定理 `CategoryTheory.ShrinkHoms.inverse_obj`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.LocallySmall.{w, v, u} C]   (X 
: CategoryTheory.ShrinkHoms…
· 使用定理 `CategoryTheory.Limits.ColimitPresentation.bind_diag_obj`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {J : Type w} {I : J → Type w}   [inst_
1 : CategoryTheory.SmallCategory J] [inst_2 :…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `CategoryTheory.ObjectProperty.le_ind`：le_ind : P <= ind.{w} P

--- 原说明 ---
`ind` is idempotent if `P` implies finitely presentable.
-/
lemma ind_ind (h : P ≤ isFinitelyPresentable.{w} C) [LocallySmall.{w} C] :
    ind.{w} (ind.{w} P) = ind.{w} P := by
  refine le_antisymm (fun X h ↦ ?_) (le_ind P.ind)
  choose J Jc Jf pres K Kc Kf pres' hp using h
  have (j : J) (i : K j) : IsFinitelyPresentable ((pres' j).diag.obj i) := h _ (hp _ _)
  have := IsFiltered.of_equivalence (ShrinkHoms.equivalence (ColimitPresentation.Total pres'))
  exact ⟨_, inferInstance, inferInstance,
    (pres.bind pres').reindex (ShrinkHoms.equivalence _).inverse, fun k ↦ by simp [hp]⟩
/-
**CategoryTheory.ObjectProperty.of_essentiallySmall_index** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：of_essentiallySmall_index {X : C} {J : Type*} [Category* J] [EssentiallySm
all.{w} J] [IsFiltered J] (pres : ColimitPresentation J X) (h : forall i, P (pre
s.diag.obj i)) : ind.{w} P X
参数：pres : ColimitPresentation J X；h : forall i, P (pres.diag.obj i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
lemma of_essentiallySmall_index {X : C} {J : Type*} [Category* J] [EssentiallySmall.{w} J]
    [IsFiltered J] (pres : ColimitPresentation J X) (h : ∀ i, P (pres.diag.obj i)) :
    ind.{w} P X :=
  ⟨SmallModel J, inferInstance, .of_equivalence (equivSmallModel _),
    pres.reindex (equivSmallModel _).inverse, fun _ ↦ h _⟩

/-- If `C` is finitely accessible and `P` implies finitely presentable, then `X`
satisfies `ind P` if and only if every morphism `Z ⟶ X` from a finitely presentable object
factors via an object satisfying `P`. -/
/-
**CategoryTheory.ObjectProperty.ind_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：ind_iff_exists (H : P <= isFinitelyPresentable.{w} C) [IsFinitelyAccessibl
eCategory.{w} C] {X : C} : ind.{w} P X ↔ forall {Z : C} (g : Z ⟶ X) [IsFinitelyP
resentable.{w} Z], exists (W : C) (u : Z ⟶ W) (v : W ⟶ X), u ≫ v = g ∧ P W
参数：H : P <= isFinitelyPresentable.{w} C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : CategoryTh
eory.SmallCategory J]   [CategoryTheory.IsFiltered…
· 使用定理 `CategoryTheory.instIsFinitelyPresentableObjFullSubcategoryIsFinitelyPres
entableι`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   (X : (Categ
oryTheory.ObjectProperty.isFinitelyPresentable C).FullSubcategory),   …
· 使用定理 `CategoryTheory.Functor.final_of_exists_of_isFiltered_of_fullyFaithful`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.IsFinitelyAccessibleCategory.instIsFilteredCostructuredAr
rowFullSubcategoryIsFinitelyPresentableι`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] [CategoryTheory.IsFinitelyAccessibleCategory C] (X : C),   Ca
tegoryTheory.IsFiltere…
· 使用定理 `CategoryTheory.CostructuredArrow.instFullCompPre`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   {B : Type u₄} [ins…
· 使用定理 `CategoryTheory.CostructuredArrow.instFaithfulCompPre`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   {B : Type u₄} [ins…
· 使用定理 `CategoryTheory.IsFiltered.of_exists_of_isFiltered_of_fullyFaithful`：∀ {C
 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : 
CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsDenseAt.of_final`：∀ {C : Type u₁} {D : Type u₂}
 [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsDense.isDenseAt`：∀ {C : Type u₁} {D : Type u₂} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v
₂, u₂} D}   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFinitelyAccessibleCategory.instIsDenseFullSubcategoryIs
FinitelyPresentableι`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [
CategoryTheory.IsFinitelyAccessibleCategory C],   (CategoryTheory.ObjectProperty
.i…
· 使用定理 `CategoryTheory.essentiallySmall_of_fully_faithful`：essentiallySmall_of_f
ully_faithful {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Full] [F.Faithful] 
[EssentiallySmall.{w} D] : EssentiallyS…
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallFullSubcategoryOfLocal
lySmallOfEssentiallySmall_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, 
u} C] (P : CategoryTheory.ObjectProperty C)   [CategoryTheory.LocallySmall.{w, v
, u} C] […
· 使用定理 `CategoryTheory.HasCardinalFilteredGenerator.toLocallySmall`：∀ {C : Type 
u} {hC : CategoryTheory.Category.{v, u} C} (κ : Cardinal.{w}) {hκ : Fact κ.IsReg
ular}   [self : CategoryTheory.HasCardinalFilter…
· 使用引理 `Cardinal.fact_isRegular_aleph0`：fact_isRegular_aleph0 : Fact (IsRegular 
ℵ₀) where out
· 使用定理 `CategoryTheory.IsCardinalAccessibleCategory.toHasCardinalFilteredGenerat
or`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {κ : Cardinal.{w}} 
{inst_1 : Fact κ.IsRegular}   [self : CategoryTheory.IsCardinalA…
· 使用定理 `CategoryTheory.IsFinitelyAccessibleCategory.instEssentiallySmallIsFinite
lyPresentable`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [Categor
yTheory.IsFinitelyAccessibleCategory C],   CategoryTheory.ObjectProperty.Es…
· 使用引理 `CategoryTheory.ObjectProperty.of_essentiallySmall_index`：of_essentiallyS
mall_index {X : C} {J : Type*} [Category* J] [EssentiallySmall.{w} J] [IsFiltere
d J] (pres : ColimitPresentation J X) (h : fo…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj

--- 原说明 ---
If `C` is finitely accessible and `P` implies finitely presentable, then `X`
satisfies `ind P` if and only if every morphism `Z ⟶ X` from a finitely presenta
ble object
factors via an object satisfying `P`.
-/
lemma ind_iff_exists (H : P ≤ isFinitelyPresentable.{w} C)
    [IsFinitelyAccessibleCategory.{w} C] {X : C} :
    ind.{w} P X ↔ ∀ {Z : C} (g : Z ⟶ X) [IsFinitelyPresentable.{w} Z],
      ∃ (W : C) (u : Z ⟶ W) (v : W ⟶ X), u ≫ v = g ∧ P W := by
  refine ⟨fun ⟨J, _, _, pres, h⟩ Z g hZ ↦ ?_, fun hfac ↦ ?_⟩
  · have : IsFinitelyPresentable Z := hZ
    obtain ⟨j, u, hcomp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit g
    exact ⟨_, u, pres.ι.app j, hcomp, h j⟩
  · let incl : P.FullSubcategory ⥤ (isFinitelyPresentable.{w} C).FullSubcategory :=
      ObjectProperty.ιOfLE H
    have H (d : CostructuredArrow (isFinitelyPresentable.{w} C).ι X) : ∃ c,
        Nonempty (d ⟶ (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X).obj c) := by
      obtain ⟨W, u, v, huv, hW⟩ := hfac d.hom
      exact ⟨CostructuredArrow.mk (Y := FullSubcategory.mk _ hW) v,
        ⟨CostructuredArrow.homMk ⟨u⟩ huv⟩⟩
    have : (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X).Final :=
      Functor.final_of_exists_of_isFiltered_of_fullyFaithful (C := CostructuredArrow (incl ⋙ _) X)
        (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X) H
    have : IsFiltered (CostructuredArrow P.ι X) :=
      .of_exists_of_isFiltered_of_fullyFaithful (C := CostructuredArrow (incl ⋙ _) X)
        (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X) H
    obtain ⟨hc⟩ : P.ι.isDenseAt X :=
      Functor.IsDenseAt.of_final (F := (isFinitelyPresentable.{w} C).ι) incl
        (Functor.IsDense.isDenseAt _ _)
    have : EssentiallySmall.{w} (CostructuredArrow P.ι X) :=
      essentiallySmall_of_fully_faithful (C := CostructuredArrow (incl ⋙ _) X)
        (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X)
    exact of_essentiallySmall_index ⟨_, _, hc⟩ fun Y ↦ Y.left.2

section

variable {D : Type*} [Category D] (P : ObjectProperty D) (F : C ⥤ D)

/-
**CategoryTheory.ObjectProperty.ind_inverseImage_le** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：ind_inverseImage_le [PreservesFilteredColimitsOfSize.{w, w} F] : ind.{w} (
P.inverseImage F) <= (ind.{w} P).inverseImage F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
lemma ind_inverseImage_le [PreservesFilteredColimitsOfSize.{w, w} F] :
    ind.{w} (P.inverseImage F) ≤ (ind.{w} P).inverseImage F := by
  intro X ⟨J, _, _, pres, h⟩
  simp only [prop_inverseImage_iff]
  use J, inferInstance, inferInstance, pres.map F, h
/-
**CategoryTheory.ObjectProperty.ind_inverseImage_eq_of_isEquivalence** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：ind_inverseImage_eq_of_isEquivalence [P.IsClosedUnderIsomorphisms] [F.IsEq
uivalence] : ind.{w} (P.inverseImage F) = (ind.{w} P).inverseImage F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.ind_inverseImage_le`：ind_inverseImage_le [
PreservesFilteredColimitsOfSize.{w, w} F] : ind.{w} (P.inverseImage F) <= (ind.{
w} P).inverseImage F
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFilteredColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
-/
lemma ind_inverseImage_eq_of_isEquivalence [P.IsClosedUnderIsomorphisms] [F.IsEquivalence] :
    ind.{w} (P.inverseImage F) = (ind.{w} P).inverseImage F := by
  refine le_antisymm (ind_inverseImage_le _ _) fun X ⟨J, _, _, pres, h⟩ ↦ ?_
  refine ⟨J, ‹_›, ‹_›, .ofIso (pres.map F.asEquivalence.inverse) ?_, fun j ↦ ?_⟩
  · exact (F.asEquivalence.unitIso.app X).symm
  · exact P.prop_of_iso ((F.asEquivalence.counitIso.app _).symm) (h j)
/-
**CategoryTheory.ObjectProperty.ind_iff_of_equivalence** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：ind_iff_of_equivalence (e : C ≌ D) [P.IsClosedUnderIsomorphisms] (X : D) :
 ind.{w} (P.inverseImage e.functor) (e.inverse.obj X) ↔ ind.{w} P X
参数：e : C ≌ D；X : D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
-/
lemma ind_iff_of_equivalence (e : C ≌ D) [P.IsClosedUnderIsomorphisms] (X : D) :
    ind.{w} (P.inverseImage e.functor) (e.inverse.obj X) ↔ ind.{w} P X := by
  dsimp only [ObjectProperty.ind]
  congr!
  refine ⟨fun ⟨pres, h⟩ ↦ ?_, fun ⟨pres, h⟩ ↦ ?_⟩
  · exact ⟨.ofIso (pres.map e.functor) (e.counitIso.app X), fun i ↦ h i⟩
  · exact ⟨pres.map e.inverse, fun i ↦ P.prop_of_iso ((e.counitIso.app _).symm) (h i)⟩

end

section Products

/-
**CategoryTheory.ObjectProperty.ind_pi_of_ind** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ind_pi_of_ind {ι : Type w} [P.IsClosedUnderLimitsOfShape (Discrete ι)]
    [HasProductsOfShape ι C] [IsIPCOfShape.{w} ι C] {X : ι → C} (hc : ∀ i, ind.{w} P (X i)) :
    ind.{w} P (∏ᶜ X) := by
  choose J _ _ pres hpres using hc
  obtain ⟨hc⟩ := IsIPCOfShape.nonempty_isColimit fun i ↦ (pres i).isColimit
  exact ⟨∀ j, J j, inferInstance, inferInstance,
    { diag := _, ι := _, isColimit := hc }, fun i ↦ P.prop_limit _ fun a ↦ hpres a.1 _⟩
/-
**CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_ind_discrete** 是 Math
lib 中的一个实例，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderLimitsOfShape_ind_discrete {ι : Type*} [Small.{w} ι] [P.IsClo
sedUnderLimitsOfShape (Discrete ι)] [HasProductsOfShape ι C] [IsIPCOfShape.{w} ι
 C] : (ind.{w} P).IsClosedUnderLimitsOfShape (Discrete ι)
参数：Discrete ι。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape.mk'`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectP
roperty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsInd`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectPrope
rty C},   P.ind.IsClosedUnderIsomorphisms
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.IsIPCOfShape.of_equiv`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] {ι : Type u_2}   [inst_1 : CategoryTheory.Li
mits.HasProductsOfShape ι C] {ι' …
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape.of_equivalence`
：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryThe
ory.ObjectProperty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.prop_iff_of_iso`：prop_iff_of_iso [IsClosed
UnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y
· 使用定理 `_private.Mathlib.CategoryTheory.ObjectProperty.Ind.0.CategoryTheory.Obje
ctProperty.ind_pi_of_ind`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} 
C] {P : CategoryTheory.ObjectProperty C} {ι : Type w}   [P.IsClosedUnderLimitsOf
Shape …
-/
instance isClosedUnderLimitsOfShape_ind_discrete {ι : Type*} [Small.{w} ι]
    [P.IsClosedUnderLimitsOfShape (Discrete ι)] [HasProductsOfShape ι C] [IsIPCOfShape.{w} ι C] :
    (ind.{w} P).IsClosedUnderLimitsOfShape (Discrete ι) := by
  refine .mk' fun X ⟨Y, h⟩ ↦ ?_
  let e := equivShrink ι
  have : HasProductsOfShape (Shrink.{w} ι) C :=
    hasLimitsOfShape_of_equivalence (Discrete.equivalence e)
  have : IsIPCOfShape.{w} (Shrink.{w} ι) C := .of_equiv e
  have : P.IsClosedUnderLimitsOfShape (Discrete (Shrink.{w} ι)) :=
    .of_equivalence (Discrete.equivalence e)
  let iso : limit Y ≅ ∏ᶜ fun i ↦ Y.obj ⟨e.symm i⟩ :=
    (Pi.isoLimit _).symm ≪≫ (Pi.reindex e.symm _).symm
  rw [(ind.{w} P).prop_iff_of_iso iso]
  exact ind_pi_of_ind fun i ↦ h _

end Products

end CategoryTheory.ObjectProperty

