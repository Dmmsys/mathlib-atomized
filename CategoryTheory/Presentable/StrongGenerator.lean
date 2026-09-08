/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Locally presentable categories and strong generators

In this file, we show that a category is locally `κ`-presentable iff
it is cocomplete and has a strong generator consisting of `κ`-presentable objects.
This is theorem 1.20 in the book by Adámek and Rosický.

In particular, if a category is locally `κ`-presentable, it is also
locally `κ'`-presentable for any regular cardinal `κ'` such that `κ ≤ κ'`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

public section

universe w v' v u' u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

variable (κ) in
/-
**CategoryTheory.IsCardinalFilteredGenerator.of_isDense** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.IsCardinalFilteredGenerator`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
ocallySmall.{w, v, u} C] {J : Type u'}   [inst_2 : CategoryTheory.Category.{v', 
u'} J] [CategoryTheory.EssentiallySmall.{w, v', u'} J]   (F : CategoryTheory.Fun
ctor J C) [F.IsDense] (κ : Cardinal.{w}) [inst_5 : Fact κ.IsRegular]   [∀ (j : J
), CategoryTheory.IsCardinalPresentable (F.obj j) κ]   [∀ (X : C), CategoryTheor
y.IsCardinalFiltered (CategoryTheory.CostructuredArrow F X) κ],   (⊤.map F).IsCa
rdinalFilteredGenerator κ
参数：F : CategoryTheory.Functor J C；κ : Cardinal.{w}；j : J；F.obj j；X : C；CategoryT
heory.CostructuredArrow F X；⊤.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isCardinalPresentable_of_iso`：isCardinalPresentable_of_is
o [IsCardinalPresentable X κ] : IsCardinalPresentable Y κ
· 使用引理 `CategoryTheory.IsCardinalFiltered.of_equivalence`：of_equivalence {J' : T
ype u'} [Category.{v'} J'] (e : J ≌ J') : IsCardinalFiltered J' κ where nonempty
_cocone F hA
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CostructuredArrow.proj_obj`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   (S : CategoryTheor…
-/
lemma IsCardinalFilteredGenerator.of_isDense
    [LocallySmall.{w} C] {J : Type u'} [Category.{v'} J] [EssentiallySmall.{w} J]
    (F : J ⥤ C) [F.IsDense] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ j, IsCardinalPresentable (F.obj j) κ]
    [∀ (X : C), IsCardinalFiltered (CostructuredArrow F X) κ] :
    ((⊤ : ObjectProperty J).map F).IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := by
    rintro X ⟨Y, hY, ⟨e⟩⟩
    exact isCardinalPresentable_of_iso e κ
  exists_colimitsOfShape X := by
    have ip := F.denseAt X
    let e := equivSmallModel.{w} (CostructuredArrow F X)
    exact ⟨SmallModel.{w} (CostructuredArrow F X), inferInstance,
      IsCardinalFiltered.of_equivalence κ e,
      ⟨{  diag := _
          ι := _
          isColimit := (F.denseAt X).whiskerEquivalence e.symm
          prop_diag_obj j := ⟨_, by simp, ⟨Iso.refl _⟩⟩ }⟩⟩

variable (κ) in
/-
**CategoryTheory.IsCardinalFilteredGenerator.of_isDense_** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsCardinalFilteredGenerator.of_isDense_ι
    (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{w} P]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [P.ι.IsDense]
    [LocallySmall.{w} C]
    (hP : P ≤ isCardinalPresentable C κ)
    [∀ (X : C), IsCardinalFiltered (CostructuredArrow P.ι X) κ] :
    P.IsCardinalFilteredGenerator κ := by
  rw [← ObjectProperty.IsCardinalFilteredGenerator.isoClosure_iff]
  have (X : P.FullSubcategory) : IsCardinalPresentable (P.ι.obj X) κ := hP _ X.property
  simpa using IsCardinalFilteredGenerator.of_isDense P.ι κ
/-
**CategoryTheory.ObjectProperty.isCardinalFiltered_costructuredArrow_colimitsCar
dinalClosure_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ObjectProperty.isCardinalFiltered_costructuredArrow_colimitsCardinalClosure_ι
    (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasColimitsOfSize.{w, w} C] (X : C) :
    IsCardinalFiltered (CostructuredArrow (P.colimitsCardinalClosure κ).ι X) κ where
  nonempty_cocone {J} _ K hJ := ⟨by
    have := ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure P κ J hJ
    exact colimit.cocone K⟩
/-
**CategoryTheory.ObjectProperty.isFiltered_costructuredArrow_colimitsCardinalClo
sure_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ObjectProperty.isFiltered_costructuredArrow_colimitsCardinalClosure_ι
    (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasColimitsOfSize.{w, w} C] (X : C) :
    IsFiltered (CostructuredArrow (P.colimitsCardinalClosure κ).ι X) :=
  isFiltered_of_isCardinalFiltered _ κ

variable {κ : Cardinal.{w}} [Fact κ.IsRegular]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.IsStrongGenerator.isDense_colimitsCardinalClosur
e_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ObjectProperty.IsStrongGenerator.isDense_colimitsCardinalClosure_ι
    [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
    {P : ObjectProperty C} [ObjectProperty.Small.{w} P] (hS₁ : P.IsStrongGenerator)
    (hS₂ : P ≤ isCardinalPresentable C κ) :
    (P.colimitsCardinalClosure κ).ι.IsDense where
  isDenseAt X := by
    let E := Functor.LeftExtension.mk _ (P.colimitsCardinalClosure κ).ι.rightUnitor.inv
    have : HasColimitsOfShape (CostructuredArrow (P.colimitsCardinalClosure κ).ι X) C :=
      hasColimitsOfShape_of_equivalence
        (equivSmallModel.{w} (CostructuredArrow (P.colimitsCardinalClosure κ).ι X)).symm
    have : Mono (colimit.desc _ (E.coconeAt X)) := by
      let Φ := CostructuredArrow.proj (P.colimitsCardinalClosure κ).ι X ⋙
        (P.colimitsCardinalClosure κ).ι
      rw [hS₁.isSeparating.mono_iff]
      intro G hG (g₁ : G ⟶ colimit Φ) (g₂ : G ⟶ colimit Φ)
        (h : g₁ ≫ colimit.desc Φ (E.coconeAt X) = g₂ ≫ colimit.desc Φ (E.coconeAt X))
      have : IsCardinalPresentable G κ := hS₂ _ hG
      obtain ⟨j, φ₁, φ₂, rfl, rfl⟩ :
          ∃ (j : CostructuredArrow (P.colimitsCardinalClosure κ).ι X)
            (φ₁ φ₂ : G ⟶ Φ.obj j), φ₁ ≫ colimit.ι _ _ = g₁ ∧ φ₂ ≫ colimit.ι _ _ = g₂ := by
        obtain ⟨j₁, f₁, hf₁⟩ :=
          IsCardinalPresentable.exists_hom_of_isColimit κ (colimit.isColimit _) g₁
        obtain ⟨j₂, f₂, hf₂⟩ :=
          IsCardinalPresentable.exists_hom_of_isColimit κ (colimit.isColimit _) g₂
        exact ⟨IsFiltered.max j₁ j₂, f₁ ≫ Φ.map (IsFiltered.leftToMax j₁ j₂),
          f₂ ≫ Φ.map (IsFiltered.rightToMax j₁ j₂), by simpa, by simpa⟩
      have : (P.colimitsCardinalClosure κ).IsClosedUnderColimitsOfShape WalkingParallelPair := by
        apply ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure
        refine .of_le ?_ (Cardinal.IsRegular.aleph0_le Fact.out)
        simp only [hasCardinalLT_aleph0_iff]
        infer_instance
      let obj : (P.colimitsCardinalClosure κ).FullSubcategory :=
        ⟨coequalizer φ₁ φ₂, by
          apply ObjectProperty.prop_colimit
          rintro (_ | _)
          · exact P.le_colimitsCardinalClosure _ _ hG
          · exact j.left.2⟩
      let a : (P.colimitsCardinalClosure κ).ι.obj obj ⟶ X :=
        coequalizer.desc ((E.coconeAt X).ι.app j) (by simpa using h)
      let ψ : j ⟶ CostructuredArrow.mk a :=
        CostructuredArrow.homMk (ObjectProperty.homMk (coequalizer.π _ _)) (by simp [E, a])
      rw [← colimit.w Φ ψ]
      apply coequalizer.condition_assoc
    have : IsIso (colimit.desc _ (E.coconeAt X)) := hS₁.isIso_of_mono _ (fun Y hY g ↦ by
      let γ : CostructuredArrow (P.colimitsCardinalClosure κ).ι X :=
        CostructuredArrow.mk (Y := ⟨Y, P.le_colimitsCardinalClosure  _ _ hY⟩) (by exact g)
      exact ⟨colimit.ι (CostructuredArrow.proj _ _ ⋙ (P.colimitsCardinalClosure κ).ι) γ,
        by simp [γ, E]⟩)
    exact ⟨IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext
      (asIso (colimit.desc _ (E.coconeAt X))))⟩
/-
**CategoryTheory.ObjectProperty.colimitsCardinalClosure_le_isCardinalPresentable
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {κ : Cardinal.{w}
} [inst_1 : Fact κ.IsRegular]   [CategoryTheory.LocallySmall.{w, v, u} C],   ∀ P
 ≤ CategoryTheory.isCardinalPresentable C κ, P.colimitsCardinalClosure κ ≤ Categ
oryTheory.isCardinalPresentable C κ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.colimitsCardinalClosure_le`：colimitsCardin
alClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms] (hQ : forall (
J : Type w) [SmallCategory J] (_ : HasCardinal…
· 使用定理 `CategoryTheory.instIsClosedUnderIsomorphismsIsCardinalPresentable`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (κ : Cardinal.{w}) [inst_
1 : Fact κ.IsRegular],   (CategoryTheory.isCardinalPres…
· 使用引理 `CategoryTheory.isClosedUnderColimitsOfShape_isCardinalPresentable`：isClo
sedUnderColimitsOfShape_isCardinalPresentable [LocallySmall.{w} C] {κ : Cardinal
.{w}} [Fact κ.IsRegular] {J : Type u'} [Category.{v'} J…
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma ObjectProperty.colimitsCardinalClosure_le_isCardinalPresentable
    [LocallySmall.{w} C] (P : ObjectProperty C) (hP : P ≤ isCardinalPresentable C κ) :
    P.colimitsCardinalClosure κ ≤ isCardinalPresentable C κ :=
  P.colimitsCardinalClosure_le κ
    (fun _ _ hJ ↦ isClosedUnderColimitsOfShape_isCardinalPresentable C hJ) hP
/-
**CategoryTheory.IsStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresenta
ble** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsStrongGenerator`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {κ : Cardinal.{w}
} [inst_1 : Fact κ.IsRegular]   [CategoryTheory.Limits.HasColimitsOfSize.{w, w, 
v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C]   {P : CategoryTheory.ObjectP
roperty C} [CategoryTheory.ObjectProperty.Small.{w, v, u} P],   P.IsStrongGenera
tor →     P ≤ CategoryTheory.isCardinalPresentable C κ →       CategoryTheory.is
CardinalPresentable C κ = P.colimitsCardinalClosure κ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.ObjectProperty.IsStrongGenerator.isDense_colimitsCardinal
Closure_ι`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {κ : Cardina
l.{w}} [inst_1 : Fact κ.IsRegular]   [CategoryTheory.Limits.HasColimits…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_eq_self`：retractClosure_eq_
self [IsStableUnderRetracts P] : retractClosure P = P
· 使用定理 `CategoryTheory.IsCardinalPresentable.exists_hom_of_isColimit`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (κ : Cardinal.{w}) [in
st_1 : Fact κ.IsRegular]   {J : Type u_1} [inst_2 …
· 使用引理 `CategoryTheory.isCardinalPresentable_iff`：isCardinalPresentable_iff (X :
 C) : isCardinalPresentable C κ X ↔ IsCardinalPresentable X κ
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallFullSubcategoryOfLocal
lySmallOfEssentiallySmall_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, 
u} C] (P : CategoryTheory.ObjectProperty C)   [CategoryTheory.LocallySmall.{w, v
, u} C] […
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallColimitsCardinalClosur
eOfLocallySmall`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : C
ategoryTheory.ObjectProperty C) (κ : Cardinal.{w})   [CategoryTheory.ObjectPr…
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallOfSmall`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProperty C
)   [CategoryTheory.ObjectProperty.Small.{w, v,…
· 使用定理 `CategoryTheory.ObjectProperty.isCardinalFiltered_costructuredArrow_colim
itsCardinalClosure_ι`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (
P : CategoryTheory.ObjectProperty C) (κ : Cardinal.{w})   [inst_1 : Fact κ.IsReg
ul…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.ObjectProperty.colimitsCardinalClosure_le_isCardinalPrese
ntable`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {κ : Cardinal.{
w}} [inst_1 : Fact κ.IsRegular]   [CategoryTheory.LocallySmall.{w, v…
-/
lemma IsStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresentable
    [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
    {P : ObjectProperty C} [ObjectProperty.Small.{w} P] (hS₁ : P.IsStrongGenerator)
    (hS₂ : P ≤ isCardinalPresentable C κ) :
    isCardinalPresentable C κ = P.colimitsCardinalClosure κ := by
  refine le_antisymm ?_ (P.colimitsCardinalClosure_le_isCardinalPresentable hS₂)
  have := hS₁.isDense_colimitsCardinalClosure_ι hS₂
  intro X hX
  rw [isCardinalPresentable_iff] at hX
  rw [← (P.colimitsCardinalClosure κ).retractClosure_eq_self]
  obtain ⟨j, φ, hφ⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
    ((P.colimitsCardinalClosure κ).ι.denseAt X) (𝟙 X)
  exact ⟨_, j.left.2, ⟨{ i := _, r := _, retract := hφ }⟩⟩

namespace IsCardinalLocallyPresentable

variable (C κ) in
/-
**CategoryTheory.IsCardinalLocallyPresentable.iff_exists_isStrongGenerator** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.IsCardinalLocallyPresentable`。
形式化陈述：iff_exists_isStrongGenerator [HasColimitsOfSize.{w, w} C] [LocallySmall.{w
} C] : IsCardinalLocallyPresentable C κ ↔ exists (P : ObjectProperty C) (_ : Obj
ectProperty.Small.{w} P), P.IsStrongGenerator ∧ P <= isCardinalPresentable C κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasCardinalFilteredGenerator.exists_small_generator`：∀ (C
 : Type u) [inst : CategoryTheory.Category.{v, u} C] (κ : Cardinal.{w}) [inst_1 
: Fact κ.IsRegular]   [CategoryTheory.HasCardinalFiltere…
· 使用定理 `CategoryTheory.IsCardinalAccessibleCategory.toHasCardinalFilteredGenerat
or`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {κ : Cardinal.{w}} 
{inst_1 : Fact κ.IsRegular}   [self : CategoryTheory.IsCardinalA…
· 使用定理 `CategoryTheory.instIsCardinalAccessibleCategoryOfIsCardinalLocallyPresen
table`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (κ : Cardinal.{w
}) [inst_1 : Fact κ.IsRegular]   [CategoryTheory.IsCardinalLocallyP…
· 使用引理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.isStrongGenera
tor`：isStrongGenerator : P.IsStrongGenerator
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.le_isCardinalP
resentable`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Catego
ryTheory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
· 使用定理 `CategoryTheory.ObjectProperty.IsStrongGenerator.isDense_colimitsCardinal
Closure_ι`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {κ : Cardina
l.{w}} [inst_1 : Fact κ.IsRegular]   [CategoryTheory.Limits.HasColimits…
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallColimitsCardinalClosur
eOfLocallySmall`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : C
ategoryTheory.ObjectProperty C) (κ : Cardinal.{w})   [CategoryTheory.ObjectPr…
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallOfSmall`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProperty C
)   [CategoryTheory.ObjectProperty.Small.{w, v,…
· 使用定理 `CategoryTheory.IsCardinalFilteredGenerator.of_isDense_ι`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProperty C) 
  [CategoryTheory.ObjectProperty.EssentiallyS…
· 使用定理 `CategoryTheory.ObjectProperty.colimitsCardinalClosure_le_isCardinalPrese
ntable`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {κ : Cardinal.{
w}} [inst_1 : Fact κ.IsRegular]   [CategoryTheory.LocallySmall.{w, v…
· 使用定理 `CategoryTheory.ObjectProperty.isCardinalFiltered_costructuredArrow_colim
itsCardinalClosure_ι`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (
P : CategoryTheory.ObjectProperty C) (κ : Cardinal.{w})   [inst_1 : Fact κ.IsReg
ul…
-/
lemma iff_exists_isStrongGenerator [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C] :
    IsCardinalLocallyPresentable C κ ↔
      ∃ (P : ObjectProperty C) (_ : ObjectProperty.Small.{w} P), P.IsStrongGenerator ∧
        P ≤ isCardinalPresentable C κ := by
  refine ⟨fun _ ↦ ?_, fun ⟨P, _, hS₁, hS₂⟩ ↦ ?_⟩
  · obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_small_generator C κ
    exact ⟨_, inferInstance, hP.isStrongGenerator, hP.le_isCardinalPresentable⟩
  · have := hS₁.isDense_colimitsCardinalClosure_ι hS₂
    have : HasCardinalFilteredGenerator C κ :=
      { exists_generator := ⟨(P.colimitsCardinalClosure κ), inferInstance,
            IsCardinalFilteredGenerator.of_isDense_ι _ _
              (P.colimitsCardinalClosure_le_isCardinalPresentable hS₂)⟩ }
    constructor

variable (C) in
/-
**CategoryTheory.IsCardinalLocallyPresentable.of_le** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.IsCardinalLocallyPresentable`。
形式化陈述：of_le [IsCardinalLocallyPresentable C κ] {κ' : Cardinal.{w}} [Fact κ'.IsRe
gular] (h : κ <= κ') : IsCardinalLocallyPresentable C κ'
参数：h : κ <= κ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsCardinalLocallyPresentable.iff_exists_isStrongGenerator
`：iff_exists_isStrongGenerator [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
 : IsCardinalLocallyPresentable C κ ↔ exists (P : ObjectProper…
· 使用定理 `CategoryTheory.IsCardinalLocallyPresentable.toHasColimitsOfSize`：∀ {C : 
Type u} {inst : CategoryTheory.Category.{v, u} C} (κ : Cardinal.{w}) {inst_1 : F
act κ.IsRegular}   [self : CategoryTheory.IsCardinalL…
· 使用定理 `CategoryTheory.HasCardinalFilteredGenerator.toLocallySmall`：∀ {C : Type 
u} {hC : CategoryTheory.Category.{v, u} C} (κ : Cardinal.{w}) {hκ : Fact κ.IsReg
ular}   [self : CategoryTheory.HasCardinalFilter…
· 使用定理 `CategoryTheory.IsCardinalAccessibleCategory.toHasCardinalFilteredGenerat
or`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {κ : Cardinal.{w}} 
{inst_1 : Fact κ.IsRegular}   [self : CategoryTheory.IsCardinalA…
· 使用定理 `CategoryTheory.instIsCardinalAccessibleCategoryOfIsCardinalLocallyPresen
table`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (κ : Cardinal.{w
}) [inst_1 : Fact κ.IsRegular]   [CategoryTheory.IsCardinalLocallyP…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.isCardinalPresentable_monotone`：isCardinalPresentable_mon
otone {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ <= κ') : isCardinalPresenta
ble C κ <= isCardinalPresentable C …
-/
lemma of_le [IsCardinalLocallyPresentable C κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular]
    (h : κ ≤ κ') :
    IsCardinalLocallyPresentable C κ' := by
  rw [iff_exists_isStrongGenerator]
  obtain ⟨S, _, h₁, h₂⟩ := (iff_exists_isStrongGenerator C κ).1 inferInstance
  exact ⟨S, inferInstance, h₁, h₂.trans (isCardinalPresentable_monotone _ h)⟩

end IsCardinalLocallyPresentable

end CategoryTheory

