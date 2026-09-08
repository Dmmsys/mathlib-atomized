/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Localization.StructuredArrow

/-!
# Pointwise left derived functors

We define pointwise left derived functors using the notion
of pointwise right Kan extensions.

We show that if `F : C ⥤ H` inverts `W : MorphismProperty C`,
then it has a pointwise left derived functor.

Note: this file was obtained by dualizing the definitions in the file
`Mathlib/CategoryTheory/Functor/Derived/PointwiseRightDerived.lean`. These two files should be
kept in sync.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
  (F' : D ⥤ H) (F : C ⥤ H) (L : C ⥤ D) (α : L ⋙ F' ⟶ F) (W : MorphismProperty C)

/-- Given `F : C ⥤ H`, `W : MorphismProperty C` and `X : C`, we say that `F` has a
pointwise left derived functor at `X` if `F` has a right Kan extension
at `L.obj X` for any localization functor `L : C ⥤ D` for `W`. In the
definition, this is stated for `L := W.Q`, see `hasPointwiseLeftDerivedFunctorAt_iff`
for the more general equivalence. -/
/-
**CategoryTheory.Functor.HasPointwiseLeftDerivedFunctorAt** 是 Mathlib 中的一个归纳类型，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：{C : Type u₁} →   {H : Type u₃} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₃, u₃} H] →         Category
Theory.Functor C H → CategoryTheory.MorphismProperty C → C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : C ⥤ H`, `W : MorphismProperty C` and `X : C`, we say that `F` has a
pointwise left derived functor at `X` if `F` has a right Kan extension
at `L.obj X` for any localization functor `L : C ⥤ D` for `W`. In the
definition, this is stated for `L := W.Q`, see `hasPointwiseLeftDerivedFunctorAt
_iff`
for the more general equivalence.
-/
class HasPointwiseLeftDerivedFunctorAt (X : C) : Prop where
  /-- Use the more general `hasLimit` lemma instead, see also
  `hasPointwiseLeftDerivedFunctorAt_iff` -/
  hasLimit' : HasPointwiseRightKanExtensionAt W.Q F (W.Q.obj X)

/-- A functor `F : C ⥤ H` has a pointwise left derived functor with respect to
`W : MorphismProperty C` if it has a pointwise left derived functor at `X`
for any `X : C`. -/
/-
**CategoryTheory.Functor.HasPointwiseLeftDerivedFunctor** 是 Mathlib 中的一个缩写定义，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：HasPointwiseLeftDerivedFunctor
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ H` has a pointwise left derived functor with respect to
`W : MorphismProperty C` if it has a pointwise left derived functor at `X`
for any `X : C`.
-/
abbrev HasPointwiseLeftDerivedFunctor := ∀ (X : C), F.HasPointwiseLeftDerivedFunctorAt W X
/-
**CategoryTheory.Functor.hasPointwiseLeftDerivedFunctorAt_iff** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseLeftDerivedFunctorAt_iff [L.IsLocalization W] (X : C) : F.HasP
ointwiseLeftDerivedFunctorAt W X ↔ HasPointwiseRightKanExtensionAt L F (L.obj X)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightKanExtensionAt_iff_of_equivalenc
e`：hasPointwiseRightKanExtensionAt_iff_of_equivalence (E : D ≌ D') (eL : L ⋙ E.f
unctor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') : Has…
· 使用定理 `CategoryTheory.Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit'`：∀ {C 
: Type u₁} {H : Type u₃} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : C
ategoryTheory.Category.{v₃, u₃} H}   {F : CategoryTheor…
-/
lemma hasPointwiseLeftDerivedFunctorAt_iff [L.IsLocalization W] (X : C) :
    F.HasPointwiseLeftDerivedFunctorAt W X ↔
      HasPointwiseRightKanExtensionAt L F (L.obj X) := by
  rw [← hasPointwiseRightKanExtensionAt_iff_of_equivalence W.Q L F
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
  exact ⟨fun h ↦ h.hasLimit', fun h ↦ ⟨h⟩⟩
/-
**CategoryTheory.Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Functor.HasPointwiseLeftDerivedFunctorAt`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} {H : Type u₃} [inst : CategoryTheory.Categor
y.{v₁, u₁} C]   [inst_1 : CategoryTheory.Category.{v₂, u₂} D] [inst_2 : Category
Theory.Category.{v₃, u₃} H]   (F : CategoryTheory.Functor C H) (L : CategoryTheo
ry.Functor C D) (W : CategoryTheory.MorphismProperty C)   [L.IsLocalization W] (
X : C) [F.HasPointwiseLeftDerivedFunctorAt W X], L.HasPointwiseRightKanExtension
At F (L.obj X)
参数：F : CategoryTheory.Functor C H；L : CategoryTheory.Functor C D；W : CategoryThe
ory.MorphismProperty C；X : C；L.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.hasPointwiseLeftDerivedFunctorAt_iff`：hasPointwis
eLeftDerivedFunctorAt_iff [L.IsLocalization W] (X : C) : F.HasPointwiseLeftDeriv
edFunctorAt W X ↔ HasPointwiseRightKanExtensionAt…
-/
lemma HasPointwiseLeftDerivedFunctorAt.hasLimit
    [L.IsLocalization W] (X : C) [F.HasPointwiseLeftDerivedFunctorAt W X] :
    HasPointwiseRightKanExtensionAt L F (L.obj X) := by
  rwa [← hasPointwiseLeftDerivedFunctorAt_iff F L W]
/-
**CategoryTheory.Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseLeftDerivedFunctorAt_iff_of_mem {X Y : C} (w : X ⟶ Y) (hw : W 
w) : F.HasPointwiseLeftDerivedFunctorAt W X ↔ F.HasPointwiseLeftDerivedFunctorAt
 W Y
参数：w : X ⟶ Y；hw : W w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.hasPointwiseLeftDerivedFunctorAt_iff`：hasPointwis
eLeftDerivedFunctorAt_iff [L.IsLocalization W] (X : C) : F.HasPointwiseLeftDeriv
edFunctorAt W X ↔ HasPointwiseRightKanExtensionAt…
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightKanExtensionAt_iff_of_iso`：hasPo
intwiseRightKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) : HasPointwiseRi
ghtKanExtensionAt L F Y₁ ↔ HasPointwiseRightKanExtensio…
-/
lemma hasPointwiseLeftDerivedFunctorAt_iff_of_mem {X Y : C} (w : X ⟶ Y) (hw : W w) :
    F.HasPointwiseLeftDerivedFunctorAt W X ↔
      F.HasPointwiseLeftDerivedFunctorAt W Y := by
  simp only [F.hasPointwiseLeftDerivedFunctorAt_iff W.Q W]
  exact hasPointwiseRightKanExtensionAt_iff_of_iso W.Q F (Localization.isoOfHom W.Q W w hw)

section

variable [F.HasPointwiseLeftDerivedFunctor W]

/-
**CategoryTheory.Functor.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerive
dFunctor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor [L.IsLocal
ization W] : HasPointwiseRightKanExtension L F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightKanExtensionAt_iff_of_iso`：hasPo
intwiseRightKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) : HasPointwiseRi
ghtKanExtensionAt L F Y₁ ↔ HasPointwiseRightKanExtensio…
· 使用引理 `CategoryTheory.Functor.hasPointwiseLeftDerivedFunctorAt_iff`：hasPointwis
eLeftDerivedFunctorAt_iff [L.IsLocalization W] (X : C) : F.HasPointwiseLeftDeriv
edFunctorAt W X ↔ HasPointwiseRightKanExtensionAt…
-/
lemma hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor [L.IsLocalization W] :
    HasPointwiseRightKanExtension L F := fun Y ↦ by
  have := Localization.essSurj L W
  rw [← hasPointwiseRightKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y),
    ← F.hasPointwiseLeftDerivedFunctorAt_iff L W]
  infer_instance
/-
**CategoryTheory.Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor : F.HasLeftDerived
Functor W where hasRightKanExtension'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightKanExtension_of_hasPointwiseLeft
DerivedFunctor`：hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor 
[L.IsLocalization W] : HasPointwiseRightKanExtension L F
· 使用定理 `CategoryTheory.Functor.instHasRightKanExtension`：∀ {C : Type u_1} {D : T
ype u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} …
-/
lemma hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor :
    F.HasLeftDerivedFunctor W where
  hasRightKanExtension' := by
    have := F.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor W.Q W
    infer_instance

attribute [instance] hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor

variable {F L}

/-- A left derived functor is a pointwise left derived functor when
there exists a pointwise left derived functor. -/
/-
**CategoryTheory.Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFu
nctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor [L.IsLocaliza
tion W] [F'.IsLeftDerivedFunctor α W] : (RightExtension.mk _ α).IsPointwiseRight
KanExtension
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightKanExtension_of_hasPointwiseLeft
DerivedFunctor`：hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor 
[L.IsLocalization W] : HasPointwiseRightKanExtension L F
· 使用定理 `CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …

--- 原说明 ---
A left derived functor is a pointwise left derived functor when
there exists a pointwise left derived functor.
-/
noncomputable def isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
     [L.IsLocalization W] [F'.IsLeftDerivedFunctor α W] :
    (RightExtension.mk _ α).IsPointwiseRightKanExtension :=
  have := hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor F L
  have := IsLeftDerivedFunctor.isRightKanExtension F' α W
  isPointwiseRightKanExtensionOfIsRightKanExtension F' α

end

section

variable {F L}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `L : C ⥤ D` is a localization functor for `W` and `e : F ≅ L ⋙ G` is an isomorphism,
then `e.inv` makes `G` a pointwise right Kan extension of `F` along `L` at `L.obj Y`
for any `Y : C`. -/
/-
**CategoryTheory.Functor.isPointwiseRightKanExtensionAtOfIsoOfIsLocalization** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isPointwiseRightKanExtensionAtOfIsoOfIsLocalization {G : D ⥤ H} (e : F ≅ L
 ⋙ G) [L.IsLocalization W] (Y : C) : (RightExtension.mk _ e.inv).IsPointwiseRigh
tKanExtensionAt (L.obj Y) where lift s
参数：e : F ≅ L ⋙ G；Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L : C ⥤ D` is a localization functor for `W` and `e : F ≅ L ⋙ G` is an isomo
rphism,
then `e.inv` makes `G` a pointwise right Kan extension of `F` along `L` at `L.ob
j Y`
for any `Y : C`.
-/
def isPointwiseRightKanExtensionAtOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] (Y : C) :
    (RightExtension.mk _ e.inv).IsPointwiseRightKanExtensionAt (L.obj Y) where
  lift s := s.π.app (StructuredArrow.mk (𝟙 (L.obj Y))) ≫ e.hom.app Y
  fac s j := by
    refine Localization.induction_structuredArrow L W _ (by simp)
      (fun X₁ X₂ f φ hφ ↦ ?_) (fun X₁ X₂ w hw φ hφ ↦ ?_) j
    · have eq := s.π.naturality
        (StructuredArrow.homMk f : StructuredArrow.mk φ ⟶ StructuredArrow.mk (φ ≫ L.map f))
      dsimp at eq hφ ⊢
      rw [id_comp] at eq
      rw [assoc] at hφ
      simp [eq, ← reassoc_of% hφ, ← e.inv.naturality f]
    · have : IsIso (F.map w) := by
        have := Localization.inverts L W w hw
        rw [← NatIso.naturality_2 e w]
        dsimp
        infer_instance
      have eq := s.π.naturality (StructuredArrow.homMk w :
          StructuredArrow.mk (φ ≫ (Localization.isoOfHom L W w hw).inv) ⟶
            StructuredArrow.mk φ)
      dsimp at eq hφ ⊢
      rw [id_comp] at eq
      rw [assoc] at hφ
      simp only [← cancel_mono (F.map w), ← eq, comp_obj, comp_map, assoc,
        ← hφ, ← NatTrans.naturality, ← G.map_comp_assoc,
        Localization.isoOfHom_inv_hom_id, comp_id]
  uniq s m hm := by
    have := hm (StructuredArrow.mk (𝟙 (L.obj Y)))
    dsimp at this m hm ⊢
    simp [← reassoc_of% this]

/-- If `L` is a localization functor for `W` and `e : F ≅ L ⋙ G` is an isomorphism,
then `e.inv` makes `G` a pointwise right Kan extension of `F` along `L`. -/
/-
**CategoryTheory.Functor.isPointwiseRightKanExtensionOfIsoOfIsLocalization** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isPointwiseRightKanExtensionOfIsoOfIsLocalization {G : D ⥤ H} (e : F ≅ L ⋙
 G) [L.IsLocalization W] : (RightExtension.mk _ e.inv).IsPointwiseRightKanExtens
ion
参数：e : F ≅ L ⋙ G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj

--- 原说明 ---
If `L` is a localization functor for `W` and `e : F ≅ L ⋙ G` is an isomorphism,
then `e.inv` makes `G` a pointwise right Kan extension of `F` along `L`.
-/
noncomputable def isPointwiseRightKanExtensionOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] :
    (RightExtension.mk _ e.inv).IsPointwiseRightKanExtension := fun Y ↦
  have := Localization.essSurj L W
  (RightExtension.mk _ e.inv).isPointwiseRightKanExtensionAtEquivOfIso'
    (L.objObjPreimageIso Y) (isPointwiseRightKanExtensionAtOfIsoOfIsLocalization W e _)

/-- Let `L : C ⥤ D` be a localization functor for `W`, if an extension `E`
of `F : C ⥤ H` along `L` is such that the natural transformation
`E.hom : L ⋙ E.right ⟶ F` is an isomorphism, then `E` is a pointwise
right Kan extension. -/
/-
**CategoryTheory.Functor.RightExtension.isPointwiseRightKanExtensionOfIsIsoOfIsL
ocalization** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.RightExtension`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     {H : Type u₃} →       [inst : Catego
ryTheory.Category.{v₁, u₁} C] →         [inst_1 : CategoryTheory.Category.{v₂, u
₂} D] →           [inst_2 : CategoryTheory.Category.{v₃, u₃} H] →             {F
 : CategoryTheory.Functor C H} →               {L : CategoryTheory.Functor C D} 
→                 (W : CategoryTheory.MorphismProperty C) →                   (E
 : L.RightExtension F) →                     [CategoryTheory.IsIso (CategoryTheo
ry.CostructuredArrow.hom E)] →                       [L.IsLocalization W] → E.Is
PointwiseRightKanExtension
参数：W : CategoryTheory.MorphismProperty C；E : L.RightExtension F；CategoryTheory.C
ostructuredArrow.hom E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `L : C ⥤ D` be a localization functor for `W`, if an extension `E`
of `F : C ⥤ H` along `L` is such that the natural transformation
`E.hom : L ⋙ E.right ⟶ F` is an isomorphism, then `E` is a pointwise
right Kan extension.
-/
noncomputable def RightExtension.isPointwiseRightKanExtensionOfIsIsoOfIsLocalization
    (E : RightExtension L F) [IsIso E.hom] [L.IsLocalization W] :
    E.IsPointwiseRightKanExtension :=
  Functor.isPointwiseRightKanExtensionOfIsoOfIsLocalization W (asIso E.hom).symm
/-
**CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_inverts** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseLeftDerivedFunctor_of_inverts (F : C ⥤ H) {W : MorphismPropert
y C} (hF : W.IsInvertedBy F) : F.HasPointwiseLeftDerivedFunctor W
参数：F : C ⥤ H；hF : W.IsInvertedBy F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.hasPointwiseLeftDerivedFunctorAt_iff`：hasPointwis
eLeftDerivedFunctorAt_iff [L.IsLocalization W] (X : C) : F.HasPointwiseLeftDeriv
edFunctorAt W X ↔ HasPointwiseRightKanExtensionAt…
· 使用定理 `CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.hasPo
intwiseRightKanExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst :
 CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2,
 u_2} …
-/
lemma hasPointwiseLeftDerivedFunctor_of_inverts
    (F : C ⥤ H) {W : MorphismProperty C} (hF : W.IsInvertedBy F) :
    F.HasPointwiseLeftDerivedFunctor W := by
  intro X
  rw [hasPointwiseLeftDerivedFunctorAt_iff F W.Q W]
  exact (isPointwiseRightKanExtensionOfIsoOfIsLocalization W
    (Localization.fac F hF W.Q).symm).hasPointwiseRightKanExtension _
/-
**CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：isLeftDerivedFunctor_of_inverts [L.IsLocalization W] (F' : D ⥤ H) (e : L ⋙
 F' ≅ F) : F'.IsLeftDerivedFunctor e.hom W where isRightKanExtension
参数：F' : D ⥤ H；e : L ⋙ F' ≅ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.isRig
htKanExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryT
heory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
-/
lemma isLeftDerivedFunctor_of_inverts
    [L.IsLocalization W] (F' : D ⥤ H) (e : L ⋙ F' ≅ F) :
    F'.IsLeftDerivedFunctor e.hom W where
  isRightKanExtension :=
    (isPointwiseRightKanExtensionOfIsoOfIsLocalization W e.symm).isRightKanExtension
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [L.IsLocalization W] (hF : W.IsInvertedBy F) :
    (Localization.lift F hF L).IsLeftDerivedFunctor (Localization.fac F hF L).hom W :=
  isLeftDerivedFunctor_of_inverts W _ _

variable {W} in
/-
**CategoryTheory.Functor.isIso_of_isLeftDerivedFunctor_of_inverts** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isIso_of_isLeftDerivedFunctor_of_inverts [L.IsLocalization W] {F : C ⥤ H} 
(LF : D ⥤ H) (α : L ⋙ LF ⟶ F) (hF : W.IsInvertedBy F) [LF.IsLeftDerivedFunctor α
 W] : IsIso α
参数：LF : D ⥤ H；α : L ⋙ LF ⟶ F；hF : W.IsInvertedBy F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instIsLeftDerivedFunctorLiftHomFac`：∀ {C : Type u
₁} {D : Type u₂} {H : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} C]   [in
st_1 : CategoryTheory.Category.{v₂, u₂} D] [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.leftDerivedNatIso_inv`：∀ {C : Type u_1} {D : Type
 u_2} {H : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : C
ategoryTheory.Category.{v_3, u_2} …
· 使用引理 `CategoryTheory.Functor.leftDerivedNatTrans_fac`：leftDerivedNatTrans_fac 
(τ : F' ⟶ F) : whiskerLeft L (leftDerivedNatTrans LF' LF α' α W τ) ≫ α = α' ≫ τ
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma isIso_of_isLeftDerivedFunctor_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    (hF : W.IsInvertedBy F) [LF.IsLeftDerivedFunctor α W] :
    IsIso α := by
  have : α = whiskerLeft _ (leftDerivedUnique _ _ (Localization.fac F hF L).hom α W).inv ≫
      (Localization.fac F hF L).hom := by simp
  rw [this]
  infer_instance

variable {W} in
/-
**CategoryTheory.Functor.isLeftDerivedFunctor_iff_of_inverts** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isLeftDerivedFunctor_iff_of_inverts [L.IsLocalization W] {F : C ⥤ H} (LF :
 D ⥤ H) (α : L ⋙ LF ⟶ F) (hF : W.IsInvertedBy F) : LF.IsLeftDerivedFunctor α W ↔
 IsIso α
参数：LF : D ⥤ H；α : L ⋙ LF ⟶ F；hF : W.IsInvertedBy F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isIso_of_isLeftDerivedFunctor_of_inverts`：isIso_o
f_isLeftDerivedFunctor_of_inverts [L.IsLocalization W] {F : C ⥤ H} (LF : D ⥤ H) 
(α : L ⋙ LF ⟶ F) (hF : W.IsInvertedBy F) [LF.IsLeftDe…
· 使用引理 `CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts`：isLeftDerivedFun
ctor_of_inverts [L.IsLocalization W] (F' : D ⥤ H) (e : L ⋙ F' ≅ F) : F'.IsLeftDe
rivedFunctor e.hom W where isRightKanExtensi…
-/
lemma isLeftDerivedFunctor_iff_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    (hF : W.IsInvertedBy F) :
    LF.IsLeftDerivedFunctor α W ↔ IsIso α :=
  ⟨fun _ ↦ isIso_of_isLeftDerivedFunctor_of_inverts LF α hF, fun _ ↦
    isLeftDerivedFunctor_of_inverts W LF (asIso α)⟩

end

end Functor

end CategoryTheory

