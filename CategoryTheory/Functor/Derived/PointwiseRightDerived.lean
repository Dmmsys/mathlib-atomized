/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Localization.StructuredArrow

/-!
# Pointwise right derived functors

We define pointwise right derived functors using the notion
of pointwise left Kan extensions.

We show that if `F : C ⥤ H` inverts `W : MorphismProperty C`,
then it has a pointwise right derived functor.

Note: the file `Mathlib/CategoryTheory/Functor/Derived/PointwiseLeftDerived.lean` was obtained
by dualizing this file. These two files should be kept in sync.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
  (F' : D ⥤ H) (F : C ⥤ H) (L : C ⥤ D) (α : F ⟶ L ⋙ F') (W : MorphismProperty C)

/-- Given `F : C ⥤ H`, `W : MorphismProperty C` and `X : C`, we say that `F` has a
pointwise right derived functor at `X` if `F` has a left Kan extension
at `L.obj X` for any localization functor `L : C ⥤ D` for `W`. In the
definition, this is stated for `L := W.Q`, see `hasPointwiseRightDerivedFunctorAt_iff`
for the more general equivalence. -/
/-
**CategoryTheory.Functor.HasPointwiseRightDerivedFunctorAt** 是 Mathlib 中的一个归纳类型，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：{C : Type u₁} →   {H : Type u₃} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₃, u₃} H] →         Category
Theory.Functor C H → CategoryTheory.MorphismProperty C → C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : C ⥤ H`, `W : MorphismProperty C` and `X : C`, we say that `F` has a
pointwise right derived functor at `X` if `F` has a left Kan extension
at `L.obj X` for any localization functor `L : C ⥤ D` for `W`. In the
definition, this is stated for `L := W.Q`, see `hasPointwiseRightDerivedFunctorA
t_iff`
for the more general equivalence.
-/
class HasPointwiseRightDerivedFunctorAt (X : C) : Prop where
  /-- Use the more general `hasColimit` lemma instead, see also
  `hasPointwiseRightDerivedFunctorAt_iff` -/
  hasColimit' : HasPointwiseLeftKanExtensionAt W.Q F (W.Q.obj X)

/-- A functor `F : C ⥤ H` has a pointwise right derived functor with respect to
`W : MorphismProperty C` if it has a pointwise right derived functor at `X`
for any `X : C`. -/
/-
**CategoryTheory.Functor.HasPointwiseRightDerivedFunctor** 是 Mathlib 中的一个缩写定义，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：HasPointwiseRightDerivedFunctor
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ H` has a pointwise right derived functor with respect to
`W : MorphismProperty C` if it has a pointwise right derived functor at `X`
for any `X : C`.
-/
abbrev HasPointwiseRightDerivedFunctor := ∀ (X : C), F.HasPointwiseRightDerivedFunctorAt W X
/-
**CategoryTheory.Functor.hasPointwiseRightDerivedFunctorAt_iff** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) : F.Has
PointwiseRightDerivedFunctorAt W X ↔ HasPointwiseLeftKanExtensionAt L F (L.obj X
)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.hasPointwiseLeftKanExtensionAt_iff_of_equivalence
`：hasPointwiseLeftKanExtensionAt_iff_of_equivalence (E : D ≌ D') (eL : L ⋙ E.fun
ctor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') : HasP…
· 使用定理 `CategoryTheory.Functor.HasPointwiseRightDerivedFunctorAt.hasColimit'`：∀ 
{C : Type u₁} {H : Type u₃} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 
: CategoryTheory.Category.{v₃, u₃} H}   {F : CategoryTheor…
-/
lemma hasPointwiseRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      HasPointwiseLeftKanExtensionAt L F (L.obj X) := by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_equivalence W.Q L F
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
  exact ⟨fun h ↦ h.hasColimit', fun h ↦ ⟨h⟩⟩
/-
**CategoryTheory.Functor.HasPointwiseRightDerivedFunctorAt.hasColimit** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.Functor.HasPointwiseRightDerivedFunctorAt`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} {H : Type u₃} [inst : CategoryTheory.Categor
y.{v₁, u₁} C]   [inst_1 : CategoryTheory.Category.{v₂, u₂} D] [inst_2 : Category
Theory.Category.{v₃, u₃} H]   (F : CategoryTheory.Functor C H) (L : CategoryTheo
ry.Functor C D) (W : CategoryTheory.MorphismProperty C)   [L.IsLocalization W] (
X : C) [F.HasPointwiseRightDerivedFunctorAt W X], L.HasPointwiseLeftKanExtension
At F (L.obj X)
参数：F : CategoryTheory.Functor C H；L : CategoryTheory.Functor C D；W : CategoryThe
ory.MorphismProperty C；X : C；L.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightDerivedFunctorAt_iff`：hasPointwi
seRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) : F.HasPointwiseRightDe
rivedFunctorAt W X ↔ HasPointwiseLeftKanExtensionA…
-/
lemma HasPointwiseRightDerivedFunctorAt.hasColimit
    [L.IsLocalization W] (X : C) [F.HasPointwiseRightDerivedFunctorAt W X] :
    HasPointwiseLeftKanExtensionAt L F (L.obj X) := by
  rwa [← hasPointwiseRightDerivedFunctorAt_iff F L W]
/-
**CategoryTheory.Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseRightDerivedFunctorAt_iff_of_mem {X Y : C} (w : X ⟶ Y) (hw : W
 w) : F.HasPointwiseRightDerivedFunctorAt W X ↔ F.HasPointwiseRightDerivedFuncto
rAt W Y
参数：w : X ⟶ Y；hw : W w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightDerivedFunctorAt_iff`：hasPointwi
seRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) : F.HasPointwiseRightDe
rivedFunctorAt W X ↔ HasPointwiseLeftKanExtensionA…
· 使用引理 `CategoryTheory.Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso`：hasPoi
ntwiseLeftKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) : HasPointwiseLeft
KanExtensionAt L F Y₁ ↔ HasPointwiseLeftKanExtensionAt…
-/
lemma hasPointwiseRightDerivedFunctorAt_iff_of_mem {X Y : C} (w : X ⟶ Y) (hw : W w) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      F.HasPointwiseRightDerivedFunctorAt W Y := by
  simp only [F.hasPointwiseRightDerivedFunctorAt_iff W.Q W]
  exact hasPointwiseLeftKanExtensionAt_iff_of_iso W.Q F (Localization.isoOfHom W.Q W w hw)

section

variable [F.HasPointwiseRightDerivedFunctor W]

/-
**CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasPointwiseRightDerive
dFunctor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor [L.IsLocal
ization W] : HasPointwiseLeftKanExtension L F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso`：hasPoi
ntwiseLeftKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) : HasPointwiseLeft
KanExtensionAt L F Y₁ ↔ HasPointwiseLeftKanExtensionAt…
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightDerivedFunctorAt_iff`：hasPointwi
seRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) : F.HasPointwiseRightDe
rivedFunctorAt W X ↔ HasPointwiseLeftKanExtensionA…
-/
lemma hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor [L.IsLocalization W] :
    HasPointwiseLeftKanExtension L F := fun Y ↦ by
  have := Localization.essSurj L W
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y),
    ← F.hasPointwiseRightDerivedFunctorAt_iff L W]
  infer_instance
/-
**CategoryTheory.Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunct
or** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor : F.HasRightDeri
vedFunctor W where hasLeftKanExtension'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasPointwiseRight
DerivedFunctor`：hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor 
[L.IsLocalization W] : HasPointwiseLeftKanExtension L F
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
-/
lemma hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor :
    F.HasRightDerivedFunctor W where
  hasLeftKanExtension' := by
    have := F.hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor W.Q W
    infer_instance

attribute [instance] hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor

variable {F L}

/-- A right derived functor is a pointwise right derived functor when
there exists a pointwise right derived functor. -/
/-
**CategoryTheory.Functor.isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFu
nctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor [L.IsLocaliza
tion W] [F'.IsRightDerivedFunctor α W] : (LeftExtension.mk _ α).IsPointwiseLeftK
anExtension
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasPointwiseRight
DerivedFunctor`：hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor 
[L.IsLocalization W] : HasPointwiseLeftKanExtension L F
· 使用定理 `CategoryTheory.Functor.IsRightDerivedFunctor.isLeftKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …

--- 原说明 ---
A right derived functor is a pointwise right derived functor when
there exists a pointwise right derived functor.
-/
noncomputable def isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
     [L.IsLocalization W] [F'.IsRightDerivedFunctor α W] :
    (LeftExtension.mk _ α).IsPointwiseLeftKanExtension :=
  have := hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor F L
  have := IsRightDerivedFunctor.isLeftKanExtension F' α W
  isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α

end

section

variable {F L}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `L : C ⥤ D` is a localization functor for `W` and `e : F ≅ L ⋙ G` is an isomorphism,
then `e.hom` makes `G` a pointwise left Kan extension of `F` along `L` at `L.obj Y`
for any `Y : C`. -/
/-
**CategoryTheory.Functor.isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization {G : D ⥤ H} (e : F ≅ L 
⋙ G) [L.IsLocalization W] (Y : C) : (LeftExtension.mk _ e.hom).IsPointwiseLeftKa
nExtensionAt (L.obj Y) where desc s
参数：e : F ≅ L ⋙ G；Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L : C ⥤ D` is a localization functor for `W` and `e : F ≅ L ⋙ G` is an isomo
rphism,
then `e.hom` makes `G` a pointwise left Kan extension of `F` along `L` at `L.obj
 Y`
for any `Y : C`.
-/
def isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] (Y : C) :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtensionAt (L.obj Y) where
  desc s := e.inv.app Y ≫ s.ι.app (CostructuredArrow.mk (𝟙 (L.obj Y)))
  fac s j := by
    refine Localization.induction_costructuredArrow L W _ (by simp)
      (fun X₁ X₂ f φ hφ ↦ ?_) (fun X₁ X₂ w hw φ hφ ↦ ?_) j
    · have eq := s.ι.naturality
        (CostructuredArrow.homMk f : CostructuredArrow.mk (L.map f ≫ φ) ⟶ CostructuredArrow.mk φ)
      dsimp at eq hφ ⊢
      rw [comp_id] at eq
      rw [assoc] at hφ
      rw [assoc, map_comp_assoc, ← eq, ← hφ, NatTrans.naturality_assoc, comp_map]
    · have : IsIso (F.map w) := by
        have := Localization.inverts L W w hw
        rw [← NatIso.naturality_2 e w]
        dsimp
        infer_instance
      have eq := s.ι.naturality
        (CostructuredArrow.homMk w : CostructuredArrow.mk φ ⟶ CostructuredArrow.mk
          ((Localization.isoOfHom L W w hw).inv ≫ φ))
      dsimp at eq hφ ⊢
      rw [comp_id] at eq
      rw [assoc] at hφ
      rw [map_comp, assoc, assoc, ← cancel_epi (F.map w), eq, ← hφ,
        NatTrans.naturality_assoc, comp_map, ← G.map_comp_assoc]
      simp
  uniq s m hm := by
    have := hm (CostructuredArrow.mk (𝟙 (L.obj Y)))
    dsimp at this m hm ⊢
    simp only [← this, map_id, comp_id, Iso.inv_hom_id_app_assoc]

/-- If `L` is a localization functor for `W` and `e : F ≅ L ⋙ G` is an isomorphism,
then `e.hom` makes `G` a pointwise left Kan extension of `F` along `L`. -/
/-
**CategoryTheory.Functor.isPointwiseLeftKanExtensionOfIsoOfIsLocalization** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isPointwiseLeftKanExtensionOfIsoOfIsLocalization {G : D ⥤ H} (e : F ≅ L ⋙ 
G) [L.IsLocalization W] : (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtension
参数：e : F ≅ L ⋙ G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj

--- 原说明 ---
If `L` is a localization functor for `W` and `e : F ≅ L ⋙ G` is an isomorphism,
then `e.hom` makes `G` a pointwise left Kan extension of `F` along `L`.
-/
noncomputable def isPointwiseLeftKanExtensionOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtension := fun Y ↦
  have := Localization.essSurj L W
  (LeftExtension.mk _ e.hom).isPointwiseLeftKanExtensionAtEquivOfIso'
    (L.objObjPreimageIso Y) (isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization W e _)

set_option backward.isDefEq.respectTransparency false in
/-- Let `L : C ⥤ D` be a localization functor for `W`, if an extension `E`
of `F : C ⥤ H` along `L` is such that the natural transformation
`E.hom : F ⟶ L ⋙ E.right` is an isomorphism, then `E` is a pointwise
left Kan extension. -/
/-
**CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionOfIsIsoOfIsLoc
alization** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     {H : Type u₃} →       [inst : Catego
ryTheory.Category.{v₁, u₁} C] →         [inst_1 : CategoryTheory.Category.{v₂, u
₂} D] →           [inst_2 : CategoryTheory.Category.{v₃, u₃} H] →             {F
 : CategoryTheory.Functor C H} →               {L : CategoryTheory.Functor C D} 
→                 (W : CategoryTheory.MorphismProperty C) →                   (E
 : L.LeftExtension F) →                     [CategoryTheory.IsIso (CategoryTheor
y.StructuredArrow.hom E)] →                       [L.IsLocalization W] → E.IsPoi
ntwiseLeftKanExtension
参数：W : CategoryTheory.MorphismProperty C；E : L.LeftExtension F；CategoryTheory.St
ructuredArrow.hom E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `L : C ⥤ D` be a localization functor for `W`, if an extension `E`
of `F : C ⥤ H` along `L` is such that the natural transformation
`E.hom : F ⟶ L ⋙ E.right` is an isomorphism, then `E` is a pointwise
left Kan extension.
-/
noncomputable def LeftExtension.isPointwiseLeftKanExtensionOfIsIsoOfIsLocalization
    (E : LeftExtension L F) [IsIso E.hom] [L.IsLocalization W] :
    E.IsPointwiseLeftKanExtension :=
  Functor.isPointwiseLeftKanExtensionOfIsoOfIsLocalization W (asIso E.hom)
/-
**CategoryTheory.Functor.hasPointwiseRightDerivedFunctor_of_inverts** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseRightDerivedFunctor_of_inverts (F : C ⥤ H) {W : MorphismProper
ty C} (hF : W.IsInvertedBy F) : F.HasPointwiseRightDerivedFunctor W
参数：F : C ⥤ H；hF : W.IsInvertedBy F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightDerivedFunctorAt_iff`：hasPointwi
seRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) : F.HasPointwiseRightDe
rivedFunctorAt W X ↔ HasPointwiseLeftKanExtensionA…
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.hasPoin
twiseLeftKanExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_
2} …
-/
lemma hasPointwiseRightDerivedFunctor_of_inverts
    (F : C ⥤ H) {W : MorphismProperty C} (hF : W.IsInvertedBy F) :
    F.HasPointwiseRightDerivedFunctor W := by
  intro X
  rw [hasPointwiseRightDerivedFunctorAt_iff F W.Q W]
  exact (isPointwiseLeftKanExtensionOfIsoOfIsLocalization W
    (Localization.fac F hF W.Q).symm).hasPointwiseLeftKanExtension _
/-
**CategoryTheory.Functor.isRightDerivedFunctor_of_inverts** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：isRightDerivedFunctor_of_inverts [L.IsLocalization W] (F' : D ⥤ H) (e : L 
⋙ F' ≅ F) : F'.IsRightDerivedFunctor e.inv W where isLeftKanExtension
参数：F' : D ⥤ H；e : L ⋙ F' ≅ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftK
anExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheo
ry.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
-/
lemma isRightDerivedFunctor_of_inverts
    [L.IsLocalization W] (F' : D ⥤ H) (e : L ⋙ F' ≅ F) :
    F'.IsRightDerivedFunctor e.inv W where
  isLeftKanExtension :=
    (isPointwiseLeftKanExtensionOfIsoOfIsLocalization W e.symm).isLeftKanExtension
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [L.IsLocalization W] (hF : W.IsInvertedBy F) :
    (Localization.lift F hF L).IsRightDerivedFunctor (Localization.fac F hF L).inv W :=
  isRightDerivedFunctor_of_inverts W _ _

variable {W} in
/-
**CategoryTheory.Functor.isIso_of_isRightDerivedFunctor_of_inverts** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isIso_of_isRightDerivedFunctor_of_inverts [L.IsLocalization W] {F : C ⥤ H}
 (RF : D ⥤ H) (α : F ⟶ L ⋙ RF) (hF : W.IsInvertedBy F) [RF.IsRightDerivedFunctor
 α W] : IsIso α
参数：RF : D ⥤ H；α : F ⟶ L ⋙ RF；hF : W.IsInvertedBy F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instIsRightDerivedFunctorLiftInvFac`：∀ {C : Type 
u₁} {D : Type u₂} {H : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} C]   [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D] [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.rightDerivedNatIso_hom`：∀ {C : Type u_1} {D : Typ
e u_2} {H : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : 
CategoryTheory.Category.{v_3, u_2} …
· 使用引理 `CategoryTheory.Functor.rightDerivedNatTrans_fac`：rightDerivedNatTrans_fa
c (τ : F ⟶ F') : α ≫ whiskerLeft L (rightDerivedNatTrans RF RF' α α' W τ) = τ ≫ 
α'
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma isIso_of_isRightDerivedFunctor_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
    (hF : W.IsInvertedBy F) [RF.IsRightDerivedFunctor α W] :
    IsIso α := by
  have : α = (Localization.fac F hF L).inv ≫
    whiskerLeft _ (rightDerivedUnique _ _ (Localization.fac F hF L).inv α W).hom := by simp
  rw [this]
  infer_instance

variable {W} in
/-
**CategoryTheory.Functor.isRightDerivedFunctor_iff_of_inverts** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isRightDerivedFunctor_iff_of_inverts [L.IsLocalization W] {F : C ⥤ H} (RF 
: D ⥤ H) (α : F ⟶ L ⋙ RF) (hF : W.IsInvertedBy F) : RF.IsRightDerivedFunctor α W
 ↔ IsIso α
参数：RF : D ⥤ H；α : F ⟶ L ⋙ RF；hF : W.IsInvertedBy F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isIso_of_isRightDerivedFunctor_of_inverts`：isIso_
of_isRightDerivedFunctor_of_inverts [L.IsLocalization W] {F : C ⥤ H} (RF : D ⥤ H
) (α : F ⟶ L ⋙ RF) (hF : W.IsInvertedBy F) [RF.IsRight…
· 使用引理 `CategoryTheory.Functor.isRightDerivedFunctor_of_inverts`：isRightDerivedF
unctor_of_inverts [L.IsLocalization W] (F' : D ⥤ H) (e : L ⋙ F' ≅ F) : F'.IsRigh
tDerivedFunctor e.inv W where isLeftKanExtens…
-/
lemma isRightDerivedFunctor_iff_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
    (hF : W.IsInvertedBy F) :
    RF.IsRightDerivedFunctor α W ↔ IsIso α :=
  ⟨fun _ ↦ isIso_of_isRightDerivedFunctor_of_inverts RF α hF, fun _ ↦
    isRightDerivedFunctor_of_inverts W RF (asIso α).symm⟩

end

end Functor

end CategoryTheory

