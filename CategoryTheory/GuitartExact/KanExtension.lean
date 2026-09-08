/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GuitartExact.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Guitart exact squares and Kan extensions

Given a Guitart exact square `w : T ⋙ R ⟶ L ⋙ B`,
```
     T
  C₁ ⥤ C₂
L |     | R
  v     v
  C₃ ⥤ C₄
     B
```
we show that an extension `F' : C₄ ⥤ D` of `F : C₂ ⥤ D` along `R`
is a pointwise left Kan extension at `B.obj X₃` iff
the composition `T ⋙ F'` is a pointwise left Kan extension at `X₃`
of `B ⋙ F'`.

When suitable (pointwise) left Kan extensions exist, we also show that
the natural transformation of functors `(C₂ ⥤ D) ⥤ C₃ ⥤ D`
`(whiskeringLeft C₁ C₂ D).obj T ⋙ L.lan ⟶ R.lan ⋙ (whiskeringLeft C₃ C₄ D).obj B`
induced by a Guitart exact square `w` is an isomorphism.

## References

* https://ncatlab.org/nlab/show/exact+square

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Limits

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} {D : Type u₅}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  [Category.{v₅} D]

namespace Functor.LeftExtension

variable {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
  {F : C₂ ⥤ D} (E : R.LeftExtension F)

/-- Given a square `w : TwoSquare T L R B` (consisting of a natural transformation
`T ⋙ R ⟶ L ⋙ B`), this is the obvious map `R.LeftExtension F → L.LeftExtension (T ⋙ F)`
obtained by the precomposition with `B` and the postcomposition with `w`. -/
/-
**CategoryTheory.Functor.LeftExtension.compTwoSquare** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：compTwoSquare (w : TwoSquare T L R B) : L.LeftExtension (T ⋙ F)
参数：w : TwoSquare T L R B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a square `w : TwoSquare T L R B` (consisting of a natural transformation
`T ⋙ R ⟶ L ⋙ B`), this is the obvious map `R.LeftExtension F → L.LeftExtension (
T ⋙ F)`
obtained by the precomposition with `B` and the postcomposition with `w`.
-/
abbrev compTwoSquare (w : TwoSquare T L R B) : L.LeftExtension (T ⋙ F) :=
  LeftExtension.mk (B ⋙ E.right)
    (whiskerLeft _ E.hom ≫ (associator _ _ _).inv ≫
      whiskerRight w.natTrans _ ≫ (associator _ _ _).hom)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- If `w : TwoSquare T L R B` is a Guitart exact square, and `E` is a left extension
of `F` along `R`, then `E` is a pointwise left Kan extension of `F` along `R` at
`B.obj X₃` iff `E.compTwoSquare w` is a pointwise left Kan extension
of `T ⋙ F` along `L` at `X₃`. -/
/-
**CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionAtCompTwoSquar
eEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：isPointwiseLeftKanExtensionAtCompTwoSquareEquiv (w : TwoSquare T L R B) (X
₃ : C₃) [Final (w.costructuredArrowRightwards X₃)] : (E.compTwoSquare w).IsPoint
wiseLeftKanExtensionAt X₃ ≃ E.IsPointwiseLeftKanExtensionAt (B.obj X₃)
参数：w : TwoSquare T L R B；X₃ : C₃；w.costructuredArrowRightwards X₃。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If `w : TwoSquare T L R B` is a Guitart exact square, and `E` is a left extensio
n
of `F` along `R`, then `E` is a pointwise left Kan extension of `F` along `R` at
`B.obj X₃` iff `E.compTwoSquare w` is a pointwise left Kan extension
of `T ⋙ F` along `L` at `X₃`.
-/
noncomputable def isPointwiseLeftKanExtensionAtCompTwoSquareEquiv
    (w : TwoSquare T L R B) (X₃ : C₃) [Final (w.costructuredArrowRightwards X₃)] :
    (E.compTwoSquare w).IsPointwiseLeftKanExtensionAt X₃ ≃
      E.IsPointwiseLeftKanExtensionAt (B.obj X₃) := by
  refine Equiv.trans ?_ (Final.isColimitWhiskerEquiv (w.costructuredArrowRightwards X₃) _)
  exact IsColimit.equivIsoColimit (Cocone.ext (Iso.refl _))
/-
**CategoryTheory.Functor.LeftExtension.nonempty_isPointwiseLeftKanExtensionAt_co
mpTwoSquare_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.LeftExtension`
。
形式化陈述：nonempty_isPointwiseLeftKanExtensionAt_compTwoSquare_iff (w : TwoSquare T 
L R B) (X₃ : C₃) [Final (w.costructuredArrowRightwards X₃)] : Nonempty ((E.compT
woSquare w).IsPointwiseLeftKanExtensionAt X₃) ↔ Nonempty (E.IsPointwiseLeftKanEx
tensionAt (B.obj X₃))
参数：w : TwoSquare T L R B；X₃ : C₃；w.costructuredArrowRightwards X₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
-/
lemma nonempty_isPointwiseLeftKanExtensionAt_compTwoSquare_iff
    (w : TwoSquare T L R B) (X₃ : C₃) [Final (w.costructuredArrowRightwards X₃)] :
    Nonempty ((E.compTwoSquare w).IsPointwiseLeftKanExtensionAt X₃) ↔
      Nonempty (E.IsPointwiseLeftKanExtensionAt (B.obj X₃)) :=
  (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w _).nonempty_congr

variable {E} in
/-- If `w : TwoSquare T L R B` is a Guitart exact square, and `E` is a pointwise
left Kan extension of `F` along `R`, then `E.compTwoSquare w` is a pointwise left
Kan extension of `T ⋙ F` along `L`. -/
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.compTwoSquare
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeft
KanExtension`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     {C₃ : Type u₃} →       {C₄ : Type 
u₄} →         {D : Type u₅} →           [inst : CategoryTheory.Category.{v₁, u₁}
 C₁] →             [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] →             
  [inst_2 : CategoryTheory.Category.{v₃, u₃} C₃] →                 [inst_3 : Cat
egoryTheory.Category.{v₄, u₄} C₄] →                   [inst_4 : CategoryTheory.C
ategory.{v₅, u₅} D] →                     {T : CategoryTheory.Functor C₁ C₂} →  
                     {L : CategoryTheory.Functor C₁ C₃} →                       
  {R : CategoryTheory.Functor C₂ C₄} →                           {B : CategoryTh
eory.Functor C₃ C₄} →                             {F : CategoryTheory.Functor C₂
 D} →                               {E : R.LeftExtension F} →                   
              E.IsPointwiseLeftKanExtension →                                   
(w : CategoryTheory.TwoSquare T L R B) →                                     [w.
GuitartExact] → (E.compTwoSquare w).IsPointwiseLeftKanExtension
参数：w : CategoryTheory.TwoSquare T L R B；E.compTwoSquare w。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.TwoSquare.instFinalCostructuredArrowObjCostructuredArrowR
ightwardsOfGuitartExact`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Ty
pe u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.C
atego…

--- 原说明 ---
If `w : TwoSquare T L R B` is a Guitart exact square, and `E` is a pointwise
left Kan extension of `F` along `R`, then `E.compTwoSquare w` is a pointwise lef
t
Kan extension of `T ⋙ F` along `L`.
-/
noncomputable def IsPointwiseLeftKanExtension.compTwoSquare
    (h : E.IsPointwiseLeftKanExtension) (w : TwoSquare T L R B) [w.GuitartExact] :
    (E.compTwoSquare w).IsPointwiseLeftKanExtension :=
  fun X₃ ↦ (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w X₃).symm (h _)

/-- If `w : TwoSquare T L R B` is a Guitart exact square, with `B` essentially surjective,
and `E` is a left extension of `F` along `R`, then `E` is a pointwise
left Kan extension of `F` along `R` provided `E.compTwoSquare w` is a pointwise left
Kan extension of `T ⋙ F` along `L`. -/
/-
**CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionOfCompTwoSquar
e** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：isPointwiseLeftKanExtensionOfCompTwoSquare (w : TwoSquare T L R B) [w.Guit
artExact] [B.EssSurj] (h : (E.compTwoSquare w).IsPointwiseLeftKanExtension) : E.
IsPointwiseLeftKanExtension
参数：w : TwoSquare T L R B；h : (E.compTwoSquare w).IsPointwiseLeftKanExtension。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `w : TwoSquare T L R B` is a Guitart exact square, with `B` essentially surje
ctive,
and `E` is a left extension of `F` along `R`, then `E` is a pointwise
left Kan extension of `F` along `R` provided `E.compTwoSquare w` is a pointwise 
left
Kan extension of `T ⋙ F` along `L`.
-/
noncomputable def isPointwiseLeftKanExtensionOfCompTwoSquare
    (w : TwoSquare T L R B) [w.GuitartExact] [B.EssSurj]
    (h : (E.compTwoSquare w).IsPointwiseLeftKanExtension) :
    E.IsPointwiseLeftKanExtension :=
  fun X₄ ↦ E.isPointwiseLeftKanExtensionAtOfIso'
    (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w _ (h (B.objPreimage X₄)))
    (B.objObjPreimageIso X₄)

/-- If `w : TwoSquare T L R B` is a Guitart exact square, with `B` essentially surjective,
and `E` is a left extension of `F` along `R`, then `E` is a pointwise left Kan extension
of `F` along `R` iff `E.compTwoSquare w` is a pointwise left Kan extension
of `T ⋙ F` along `L`. -/
/-
**CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionEquivOfGuitart
Exact** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：isPointwiseLeftKanExtensionEquivOfGuitartExact (w : TwoSquare T L R B) [w.
GuitartExact] [B.EssSurj] : (E.compTwoSquare w).IsPointwiseLeftKanExtension ≃ E.
IsPointwiseLeftKanExtension where toFun h
参数：w : TwoSquare T L R B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `w : TwoSquare T L R B` is a Guitart exact square, with `B` essentially surje
ctive,
and `E` is a left extension of `F` along `R`, then `E` is a pointwise left Kan e
xtension
of `F` along `R` iff `E.compTwoSquare w` is a pointwise left Kan extension
of `T ⋙ F` along `L`.
-/
noncomputable def isPointwiseLeftKanExtensionEquivOfGuitartExact
    (w : TwoSquare T L R B) [w.GuitartExact] [B.EssSurj] :
    (E.compTwoSquare w).IsPointwiseLeftKanExtension ≃
      E.IsPointwiseLeftKanExtension where
  toFun h := E.isPointwiseLeftKanExtensionOfCompTwoSquare w h
  invFun h := h.compTwoSquare w
  left_inv _ := by subsingleton
  right_inv _ := by subsingleton

end Functor.LeftExtension

namespace TwoSquare

variable {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
  (w : TwoSquare T L R B)

include w

/-
**CategoryTheory.TwoSquare.hasPointwiseLeftKanExtensionAt_iff** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.TwoSquare`。
形式化陈述：hasPointwiseLeftKanExtensionAt_iff (F : C₂ ⥤ D) (X₃ : C₃) [(w.costructured
ArrowRightwards X₃).Final] : L.HasPointwiseLeftKanExtensionAt (T ⋙ F) X₃ ↔ R.Has
PointwiseLeftKanExtensionAt F (B.obj X₃)
参数：F : C₂ ⥤ D；X₃ : C₃；w.costructuredArrowRightwards X₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.Final.hasColimit_comp_iff`：hasColimit_comp_iff : 
HasColimit (F ⋙ G) ↔ HasColimit G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasPointwiseLeftKanExtensionAt_iff
    (F : C₂ ⥤ D) (X₃ : C₃) [(w.costructuredArrowRightwards X₃).Final] :
    L.HasPointwiseLeftKanExtensionAt (T ⋙ F) X₃ ↔
      R.HasPointwiseLeftKanExtensionAt F (B.obj X₃) := by
  dsimp [Functor.HasPointwiseLeftKanExtensionAt]
  rw [← Functor.Final.hasColimit_comp_iff (w.costructuredArrowRightwards X₃)]
  rfl
/-
**CategoryTheory.TwoSquare.hasPointwiseLeftKanExtension_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.TwoSquare`。
形式化陈述：hasPointwiseLeftKanExtension_iff [w.GuitartExact] [B.EssSurj] (F : C₂ ⥤ D)
 : L.HasPointwiseLeftKanExtension (T ⋙ F) ↔ R.HasPointwiseLeftKanExtension F
参数：F : C₂ ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `CategoryTheory.TwoSquare.hasPointwiseLeftKanExtensionAt_iff`：hasPointwis
eLeftKanExtensionAt_iff (F : C₂ ⥤ D) (X₃ : C₃) [(w.costructuredArrowRightwards X
₃).Final] : L.HasPointwiseLeftKanExtensionAt (T ⋙…
· 使用定理 `CategoryTheory.TwoSquare.instFinalCostructuredArrowObjCostructuredArrowR
ightwardsOfGuitartExact`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Ty
pe u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.C
atego…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso`：hasPoi
ntwiseLeftKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) : HasPointwiseLeft
KanExtensionAt L F Y₁ ↔ HasPointwiseLeftKanExtensionAt…
-/
lemma hasPointwiseLeftKanExtension_iff [w.GuitartExact] [B.EssSurj] (F : C₂ ⥤ D) :
    L.HasPointwiseLeftKanExtension (T ⋙ F) ↔
      R.HasPointwiseLeftKanExtension F := by
  dsimp [Functor.HasPointwiseLeftKanExtension]
  simp only [hasPointwiseLeftKanExtensionAt_iff w]
  refine ⟨fun h X₄ ↦ ?_, fun h _ ↦ h _⟩
  rw [← Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso _ _ (B.objObjPreimageIso X₄)]
  apply h
/-
**CategoryTheory.TwoSquare.hasPointwiseLeftKanExtension** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.TwoSquare`。
形式化陈述：hasPointwiseLeftKanExtension [w.GuitartExact] (F : C₂ ⥤ D) [R.HasPointwise
LeftKanExtension F] : L.HasPointwiseLeftKanExtension (T ⋙ F)
参数：F : C₂ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.hasPoin
twiseLeftKanExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_
2} …
-/
lemma hasPointwiseLeftKanExtension [w.GuitartExact]
    (F : C₂ ⥤ D) [R.HasPointwiseLeftKanExtension F] :
    L.HasPointwiseLeftKanExtension (T ⋙ F) :=
  ((R.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
    F).compTwoSquare w).hasPointwiseLeftKanExtension
/-
**CategoryTheory.TwoSquare.hasLeftKanExtension** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.TwoSquare`。
形式化陈述：hasLeftKanExtension [w.GuitartExact] (F : C₂ ⥤ D) [R.HasPointwiseLeftKanEx
tension F] : L.HasLeftKanExtension (T ⋙ F)
参数：F : C₂ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.hasPointwiseLeftKanExtension`：hasPointwiseLeftK
anExtension [w.GuitartExact] (F : C₂ ⥤ D) [R.HasPointwiseLeftKanExtension F] : L
.HasPointwiseLeftKanExtension (T ⋙ F)
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
-/
lemma hasLeftKanExtension [w.GuitartExact]
    (F : C₂ ⥤ D) [R.HasPointwiseLeftKanExtension F] :
    L.HasLeftKanExtension (T ⋙ F) := by
  have := w.hasPointwiseLeftKanExtension F
  infer_instance

section

open CategoryTheory.Functor

section

variable [∀ (F : C₁ ⥤ D), L.HasLeftKanExtension F] [∀ (F : C₂ ⥤ D), R.HasLeftKanExtension F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The base change natural transformation for left Kan extensions associated to
a 2-square. -/
@[simps -isSimp]
/-
**CategoryTheory.TwoSquare.lanBaseChange** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.TwoSquare`。
形式化陈述：lanBaseChange : (whiskeringLeft C₁ C₂ D).obj T ⋙ L.lan ⟶ R.lan ⋙ (whiskeri
ngLeft C₃ C₄ D).obj B where app F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The base change natural transformation for left Kan extensions associated to
a 2-square.
-/
noncomputable def lanBaseChange :
    (whiskeringLeft C₁ C₂ D).obj T ⋙ L.lan ⟶ R.lan ⋙ (whiskeringLeft C₃ C₄ D).obj B where
  app F :=
    ((L.lanAdjunction D).homEquiv _ _).symm
      ((LeftExtension.mk _ (R.lanUnit.app F)).compTwoSquare w).hom
  naturality {F₁ F₂} τ := by
    dsimp
    refine (Adjunction.homEquiv_naturality_left_symm ..).symm.trans
      (Eq.trans ?_ (Adjunction.homEquiv_naturality_right_symm ..))
    congr 1
    ext X
    have := R.lanUnit.naturality_app (T.obj X) τ
    simp [reassoc_of% this]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.TwoSquare.isIso_lanBaseChange_app_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.TwoSquare`。
形式化陈述：isIso_lanBaseChange_app_iff (F : C₂ ⥤ D) : IsIso (w.lanBaseChange.app F) ↔
 IsLeftKanExtension _ ((LeftExtension.mk _ (R.lanUnit.app F)).compTwoSquare w).h
om
参数：F : C₂ ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.TwoSquare.lanBaseChange_app`：∀ {C₁ : Type u₁} {C₂ : Type 
u₂} {C₃ : Type u₃} {C₄ : Type u₄} {D : Type u₅} [inst : CategoryTheory.Category.
{v₁, u₁} C₁]   [inst_1 : Categor…
· 使用引理 `CategoryTheory.Functor.isIso_lanAdjunction_homEquiv_symm_iff`：isIso_lanA
djunction_homEquiv_symm_iff {F : C ⥤ H} {G : D ⥤ H} (α : F ⟶ L ⋙ G) : IsIso (((L
.lanAdjunction H).homEquiv _ _).symm α) ↔ G.IsLeft…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isIso_lanBaseChange_app_iff (F : C₂ ⥤ D) :
    IsIso (w.lanBaseChange.app F) ↔
      IsLeftKanExtension _ ((LeftExtension.mk _ (R.lanUnit.app F)).compTwoSquare w).hom := by
  rw [lanBaseChange_app, isIso_lanAdjunction_homEquiv_symm_iff]
  simp
/-
**CategoryTheory.TwoSquare.isIso_lanBaseChange_app** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.TwoSquare`。
形式化陈述：isIso_lanBaseChange_app (F : C₂ ⥤ D) [R.HasPointwiseLeftKanExtension F] [w
.GuitartExact] : IsIso (w.lanBaseChange.app F)
参数：F : C₂ ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.TwoSquare.isIso_lanBaseChange_app_iff`：isIso_lanBaseChang
e_app_iff (F : C₂ ⥤ D) : IsIso (w.lanBaseChange.app F) ↔ IsLeftKanExtension _ ((
LeftExtension.mk _ (R.lanUnit.app F)).comp…
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionObjLanAppLanUnit`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftK
anExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheo
ry.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
-/
instance isIso_lanBaseChange_app (F : C₂ ⥤ D)
    [R.HasPointwiseLeftKanExtension F] [w.GuitartExact] :
    IsIso (w.lanBaseChange.app F) := by
  rw [isIso_lanBaseChange_app_iff]
  let hF := isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _ (R.lanUnit.app F)
  exact (hF.compTwoSquare w).isLeftKanExtension

end

/-
**CategoryTheory.TwoSquare.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.TwoSquare`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ (F : C₁ ⥤ D), L.HasLeftKanExtension F]
    [∀ (F : C₂ ⥤ D), R.HasPointwiseLeftKanExtension F] [w.GuitartExact] :
    IsIso (w.lanBaseChange (D := D)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  infer_instance

end

end TwoSquare

end CategoryTheory

