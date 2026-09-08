/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Pointwise Kan extensions

In this file, we define the notion of pointwise (left) Kan extension. Given two functors
`L : C ⥤ D` and `F : C ⥤ H`, and `E : LeftExtension L F`, we introduce a cocone
`E.coconeAt Y` for the functor `CostructuredArrow.proj L Y ⋙ F : CostructuredArrow L Y ⥤ H`
the point of which is `E.right.obj Y`, and the type `E.IsPointwiseLeftKanExtensionAt Y`
which expresses that `E.coconeAt Y` is a colimit. When this holds for all `Y : D`,
we may say that `E` is a pointwise left Kan extension (`E.IsPointwiseLeftKanExtension`).

Conversely, when `CostructuredArrow.proj L Y ⋙ F` has a colimit, we say that
`F` has a pointwise left Kan extension at `Y : D` (`HasPointwiseLeftKanExtensionAt L F Y`),
and if this holds for all `Y : D`, we construct a functor
`pointwiseLeftKanExtension L F : D ⥤ H` and show it is a pointwise Kan extension.

A dual API for pointwise right Kan extension is also formalized.

## References
* https://ncatlab.org/nlab/show/Kan+extension

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D D' H : Type*} [Category* C] [Category* D] [Category* D'] [Category* H]
  (L : C ⥤ D) (L' : C ⥤ D') (F : C ⥤ H)

/-- The condition that a functor `F` has a pointwise left Kan extension along `L` at `Y`.
It means that the functor `CostructuredArrow.proj L Y ⋙ F : CostructuredArrow L Y ⥤ H`
has a colimit. -/
/-
**CategoryTheory.Functor.HasPointwiseLeftKanExtensionAt** 是 Mathlib 中的一个缩写定义，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：HasPointwiseLeftKanExtensionAt (Y : D)
参数：Y : D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a functor `F` has a pointwise left Kan extension along `L` at
 `Y`.
It means that the functor `CostructuredArrow.proj L Y ⋙ F : CostructuredArrow L 
Y ⥤ H`
has a colimit.
-/
abbrev HasPointwiseLeftKanExtensionAt (Y : D) :=
  HasColimit (CostructuredArrow.proj L Y ⋙ F)

/-- The condition that a functor `F` has a pointwise left Kan extension along `L`: it means
that it has a pointwise left Kan extension at any object. -/
/-
**CategoryTheory.Functor.HasPointwiseLeftKanExtension** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：HasPointwiseLeftKanExtension
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a functor `F` has a pointwise left Kan extension along `L`: i
t means
that it has a pointwise left Kan extension at any object.
-/
abbrev HasPointwiseLeftKanExtension := ∀ (Y : D), HasPointwiseLeftKanExtensionAt L F Y

/-- The condition that a functor `F` has a pointwise right Kan extension along `L` at `Y`.
It means that the functor `StructuredArrow.proj Y L ⋙ F : StructuredArrow Y L ⥤ H`
has a limit. -/
/-
**CategoryTheory.Functor.HasPointwiseRightKanExtensionAt** 是 Mathlib 中的一个缩写定义，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：HasPointwiseRightKanExtensionAt (Y : D)
参数：Y : D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a functor `F` has a pointwise right Kan extension along `L` a
t `Y`.
It means that the functor `StructuredArrow.proj Y L ⋙ F : StructuredArrow Y L ⥤ 
H`
has a limit.
-/
abbrev HasPointwiseRightKanExtensionAt (Y : D) :=
  HasLimit (StructuredArrow.proj Y L ⋙ F)

/-- The condition that a functor `F` has a pointwise right Kan extension along `L`: it means
that it has a pointwise right Kan extension at any object. -/
/-
**CategoryTheory.Functor.HasPointwiseRightKanExtension** 是 Mathlib 中的一个缩写定义，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：HasPointwiseRightKanExtension
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a functor `F` has a pointwise right Kan extension along `L`: 
it means
that it has a pointwise right Kan extension at any object.
-/
abbrev HasPointwiseRightKanExtension := ∀ (Y : D), HasPointwiseRightKanExtensionAt L F Y
/-
**CategoryTheory.Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseLeftKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) : HasP
ointwiseLeftKanExtensionAt L F Y₁ ↔ HasPointwiseLeftKanExtensionAt L F Y₂
参数：e : Y₁ ≅ Y₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasPointwiseLeftKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) :
    HasPointwiseLeftKanExtensionAt L F Y₁ ↔
      HasPointwiseLeftKanExtensionAt L F Y₂ := by
  revert Y₁ Y₂ e
  suffices ∀ ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [HasPointwiseLeftKanExtensionAt L F Y₁],
      HasPointwiseLeftKanExtensionAt L F Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasColimit ((CostructuredArrow.mapIso e.symm).functor ⋙ CostructuredArrow.proj L Y₁ ⋙ F)
  infer_instance
/-
**CategoryTheory.Functor.hasPointwiseRightKanExtensionAt_iff_of_iso** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseRightKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) : Has
PointwiseRightKanExtensionAt L F Y₁ ↔ HasPointwiseRightKanExtensionAt L F Y₂
参数：e : Y₁ ≅ Y₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasPointwiseRightKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) :
    HasPointwiseRightKanExtensionAt L F Y₁ ↔
      HasPointwiseRightKanExtensionAt L F Y₂ := by
  revert Y₁ Y₂ e
  suffices ∀ ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [HasPointwiseRightKanExtensionAt L F Y₁],
      HasPointwiseRightKanExtensionAt L F Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasLimit ((StructuredArrow.mapIso e.symm).functor ⋙ StructuredArrow.proj Y₁ L ⋙ F)
  infer_instance

variable {L} in
/-
**CategoryTheory.Functor.hasPointwiseLeftKanExtensionAt_iff_of_natIso_left** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hasPointwiseLeftKanExtensionAt_iff_of_natIso_left {L' : C ⥤ D} (e : L ≅ L') (Y : D) :
    HasPointwiseLeftKanExtensionAt L F Y ↔
      HasPointwiseLeftKanExtensionAt L' F Y := by
  revert L L' e
  suffices ∀ ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [HasPointwiseLeftKanExtensionAt L F Y],
      HasPointwiseLeftKanExtensionAt L' F Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : CostructuredArrow L' Y ≌ CostructuredArrow L Y := Comma.mapLeftIso _ e.symm
  let e' : CostructuredArrow.proj L' Y ⋙ F ≅
    Φ.functor ⋙ CostructuredArrow.proj L Y ⋙ F := Iso.refl _
  exact hasColimit_of_iso e'

variable {L} in
/-
**CategoryTheory.Functor.hasPointwiseRightKanExtensionAt_iff_of_natIso_left** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hasPointwiseRightKanExtensionAt_iff_of_natIso_left {L' : C ⥤ D} (e : L ≅ L') (Y : D) :
    HasPointwiseRightKanExtensionAt L F Y ↔
      HasPointwiseRightKanExtensionAt L' F Y := by
  revert L L' e
  suffices ∀ ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [HasPointwiseRightKanExtensionAt L F Y],
      HasPointwiseRightKanExtensionAt L' F Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : StructuredArrow Y L' ≌ StructuredArrow Y L := Comma.mapRightIso _ e.symm
  let e' : StructuredArrow.proj Y L' ⋙ F ≅
    Φ.functor ⋙ StructuredArrow.proj Y L ⋙ F := Iso.refl _
  exact hasLimit_of_iso e'.symm
/-
**CategoryTheory.Functor.hasPointwiseLeftKanExtensionAt_of_equivalence** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseLeftKanExtensionAt_of_equivalence (E : D ≌ D') (eL : L ⋙ E.fun
ctor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') [HasPointwiseLeftKanExte
nsionAt L F Y] : HasPointwiseLeftKanExtensionAt L' F Y'
参数：E : D ≌ D'；eL : L ⋙ E.functor ≅ L'；Y : D；Y' : D'；e : E.functor.obj Y ≅ Y'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise.0.Categor
yTheory.Functor.hasPointwiseLeftKanExtensionAt_iff_of_natIso_left`：∀ {C : Type u
_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用引理 `CategoryTheory.Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso`：hasPoi
ntwiseLeftKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) : HasPointwiseLeft
KanExtensionAt L F Y₁ ↔ HasPointwiseLeftKanExtensionAt…
· 使用定理 `CategoryTheory.CostructuredArrow.isEquivalence_post`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {B : Type u₄} [ins…
· 使用定理 `CategoryTheory.Limits.hasColimit_of_equivalence_comp`：hasColimit_of_equi
valence_comp (e : K ≌ J) [HasColimit (e.functor ⋙ F)] : HasColimit F
-/
lemma hasPointwiseLeftKanExtensionAt_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y')
    [HasPointwiseLeftKanExtensionAt L F Y] :
    HasPointwiseLeftKanExtensionAt L' F Y' := by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_natIso_left F eL,
    hasPointwiseLeftKanExtensionAt_iff_of_iso _ F e.symm]
  let Φ := CostructuredArrow.post L E.functor Y
  have : HasColimit ((asEquivalence Φ).functor ⋙
    CostructuredArrow.proj (L ⋙ E.functor) (E.functor.obj Y) ⋙ F) :=
    (inferInstance : HasPointwiseLeftKanExtensionAt L F Y)
  exact hasColimit_of_equivalence_comp (asEquivalence Φ)
/-
**CategoryTheory.Functor.hasPointwiseLeftKanExtensionAt_iff_of_equivalence** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseLeftKanExtensionAt_iff_of_equivalence (E : D ≌ D') (eL : L ⋙ E
.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') : HasPointwiseLeftKa
nExtensionAt L F Y ↔ HasPointwiseLeftKanExtensionAt L' F Y'
参数：E : D ≌ D'；eL : L ⋙ E.functor ≅ L'；Y : D；Y' : D'；e : E.functor.obj Y ≅ Y'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hasPointwiseLeftKanExtensionAt_of_equivalence`：ha
sPointwiseLeftKanExtensionAt_of_equivalence (E : D ≌ D') (eL : L ⋙ E.functor ≅ L
') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') [HasPointw…
-/
lemma hasPointwiseLeftKanExtensionAt_iff_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') :
    HasPointwiseLeftKanExtensionAt L F Y ↔
      HasPointwiseLeftKanExtensionAt L' F Y' := by
  constructor
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L L' F E eL Y Y' e
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L' L F E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUnitor) Y' Y
      (E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app Y)
/-
**CategoryTheory.Functor.hasPointwiseRightKanExtensionAt_of_equivalence** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseRightKanExtensionAt_of_equivalence (E : D ≌ D') (eL : L ⋙ E.fu
nctor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') [HasPointwiseRightKanEx
tensionAt L F Y] : HasPointwiseRightKanExtensionAt L' F Y'
参数：E : D ≌ D'；eL : L ⋙ E.functor ≅ L'；Y : D；Y' : D'；e : E.functor.obj Y ≅ Y'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise.0.Categor
yTheory.Functor.hasPointwiseRightKanExtensionAt_iff_of_natIso_left`：∀ {C : Type 
u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]
   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightKanExtensionAt_iff_of_iso`：hasPo
intwiseRightKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) : HasPointwiseRi
ghtKanExtensionAt L F Y₁ ↔ HasPointwiseRightKanExtensio…
· 使用定理 `CategoryTheory.StructuredArrow.isEquivalence_post`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {B : Type u₄} [ins…
· 使用定理 `CategoryTheory.Limits.hasLimit_of_equivalence_comp`：hasLimit_of_equivale
nce_comp (e : K ≌ J) [HasLimit (e.functor ⋙ F)] : HasLimit F
-/
lemma hasPointwiseRightKanExtensionAt_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y')
    [HasPointwiseRightKanExtensionAt L F Y] :
    HasPointwiseRightKanExtensionAt L' F Y' := by
  rw [← hasPointwiseRightKanExtensionAt_iff_of_natIso_left F eL,
    hasPointwiseRightKanExtensionAt_iff_of_iso _ F e.symm]
  let Φ := StructuredArrow.post Y L E.functor
  have : HasLimit ((asEquivalence Φ).functor ⋙
    StructuredArrow.proj (E.functor.obj Y) (L ⋙ E.functor) ⋙ F) :=
    (inferInstance : HasPointwiseRightKanExtensionAt L F Y)
  exact hasLimit_of_equivalence_comp (asEquivalence Φ)
/-
**CategoryTheory.Functor.hasPointwiseRightKanExtensionAt_iff_of_equivalence** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseRightKanExtensionAt_iff_of_equivalence (E : D ≌ D') (eL : L ⋙ 
E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') : HasPointwiseRight
KanExtensionAt L F Y ↔ HasPointwiseRightKanExtensionAt L' F Y'
参数：E : D ≌ D'；eL : L ⋙ E.functor ≅ L'；Y : D；Y' : D'；e : E.functor.obj Y ≅ Y'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hasPointwiseRightKanExtensionAt_of_equivalence`：h
asPointwiseRightKanExtensionAt_of_equivalence (E : D ≌ D') (eL : L ⋙ E.functor ≅
 L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') [HasPoint…
-/
lemma hasPointwiseRightKanExtensionAt_iff_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') :
    HasPointwiseRightKanExtensionAt L F Y ↔
      HasPointwiseRightKanExtensionAt L' F Y' := by
  constructor
  · intro
    exact hasPointwiseRightKanExtensionAt_of_equivalence L L' F E eL Y Y' e
  · intro
    exact hasPointwiseRightKanExtensionAt_of_equivalence L' L F E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUnitor) Y' Y
      (E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app Y)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.HasPointwiseLeftKanExtensionAt.of_natIso** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Functor.HasPointwiseLeftKanExtensionAt`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L L' : CategoryTheory.Functor C D} {F F'
 : CategoryTheory.Functor C H} (Y : D) [L.HasPointwiseLeftKanExtensionAt F Y]   
(e₁ : L ≅ L') (e₂ : F ≅ F'), L'.HasPointwiseLeftKanExtensionAt F' Y
参数：Y : D；e₁ : L ≅ L'；e₂ : F ≅ F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise.0.Categor
yTheory.Functor.hasPointwiseLeftKanExtensionAt_iff_of_natIso_left`：∀ {C : Type u
_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.HasPointwiseLeftKanExtensionAt.eq_1`：∀ {C : Type 
u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]
   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.hasColimit_iff_of_iso`：∀ {J : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.
{v, u} C]   {F G : CategoryTheory…
-/
lemma HasPointwiseLeftKanExtensionAt.of_natIso {L L' : C ⥤ D} {F F' : C ⥤ H} (Y : D)
    [L.HasPointwiseLeftKanExtensionAt F Y] (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L'.HasPointwiseLeftKanExtensionAt F' Y := by
  rw [hasPointwiseLeftKanExtensionAt_iff_of_natIso_left _ e₁.symm]
  let e : CostructuredArrow.proj L Y ⋙ F' ≅ CostructuredArrow.proj L Y ⋙ F :=
    NatIso.ofComponents fun X ↦ (e₂.app _).symm
  rw [HasPointwiseLeftKanExtensionAt, hasColimit_iff_of_iso e]
  infer_instance

/-- `HasPointwiseLeftKanExtensionAt` is invariant when we replace `L` and `F` by isomorphic
functors. -/
/-
**CategoryTheory.Functor.hasPointwiseLeftKanExtensionAt_iff_of_natIso** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseLeftKanExtensionAt_iff_of_natIso {L L' : C ⥤ D} {F F' : C ⥤ H}
 {Y : D} (e₁ : L ≅ L') (e₂ : F ≅ F') : L.HasPointwiseLeftKanExtensionAt F Y ↔ L'
.HasPointwiseLeftKanExtensionAt F' Y
参数：e₁ : L ≅ L'；e₂ : F ≅ F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasPointwiseLeftKanExtensionAt.of_natIso`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_
1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …

--- 原说明 ---
`HasPointwiseLeftKanExtensionAt` is invariant when we replace `L` and `F` by iso
morphic
functors.
-/
lemma hasPointwiseLeftKanExtensionAt_iff_of_natIso {L L' : C ⥤ D} {F F' : C ⥤ H} {Y : D}
    (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L.HasPointwiseLeftKanExtensionAt F Y ↔ L'.HasPointwiseLeftKanExtensionAt F' Y :=
  ⟨fun _ ↦ .of_natIso Y e₁ e₂, fun _ ↦ .of_natIso Y e₁.symm e₂.symm⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.HasPointwiseRightKanExtensionAt.of_natIso** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Functor.HasPointwiseRightKanExtensionAt`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L L' : CategoryTheory.Functor C D} {F F'
 : CategoryTheory.Functor C H} (Y : D)   [L.HasPointwiseRightKanExtensionAt F Y]
 (e₁ : L ≅ L') (e₂ : F ≅ F'), L'.HasPointwiseRightKanExtensionAt F' Y
参数：Y : D；e₁ : L ≅ L'；e₂ : F ≅ F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise.0.Categor
yTheory.Functor.hasPointwiseRightKanExtensionAt_iff_of_natIso_left`：∀ {C : Type 
u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]
   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.HasPointwiseRightKanExtensionAt.eq_1`：∀ {C : Type
 u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C
]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.hasLimit_iff_of_iso`：hasLimit_iff_of_iso {F G : J 
⥤ C} (α : F ≅ G) : HasLimit F ↔ HasLimit G
-/
lemma HasPointwiseRightKanExtensionAt.of_natIso {L L' : C ⥤ D} {F F' : C ⥤ H} (Y : D)
    [L.HasPointwiseRightKanExtensionAt F Y] (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L'.HasPointwiseRightKanExtensionAt F' Y := by
  rw [hasPointwiseRightKanExtensionAt_iff_of_natIso_left _ e₁.symm]
  let e : StructuredArrow.proj Y L ⋙ F' ≅ StructuredArrow.proj Y L ⋙ F :=
    NatIso.ofComponents fun X ↦ (e₂.app _).symm
  rw [HasPointwiseRightKanExtensionAt, hasLimit_iff_of_iso e]
  infer_instance

/-- `HasPointwiseRightKanExtensionAt` is invariant when we replace `L` and `F` by isomorphic
functors. -/
/-
**CategoryTheory.Functor.hasPointwiseRightKanExtensionAt_iff_of_natIso** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseRightKanExtensionAt_iff_of_natIso {L L' : C ⥤ D} {F F' : C ⥤ H
} {Y : D} (e₁ : L ≅ L') (e₂ : F ≅ F') : L.HasPointwiseRightKanExtensionAt F Y ↔ 
L'.HasPointwiseRightKanExtensionAt F' Y
参数：e₁ : L ≅ L'；e₂ : F ≅ F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasPointwiseRightKanExtensionAt.of_natIso`：∀ {C :
 Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u
_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …

--- 原说明 ---
`HasPointwiseRightKanExtensionAt` is invariant when we replace `L` and `F` by is
omorphic
functors.
-/
lemma hasPointwiseRightKanExtensionAt_iff_of_natIso {L L' : C ⥤ D} {F F' : C ⥤ H} {Y : D}
    (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L.HasPointwiseRightKanExtensionAt F Y ↔ L'.HasPointwiseRightKanExtensionAt F' Y :=
  ⟨fun _ ↦ .of_natIso Y e₁ e₂, fun _ ↦ .of_natIso Y e₁.symm e₂.symm⟩
/-
**CategoryTheory.Functor.HasPointwiseLeftKanExtension.of_iso** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Functor.HasPointwiseLeftKanExtension`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L L' : CategoryTheory.Functor C D} {F F'
 : CategoryTheory.Functor C H} [L.HasPointwiseLeftKanExtension F]   (e₁ : L ≅ L'
) (e₂ : F ≅ F'), L'.HasPointwiseLeftKanExtension F'
参数：e₁ : L ≅ L'；e₂ : F ≅ F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasPointwiseLeftKanExtensionAt.of_natIso`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_
1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
-/
lemma HasPointwiseLeftKanExtension.of_iso {L L' : C ⥤ D} {F F' : C ⥤ H}
    [L.HasPointwiseLeftKanExtension F] (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L'.HasPointwiseLeftKanExtension F' :=
  fun _ ↦ .of_natIso _ e₁ e₂
/-
**CategoryTheory.Functor.HasPointwiseRightKanExtension.of_iso** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Functor.HasPointwiseRightKanExtension`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L L' : CategoryTheory.Functor C D} {F F'
 : CategoryTheory.Functor C H} [L.HasPointwiseRightKanExtension F]   (e₁ : L ≅ L
') (e₂ : F ≅ F'), L'.HasPointwiseRightKanExtension F'
参数：e₁ : L ≅ L'；e₂ : F ≅ F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasPointwiseRightKanExtensionAt.of_natIso`：∀ {C :
 Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u
_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
-/
lemma HasPointwiseRightKanExtension.of_iso {L L' : C ⥤ D} {F F' : C ⥤ H}
    [L.HasPointwiseRightKanExtension F] (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L'.HasPointwiseRightKanExtension F' :=
  fun _ ↦ .of_natIso _ e₁ e₂
/-
**CategoryTheory.Functor.hasPointwiseLeftKanExtension_iff_of_iso** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseLeftKanExtension_iff_of_iso {L L' : C ⥤ D} {F F' : C ⥤ H} (e₁ 
: L ≅ L') (e₂ : F ≅ F') : L.HasPointwiseLeftKanExtension F ↔ L'.HasPointwiseLeft
KanExtension F'
参数：e₁ : L ≅ L'；e₂ : F ≅ F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasPointwiseLeftKanExtension.of_iso`：∀ {C : Type 
u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]
   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
-/
lemma hasPointwiseLeftKanExtension_iff_of_iso {L L' : C ⥤ D} {F F' : C ⥤ H} (e₁ : L ≅ L')
    (e₂ : F ≅ F') :
    L.HasPointwiseLeftKanExtension F ↔ L'.HasPointwiseLeftKanExtension F' :=
  ⟨fun _ ↦ .of_iso e₁ e₂, fun _ ↦ .of_iso e₁.symm e₂.symm⟩
/-
**CategoryTheory.Functor.hasPointwiseRightKanExtension_iff_of_iso** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseRightKanExtension_iff_of_iso {L L' : C ⥤ D} {F F' : C ⥤ H} (e₁
 : L ≅ L') (e₂ : F ≅ F') : L.HasPointwiseRightKanExtension F ↔ L'.HasPointwiseRi
ghtKanExtension F'
参数：e₁ : L ≅ L'；e₂ : F ≅ F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasPointwiseRightKanExtension.of_iso`：∀ {C : Type
 u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C
]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
-/
lemma hasPointwiseRightKanExtension_iff_of_iso {L L' : C ⥤ D} {F F' : C ⥤ H} (e₁ : L ≅ L')
    (e₂ : F ≅ F') :
    L.HasPointwiseRightKanExtension F ↔ L'.HasPointwiseRightKanExtension F' :=
  ⟨fun _ ↦ .of_iso e₁ e₂, fun _ ↦ .of_iso e₁.symm e₂.symm⟩

namespace LeftExtension

variable {F L}
variable (E : LeftExtension L F)

set_option backward.defeqAttrib.useBackward true in
/-- The cocone for `CostructuredArrow.proj L Y ⋙ F` attached to `E : LeftExtension L F`.
The point of this cocone is `E.right.obj Y` -/
@[simps]
/-
**CategoryTheory.Functor.LeftExtension.coconeAt** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor.LeftExtension`。
形式化陈述：coconeAt (Y : D) : Cocone (CostructuredArrow.proj L Y ⋙ F) where pt
参数：Y : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone for `CostructuredArrow.proj L Y ⋙ F` attached to `E : LeftExtension L
 F`.
The point of this cocone is `E.right.obj Y`
-/
def coconeAt (Y : D) : Cocone (CostructuredArrow.proj L Y ⋙ F) where
  pt := E.right.obj Y
  ι :=
    { app := fun g => E.hom.app g.left ≫ E.right.map g.hom
      naturality := fun g₁ g₂ φ => by
        dsimp
        rw [← CostructuredArrow.w φ]
        simp only [NatTrans.naturality_assoc, Functor.comp_map,
          Functor.map_comp, comp_id] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (L F) in
/-- The cocones for `CostructuredArrow.proj L Y ⋙ F`, as a functor from `LeftExtension L F`. -/
@[simps]
/-
**CategoryTheory.Functor.LeftExtension.coconeAtFunctor** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：coconeAtFunctor (Y : D) : LeftExtension L F ⥤ Cocone (CostructuredArrow.pr
oj L Y ⋙ F) where obj E
参数：Y : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocones for `CostructuredArrow.proj L Y ⋙ F`, as a functor from `LeftExtensi
on L F`.
-/
def coconeAtFunctor (Y : D) :
    LeftExtension L F ⥤ Cocone (CostructuredArrow.proj L Y ⋙ F) where
  obj E := E.coconeAt Y
  map {E E'} φ := CoconeMorphism.mk (φ.right.app Y) (fun G => by
    dsimp
    rw [← StructuredArrow.w φ]
    simp)

/-- A left extension `E : LeftExtension L F` is a pointwise left Kan extension at `Y` when
`E.coconeAt Y` is a colimit cocone. -/
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：IsPointwiseLeftKanExtensionAt (Y : D)
参数：Y : D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left extension `E : LeftExtension L F` is a pointwise left Kan extension at `Y
` when
`E.coconeAt Y` is a colimit cocone.
-/
def IsPointwiseLeftKanExtensionAt (Y : D) := IsColimit (E.coconeAt Y)
/-
**CategoryTheory.Functor.LeftExtension.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Functor.LeftExtension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Y : D) : Subsingleton (E.IsPointwiseLeftKanExtensionAt Y) :=
  inferInstanceAs (Subsingleton (IsColimit _))

variable {E} in
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.hasPointwis
eLeftKanExtensionAt** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.LeftExtens
ion.IsPointwiseLeftKanExtensionAt`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} {E : L.LeftExtension F} {Y : D}   (h : E.IsPointwiseLef
tKanExtensionAt Y), L.HasPointwiseLeftKanExtensionAt F Y
参数：h : E.IsPointwiseLeftKanExtensionAt Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsPointwiseLeftKanExtensionAt.hasPointwiseLeftKanExtensionAt
    {Y : D} (h : E.IsPointwiseLeftKanExtensionAt Y) :
    HasPointwiseLeftKanExtensionAt L F Y := ⟨_, h⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isIso_hom_a
pp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwiseLe
ftKanExtensionAt`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} (E : L.LeftExtension F) {X : C}   (h : E.IsPointwiseLef
tKanExtensionAt (L.obj X)) [L.Full] [L.Faithful],   CategoryTheory.IsIso ((Categ
oryTheory.StructuredArrow.hom E).app X)
参数：E : L.LeftExtension F；h : E.IsPointwiseLeftKanExtensionAt (L.obj X)；(Category
Theory.StructuredArrow.hom E).app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.IsColimit.isIso_ι_app_of_isTerminal`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type u} [inst_1 : CategoryTh
eory.Category.{v, u} J]   {F : CategoryTheory.F…
-/
lemma IsPointwiseLeftKanExtensionAt.isIso_hom_app
    {X : C} (h : E.IsPointwiseLeftKanExtensionAt (L.obj X)) [L.Full] [L.Faithful] :
    IsIso (E.hom.app X) := by
  simpa using h.isIso_ι_app_of_isTerminal _ CostructuredArrow.mkIdTerminal

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The condition of being a pointwise left Kan extension at an object `Y` is
unchanged by replacing `Y` by an isomorphic object `Y'`. -/
/-
**CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionAtOfIso'** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：isPointwiseLeftKanExtensionAtOfIso' {Y : D} (hY : E.IsPointwiseLeftKanExte
nsionAt Y) {Y' : D} (e : Y ≅ Y') : E.IsPointwiseLeftKanExtensionAt Y'
参数：hY : E.IsPointwiseLeftKanExtensionAt Y；e : Y ≅ Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition of being a pointwise left Kan extension at an object `Y` is
unchanged by replacing `Y` by an isomorphic object `Y'`.
-/
def isPointwiseLeftKanExtensionAtOfIso'
    {Y : D} (hY : E.IsPointwiseLeftKanExtensionAt Y) {Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseLeftKanExtensionAt Y' :=
  IsColimit.ofIsoColimit (hY.whiskerEquivalence (CostructuredArrow.mapIso e.symm))
    (Cocone.ext (E.right.mapIso e))

set_option backward.isDefEq.respectTransparency.types false in
/-- The condition of being a pointwise left Kan extension at an object `Y` is
unchanged by replacing `Y` by an isomorphic object `Y'`. -/
/-
**CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionAtEquivOfIso'*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：isPointwiseLeftKanExtensionAtEquivOfIso' {Y Y' : D} (e : Y ≅ Y') : E.IsPoi
ntwiseLeftKanExtensionAt Y ≃ E.IsPointwiseLeftKanExtensionAt Y' where toFun h
参数：e : Y ≅ Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition of being a pointwise left Kan extension at an object `Y` is
unchanged by replacing `Y` by an isomorphic object `Y'`.
-/
def isPointwiseLeftKanExtensionAtEquivOfIso' {Y Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseLeftKanExtensionAt Y ≃ E.IsPointwiseLeftKanExtensionAt Y' where
  toFun h := E.isPointwiseLeftKanExtensionAtOfIso' h e
  invFun h := E.isPointwiseLeftKanExtensionAtOfIso' h e.symm
  left_inv h := by subsingleton
  right_inv h := by subsingleton

namespace IsPointwiseLeftKanExtensionAt

variable {E} {Y : D} (h : E.IsPointwiseLeftKanExtensionAt Y)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
include h in
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.hom_ext'** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKan
ExtensionAt`。
形式化陈述：hom_ext' {T : H} {f g : E.right.obj Y ⟶ T} (hfg : forall ⦃X : C⦄ (φ : L.ob
j X ⟶ Y), E.hom.app X ≫ E.right.map φ ≫ f = E.hom.app X ≫ E.right.map φ ≫ g) : f
 = g
参数：hfg : forall ⦃X : C⦄ (φ : L.obj X ⟶ Y), E.hom.app X ≫ E.right.map φ ≫ f = E.h
om.app X ≫ E.right.map φ ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma hom_ext' {T : H} {f g : E.right.obj Y ⟶ T}
    (hfg : ∀ ⦃X : C⦄ (φ : L.obj X ⟶ Y),
      E.hom.app X ≫ E.right.map φ ≫ f = E.hom.app X ≫ E.right.map φ ≫ g) : f = g :=
  h.hom_ext (fun j ↦ by simpa using hfg j.hom)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.comp_homEqu
iv_symm** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointw
iseLeftKanExtensionAt`。
形式化陈述：comp_homEquiv_symm {Z : H} (φ : CostructuredArrow.proj L Y ⋙ F ⟶ (Functor.
const _).obj Z) (g : CostructuredArrow L Y) : E.hom.app g.left ≫ E.right.map g.h
om ≫ h.homEquiv.symm φ = φ.app g
参数：φ : CostructuredArrow.proj L Y ⋙ F ⟶ (Functor.const _).obj Z；g : Costructured
Arrow L Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsColimit.ι_app_homEquiv_symm`：∀ {J : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.
Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
lemma comp_homEquiv_symm {Z : H}
    (φ : CostructuredArrow.proj L Y ⋙ F ⟶ (Functor.const _).obj Z)
    (g : CostructuredArrow L Y) :
    E.hom.app g.left ≫ E.right.map g.hom ≫ h.homEquiv.symm φ = φ.app g := by
  simpa using h.ι_app_homEquiv_symm φ g

variable [HasColimit (CostructuredArrow.proj L Y ⋙ F)]

/-- A pointwise left Kan extension of `F` along `L` applied to an object `Y` is isomorphic to
`colimit (CostructuredArrow.proj L Y ⋙ F)`. -/
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isoColimit*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftK
anExtensionAt`。
形式化陈述：isoColimit : E.right.obj Y ≅ colimit (CostructuredArrow.proj L Y ⋙ F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pointwise left Kan extension of `F` along `L` applied to an object `Y` is isom
orphic to
`colimit (CostructuredArrow.proj L Y ⋙ F)`.
-/
noncomputable def isoColimit :
    E.right.obj Y ≅ colimit (CostructuredArrow.proj L Y ⋙ F) :=
  h.coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensio
nAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_isoColimit_inv (g : CostructuredArrow L Y) :
    colimit.ι _ g ≫ h.isoColimit.inv = E.hom.app g.left ≫ E.right.map g.hom :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensio
nAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_isoColimit_hom (g : CostructuredArrow L Y) :
    E.hom.app g.left ≫ E.right.map g.hom ≫ h.isoColimit.hom =
      colimit.ι (CostructuredArrow.proj L Y ⋙ F) g := by
  simpa using! h.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) g

end IsPointwiseLeftKanExtensionAt

/-- Given `E : Functor.LeftExtension L F`, this is the property of objects where
`E` is a pointwise left Kan extension. -/
/-
**CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionAt** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：isPointwiseLeftKanExtensionAt : ObjectProperty D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `E : Functor.LeftExtension L F`, this is the property of objects where
`E` is a pointwise left Kan extension.
-/
def isPointwiseLeftKanExtensionAt : ObjectProperty D :=
  fun Y ↦ Nonempty (E.IsPointwiseLeftKanExtensionAt Y)
/-
**CategoryTheory.Functor.LeftExtension.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Functor.LeftExtension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : E.isPointwiseLeftKanExtensionAt.IsClosedUnderIsomorphisms where
  of_iso e h := ⟨E.isPointwiseLeftKanExtensionAtOfIso' h.some e⟩

/-- A left extension `E : LeftExtension L F` is a pointwise left Kan extension when
it is a pointwise left Kan extension at any object. -/
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension** 是 Mathlib 中
的一个缩写定义，位于命名空间 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：IsPointwiseLeftKanExtension
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left extension `E : LeftExtension L F` is a pointwise left Kan extension when
it is a pointwise left Kan extension at any object.
-/
abbrev IsPointwiseLeftKanExtension := ∀ (Y : D), E.IsPointwiseLeftKanExtensionAt Y

variable {E E'}

/-- If two left extensions `E` and `E'` are isomorphic, `E` is a pointwise
left Kan extension at `Y` iff `E'` is. -/
/-
**CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionAtEquivOfIso**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：isPointwiseLeftKanExtensionAtEquivOfIso (e : E ≅ E') (Y : D) : E.IsPointwi
seLeftKanExtensionAt Y ≃ E'.IsPointwiseLeftKanExtensionAt Y
参数：e : E ≅ E'；Y : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two left extensions `E` and `E'` are isomorphic, `E` is a pointwise
left Kan extension at `Y` iff `E'` is.
-/
def isPointwiseLeftKanExtensionAtEquivOfIso (e : E ≅ E') (Y : D) :
    E.IsPointwiseLeftKanExtensionAt Y ≃ E'.IsPointwiseLeftKanExtensionAt Y :=
  IsColimit.equivIsoColimit ((coconeAtFunctor L F Y).mapIso e)

/-- If two left extensions `E` and `E'` are isomorphic, `E` is a pointwise
left Kan extension iff `E'` is. -/
/-
**CategoryTheory.Functor.LeftExtension.isPointwiseLeftKanExtensionEquivOfIso** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：isPointwiseLeftKanExtensionEquivOfIso (e : E ≅ E') : E.IsPointwiseLeftKanE
xtension ≃ E'.IsPointwiseLeftKanExtension where toFun h
参数：e : E ≅ E'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If two left extensions `E` and `E'` are isomorphic, `E` is a pointwise
left Kan extension iff `E'` is.
-/
def isPointwiseLeftKanExtensionEquivOfIso (e : E ≅ E') :
    E.IsPointwiseLeftKanExtension ≃ E'.IsPointwiseLeftKanExtension where
  toFun h := fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y) (h Y)
  invFun h := fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y).symm (h Y)
  left_inv h := by simp
  right_inv h := by simp

variable (h : E.IsPointwiseLeftKanExtension)
include h
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.hasPointwiseL
eftKanExtension** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.LeftExtension.
IsPointwiseLeftKanExtension`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} {E : L.LeftExtension F}   (h : E.IsPointwiseLeftKanExte
nsion), L.HasPointwiseLeftKanExtension F
参数：h : E.IsPointwiseLeftKanExtension。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.hasPo
intwiseLeftKanExtensionAt`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst 
: CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2
, u_2} …
-/
lemma IsPointwiseLeftKanExtension.hasPointwiseLeftKanExtension :
    HasPointwiseLeftKanExtension L F :=
  fun Y => (h Y).hasPointwiseLeftKanExtensionAt

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The (unique) morphism from a pointwise left Kan extension. -/
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.homFrom** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExt
ension`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     {H : Type u_4} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_2, u_2} D] →           [inst_2 : CategoryTheory.Category.{v_4, u_4} H] →      
       {L : CategoryTheory.Functor C D} →               {F : CategoryTheory.Func
tor C H} →                 {E : L.LeftExtension F} → E.IsPointwiseLeftKanExtensi
on → (G : L.LeftExtension F) → E ⟶ G
参数：G : L.LeftExtension F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) morphism from a pointwise left Kan extension.
-/
def IsPointwiseLeftKanExtension.homFrom (G : LeftExtension L F) : E ⟶ G :=
  StructuredArrow.homMk
    { app := fun Y => (h Y).desc (LeftExtension.coconeAt G Y)
      naturality := fun Y₁ Y₂ φ => (h Y₁).hom_ext (fun X => by
        rw [(h Y₁).fac_assoc (coconeAt G Y₁) X]
        simpa using (h Y₂).fac (coconeAt G Y₂) ((CostructuredArrow.map φ).obj X)) }
    (by
      ext X
      simpa using (h (L.obj X)).fac (LeftExtension.coconeAt G _) (CostructuredArrow.mk (𝟙 _)))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.hom_ext** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExt
ension`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} {E : L.LeftExtension F}   (h : E.IsPointwiseLeftKanExte
nsion) {G : L.LeftExtension F} {f₁ f₂ : E ⟶ G}, f₁ = f₂
参数：h : E.IsPointwiseLeftKanExtension。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.StructuredArrow.hom_ext`：hom_ext {X Y : StructuredArrow S
 T} (f g : X ⟶ Y) (h : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.StructuredArrow.w`：w : X.hom ≫ T.map f.right = Y.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
-/
lemma IsPointwiseLeftKanExtension.hom_ext
    {G : LeftExtension L F} {f₁ f₂ : E ⟶ G} : f₁ = f₂ := by
  ext Y
  apply (h Y).hom_ext
  intro X
  have eq₁ := congr_app (StructuredArrow.w f₁) X.left
  have eq₂ := congr_app (StructuredArrow.w f₂) X.left
  dsimp at eq₁ eq₂ ⊢
  simp only [assoc, NatTrans.naturality]
  rw [reassoc_of% eq₁, reassoc_of% eq₂]

/-- A pointwise left Kan extension is universal, i.e. it is a left Kan extension. -/
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.isUniversal**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKa
nExtension`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     {H : Type u_4} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_2, u_2} D] →           [inst_2 : CategoryTheory.Category.{v_4, u_4} H] →      
       {L : CategoryTheory.Functor C D} →               {F : CategoryTheory.Func
tor C H} →                 {E : L.LeftExtension F} → E.IsPointwiseLeftKanExtensi
on → CategoryTheory.StructuredArrow.IsUniversal E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pointwise left Kan extension is universal, i.e. it is a left Kan extension.
-/
def IsPointwiseLeftKanExtension.isUniversal : E.IsUniversal :=
  IsInitial.ofUniqueHom h.homFrom (fun _ _ => h.hom_ext)
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftKanExte
nsion** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwis
eLeftKanExtension`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} {E : L.LeftExtension F}   (h : E.IsPointwiseLeftKanExte
nsion),   (CategoryTheory.StructuredArrow.right E).IsLeftKanExtension (CategoryT
heory.StructuredArrow.hom E)
参数：h : E.IsPointwiseLeftKanExtension；CategoryTheory.StructuredArrow.right E；Cate
goryTheory.StructuredArrow.hom E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsPointwiseLeftKanExtension.isLeftKanExtension :
    E.right.IsLeftKanExtension E.hom where
  nonempty_isUniversal := ⟨h.isUniversal⟩
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.hasLeftKanExt
ension** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwi
seLeftKanExtension`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} {E : L.LeftExtension F}   (h : E.IsPointwiseLeftKanExte
nsion), L.HasLeftKanExtension F
参数：h : E.IsPointwiseLeftKanExtension。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftK
anExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheo
ry.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.HasLeftKanExtension.mk`：∀ {C : Type u_1} {H : Typ
e u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : 
CategoryTheory.Category.{v_3, u_3} …
-/
lemma IsPointwiseLeftKanExtension.hasLeftKanExtension :
    HasLeftKanExtension L F :=
  have := h.isLeftKanExtension
  HasLeftKanExtension.mk E.right E.hom
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.isIso_hom** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanE
xtension`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} {E : L.LeftExtension F}   (h : E.IsPointwiseLeftKanExte
nsion) [L.Full] [L.Faithful], CategoryTheory.IsIso (CategoryTheory.StructuredArr
ow.hom E)
参数：h : E.IsPointwiseLeftKanExtension；CategoryTheory.StructuredArrow.hom E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isIso
_hom_app`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.
Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
lemma IsPointwiseLeftKanExtension.isIso_hom [L.Full] [L.Faithful] :
    IsIso (E.hom) :=
  have := fun X => (h (L.obj X)).isIso_hom_app
  NatIso.isIso_of_isIso_app ..

end LeftExtension

namespace RightExtension

variable {F L}
variable (E E' : RightExtension L F)

set_option backward.defeqAttrib.useBackward true in
/-- The cone for `StructuredArrow.proj Y L ⋙ F` attached to `E : RightExtension L F`.
The point of this cone is `E.left.obj Y` -/
@[simps]
/-
**CategoryTheory.Functor.RightExtension.coneAt** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor.RightExtension`。
形式化陈述：coneAt (Y : D) : Cone (StructuredArrow.proj Y L ⋙ F) where pt
参数：Y : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone for `StructuredArrow.proj Y L ⋙ F` attached to `E : RightExtension L F`
.
The point of this cone is `E.left.obj Y`
-/
def coneAt (Y : D) : Cone (StructuredArrow.proj Y L ⋙ F) where
  pt := E.left.obj Y
  π :=
    { app := fun g ↦ E.left.map g.hom ≫ E.hom.app g.right
      naturality := fun g₁ g₂ φ ↦ by
        dsimp
        rw [assoc, id_comp, ← StructuredArrow.w φ, Functor.map_comp, assoc]
        congr 1
        apply E.hom.naturality }

set_option backward.defeqAttrib.useBackward true in
variable (L F) in
/-- The cones for `StructuredArrow.proj Y L ⋙ F`, as a functor from `RightExtension L F`. -/
@[simps]
/-
**CategoryTheory.Functor.RightExtension.coneAtFunctor** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor.RightExtension`。
形式化陈述：coneAtFunctor (Y : D) : RightExtension L F ⥤ Cone (StructuredArrow.proj Y 
L ⋙ F) where obj E
参数：Y : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cones for `StructuredArrow.proj Y L ⋙ F`, as a functor from `RightExtension 
L F`.
-/
def coneAtFunctor (Y : D) :
    RightExtension L F ⥤ Cone (StructuredArrow.proj Y L ⋙ F) where
  obj E := E.coneAt Y
  map {E E'} φ := ConeMorphism.mk (φ.left.app Y) (fun G ↦ by
    dsimp
    rw [← CostructuredArrow.w φ]
    simp)

/-- A right extension `E : RightExtension L F` is a pointwise right Kan extension at `Y` when
`E.coneAt Y` is a limit cone. -/
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtensionAt** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Functor.RightExtension`。
形式化陈述：IsPointwiseRightKanExtensionAt (Y : D)
参数：Y : D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A right extension `E : RightExtension L F` is a pointwise right Kan extension at
 `Y` when
`E.coneAt Y` is a limit cone.
-/
def IsPointwiseRightKanExtensionAt (Y : D) := IsLimit (E.coneAt Y)
/-
**CategoryTheory.Functor.RightExtension.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor.RightExtension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Y : D) : Subsingleton (E.IsPointwiseRightKanExtensionAt Y) :=
  inferInstanceAs (Subsingleton (IsLimit _))

variable {E} in
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtensionAt.hasPointw
iseRightKanExtensionAt** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.RightEx
tension.IsPointwiseRightKanExtensionAt`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} {E : L.RightExtension F} {Y : D}   (h : E.IsPointwiseRi
ghtKanExtensionAt Y), L.HasPointwiseRightKanExtensionAt F Y
参数：h : E.IsPointwiseRightKanExtensionAt Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsPointwiseRightKanExtensionAt.hasPointwiseRightKanExtensionAt
    {Y : D} (h : E.IsPointwiseRightKanExtensionAt Y) :
    HasPointwiseRightKanExtensionAt L F Y := ⟨_, h⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtensionAt.isIso_hom
_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.RightExtension.IsPointwis
eRightKanExtensionAt`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} (E : L.RightExtension F) {X : C}   (h : E.IsPointwiseRi
ghtKanExtensionAt (L.obj X)) [L.Full] [L.Faithful],   CategoryTheory.IsIso ((Cat
egoryTheory.CostructuredArrow.hom E).app X)
参数：E : L.RightExtension F；h : E.IsPointwiseRightKanExtensionAt (L.obj X)；(Catego
ryTheory.CostructuredArrow.hom E).app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.IsLimit.isIso_π_app_of_isInitial`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type u} [inst_1 : CategoryTheor
y.Category.{v, u} J]   {F : CategoryTheory.F…
-/
lemma IsPointwiseRightKanExtensionAt.isIso_hom_app
    {X : C} (h : E.IsPointwiseRightKanExtensionAt (L.obj X)) [L.Full] [L.Faithful] :
    IsIso (E.hom.app X) := by
  simpa using h.isIso_π_app_of_isInitial _ StructuredArrow.mkIdInitial

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The condition of being a pointwise right Kan extension at an object `Y` is
unchanged by replacing `Y` by an isomorphic object `Y'`. -/
/-
**CategoryTheory.Functor.RightExtension.isPointwiseRightKanExtensionAtOfIso'** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.RightExtension`。
形式化陈述：isPointwiseRightKanExtensionAtOfIso' {Y : D} (hY : E.IsPointwiseRightKanEx
tensionAt Y) {Y' : D} (e : Y ≅ Y') : E.IsPointwiseRightKanExtensionAt Y'
参数：hY : E.IsPointwiseRightKanExtensionAt Y；e : Y ≅ Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition of being a pointwise right Kan extension at an object `Y` is
unchanged by replacing `Y` by an isomorphic object `Y'`.
-/
def isPointwiseRightKanExtensionAtOfIso'
    {Y : D} (hY : E.IsPointwiseRightKanExtensionAt Y) {Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseRightKanExtensionAt Y' :=
  IsLimit.ofIsoLimit (hY.whiskerEquivalence (StructuredArrow.mapIso e.symm))
    (Cone.ext (E.left.mapIso e))

set_option backward.isDefEq.respectTransparency.types false in
/-- The condition of being a pointwise right Kan extension at an object `Y` is
unchanged by replacing `Y` by an isomorphic object `Y'`. -/
/-
**CategoryTheory.Functor.RightExtension.isPointwiseRightKanExtensionAtEquivOfIso
'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.RightExtension`。
形式化陈述：isPointwiseRightKanExtensionAtEquivOfIso' {Y Y' : D} (e : Y ≅ Y') : E.IsPo
intwiseRightKanExtensionAt Y ≃ E.IsPointwiseRightKanExtensionAt Y' where toFun h
参数：e : Y ≅ Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition of being a pointwise right Kan extension at an object `Y` is
unchanged by replacing `Y` by an isomorphic object `Y'`.
-/
def isPointwiseRightKanExtensionAtEquivOfIso' {Y Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseRightKanExtensionAt Y ≃ E.IsPointwiseRightKanExtensionAt Y' where
  toFun h := E.isPointwiseRightKanExtensionAtOfIso' h e
  invFun h := E.isPointwiseRightKanExtensionAtOfIso' h e.symm
  left_inv h := by subsingleton
  right_inv h := by subsingleton

namespace IsPointwiseRightKanExtensionAt

variable {E} {Y : D} (h : E.IsPointwiseRightKanExtensionAt Y)

include h in
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtensionAt.hom_ext'*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.RightExtension.IsPointwiseRigh
tKanExtensionAt`。
形式化陈述：hom_ext' {T : H} {f g : T ⟶ E.left.obj Y} (hfg : forall ⦃X : C⦄ (φ : Y ⟶ L
.obj X), f ≫ E.left.map φ ≫ E.hom.app X = g ≫ E.left.map φ ≫ E.hom.app X) : f = 
g
参数：hfg : forall ⦃X : C⦄ (φ : Y ⟶ L.obj X), f ≫ E.left.map φ ≫ E.hom.app X = g ≫ 
E.left.map φ ≫ E.hom.app X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
-/
lemma hom_ext' {T : H} {f g : T ⟶ E.left.obj Y}
    (hfg : ∀ ⦃X : C⦄ (φ : Y ⟶ L.obj X),
      f ≫ E.left.map φ ≫ E.hom.app X = g ≫ E.left.map φ ≫ E.hom.app X) : f = g :=
  h.hom_ext (fun j ↦ hfg j.hom)

variable [HasLimit (StructuredArrow.proj Y L ⋙ F)]

/-- A pointwise right Kan extension of `F` along `L` applied to an object `Y` is isomorphic to
`limit (StructuredArrow.proj Y L ⋙ F)`. -/
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtensionAt.isoLimit*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.RightExtension.IsPointwiseRigh
tKanExtensionAt`。
形式化陈述：isoLimit : E.left.obj Y ≅ limit (StructuredArrow.proj Y L ⋙ F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pointwise right Kan extension of `F` along `L` applied to an object `Y` is iso
morphic to
`limit (StructuredArrow.proj Y L ⋙ F)`.
-/
noncomputable def isoLimit :
    E.left.obj Y ≅ limit (StructuredArrow.proj Y L ⋙ F) :=
  h.conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtensionAt.isoLimit_
hom_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.RightExtension.IsPointwis
eRightKanExtensionAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoLimit_hom_π (g : StructuredArrow Y L) :
    h.isoLimit.hom ≫ limit.π _ g = E.left.map g.hom ≫ E.hom.app g.right :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtensionAt.isoLimit_
inv_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.RightExtension.IsPointwis
eRightKanExtensionAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoLimit_inv_π (g : StructuredArrow Y L) :
    h.isoLimit.inv ≫ E.left.map g.hom ≫ E.hom.app g.right =
      limit.π (StructuredArrow.proj Y L ⋙ F) g := by
  simpa using! h.conePointUniqueUpToIso_inv_comp (limit.isLimit _) g

end IsPointwiseRightKanExtensionAt

/-- Given `E : Functor.RightExtension L F`, this is the property of objects where
`E` is a pointwise right Kan extension. -/
/-
**CategoryTheory.Functor.RightExtension.isPointwiseRightKanExtensionAt** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Functor.RightExtension`。
形式化陈述：isPointwiseRightKanExtensionAt : ObjectProperty D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `E : Functor.RightExtension L F`, this is the property of objects where
`E` is a pointwise right Kan extension.
-/
def isPointwiseRightKanExtensionAt : ObjectProperty D :=
  fun Y ↦ Nonempty (E.IsPointwiseRightKanExtensionAt Y)
/-
**CategoryTheory.Functor.RightExtension.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor.RightExtension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : E.isPointwiseRightKanExtensionAt.IsClosedUnderIsomorphisms where
  of_iso e h := ⟨E.isPointwiseRightKanExtensionAtOfIso' h.some e⟩

/-- A right extension `E : RightExtension L F` is a pointwise right Kan extension when
it is a pointwise right Kan extension at any object. -/
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension** 是 Mathlib
 中的一个缩写定义，位于命名空间 `CategoryTheory.Functor.RightExtension`。
形式化陈述：IsPointwiseRightKanExtension
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A right extension `E : RightExtension L F` is a pointwise right Kan extension wh
en
it is a pointwise right Kan extension at any object.
-/
abbrev IsPointwiseRightKanExtension := ∀ (Y : D), E.IsPointwiseRightKanExtensionAt Y

variable {E E'}

/-- If two right extensions `E` and `E'` are isomorphic, `E` is a pointwise
right Kan extension at `Y` iff `E'` is. -/
/-
**CategoryTheory.Functor.RightExtension.isPointwiseRightKanExtensionAtEquivOfIso
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.RightExtension`。
形式化陈述：isPointwiseRightKanExtensionAtEquivOfIso (e : E ≅ E') (Y : D) : E.IsPointw
iseRightKanExtensionAt Y ≃ E'.IsPointwiseRightKanExtensionAt Y
参数：e : E ≅ E'；Y : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two right extensions `E` and `E'` are isomorphic, `E` is a pointwise
right Kan extension at `Y` iff `E'` is.
-/
def isPointwiseRightKanExtensionAtEquivOfIso (e : E ≅ E') (Y : D) :
    E.IsPointwiseRightKanExtensionAt Y ≃ E'.IsPointwiseRightKanExtensionAt Y :=
  IsLimit.equivIsoLimit ((coneAtFunctor L F Y).mapIso e)

/-- If two right extensions `E` and `E'` are isomorphic, `E` is a pointwise
right Kan extension iff `E'` is. -/
/-
**CategoryTheory.Functor.RightExtension.isPointwiseRightKanExtensionEquivOfIso**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.RightExtension`。
形式化陈述：isPointwiseRightKanExtensionEquivOfIso (e : E ≅ E') : E.IsPointwiseRightKa
nExtension ≃ E'.IsPointwiseRightKanExtension where toFun h
参数：e : E ≅ E'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If two right extensions `E` and `E'` are isomorphic, `E` is a pointwise
right Kan extension iff `E'` is.
-/
def isPointwiseRightKanExtensionEquivOfIso (e : E ≅ E') :
    E.IsPointwiseRightKanExtension ≃ E'.IsPointwiseRightKanExtension where
  toFun h := fun Y => (isPointwiseRightKanExtensionAtEquivOfIso e Y) (h Y)
  invFun h := fun Y => (isPointwiseRightKanExtensionAtEquivOfIso e Y).symm (h Y)
  left_inv h := by simp
  right_inv h := by simp

variable (h : E.IsPointwiseRightKanExtension)
include h
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.hasPointwis
eRightKanExtension** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.RightExtens
ion.IsPointwiseRightKanExtension`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} {E : L.RightExtension F}   (h : E.IsPointwiseRightKanEx
tension), L.HasPointwiseRightKanExtension F
参数：h : E.IsPointwiseRightKanExtension。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtensionAt.has
PointwiseRightKanExtensionAt`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [in
st : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{
v_2, u_2} …
-/
lemma IsPointwiseRightKanExtension.hasPointwiseRightKanExtension :
    HasPointwiseRightKanExtension L F :=
  fun Y => (h Y).hasPointwiseRightKanExtensionAt

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The (unique) morphism to a pointwise right Kan extension. -/
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.homTo** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.RightExtension.IsPointwiseRightKanE
xtension`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     {H : Type u_4} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_2, u_2} D] →           [inst_2 : CategoryTheory.Category.{v_4, u_4} H] →      
       {L : CategoryTheory.Functor C D} →               {F : CategoryTheory.Func
tor C H} →                 {E : L.RightExtension F} → E.IsPointwiseRightKanExten
sion → (G : L.RightExtension F) → G ⟶ E
参数：G : L.RightExtension F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) morphism to a pointwise right Kan extension.
-/
def IsPointwiseRightKanExtension.homTo (G : RightExtension L F) : G ⟶ E :=
  CostructuredArrow.homMk
    { app := fun Y ↦ (h Y).lift (RightExtension.coneAt G Y)
      naturality := fun Y₁ Y₂ φ ↦ (h Y₂).hom_ext (fun X ↦ by
        rw [assoc, (h Y₂).fac (coneAt G Y₂) X]
        simpa using ((h Y₁).fac (coneAt G Y₁) ((StructuredArrow.map φ).obj X)).symm) }
    (by
      ext X
      simpa using (h (L.obj X)).fac (RightExtension.coneAt G _) (StructuredArrow.mk (𝟙 _)))

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.hom_ext** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.RightExtension.IsPointwiseRightKa
nExtension`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} {E : L.RightExtension F}   (h : E.IsPointwiseRightKanEx
tension) {G : L.RightExtension F} {f₁ f₂ : G ⟶ E}, f₁ = f₂
参数：h : E.IsPointwiseRightKanExtension。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CostructuredArrow.hom_ext`：hom_ext {X Y : CostructuredArr
ow S T} (f g : X ⟶ Y) (h : f.left = g.left) : f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.CostructuredArrow.w`：w (f : X ⟶ Y) : S.map f.left ≫ Y.hom
 = X.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsPointwiseRightKanExtension.hom_ext
    {G : RightExtension L F} {f₁ f₂ : G ⟶ E} : f₁ = f₂ := by
  ext Y
  apply (h Y).hom_ext
  intro X
  have eq₁ := congr_app (CostructuredArrow.w f₁) X.right
  have eq₂ := congr_app (CostructuredArrow.w f₂) X.right
  dsimp at eq₁ eq₂ ⊢
  simp only [← NatTrans.naturality_assoc, eq₁, eq₂]

/-- A pointwise right Kan extension is universal, i.e. it is a right Kan extension. -/
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.isUniversal
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.RightExtension.IsPointwiseRig
htKanExtension`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     {H : Type u_4} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_2, u_2} D] →           [inst_2 : CategoryTheory.Category.{v_4, u_4} H] →      
       {L : CategoryTheory.Functor C D} →               {F : CategoryTheory.Func
tor C H} →                 {E : L.RightExtension F} →                   E.IsPoin
twiseRightKanExtension → CategoryTheory.CostructuredArrow.IsUniversal E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pointwise right Kan extension is universal, i.e. it is a right Kan extension.
-/
def IsPointwiseRightKanExtension.isUniversal : E.IsUniversal :=
  IsTerminal.ofUniqueHom h.homTo (fun _ _ => h.hom_ext)
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.isRightKanE
xtension** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.RightExtension.IsPoin
twiseRightKanExtension`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} {E : L.RightExtension F}   (h : E.IsPointwiseRightKanEx
tension),   (CategoryTheory.CostructuredArrow.left E).IsRightKanExtension (Categ
oryTheory.CostructuredArrow.hom E)
参数：h : E.IsPointwiseRightKanExtension；CategoryTheory.CostructuredArrow.left E；Ca
tegoryTheory.CostructuredArrow.hom E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsPointwiseRightKanExtension.isRightKanExtension :
    E.left.IsRightKanExtension E.hom where
  nonempty_isUniversal := ⟨h.isUniversal⟩
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.hasRightKan
Extension** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.RightExtension.IsPoi
ntwiseRightKanExtension`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} {E : L.RightExtension F}   (h : E.IsPointwiseRightKanEx
tension), L.HasRightKanExtension F
参数：h : E.IsPointwiseRightKanExtension。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.isRig
htKanExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryT
heory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.HasRightKanExtension.mk`：∀ {C : Type u_1} {H : Ty
pe u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_3, u_3} …
-/
lemma IsPointwiseRightKanExtension.hasRightKanExtension :
    HasRightKanExtension L F :=
  have := h.isRightKanExtension
  HasRightKanExtension.mk E.left E.hom
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.isIso_hom**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.RightExtension.IsPointwiseRight
KanExtension`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} H]   {L : CategoryTheory.Functor C D} {F : Cat
egoryTheory.Functor C H} {E : L.RightExtension F}   (h : E.IsPointwiseRightKanEx
tension) [L.Full] [L.Faithful],   CategoryTheory.IsIso (CategoryTheory.Costructu
redArrow.hom E)
参数：h : E.IsPointwiseRightKanExtension；CategoryTheory.CostructuredArrow.hom E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtensionAt.isI
so_hom_app`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheor
y.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
lemma IsPointwiseRightKanExtension.isIso_hom [L.Full] [L.Faithful] :
    IsIso (E.hom) :=
  have := fun X => (h (L.obj X)).isIso_hom_app
  NatIso.isIso_of_isIso_app ..

end RightExtension

section

variable [HasPointwiseLeftKanExtension L F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constructed pointwise left Kan extension when `HasPointwiseLeftKanExtension L F` holds. -/
@[simps]
/-
**CategoryTheory.Functor.pointwiseLeftKanExtension** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：pointwiseLeftKanExtension : D ⥤ H where obj Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructed pointwise left Kan extension when `HasPointwiseLeftKanExtension 
L F` holds.
-/
noncomputable def pointwiseLeftKanExtension : D ⥤ H where
  obj Y := colimit (CostructuredArrow.proj L Y ⋙ F)
  map {Y₁ Y₂} f :=
    colimit.desc (CostructuredArrow.proj L Y₁ ⋙ F)
      (Cocone.mk (colimit (CostructuredArrow.proj L Y₂ ⋙ F))
        { app := fun g => colimit.ι (CostructuredArrow.proj L Y₂ ⋙ F)
            ((CostructuredArrow.map f).obj g)
          naturality := fun g₁ g₂ φ => by
            simpa using colimit.w (CostructuredArrow.proj L Y₂ ⋙ F)
              ((CostructuredArrow.map f).map φ) })
  map_id Y := colimit.hom_ext (fun j => by
    dsimp
    simp only [colimit.ι_desc, comp_id]
    congr
    apply CostructuredArrow.map_id)
  map_comp {Y₁ Y₂ Y₃} f f' := colimit.hom_ext (fun j => by
    dsimp
    simp only [colimit.ι_desc, colimit.ι_desc_assoc, comp_obj, CostructuredArrow.proj_obj]
    congr 1
    apply CostructuredArrow.map_comp)

set_option backward.isDefEq.respectTransparency false in
/-- The unit of the constructed pointwise left Kan extension when
`HasPointwiseLeftKanExtension L F` holds. -/
@[simps]
/-
**CategoryTheory.Functor.pointwiseLeftKanExtensionUnit** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：pointwiseLeftKanExtensionUnit : F ⟶ L ⋙ pointwiseLeftKanExtension L F wher
e app X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit of the constructed pointwise left Kan extension when
`HasPointwiseLeftKanExtension L F` holds.
-/
noncomputable def pointwiseLeftKanExtensionUnit : F ⟶ L ⋙ pointwiseLeftKanExtension L F where
  app X := colimit.ι (CostructuredArrow.proj L (L.obj X) ⋙ F)
    (CostructuredArrow.mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f := by
    simp only [comp_map,
      pointwiseLeftKanExtension_map, colimit.ι_desc, CostructuredArrow.map_mk]
    rw [id_comp]
    let φ : CostructuredArrow.mk (L.map f) ⟶ CostructuredArrow.mk (𝟙 (L.obj X₂)) :=
      CostructuredArrow.homMk f
    exact colimit.w (CostructuredArrow.proj L (L.obj X₂) ⋙ F) φ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor `pointwiseLeftKanExtension L F` is a pointwise left Kan
extension of `F` along `L`. -/
/-
**CategoryTheory.Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseLeftKanExtensionIsPointwiseLeftKanExtension : (LeftExtension.mk _
 (pointwiseLeftKanExtensionUnit L F)).IsPointwiseLeftKanExtension
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `pointwiseLeftKanExtension L F` is a pointwise left Kan
extension of `F` along `L`.
-/
noncomputable def pointwiseLeftKanExtensionIsPointwiseLeftKanExtension :
    (LeftExtension.mk _ (pointwiseLeftKanExtensionUnit L F)).IsPointwiseLeftKanExtension :=
  fun X => IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [comp_id, colimit.ι_desc, CostructuredArrow.map_mk]
    congr 1
    rw [id_comp, ← CostructuredArrow.eq_mk]))

/-- The functor `pointwiseLeftKanExtension L F` is a left Kan extension of `F` along `L`. -/
/-
**CategoryTheory.Functor.pointwiseLeftKanExtensionIsUniversal** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseLeftKanExtensionIsUniversal : (LeftExtension.mk _ (pointwiseLeftK
anExtensionUnit L F)).IsUniversal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `pointwiseLeftKanExtension L F` is a left Kan extension of `F` along
 `L`.
-/
noncomputable def pointwiseLeftKanExtensionIsUniversal :
    (LeftExtension.mk _ (pointwiseLeftKanExtensionUnit L F)).IsUniversal :=
  (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F).isUniversal
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pointwiseLeftKanExtension L F).IsLeftKanExtension
    (pointwiseLeftKanExtensionUnit L F) where
  nonempty_isUniversal := ⟨pointwiseLeftKanExtensionIsUniversal L F⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLeftKanExtension L F :=
  HasLeftKanExtension.mk _ (pointwiseLeftKanExtensionUnit L F)

set_option backward.defeqAttrib.useBackward true in
/-- An auxiliary cocone used in the lemma `pointwiseLeftKanExtension_desc_app` -/
@[simps]
/-
**CategoryTheory.Functor.costructuredArrowMapCocone** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：costructuredArrowMapCocone (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D) : Cocone (C
ostructuredArrow.proj L Y ⋙ F) where pt
参数：G : D ⥤ H；α : F ⟶ L ⋙ G；Y : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary cocone used in the lemma `pointwiseLeftKanExtension_desc_app`
-/
def costructuredArrowMapCocone (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D) :
    Cocone (CostructuredArrow.proj L Y ⋙ F) where
  pt := G.obj Y
  ι := {
    app := fun f ↦ α.app f.left ≫ G.map f.hom
    naturality := by simp [← G.map_comp] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Functor.pointwiseLeftKanExtension_desc_app** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseLeftKanExtension_desc_app (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D) : (
(pointwiseLeftKanExtension L F).descOfIsLeftKanExtension (pointwiseLeftKanExtens
ionUnit L F) .app Y) = colimit.desc _ (costructuredArrowMapCocone L F G α Y)
参数：G : D ⥤ H；α : F ⟶ L ⋙ G；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionPointwiseLeftKanExtensionPo
intwiseLeftKanExtensionUnit`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [ins
t : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v
_2, u_2} …
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
-/
lemma pointwiseLeftKanExtension_desc_app (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D) :
    ((pointwiseLeftKanExtension L F).descOfIsLeftKanExtension (pointwiseLeftKanExtensionUnit L F)
      G α |>.app Y) = colimit.desc _ (costructuredArrowMapCocone L F G α Y) := by
  let β : L.pointwiseLeftKanExtension F ⟶ G :=
    { app := fun Y ↦ colimit.desc _ (costructuredArrowMapCocone L F G α Y) }
  have h : (pointwiseLeftKanExtension L F).descOfIsLeftKanExtension
      (pointwiseLeftKanExtensionUnit L F) G α = β := by
    apply hom_ext_of_isLeftKanExtension (α := pointwiseLeftKanExtensionUnit L F)
    aesop
  exact NatTrans.congr_app h Y

variable {F L}

/-- If `F` admits a pointwise left Kan extension along `L`, then any left Kan extension of `F`
along `L` is a pointwise left Kan extension. -/
/-
**CategoryTheory.Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isPointwiseLeftKanExtensionOfIsLeftKanExtension (F' : D ⥤ H) (α : F ⟶ L ⋙ 
F') [F'.IsLeftKanExtension α] : (LeftExtension.mk _ α).IsPointwiseLeftKanExtensi
on
参数：F' : D ⥤ H；α : F ⟶ L ⋙ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` admits a pointwise left Kan extension along `L`, then any left Kan extens
ion of `F`
along `L` is a pointwise left Kan extension.
-/
noncomputable def isPointwiseLeftKanExtensionOfIsLeftKanExtension (F' : D ⥤ H) (α : F ⟶ L ⋙ F')
    [F'.IsLeftKanExtension α] :
    (LeftExtension.mk _ α).IsPointwiseLeftKanExtension :=
  LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
    (IsColimit.coconePointUniqueUpToIso (pointwiseLeftKanExtensionIsUniversal L F)
      (F'.isUniversalOfIsLeftKanExtension α))
    (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F)

end

section

variable [HasPointwiseRightKanExtension L F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constructed pointwise right Kan extension
when `HasPointwiseRightKanExtension L F` holds. -/
@[simps]
/-
**CategoryTheory.Functor.pointwiseRightKanExtension** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：pointwiseRightKanExtension : D ⥤ H where obj Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructed pointwise right Kan extension
when `HasPointwiseRightKanExtension L F` holds.
-/
noncomputable def pointwiseRightKanExtension : D ⥤ H where
  obj Y := limit (StructuredArrow.proj Y L ⋙ F)
  map {Y₁ Y₂} f := limit.lift (StructuredArrow.proj Y₂ L ⋙ F)
      (Cone.mk (limit (StructuredArrow.proj Y₁ L ⋙ F))
        { app := fun g ↦ limit.π (StructuredArrow.proj Y₁ L ⋙ F)
            ((StructuredArrow.map f).obj g)
          naturality := fun g₁ g₂ φ ↦ by
            simpa using (limit.w (StructuredArrow.proj Y₁ L ⋙ F)
              ((StructuredArrow.map f).map φ)).symm })
  map_id Y := limit.hom_ext (fun j => by
    dsimp
    simp only [limit.lift_π, id_comp]
    congr
    apply StructuredArrow.map_id)
  map_comp {Y₁ Y₂ Y₃} f f' := limit.hom_ext (fun j => by
    dsimp
    simp only [limit.lift_π, assoc]
    congr 1
    apply StructuredArrow.map_comp)

set_option backward.isDefEq.respectTransparency false in
/-- The counit of the constructed pointwise right Kan extension when
`HasPointwiseRightKanExtension L F` holds. -/
@[simps]
/-
**CategoryTheory.Functor.pointwiseRightKanExtensionCounit** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseRightKanExtensionCounit : L ⋙ pointwiseRightKanExtension L F ⟶ F 
where app X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit of the constructed pointwise right Kan extension when
`HasPointwiseRightKanExtension L F` holds.
-/
noncomputable def pointwiseRightKanExtensionCounit :
    L ⋙ pointwiseRightKanExtension L F ⟶ F where
  app X := limit.π (StructuredArrow.proj (L.obj X) L ⋙ F)
    (StructuredArrow.mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f := by
    simp only [comp_map,
      pointwiseRightKanExtension_map, limit.lift_π, StructuredArrow.map_mk]
    rw [comp_id]
    let φ : StructuredArrow.mk (𝟙 (L.obj X₁)) ⟶ StructuredArrow.mk (L.map f) :=
      StructuredArrow.homMk f
    exact (limit.w (StructuredArrow.proj (L.obj X₁) L ⋙ F) φ).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor `pointwiseRightKanExtension L F` is a pointwise right Kan
extension of `F` along `L`. -/
/-
**CategoryTheory.Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseRightKanExtensionIsPointwiseRightKanExtension : (RightExtension.m
k _ (pointwiseRightKanExtensionCounit L F)).IsPointwiseRightKanExtension
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `pointwiseRightKanExtension L F` is a pointwise right Kan
extension of `F` along `L`.
-/
noncomputable def pointwiseRightKanExtensionIsPointwiseRightKanExtension :
    (RightExtension.mk _ (pointwiseRightKanExtensionCounit L F)).IsPointwiseRightKanExtension :=
  fun X => IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [limit.lift_π, StructuredArrow.map_mk, id_comp]
    congr
    rw [comp_id, ← StructuredArrow.eq_mk]))

/-- The functor `pointwiseRightKanExtension L F` is a right Kan extension of `F` along `L`. -/
/-
**CategoryTheory.Functor.pointwiseRightKanExtensionIsUniversal** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseRightKanExtensionIsUniversal : (RightExtension.mk _ (pointwiseRig
htKanExtensionCounit L F)).IsUniversal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `pointwiseRightKanExtension L F` is a right Kan extension of `F` alo
ng `L`.
-/
noncomputable def pointwiseRightKanExtensionIsUniversal :
    (RightExtension.mk _ (pointwiseRightKanExtensionCounit L F)).IsUniversal :=
  (pointwiseRightKanExtensionIsPointwiseRightKanExtension L F).isUniversal
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pointwiseRightKanExtension L F).IsRightKanExtension
    (pointwiseRightKanExtensionCounit L F) where
  nonempty_isUniversal := ⟨pointwiseRightKanExtensionIsUniversal L F⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasRightKanExtension L F :=
  HasRightKanExtension.mk _ (pointwiseRightKanExtensionCounit L F)

set_option backward.defeqAttrib.useBackward true in
/-- An auxiliary cocone used in the lemma `pointwiseRightKanExtension_lift_app` -/
@[simps]
/-
**CategoryTheory.Functor.structuredArrowMapCone** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：structuredArrowMapCone (G : D ⥤ H) (α : L ⋙ G ⟶ F) (Y : D) : Cone (Structu
redArrow.proj Y L ⋙ F) where pt
参数：G : D ⥤ H；α : L ⋙ G ⟶ F；Y : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary cocone used in the lemma `pointwiseRightKanExtension_lift_app`
-/
def structuredArrowMapCone (G : D ⥤ H) (α : L ⋙ G ⟶ F) (Y : D) :
    Cone (StructuredArrow.proj Y L ⋙ F) where
  pt := G.obj Y
  π := {
    app := fun f ↦ G.map f.hom ≫ α.app f.right
    naturality := by simp [← α.naturality, ← G.map_comp_assoc] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Functor.pointwiseRightKanExtension_lift_app** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseRightKanExtension_lift_app (G : D ⥤ H) (α : L ⋙ G ⟶ F) (Y : D) : 
((pointwiseRightKanExtension L F).liftOfIsRightKanExtension .app Y) = (pointwise
RightKanExtensionCounit L F) G α limit.lift _ (structuredArrowMapCone L F G α Y)
参数：G : D ⥤ H；α : L ⋙ G ⟶ F；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.instIsRightKanExtensionPointwiseRightKanExtension
PointwiseRightKanExtensionCounit`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4}
 [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Catego
ry.{v_2, u_2} …
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isRightKanExtension`：hom_ext_of_isRigh
tKanExtension {G : D ⥤ H} (γ₁ γ₂ : G ⟶ F') (hγ : whiskerLeft L γ₁ ≫ α = whiskerL
eft L γ₂ ≫ α) : γ₁ = γ₂
· 使用引理 `CategoryTheory.Functor.liftOfIsRightKanExtension_fac`：liftOfIsRightKanEx
tension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) : whiskerLeft L (F'.liftOfIsRightKanExte
nsion α G β) ≫ α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
-/
lemma pointwiseRightKanExtension_lift_app (G : D ⥤ H) (α : L ⋙ G ⟶ F) (Y : D) :
    ((pointwiseRightKanExtension L F).liftOfIsRightKanExtension
      (pointwiseRightKanExtensionCounit L F) G α |>.app Y) =
        limit.lift _ (structuredArrowMapCone L F G α Y) := by
  let β : G ⟶ L.pointwiseRightKanExtension F :=
    { app := fun Y ↦ limit.lift _ (structuredArrowMapCone L F G α Y) }
  have h : (pointwiseRightKanExtension L F).liftOfIsRightKanExtension
      (pointwiseRightKanExtensionCounit L F) G α = β := by
    apply hom_ext_of_isRightKanExtension (α := pointwiseRightKanExtensionCounit L F)
    aesop
  exact NatTrans.congr_app h Y

variable {F L}

/-- If `F` admits a pointwise right Kan extension along `L`, then any right Kan extension of `F`
along `L` is a pointwise right Kan extension. -/
/-
**CategoryTheory.Functor.isPointwiseRightKanExtensionOfIsRightKanExtension** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isPointwiseRightKanExtensionOfIsRightKanExtension (F' : D ⥤ H) (α : L ⋙ F'
 ⟶ F) [F'.IsRightKanExtension α] : (RightExtension.mk _ α).IsPointwiseRightKanEx
tension
参数：F' : D ⥤ H；α : L ⋙ F' ⟶ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` admits a pointwise right Kan extension along `L`, then any right Kan exte
nsion of `F`
along `L` is a pointwise right Kan extension.
-/
noncomputable def isPointwiseRightKanExtensionOfIsRightKanExtension (F' : D ⥤ H) (α : L ⋙ F' ⟶ F)
    [F'.IsRightKanExtension α] :
    (RightExtension.mk _ α).IsPointwiseRightKanExtension :=
  RightExtension.isPointwiseRightKanExtensionEquivOfIso
    (IsLimit.conePointUniqueUpToIso (pointwiseRightKanExtensionIsUniversal L F)
      (F'.isUniversalOfIsRightKanExtension α))
    (pointwiseRightKanExtensionIsPointwiseRightKanExtension L F)

end

end Functor

end CategoryTheory

