/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Final

/-!
# (Co)limit presentations

Let `J` and `C` be categories and `X : C`. We define type `ColimitPresentation J X` that contains
the data of objects `Dⱼ` and natural maps `sⱼ : Dⱼ ⟶ X` that make `X` the colimit of the `Dⱼ`.

(See `Mathlib/CategoryTheory/Presentable/ColimitPresentation.lean` for the construction of a
presentation of a colimit of objects that are equipped with presentations.)

## Main definitions:

- `CategoryTheory.Limits.ColimitPresentation`: A colimit presentation of `X` over `J` is a diagram
  `{Dᵢ}` in `C` and natural maps `sᵢ : Dᵢ ⟶ X` making `X` into the colimit of the `Dᵢ`.
- `CategoryTheory.Limits.LimitPresentation`: A limit presentation of `X` over `J` is a diagram
  `{Dᵢ}` in `C` and natural maps `sᵢ : X ⟶ Dᵢ` making `X` into the limit of the `Dᵢ`.

## TODOs:

- Refactor `TransfiniteCompositionOfShape` so that it extends `ColimitPresentation`.
-/

@[expose] public section

universe s t w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- A colimit presentation of `X` over `J` is a diagram `{Dᵢ}` in `C` and natural maps
`sᵢ : Dᵢ ⟶ X` making `X` into the colimit of the `Dᵢ`. -/
/-
**CategoryTheory.Limits.ColimitPresentation** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：{C : Type u} →   [CategoryTheory.Category.{v, u} C] →     (J : Type w) → [
CategoryTheory.Category.{t, w} J] → C → Type (max (max (max t u) v) w)
参数：J : Type w；max (max (max t u) v) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A colimit presentation of `X` over `J` is a diagram `{Dᵢ}` in `C` and natural ma
ps
`sᵢ : Dᵢ ⟶ X` making `X` into the colimit of the `Dᵢ`.
-/
structure ColimitPresentation (J : Type w) [Category.{t} J] (X : C) where
  /-- The diagram `{Dᵢ}`. -/
  diag : J ⥤ C
  /-- The natural maps `sᵢ : Dᵢ ⟶ X`. -/
  ι : diag ⟶ (Functor.const J).obj X
  /-- `X` is the colimit of the `Dᵢ` via `sᵢ`. -/
  isColimit : IsColimit (Cocone.mk _ ι)

variable {J : Type w} [Category.{t} J] {X : C}

namespace ColimitPresentation

initialize_simps_projections ColimitPresentation (-isColimit)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.ColimitPresentation.w** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits.ColimitPresentation`。
形式化陈述：w (pres : ColimitPresentation J X) {i j : J} (f : i ⟶ j) : pres.diag.map f
 ≫ pres.ι.app j = pres.ι.app i
参数：pres : ColimitPresentation J X；f : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma w (pres : ColimitPresentation J X) {i j : J} (f : i ⟶ j) :
    pres.diag.map f ≫ pres.ι.app j = pres.ι.app i := by
  simp

/-- The cocone associated to a colimit presentation. -/
/-
**CategoryTheory.Limits.ColimitPresentation.cocone** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.Limits.ColimitPresentation`。
形式化陈述：cocone (pres : ColimitPresentation J X) : Cocone pres.diag
参数：pres : ColimitPresentation J X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone associated to a colimit presentation.
-/
abbrev cocone (pres : ColimitPresentation J X) : Cocone pres.diag :=
  Cocone.mk _ pres.ι
/-
**CategoryTheory.Limits.ColimitPresentation.hasColimit** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits.ColimitPresentation`。
形式化陈述：hasColimit (pres : ColimitPresentation J X) : HasColimit pres.diag
参数：pres : ColimitPresentation J X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasColimit (pres : ColimitPresentation J X) : HasColimit pres.diag :=
  ⟨_, pres.isColimit⟩

/-- The canonical colimit presentation of any object over a point. -/
@[simps]
noncomputable
/-
**CategoryTheory.Limits.ColimitPresentation.self** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.ColimitPresentation`。
形式化陈述：self (X : C) : ColimitPresentation PUnit.{s + 1} X where diag
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def self (X : C) : ColimitPresentation PUnit.{s + 1} X where
  diag := (Functor.const _).obj X
  ι := 𝟙 _
  isColimit := isColimitConstCocone _ _

/-- If `F : J ⥤ C` is a functor that has a colimit, then this is the obvious
colimit presentation of `colimit F`. -/
/-
**CategoryTheory.Limits.ColimitPresentation.colimit** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.ColimitPresentation`。
形式化陈述：colimit (F : J ⥤ C) [HasColimit F] : ColimitPresentation J (colimit F) whe
re diag
参数：F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : J ⥤ C` is a functor that has a colimit, then this is the obvious
colimit presentation of `colimit F`.
-/
noncomputable def colimit (F : J ⥤ C) [HasColimit F] :
    ColimitPresentation J (colimit F) where
  diag := F
  ι := _
  isColimit := colimit.isColimit _

set_option backward.defeqAttrib.useBackward true in
/-- If `F` preserves colimits of shape `J`, it maps colimit presentations of `X` to
colimit presentations of `F(X)`. -/
@[simps]
noncomputable
/-
**CategoryTheory.Limits.ColimitPresentation.map** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.ColimitPresentation`。
形式化陈述：map (P : ColimitPresentation J X) {D : Type*} [Category* D] (F : C ⥤ D) [P
reservesColimitsOfShape J F] : ColimitPresentation J (F.obj X) where diag
参数：P : ColimitPresentation J X；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (P : ColimitPresentation J X) {D : Type*} [Category* D] (F : C ⥤ D)
    [PreservesColimitsOfShape J F] : ColimitPresentation J (F.obj X) where
  diag := P.diag ⋙ F
  ι := Functor.whiskerRight P.ι F ≫ (F.constComp _ _).hom
  isColimit := (isColimitOfPreserves F P.isColimit).ofIsoColimit (Cocone.ext (.refl _) (by simp))

/-- If `P` is a colimit presentation of `X`, it is possible to define another
colimit presentation of `X` where `P.diag` is replaced by an isomorphic functor. -/
@[simps]
/-
**CategoryTheory.Limits.ColimitPresentation.changeDiag** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.ColimitPresentation`。
形式化陈述：changeDiag (P : ColimitPresentation J X) {F : J ⥤ C} (e : F ≅ P.diag) : Co
limitPresentation J X where diag
参数：P : ColimitPresentation J X；e : F ≅ P.diag。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is a colimit presentation of `X`, it is possible to define another
colimit presentation of `X` where `P.diag` is replaced by an isomorphic functor.
-/
def changeDiag (P : ColimitPresentation J X) {F : J ⥤ C} (e : F ≅ P.diag) :
    ColimitPresentation J X where
  diag := F
  ι := e.hom ≫ P.ι
  isColimit := (IsColimit.precomposeHomEquiv e _).2 P.isColimit

/-- Map a colimit presentation under an isomorphism. -/
@[simps]
/-
**CategoryTheory.Limits.ColimitPresentation.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.ColimitPresentation`。
形式化陈述：ofIso (P : ColimitPresentation J X) {Y : C} (e : X ≅ Y) : ColimitPresentat
ion J Y where diag
参数：P : ColimitPresentation J X；e : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a colimit presentation under an isomorphism.
-/
def ofIso (P : ColimitPresentation J X) {Y : C} (e : X ≅ Y) : ColimitPresentation J Y where
  diag := P.diag
  ι := P.ι ≫ (Functor.const J).map e.hom
  isColimit := P.isColimit.ofIsoColimit (Cocone.ext e fun _ ↦ rfl)

/-- Change the index category of a colimit presentation. -/
@[simps]
noncomputable
/-
**CategoryTheory.Limits.ColimitPresentation.reindex** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.ColimitPresentation`。
形式化陈述：reindex (P : ColimitPresentation J X) {J' : Type*} [Category* J'] (F : J' 
⥤ J) [F.Final] : ColimitPresentation J' X where diag
参数：P : ColimitPresentation J X；F : J' ⥤ J。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def reindex (P : ColimitPresentation J X) {J' : Type*} [Category* J'] (F : J' ⥤ J) [F.Final] :
    ColimitPresentation J' X where
  diag := F ⋙ P.diag
  ι := F.whiskerLeft P.ι
  isColimit := (Functor.Final.isColimitWhiskerEquiv F _).symm P.isColimit

end ColimitPresentation

/-- A limit presentation of `X` over `J` is a diagram `{Dᵢ}` in `C` and natural maps
`sᵢ : X ⟶ Dᵢ` making `X` into the limit of the `Dᵢ`. -/
/-
**CategoryTheory.Limits.LimitPresentation** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：{C : Type u} →   [CategoryTheory.Category.{v, u} C] →     (J : Type w) → [
CategoryTheory.Category.{t, w} J] → C → Type (max (max (max t u) v) w)
参数：J : Type w；max (max (max t u) v) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A limit presentation of `X` over `J` is a diagram `{Dᵢ}` in `C` and natural maps
`sᵢ : X ⟶ Dᵢ` making `X` into the limit of the `Dᵢ`.
-/
structure LimitPresentation (J : Type w) [Category.{t} J] (X : C) where
  /-- The diagram `{Dᵢ}`. -/
  diag : J ⥤ C
  /-- The natural maps `sᵢ : X ⟶ Dᵢ`. -/
  π : (Functor.const J).obj X ⟶ diag
  /-- `X` is the limit of the `Dᵢ` via `sᵢ`. -/
  isLimit : IsLimit (Cone.mk _ π)

variable {J : Type w} [Category.{t} J] {X : C}

namespace LimitPresentation

initialize_simps_projections LimitPresentation (-isLimit)

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Limits.LimitPresentation.w** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Limits.LimitPresentation`。
形式化陈述：w (pres : LimitPresentation J X) {i j : J} (f : i ⟶ j) : pres.π.app i ≫ pr
es.diag.map f = pres.π.app j
参数：pres : LimitPresentation J X；f : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma w (pres : LimitPresentation J X) {i j : J} (f : i ⟶ j) :
    pres.π.app i ≫ pres.diag.map f = pres.π.app j := by
  simpa using (pres.π.naturality f).symm

/-- The cone associated to a limit presentation. -/
/-
**CategoryTheory.Limits.LimitPresentation.cone** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.Limits.LimitPresentation`。
形式化陈述：cone (pres : LimitPresentation J X) : Cone pres.diag
参数：pres : LimitPresentation J X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone associated to a limit presentation.
-/
abbrev cone (pres : LimitPresentation J X) : Cone pres.diag :=
  Cone.mk _ pres.π
/-
**CategoryTheory.Limits.LimitPresentation.hasLimit** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits.LimitPresentation`。
形式化陈述：hasLimit (pres : LimitPresentation J X) : HasLimit pres.diag
参数：pres : LimitPresentation J X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasLimit (pres : LimitPresentation J X) : HasLimit pres.diag :=
  ⟨_, pres.isLimit⟩

/-- The canonical limit presentation of any object over a point. -/
@[simps]
noncomputable
/-
**CategoryTheory.Limits.LimitPresentation.self** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.LimitPresentation`。
形式化陈述：self (X : C) : LimitPresentation PUnit.{s + 1} X where diag
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def self (X : C) : LimitPresentation PUnit.{s + 1} X where
  diag := (Functor.const _).obj X
  π := 𝟙 _
  isLimit := isLimitConstCone _ _

/-- If `F : J ⥤ C` is a functor that has a limit, then this is the obvious
limit presentation of `limit F`. -/
/-
**CategoryTheory.Limits.LimitPresentation.limit** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.LimitPresentation`。
形式化陈述：limit (F : J ⥤ C) [HasLimit F] : LimitPresentation J (limit F) where diag
参数：F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : J ⥤ C` is a functor that has a limit, then this is the obvious
limit presentation of `limit F`.
-/
noncomputable def limit (F : J ⥤ C) [HasLimit F] :
    LimitPresentation J (limit F) where
  diag := F
  π := _
  isLimit := limit.isLimit _

set_option backward.defeqAttrib.useBackward true in
/-- If `F` preserves limits of shape `J`, it maps limit presentations of `X` to
limit presentations of `F(X)`. -/
@[simps]
noncomputable
/-
**CategoryTheory.Limits.LimitPresentation.map** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.LimitPresentation`。
形式化陈述：map (P : LimitPresentation J X) {D : Type*} [Category* D] (F : C ⥤ D) [Pre
servesLimitsOfShape J F] : LimitPresentation J (F.obj X) where diag
参数：P : LimitPresentation J X；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (P : LimitPresentation J X) {D : Type*} [Category* D] (F : C ⥤ D)
    [PreservesLimitsOfShape J F] : LimitPresentation J (F.obj X) where
  diag := P.diag ⋙ F
  π := (F.constComp _ _).inv ≫ Functor.whiskerRight P.π F
  isLimit := (isLimitOfPreserves F P.isLimit).ofIsoLimit (Cone.ext (.refl _) (by simp))

/-- If `P` is a limit presentation of `X`, it is possible to define another
limit presentation of `X` where `P.diag` is replaced by an isomorphic functor. -/
@[simps]
/-
**CategoryTheory.Limits.LimitPresentation.changeDiag** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.LimitPresentation`。
形式化陈述：changeDiag (P : LimitPresentation J X) {F : J ⥤ C} (e : F ≅ P.diag) : Limi
tPresentation J X where diag
参数：P : LimitPresentation J X；e : F ≅ P.diag。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is a limit presentation of `X`, it is possible to define another
limit presentation of `X` where `P.diag` is replaced by an isomorphic functor.
-/
def changeDiag (P : LimitPresentation J X) {F : J ⥤ C} (e : F ≅ P.diag) :
    LimitPresentation J X where
  diag := F
  π := P.π ≫ e.inv
  isLimit := (IsLimit.postcomposeHomEquiv e.symm _).2 P.isLimit

set_option backward.defeqAttrib.useBackward true in
/-- Map a limit presentation under an isomorphism. -/
@[simps]
/-
**CategoryTheory.Limits.LimitPresentation.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.LimitPresentation`。
形式化陈述：ofIso (P : LimitPresentation J X) {Y : C} (e : X ≅ Y) : LimitPresentation 
J Y where diag
参数：P : LimitPresentation J X；e : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a limit presentation under an isomorphism.
-/
def ofIso (P : LimitPresentation J X) {Y : C} (e : X ≅ Y) : LimitPresentation J Y where
  diag := P.diag
  π := (Functor.const J).map e.inv ≫ P.π
  isLimit := P.isLimit.ofIsoLimit (Cone.ext e)

/-- Change the index category of a limit presentation. -/
@[simps]
noncomputable
/-
**CategoryTheory.Limits.LimitPresentation.reindex** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.LimitPresentation`。
形式化陈述：reindex (P : LimitPresentation J X) {J' : Type*} [Category* J'] (F : J' ⥤ 
J) [F.Initial] : LimitPresentation J' X where diag
参数：P : LimitPresentation J X；F : J' ⥤ J。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def reindex (P : LimitPresentation J X) {J' : Type*} [Category* J'] (F : J' ⥤ J) [F.Initial] :
    LimitPresentation J' X where
  diag := F ⋙ P.diag
  π := F.whiskerLeft P.π
  isLimit := (Functor.Initial.isLimitWhiskerEquiv F _).symm P.isLimit

end LimitPresentation

end CategoryTheory.Limits

