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

/--
Definition of `ColimitPresentation` / `ColimitPresentation` 的定义

English:
structure ColimitPresentation
  parameters: (J : Type w) [Category.{t} J] (X : C)
  axioms and operations (3):
    - diag : J ⥤ C
    - ι : diag ⟶ (Functor.const J).obj X
    - isColimit : IsColimit (Cocone.mk _ ι)

中文:
结构 ColimitPresentation
  参数: (J : Type w) [Category.{t} J] (X : C)
  公理与运算 (3 个):
    - diag : J ⥤ C
    - ι : diag ⟶ (Functor.const J).obj X
    - isColimit : IsColimit (Cocone.mk _ ι)
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
/--
lemma `w` / 引理 `w`

English:
lemma w
  given: (pres : ColimitPresentation J X) {i j : J} (f : i ⟶ j)
  proof: by
  simp

中文:
引理 w
  条件: (pres : ColimitPresentation J X) {i j : J} (f : i ⟶ j)
  证明: by
  simp
-/
lemma w (pres : ColimitPresentation J X) {i j : J} (f : i ⟶ j) :
    pres.diag.map f ≫ pres.ι.app j = pres.ι.app i := by
  simp

/--
Definition of `cocone` / `cocone` 的定义

English:
abbreviation cocone
  signature: (pres : ColimitPresentation J X)
  body: Cocone.mk _ pres.ι

中文:
缩写 cocone
  签名: (pres : ColimitPresentation J X)
  定义体: Cocone.mk _ pres.ι

Depends on / 依赖: Cocone, Cocone.mk
-/
abbrev cocone (pres : ColimitPresentation J X) : Cocone pres.diag :=
  Cocone.mk _ pres.ι

/--
lemma `hasColimit` / 引理 `hasColimit`

English:
lemma hasColimit
  given: (pres : ColimitPresentation J X)
  statement: HasColimit pres.diag
  proof: ⟨_, pres.isColimit⟩

中文:
引理 hasColimit
  条件: (pres : ColimitPresentation J X)
  结论: HasColimit pres.diag
  证明: ⟨_, pres.isColimit⟩

Depends on / 依赖: isColimit, pres.isColimit
-/
lemma hasColimit (pres : ColimitPresentation J X) : HasColimit pres.diag :=
  ⟨_, pres.isColimit⟩

/-- The canonical colimit presentation of any object over a point. -/
@[simps]
noncomputable
/--
Definition of `self` / `self` 的定义

English:
definition self
  signature: (X : C)
  body: (Functor.const _).obj X
  ι := 𝟙 _
  isColimit := isColimitConstCocone _ _

中文:
定义 self
  签名: (X : C)
  定义体: (Functor.const _).obj X
  ι := 𝟙 _
  isColimit := isColimitConstCocone _ _

Depends on / 依赖: Functor, Functor.const
-/
def self (X : C) : ColimitPresentation PUnit.{s + 1} X where
  diag := (Functor.const _).obj X
  ι := 𝟙 _
  isColimit := isColimitConstCocone _ _

/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: (F : J ⥤ C) [HasColimit F]
  body: F
  ι := _
  isColimit := colimit.isColimit _

中文:
定义 colimit
  签名: (F : J ⥤ C) [HasColimit F]
  定义体: F
  ι := _
  isColimit := colimit.isColimit _
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
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (P : ColimitPresentation J X) {D : Type*} [Category* D] (F : C ⥤ D)
  body: P.diag ⋙ F
  ι := Functor.whiskerRight P.ι F ≫ (F.constComp _ _).hom
  isColimit := (isColimitOfPreserves F P.isColimit).ofIsoColimit (Cocone.ext (.refl _) (by simp))

中文:
定义 map
  签名: (P : ColimitPresentation J X) {D : 类型} [Category* D] (F : C ⥤ D)
  定义体: P.diag ⋙ F
  ι := Functor.whiskerRight P.ι F ≫ (F.constComp _ _).hom
  isColimit := (isColimitOfPreserves F P.isColimit).ofIsoColimit (Cocone.ext (.refl _) (by simp))

Depends on / 依赖: P.diag
-/
def map (P : ColimitPresentation J X) {D : Type*} [Category* D] (F : C ⥤ D)
    [PreservesColimitsOfShape J F] : ColimitPresentation J (F.obj X) where
  diag := P.diag ⋙ F
  ι := Functor.whiskerRight P.ι F ≫ (F.constComp _ _).hom
  isColimit := (isColimitOfPreserves F P.isColimit).ofIsoColimit (Cocone.ext (.refl _) (by simp))

/-- If `P` is a colimit presentation of `X`, it is possible to define another
colimit presentation of `X` where `P.diag` is replaced by an isomorphic functor. -/
@[simps]
/--
Definition of `changeDiag` / `changeDiag` 的定义

English:
definition changeDiag
  signature: (P : ColimitPresentation J X) {F : J ⥤ C} (e : F ≅ P.diag)
  body: F
  ι := e.hom ≫ P.ι
  isColimit := (IsColimit.precomposeHomEquiv e _).2 P.isColimit

中文:
定义 changeDiag
  签名: (P : ColimitPresentation J X) {F : J ⥤ C} (e : F ≅ P.diag)
  定义体: F
  ι := e.hom ≫ P.ι
  isColimit := (IsColimit.precomposeHomEquiv e _).2 P.isColimit
-/
def changeDiag (P : ColimitPresentation J X) {F : J ⥤ C} (e : F ≅ P.diag) :
    ColimitPresentation J X where
  diag := F
  ι := e.hom ≫ P.ι
  isColimit := (IsColimit.precomposeHomEquiv e _).2 P.isColimit

/-- Map a colimit presentation under an isomorphism. -/
@[simps]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: (P : ColimitPresentation J X) {Y : C} (e : X ≅ Y)
  body: P.diag
  ι := P.ι ≫ (Functor.const J).map e.hom
  isColimit := P.isColimit.ofIsoColimit (Cocone.ext e fun _ => rfl)

中文:
定义 ofIso
  签名: (P : ColimitPresentation J X) {Y : C} (e : X ≅ Y)
  定义体: P.diag
  ι := P.ι ≫ (Functor.const J).map e.hom
  isColimit := P.isColimit.ofIsoColimit (Cocone.ext e fun _ => rfl)

Depends on / 依赖: P.diag
-/
def ofIso (P : ColimitPresentation J X) {Y : C} (e : X ≅ Y) : ColimitPresentation J Y where
  diag := P.diag
  ι := P.ι ≫ (Functor.const J).map e.hom
  isColimit := P.isColimit.ofIsoColimit (Cocone.ext e fun _ => rfl)

/-- Change the index category of a colimit presentation. -/
@[simps]
noncomputable
/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: (P : ColimitPresentation J X) {J' : Type*} [Category* J'] (F : J' ⥤ J) [F.Final]
  body: F ⋙ P.diag
  ι := F.whiskerLeft P.ι
  isColimit := (Functor.Final.isColimitWhiskerEquiv F _).symm P.isColimit

中文:
定义 reindex
  签名: (P : ColimitPresentation J X) {J' : 类型} [Category* J'] (F : J' ⥤ J) [F.Final]
  定义体: F ⋙ P.diag
  ι := F.whiskerLeft P.ι
  isColimit := (Functor.Final.isColimitWhiskerEquiv F _).symm P.isColimit

Depends on / 依赖: P.diag
-/
def reindex (P : ColimitPresentation J X) {J' : Type*} [Category* J'] (F : J' ⥤ J) [F.Final] :
    ColimitPresentation J' X where
  diag := F ⋙ P.diag
  ι := F.whiskerLeft P.ι
  isColimit := (Functor.Final.isColimitWhiskerEquiv F _).symm P.isColimit

end ColimitPresentation

/--
Definition of `LimitPresentation` / `LimitPresentation` 的定义

English:
structure LimitPresentation
  parameters: (J : Type w) [Category.{t} J] (X : C)
  axioms and operations (3):
    - diag : J ⥤ C
    - π : (Functor.const J).obj X ⟶ diag
    - isLimit : IsLimit (Cone.mk _ π)

中文:
结构 LimitPresentation
  参数: (J : Type w) [Category.{t} J] (X : C)
  公理与运算 (3 个):
    - diag : J ⥤ C
    - π : (Functor.const J).obj X ⟶ diag
    - isLimit : IsLimit (Cone.mk _ π)
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
/--
lemma `w` / 引理 `w`

English:
lemma w
  given: (pres : LimitPresentation J X) {i j : J} (f : i ⟶ j)
  proof: by
  simpa using (pres.π.naturality f).symm

中文:
引理 w
  条件: (pres : LimitPresentation J X) {i j : J} (f : i ⟶ j)
  证明: by
  simpa using (pres.π.naturality f).symm

Depends on / 依赖: naturality
-/
lemma w (pres : LimitPresentation J X) {i j : J} (f : i ⟶ j) :
    pres.π.app i ≫ pres.diag.map f = pres.π.app j := by
  simpa using (pres.π.naturality f).symm

/--
Definition of `cone` / `cone` 的定义

English:
abbreviation cone
  signature: (pres : LimitPresentation J X)
  body: Cone.mk _ pres.π

中文:
缩写 cone
  签名: (pres : LimitPresentation J X)
  定义体: Cone.mk _ pres.π

Depends on / 依赖: Cone.mk
-/
abbrev cone (pres : LimitPresentation J X) : Cone pres.diag :=
  Cone.mk _ pres.π

/--
lemma `hasLimit` / 引理 `hasLimit`

English:
lemma hasLimit
  given: (pres : LimitPresentation J X)
  statement: HasLimit pres.diag
  proof: ⟨_, pres.isLimit⟩

中文:
引理 hasLimit
  条件: (pres : LimitPresentation J X)
  结论: HasLimit pres.diag
  证明: ⟨_, pres.isLimit⟩

Depends on / 依赖: isLimit, pres.isLimit
-/
lemma hasLimit (pres : LimitPresentation J X) : HasLimit pres.diag :=
  ⟨_, pres.isLimit⟩

/-- The canonical limit presentation of any object over a point. -/
@[simps]
noncomputable
/--
Definition of `self` / `self` 的定义

English:
definition self
  signature: (X : C)
  body: (Functor.const _).obj X
  π := 𝟙 _
  isLimit := isLimitConstCone _ _

中文:
定义 self
  签名: (X : C)
  定义体: (Functor.const _).obj X
  π := 𝟙 _
  isLimit := isLimitConstCone _ _

Depends on / 依赖: Functor, Functor.const
-/
def self (X : C) : LimitPresentation PUnit.{s + 1} X where
  diag := (Functor.const _).obj X
  π := 𝟙 _
  isLimit := isLimitConstCone _ _

/--
Definition of `limit` / `limit` 的定义

English:
definition limit
  signature: (F : J ⥤ C) [HasLimit F]
  body: F
  π := _
  isLimit := limit.isLimit _

中文:
定义 limit
  签名: (F : J ⥤ C) [HasLimit F]
  定义体: F
  π := _
  isLimit := limit.isLimit _
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
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (P : LimitPresentation J X) {D : Type*} [Category* D] (F : C ⥤ D)
  body: P.diag ⋙ F
  π := (F.constComp _ _).inv ≫ Functor.whiskerRight P.π F
  isLimit := (isLimitOfPreserves F P.isLimit).ofIsoLimit (Cone.ext (.refl _) (by simp))

中文:
定义 map
  签名: (P : LimitPresentation J X) {D : 类型} [Category* D] (F : C ⥤ D)
  定义体: P.diag ⋙ F
  π := (F.constComp _ _).inv ≫ Functor.whiskerRight P.π F
  isLimit := (isLimitOfPreserves F P.isLimit).ofIsoLimit (Cone.ext (.refl _) (by simp))

Depends on / 依赖: P.diag
-/
def map (P : LimitPresentation J X) {D : Type*} [Category* D] (F : C ⥤ D)
    [PreservesLimitsOfShape J F] : LimitPresentation J (F.obj X) where
  diag := P.diag ⋙ F
  π := (F.constComp _ _).inv ≫ Functor.whiskerRight P.π F
  isLimit := (isLimitOfPreserves F P.isLimit).ofIsoLimit (Cone.ext (.refl _) (by simp))

/-- If `P` is a limit presentation of `X`, it is possible to define another
limit presentation of `X` where `P.diag` is replaced by an isomorphic functor. -/
@[simps]
/--
Definition of `changeDiag` / `changeDiag` 的定义

English:
definition changeDiag
  signature: (P : LimitPresentation J X) {F : J ⥤ C} (e : F ≅ P.diag)
  body: F
  π := P.π ≫ e.inv
  isLimit := (IsLimit.postcomposeHomEquiv e.symm _).2 P.isLimit

中文:
定义 changeDiag
  签名: (P : LimitPresentation J X) {F : J ⥤ C} (e : F ≅ P.diag)
  定义体: F
  π := P.π ≫ e.inv
  isLimit := (IsLimit.postcomposeHomEquiv e.symm _).2 P.isLimit
-/
def changeDiag (P : LimitPresentation J X) {F : J ⥤ C} (e : F ≅ P.diag) :
    LimitPresentation J X where
  diag := F
  π := P.π ≫ e.inv
  isLimit := (IsLimit.postcomposeHomEquiv e.symm _).2 P.isLimit

set_option backward.defeqAttrib.useBackward true in
/-- Map a limit presentation under an isomorphism. -/
@[simps]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: (P : LimitPresentation J X) {Y : C} (e : X ≅ Y)
  body: P.diag
  π := (Functor.const J).map e.inv ≫ P.π
  isLimit := P.isLimit.ofIsoLimit (Cone.ext e)

中文:
定义 ofIso
  签名: (P : LimitPresentation J X) {Y : C} (e : X ≅ Y)
  定义体: P.diag
  π := (Functor.const J).map e.inv ≫ P.π
  isLimit := P.isLimit.ofIsoLimit (Cone.ext e)

Depends on / 依赖: P.diag
-/
def ofIso (P : LimitPresentation J X) {Y : C} (e : X ≅ Y) : LimitPresentation J Y where
  diag := P.diag
  π := (Functor.const J).map e.inv ≫ P.π
  isLimit := P.isLimit.ofIsoLimit (Cone.ext e)

/-- Change the index category of a limit presentation. -/
@[simps]
noncomputable
/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: (P : LimitPresentation J X) {J' : Type*} [Category* J'] (F : J' ⥤ J) [F.Initial]
  body: F ⋙ P.diag
  π := F.whiskerLeft P.π
  isLimit := (Functor.Initial.isLimitWhiskerEquiv F _).symm P.isLimit

中文:
定义 reindex
  签名: (P : LimitPresentation J X) {J' : 类型} [Category* J'] (F : J' ⥤ J) [F.Initial]
  定义体: F ⋙ P.diag
  π := F.whiskerLeft P.π
  isLimit := (Functor.Initial.isLimitWhiskerEquiv F _).symm P.isLimit

Depends on / 依赖: P.diag
-/
def reindex (P : LimitPresentation J X) {J' : Type*} [Category* J'] (F : J' ⥤ J) [F.Initial] :
    LimitPresentation J' X where
  diag := F ⋙ P.diag
  π := F.whiskerLeft P.π
  isLimit := (Functor.Initial.isLimitWhiskerEquiv F _).symm P.isLimit

end LimitPresentation

end CategoryTheory.Limits
