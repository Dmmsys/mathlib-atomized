/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Canonical colimits, or functors that are dense at an object

Given a functor `F : C ⥤ D` and `Y : D`, we say that `F` is dense at `Y` (`F.DenseAt Y`),
if `Y` identifies to the colimit of all `F.obj X` for `X : C`
and `f : F.obj X ⟶ Y`, i.e. `Y` identifies to the colimit of
the obvious functor `CostructuredArrow F Y ⥤ D`. In some references,
it is also said that `Y` is a canonical colimit relatively to `F`.
While `F.DenseAt Y` contains data, we also introduce the
corresponding property `isDenseAt F` of objects of `D`.

## TODO

* formalize dense subcategories
* show the presheaves of types are canonical colimits relatively
  to the Yoneda embedding

## References
* https://ncatlab.org/nlab/show/dense+functor

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (F : C ⥤ D)

namespace Functor

/-- A functor `F : C ⥤ D` is dense at `Y : D` if the obvious natural transformation
`F ⟶ F ⋙ 𝟭 D` makes `𝟭 D` a pointwise left Kan extension of `F` along itself at `Y`,
i.e. `Y` identifies to the colimit of the obvious functor `CostructuredArrow F Y ⥤ D`. -/
/-
**CategoryTheory.Functor.DenseAt** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：DenseAt (Y : D) : Type max u₁ u₂ v₂
参数：Y : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` is dense at `Y : D` if the obvious natural transformation
`F ⟶ F ⋙ 𝟭 D` makes `𝟭 D` a pointwise left Kan extension of `F` along itself at 
`Y`,
i.e. `Y` identifies to the colimit of the obvious functor `CostructuredArrow F Y
 ⥤ D`.
-/
abbrev DenseAt (Y : D) : Type max u₁ u₂ v₂ :=
  (Functor.LeftExtension.mk (𝟭 D) F.rightUnitor.inv).IsPointwiseLeftKanExtensionAt Y

/-- `F` is dense at `Y` if `Y` identifies to the colimit of the obvious functor
`CostructuredArrow F Y ⥤ D`. -/
/-
**CategoryTheory.Functor.denseAtEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：denseAtEquiv (Y : D) : F.DenseAt Y ≃ IsColimit ((LeftExtension.mk (𝟭 D) F.
rightUnitor.inv).coconeAt Y)
参数：Y : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`F` is dense at `Y` if `Y` identifies to the colimit of the obvious functor
`CostructuredArrow F Y ⥤ D`.
-/
def denseAtEquiv (Y : D) :
    F.DenseAt Y ≃ IsColimit ((LeftExtension.mk (𝟭 D) F.rightUnitor.inv).coconeAt Y) :=
  .refl _

variable {F} {Y : D} (hY : F.DenseAt Y)

/-- If `F : C ⥤ D` is dense at `Y : D`, then it is also at `Y'`
if `Y` and `Y'` are isomorphic. -/
/-
**CategoryTheory.Functor.DenseAt.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor.DenseAt`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F : Cat
egoryTheory.Functor C D} → {Y : D} → F.DenseAt Y → {Y' : D} → (Y ≅ Y') → F.Dense
At Y'
参数：Y ≅ Y'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` is dense at `Y : D`, then it is also at `Y'`
if `Y` and `Y'` are isomorphic.
-/
def DenseAt.ofIso {Y' : D} (e : Y ≅ Y') : F.DenseAt Y' :=
  LeftExtension.isPointwiseLeftKanExtensionAtOfIso' _ hY e

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F : C ⥤ D` is dense at `Y : D`, and `G` is a functor that is isomorphic to `F`,
then `G` is also dense at `Y`. -/
/-
**CategoryTheory.Functor.DenseAt.ofNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.DenseAt`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F : Cat
egoryTheory.Functor C D} →           {Y : D} → F.DenseAt Y → {G : CategoryTheory
.Functor C D} → (F ≅ G) → G.DenseAt Y
参数：F ≅ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` is dense at `Y : D`, and `G` is a functor that is isomorphic to `
F`,
then `G` is also dense at `Y`.
-/
def DenseAt.ofNatIso {G : C ⥤ D} (e : F ≅ G) : G.DenseAt Y :=
  (IsColimit.equivOfNatIsoOfIso
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerLeft _ e) _ _
      (by exact Cocone.ext (Iso.refl _)))
    (hY.whiskerEquivalence (CostructuredArrow.mapNatIso e.symm))

/-- If the canonical functor `CostructuredArrow (G ≫ F) Y ⥤ CostructuredArrow F Y` is final, then
`G ⋙ F` is dense at `Y` if and only if `F` is dense at `Y`. -/
/-
**CategoryTheory.Functor.DenseAt.precompEquivOfFinal** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor.DenseAt`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F : Cat
egoryTheory.Functor C D} →           {Y : D} →             {C' : Type u_1} →    
           [inst_2 : CategoryTheory.Category.{v_1, u_1} C'] →                 (G
 : CategoryTheory.Functor C' C) →                   [(CategoryTheory.Costructure
dArrow.pre G F Y).Final] → (G.comp F).DenseAt Y ≃ F.DenseAt Y
参数：G : CategoryTheory.Functor C' C；CategoryTheory.CostructuredArrow.pre G F Y；G.
comp F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the canonical functor `CostructuredArrow (G ≫ F) Y ⥤ CostructuredArrow F Y` i
s final, then
`G ⋙ F` is dense at `Y` if and only if `F` is dense at `Y`.
-/
noncomputable def DenseAt.precompEquivOfFinal
    {C' : Type*} [Category* C'] (G : C' ⥤ C) [(CostructuredArrow.pre G F Y).Final] :
    (G ⋙ F).DenseAt Y ≃ F.DenseAt Y :=
  Functor.Final.isColimitWhiskerEquiv (CostructuredArrow.pre G F Y)
    ((LeftExtension.mk (𝟭 D) F.rightUnitor.inv).coconeAt Y)

/-- If `F : C ⥤ D` is dense at `Y : D`, then so is `G ⋙ F` if
the canonical functor `CostructuredArrow (G ≫ F) Y ⥤ CostructuredArrow F Y` is final.
This holds in particular if `G` is an equivalence. -/
/-
**CategoryTheory.Functor.DenseAt.precompOfFinal** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor.DenseAt`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F : Cat
egoryTheory.Functor C D} →           {Y : D} →             F.DenseAt Y →        
       {C' : Type u_1} →                 [inst_2 : CategoryTheory.Category.{v_1,
 u_1} C'] →                   (G : CategoryTheory.Functor C' C) →               
      [(CategoryTheory.CostructuredArrow.pre G F Y).Final] → (G.comp F).DenseAt 
Y
参数：G : CategoryTheory.Functor C' C；CategoryTheory.CostructuredArrow.pre G F Y；G.
comp F。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F : C ⥤ D` is dense at `Y : D`, then so is `G ⋙ F` if
the canonical functor `CostructuredArrow (G ≫ F) Y ⥤ CostructuredArrow F Y` is f
inal.
This holds in particular if `G` is an equivalence.
-/
noncomputable def DenseAt.precompOfFinal
    {C' : Type*} [Category* C'] (G : C' ⥤ C) [(CostructuredArrow.pre G F Y).Final] :
    (G ⋙ F).DenseAt Y :=
  (DenseAt.precompEquivOfFinal G).symm hY

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F : C ⥤ D` is dense at `Y : D` and `G : D ⥤ D'` is an equivalence,
then `F ⋙ G` is dense at `G.obj Y`. -/
/-
**CategoryTheory.Functor.DenseAt.postcompEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor.DenseAt`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F : Cat
egoryTheory.Functor C D} →           {Y : D} →             F.DenseAt Y →        
       {D' : Type u_1} →                 [inst_2 : CategoryTheory.Category.{v_1,
 u_1} D'] →                   (G : CategoryTheory.Functor D D') → [G.IsEquivalen
ce] → (F.comp G).DenseAt (G.obj Y)
参数：G : CategoryTheory.Functor D D'；F.comp G；G.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` is dense at `Y : D` and `G : D ⥤ D'` is an equivalence,
then `F ⋙ G` is dense at `G.obj Y`.
-/
noncomputable def DenseAt.postcompEquivalence
    {D' : Type*} [Category* D'] (G : D ⥤ D') [G.IsEquivalence] :
    (F ⋙ G).DenseAt (G.obj Y) :=
  IsColimit.ofWhiskerEquivalence (CostructuredArrow.post F G Y).asEquivalence
    (IsColimit.ofIsoColimit ((isColimitOfPreserves G hY)) (Cocone.ext (Iso.refl _)))
/-
**CategoryTheory.Functor.DenseAt.hasPointwiseLeftKanExtensionAt** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Functor.DenseAt`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {Y : D} (hf : F.DenseAt Y), F.HasPointwiseLeftKanExtensionAt F Y
参数：hf : F.DenseAt Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma DenseAt.hasPointwiseLeftKanExtensionAt (hf : F.DenseAt Y) :
    F.HasPointwiseLeftKanExtensionAt F Y :=
  ⟨_, hf⟩

variable (F) in
/-- Given a functor `F : C ⥤ D`, this is the property of objects `Y : D` such
that `F` is dense at `Y`. -/
/-
**CategoryTheory.Functor.isDenseAt** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：isDenseAt : ObjectProperty D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C ⥤ D`, this is the property of objects `Y : D` such
that `F` is dense at `Y`.
-/
def isDenseAt : ObjectProperty D :=
  fun Y ↦ Nonempty (F.DenseAt Y)
/-
**CategoryTheory.Functor.isDenseAt_eq_isPointwiseLeftKanExtensionAt** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isDenseAt_eq_isPointwiseLeftKanExtensionAt : F.isDenseAt = (Functor.LeftEx
tension.mk (𝟭 D) F.rightUnitor.inv).isPointwiseLeftKanExtensionAt
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isDenseAt_eq_isPointwiseLeftKanExtensionAt :
    F.isDenseAt =
      (Functor.LeftExtension.mk (𝟭 D) F.rightUnitor.inv).isPointwiseLeftKanExtensionAt :=
  rfl
/-
**CategoryTheory.Functor.isDenseAt_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：isDenseAt_iff {X : D} : F.isDenseAt X ↔ Nonempty (IsColimit <| (LeftExtens
ion.mk (𝟭 D) F.rightUnitor.inv).coconeAt X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isDenseAt_iff {X : D} :
    F.isDenseAt X ↔ Nonempty (IsColimit <| (LeftExtension.mk (𝟭 D) F.rightUnitor.inv).coconeAt X) :=
  .rfl
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : F.isDenseAt.IsClosedUnderIsomorphisms := by
  rw [isDenseAt_eq_isPointwiseLeftKanExtensionAt]
  infer_instance
/-
**CategoryTheory.Functor.congr_isDenseAt** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：congr_isDenseAt {G : C ⥤ D} (e : F ≅ G) : F.isDenseAt = G.isDenseAt
参数：e : F ≅ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma congr_isDenseAt {G : C ⥤ D} (e : F ≅ G) :
    F.isDenseAt = G.isDenseAt := by
  ext X
  exact ⟨fun ⟨h⟩ ↦ ⟨h.ofNatIso e⟩, fun ⟨h⟩ ↦ ⟨h.ofNatIso e.symm⟩⟩
/-
**CategoryTheory.Functor.IsDenseAt.iff_of_final** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Functor.IsDenseAt`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {Y : D} {C' : Type u_1} [inst_2 : CategoryTheory.Category.{v_1, u_1} C']   (G :
 CategoryTheory.Functor C' C) [(CategoryTheory.CostructuredArrow.pre G F Y).Fina
l],   (G.comp F).isDenseAt Y ↔ F.isDenseAt Y
参数：G : CategoryTheory.Functor C' C；CategoryTheory.CostructuredArrow.pre G F Y；G.
comp F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
-/
lemma IsDenseAt.iff_of_final {C' : Type*} [Category* C'] (G : C' ⥤ C)
    [(CostructuredArrow.pre G F Y).Final] :
    (G ⋙ F).isDenseAt Y ↔ F.isDenseAt Y :=
  (DenseAt.precompEquivOfFinal G).nonempty_congr
/-
**CategoryTheory.Functor.IsDenseAt.of_final** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor.IsDenseAt`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {Y : D} {C' : Type u_1} [inst_2 : CategoryTheory.Category.{v_1, u_1} C']   (G :
 CategoryTheory.Functor C' C) [(CategoryTheory.CostructuredArrow.pre G F Y).Fina
l],   F.isDenseAt Y → (G.comp F).isDenseAt Y
参数：G : CategoryTheory.Functor C' C；CategoryTheory.CostructuredArrow.pre G F Y；G.
comp F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Functor.IsDenseAt.iff_of_final`：∀ {C : Type u₁} {D : Type
 u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F : CategoryTheor…
-/
lemma IsDenseAt.of_final {C' : Type*} [Category* C'] (G : C' ⥤ C)
    [(CostructuredArrow.pre G F Y).Final] (hY : F.isDenseAt Y) :
    (G ⋙ F).isDenseAt Y :=
  (iff_of_final G).mpr hY

end Functor

end CategoryTheory

