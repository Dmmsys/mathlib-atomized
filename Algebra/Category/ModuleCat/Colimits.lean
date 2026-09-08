/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# The category of R-modules has all colimits.

From the existence of colimits in `AddCommGrpCat`, we deduce the existence of colimits
in `ModuleCat R`. This way, we get for free that the functor
`forget₂ (ModuleCat R) AddCommGrpCat` commutes with colimits.

Note that finite colimits can already be obtained from the instance `Abelian (Module R)`.

TODO:
In fact, in `ModuleCat R` there is a much nicer model of colimits as quotients
of finitely supported functions, and we really should implement this as well.
-/

@[expose] public section

universe w' w u v

open CategoryTheory Category Limits

variable {R : Type w} [Ring R]

namespace ModuleCat

variable {J : Type u} [Category.{v} J] (F : J ⥤ ModuleCat.{w'} R)

namespace HasColimit

variable [HasColimit (F ⋙ forget₂ _ AddCommGrpCat)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The induced scalar multiplication on
`colimit (F ⋙ forget₂ _ AddCommGrpCat)`. -/
@[simps]
/-
**ModuleCat.HasColimit.coconePointSMul** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.HasC
olimit`。
形式化陈述：coconePointSMul : R ->+* End (colimit (F ⋙ forget₂ _ AddCommGrpCat)) where
 toFun r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced scalar multiplication on
`colimit (F ⋙ forget₂ _ AddCommGrpCat)`.
-/
noncomputable def coconePointSMul :
    R →+* End (colimit (F ⋙ forget₂ _ AddCommGrpCat)) where
  toFun r := colimMap
    { app := fun j => (F.obj j).smul r
      naturality := fun _ _ _ => smul_naturality _ _ }
  map_zero' := colimit.hom_ext (by simp +instances)
  map_one' := colimit.hom_ext (by simp +instances)
  map_add' r s := colimit.hom_ext (fun j => by
    simp +instances only [Functor.comp_obj, forget₂_obj, map_add, ι_colimMap]
    rw [Preadditive.add_comp, Preadditive.comp_add]
    simp only [ι_colimMap, Functor.comp_obj, forget₂_obj])
  map_mul' r s := colimit.hom_ext (fun j => by simp +instances)

set_option backward.isDefEq.respectTransparency false in
/-- The cocone for `F` constructed from the colimit of
`(F ⋙ forget₂ (ModuleCat R) AddCommGrpCat)`. -/
@[simps]
/-
**ModuleCat.HasColimit.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.HasCol
imit`。
形式化陈述：colimitCocone : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone for `F` constructed from the colimit of
`(F ⋙ forget₂ (ModuleCat R) AddCommGrpCat)`.
-/
noncomputable def colimitCocone : Cocone F where
  pt := mkOfSMul (coconePointSMul F)
  ι :=
    { app := fun j => homMk (colimit.ι (F ⋙ forget₂ _ AddCommGrpCat) j) (fun r => by
        dsimp
        -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
        erw [mkOfSMul_smul]
        simp)
      naturality := fun i j f => by
        apply (forget₂ _ AddCommGrpCat).map_injective
        simp only [Functor.map_comp, forget₂_map_homMk]
        dsimp
        erw [colimit.w (F ⋙ forget₂ _ AddCommGrpCat), comp_id] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cocone for `F` constructed from the colimit of
`(F ⋙ forget₂ (ModuleCat R) AddCommGrpCat)` is a colimit cocone. -/
/-
**ModuleCat.HasColimit.isColimitColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `ModuleC
at.HasColimit`。
形式化陈述：isColimitColimitCocone : IsColimit (colimitCocone F) where desc s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone for `F` constructed from the colimit of
`(F ⋙ forget₂ (ModuleCat R) AddCommGrpCat)` is a colimit cocone.
-/
noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) where
  desc s := homMk (colimit.desc _ ((forget₂ _ AddCommGrpCat).mapCocone s)) (fun r => by
    apply colimit.hom_ext
    intro j
    dsimp
    rw [colimit.ι_desc_assoc]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [mkOfSMul_smul]
    dsimp
    simp only [ι_colimMap_assoc, Functor.comp_obj, forget₂_obj, colimit.ι_desc,
      Functor.mapCocone_pt, Functor.mapCocone_ι_app, forget₂_map]
    exact smul_naturality (s.ι.app j) r)
  fac s j := by
    apply (forget₂ _ AddCommGrpCat).map_injective
    exact colimit.ι_desc ((forget₂ _ AddCommGrpCat).mapCocone s) j
  uniq s m hm := by
    apply (forget₂ _ AddCommGrpCat).map_injective
    apply colimit.hom_ext
    intro j
    erw [colimit.ι_desc ((forget₂ _ AddCommGrpCat).mapCocone s) j]
    dsimp
    rw [← hm]
    rfl
/-
**ModuleCat.HasColimit.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.HasColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasColimit F := ⟨_, isColimitColimitCocone F⟩
/-
**ModuleCat.HasColimit.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.HasColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesColimit F (forget₂ _ AddCommGrpCat) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F) (colimit.isColimit _)
/-
**ModuleCat.HasColimit.reflectsColimit** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.HasC
olimit`。
形式化陈述：reflectsColimit : ReflectsColimit F (forget₂ (ModuleCat.{w'} R) AddCommGrp
Cat)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimit_of_reflectsIsomorphisms`：reflectsC
olimit_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms] 
[HasColimit F] [PreservesColimit F G] : ReflectsCol…
· 使用定理 `ModuleCat.instReflectsIsomorphismsAddCommGrpCatForget₂LinearMapIdCarrier
AddMonoidHomCarrier`：∀ {R : Type u} [inst : Ring R], (CategoryTheory.forget₂ (Mo
duleCat R) AddCommGrpCat).ReflectsIsomorphisms
· 使用定理 `ModuleCat.HasColimit.instHasColimit`：∀ {R : Type w} [inst : Ring R] {J :
 Type u} [inst_1 : CategoryTheory.Category.{v, u} J]   (F : CategoryTheory.Funct
or J (ModuleCat R))   [Ca…
· 使用定理 `ModuleCat.HasColimit.instPreservesColimitAddCommGrpCatForget₂LinearMapId
CarrierAddMonoidHomCarrier`：∀ {R : Type w} [inst : Ring R] {J : Type u} [inst_1 
: CategoryTheory.Category.{v, u} J]   (F : CategoryTheory.Functor J (ModuleCat R
))   [Ca…
-/
noncomputable instance reflectsColimit :
    ReflectsColimit F (forget₂ (ModuleCat.{w'} R) AddCommGrpCat) :=
  reflectsColimit_of_reflectsIsomorphisms _ _

end HasColimit

variable (J R)

/-
**ModuleCat.hasColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ (R : Type w) [inst : Ring R] (J : Type u) [inst_1 : CategoryTheory.Categ
ory.{v, u} J]   [CategoryTheory.Limits.HasColimitsOfShape J AddCommGrpCat], Cate
goryTheory.Limits.HasColimitsOfShape J (ModuleCat R)
参数：R : Type w；J : Type u；ModuleCat R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.HasColimit.instHasColimit`：∀ {R : Type w} [inst : Ring R] {J :
 Type u} [inst_1 : CategoryTheory.Category.{v, u} J]   (F : CategoryTheory.Funct
or J (ModuleCat R))   [Ca…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasColimitsOfShape [HasColimitsOfShape J AddCommGrpCat.{w'}] :
    HasColimitsOfShape J (ModuleCat.{w'} R) where
/-
**ModuleCat.reflectsColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ (R : Type w) [inst : Ring R] (J : Type u) [inst_1 : CategoryTheory.Categ
ory.{v, u} J]   [CategoryTheory.Limits.HasColimitsOfShape J AddCommGrpCat],   Ca
tegoryTheory.Limits.ReflectsColimitsOfShape J (CategoryTheory.forget₂ (ModuleCat
 R) AddCommGrpCat)
参数：R : Type w；J : Type u；CategoryTheory.forget₂ (ModuleCat R) AddCommGrpCat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
noncomputable instance reflectsColimitsOfShape [HasColimitsOfShape J AddCommGrpCat.{w'}] :
    ReflectsColimitsOfShape J (forget₂ (ModuleCat.{w'} R) AddCommGrpCat) where
/-
**ModuleCat.hasColimitsOfSize** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ (R : Type w) [inst : Ring R] [CategoryTheory.Limits.HasColimitsOfSize.{v
, u, w', w' + 1} AddCommGrpCat],   CategoryTheory.Limits.HasColimitsOfSize.{v, u
, w', max (w' + 1) w} (ModuleCat R)
参数：R : Type w；w' + 1；ModuleCat R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.hasColimitsOfShape`：∀ (R : Type w) [inst : Ring R] (J : Type u
) [inst_1 : CategoryTheory.Category.{v, u} J]   [CategoryTheory.Limits.HasColimi
tsOfShape J AddCom…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasColimitsOfSize [HasColimitsOfSize.{v, u} AddCommGrpCat.{w'}] :
    HasColimitsOfSize.{v, u} (ModuleCat.{w'} R) where
/-
**ModuleCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget₂PreservesColimitsOfShape
    [HasColimitsOfShape J AddCommGrpCat.{w'}] :
    PreservesColimitsOfShape J (forget₂ (ModuleCat.{w'} R) AddCommGrpCat) where
/-
**ModuleCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget₂PreservesColimitsOfSize
    [HasColimitsOfSize.{u, v} AddCommGrpCat.{w'}] :
    PreservesColimitsOfSize.{u, v} (forget₂ (ModuleCat.{w'} R) AddCommGrpCat) where
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance
    [HasColimitsOfSize.{u, v} AddCommGrpMax.{w, w'}] :
    PreservesColimitsOfSize.{u, v} (forget₂ (ModuleCat.{max w w'} R) AddCommGrpCat) where
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasFiniteColimits (ModuleCat.{w'} R) := inferInstance

-- Sanity checks, just to make sure typeclass search can find the instances we want.
/-
**ModuleCat.** 是 Mathlib 中的一个示例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (R : Type u) [Ring R] : HasColimits (ModuleCat.{max v u} R) :=
  inferInstance
/-
**ModuleCat.** 是 Mathlib 中的一个示例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (R : Type u) [Ring R] : HasColimits (ModuleCat.{max u v} R) :=
  inferInstance
/-
**ModuleCat.** 是 Mathlib 中的一个示例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (R : Type u) [Ring R] : HasColimits (ModuleCat.{u} R) :=
  inferInstance
/-
**ModuleCat.** 是 Mathlib 中的一个示例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (R : Type u) [Ring R] : HasCoequalizers (ModuleCat.{u} R) := by
  infer_instance

-- for some reason, this instance is not found automatically later on
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasCoequalizers (ModuleCat.{v} R) where
/-
**ModuleCat.** 是 Mathlib 中的一个示例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example (R : Type u) [Ring R] :
    PreservesColimits (forget₂ (ModuleCat.{u} R) AddCommGrpCat) := inferInstance

section

variable (R : Type w) [CommRing R] (M ι : Type u) [AddCommGroup M] [Module R M]

/-- The coproduct cone induced by the concrete coproduct. -/
noncomputable
/-
**ModuleCat.finsuppCocone** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：finsuppCocone : Cofan fun _ : ι => ModuleCat.of R M
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def finsuppCocone : Cofan fun _ : ι ↦ ModuleCat.of R M :=
  Cofan.mk (ModuleCat.of R (ι →₀ M)) fun i ↦
    ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := ModuleCat.of R M))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The concrete coproduct cone is colimiting. -/
noncomputable
/-
**ModuleCat.finsuppCoconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：finsuppCoconeIsColimit : IsColimit (finsuppCocone R M ι) where desc s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def finsuppCoconeIsColimit : IsColimit (finsuppCocone R M ι) where
  desc s := ModuleCat.ofHom <| Finsupp.lsum R (N := s.pt) (fun i ↦ (s.ι.app ⟨i⟩).hom)
  fac := by aesop (add simp finsuppCocone)
  uniq s f h := by
    ext : 1
    exact Finsupp.lhom_ext' fun i ↦ LinearMap.ext fun x ↦ by simpa using! congr($(h ⟨i⟩) (x : M))

end

end ModuleCat

