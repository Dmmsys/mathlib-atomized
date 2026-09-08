/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Module.Shrink -- shake: keep (Module R (Shrink.{w, max v w} ↥(sectionsSubmodule F))), cf. lean#13417

/-!
# The category of R-modules has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

@[expose] public section


open CategoryTheory Limits

universe t v w u

-- `u` is determined by the ring, so can come later
noncomputable section

namespace ModuleCat

variable {R : Type u} [Ring R]
variable {J : Type v} [Category.{t} J] (F : J ⥤ ModuleCat.{w} R)

/-
**ModuleCat.addCommGroupObj** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：addCommGroupObj (j) : AddCommGroup ((F ⋙ forget (ModuleCat R)).obj j)
参数：j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroupObj (j) :
    AddCommGroup ((F ⋙ forget (ModuleCat R)).obj j) :=
  inferInstanceAs <| AddCommGroup (F.obj j)
/-
**ModuleCat.moduleObj** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：moduleObj (j) : Module.{u, w} R ((F ⋙ forget (ModuleCat R)).obj j)
参数：j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance moduleObj (j) :
    Module.{u, w} R ((F ⋙ forget (ModuleCat R)).obj j) :=
  inferInstanceAs <| Module R (F.obj j)

set_option backward.isDefEq.respectTransparency false in
/-- The flat sections of a functor into `ModuleCat R` form a submodule of all sections.
-/
/-
**ModuleCat.sectionsSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：sectionsSubmodule : Submodule R (forall j, F.obj j)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The flat sections of a functor into `ModuleCat R` form a submodule of all sectio
ns.
-/
def sectionsSubmodule : Submodule R (∀ j, F.obj j) :=
  { AddGrpCat.sectionsAddSubgroup.{v, w}
      (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{w} ⋙
          forget₂ AddCommGrpCat AddGrpCat.{w}) with
    carrier := (F ⋙ forget (ModuleCat R)).sections
    smul_mem' := fun r s sh j j' f => by
      simpa [Functor.sections] using congr_arg (r • ·) (sh f) }
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (F ⋙ forget (ModuleCat R)).sections :=
  inferInstanceAs <| AddCommMonoid (sectionsSubmodule F)
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (F ⋙ forget (ModuleCat R)).sections :=
  inferInstanceAs <| Module R (sectionsSubmodule F)

section

variable [Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))]

/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Small.{w} (sectionsSubmodule F) :=
  inferInstanceAs <| Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))

-- Adding the following instance speeds up `limitModule` noticeably,
-- by preventing a bad unfold of `limitAddCommGroup`.
/-
**ModuleCat.limitAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：limitAddCommMonoid : AddCommMonoid (Types.Small.limitCone.{v, w} (F ⋙ forg
et (ModuleCat.{w} R))).pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance limitAddCommMonoid :
    AddCommMonoid (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
  inferInstanceAs <| AddCommMonoid (Shrink (sectionsSubmodule F))
/-
**ModuleCat.limitAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：limitAddCommGroup : AddCommGroup (Types.Small.limitCone.{v, w} (F ⋙ forget
 (ModuleCat.{w} R))).pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance limitAddCommGroup :
    AddCommGroup (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
  inferInstanceAs <| AddCommGroup (Shrink.{w} (sectionsSubmodule F))
/-
**ModuleCat.limitModule** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：limitModule : Module R (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCa
t.{w} R))).pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance limitModule :
    Module R (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
  inferInstanceAs <| Module R (Shrink (sectionsSubmodule F))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `limit.π (F ⋙ forget (ModuleCat.{w} R)) j` as an `R`-linear map. -/
/-
**ModuleCat.limit** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`limit.π (F ⋙ forget (ModuleCat.{w} R)) j` as an `R`-linear map.
-/
def limitπLinearMap (j) :
    (Types.Small.limitCone (F ⋙ forget (ModuleCat.{w} R))).pt →ₗ[R]
      (F ⋙ forget (ModuleCat R)).obj j where
  toFun := (Types.Small.limitCone (F ⋙ forget (ModuleCat R))).π.app j
  map_smul' _ _ := by simp; rfl
  map_add' _ _ := by simp; rfl

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits (ModuleCat R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/-- Construction of a limit cone in `ModuleCat R`.
(Internal use only; use the limits API.)
-/
/-
**ModuleCat.HasLimits.limitCone** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.HasLimits`。
形式化陈述：limitCone : Cone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construction of a limit cone in `ModuleCat R`.
(Internal use only; use the limits API.)
-/
def limitCone : Cone F where
  pt := ModuleCat.of R (Types.Small.limitCone.{v, w} (F ⋙ forget _)).pt
  π :=
    { app j := ofHom (limitπLinearMap F j)
      naturality _ _ f := by
        ext
        simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Witness that the limit cone in `ModuleCat R` is a limit cone.
(Internal use only; use the limits API.)
-/
/-
**ModuleCat.HasLimits.limitConeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.HasL
imits`。
形式化陈述：limitConeIsLimit : IsLimit (limitCone.{t, v, w} F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Witness that the limit cone in `ModuleCat R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit : IsLimit (limitCone.{t, v, w} F) := by
  refine IsLimit.ofFaithful (forget (ModuleCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
    (fun s => ofHom ⟨⟨(Types.Small.limitConeIsLimit.{v, w} _).lift
                ((forget (ModuleCat R)).mapCone s), ?_⟩, ?_⟩)
    (fun s => rfl)
  · intro x y
    simp [← equivShrink_add]
    rfl
  · intro r x
    simp [← equivShrink_smul]
    rfl

end HasLimits

open HasLimits

/-- If `(F ⋙ forget (ModuleCat R)).sections` is `u`-small, `F` has a limit. -/
/-
**ModuleCat.hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：hasLimit : HasLimit F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…

--- 原说明 ---
If `(F ⋙ forget (ModuleCat R)).sections` is `u`-small, `F` has a limit.
-/
instance hasLimit : HasLimit F := HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/-- If `J` is `u`-small, the category of `R`-modules has limits of shape `J`. -/
/-
**ModuleCat.hasLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {J : Type v} [inst_1 : CategoryTheory.Categ
ory.{t, v} J] [Small.{w, v} J],   CategoryTheory.Limits.HasLimitsOfShape J (Modu
leCat R)
参数：ModuleCat R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
If `J` is `u`-small, the category of `R`-modules has limits of shape `J`.
-/
lemma hasLimitsOfShape [Small.{w} J] : HasLimitsOfShape J (ModuleCat.{w} R) where

/-- The category of R-modules has all limits. -/
/-
**ModuleCat.hasLimitsOfSize** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (ModuleCat.{w} R)
 where has_limits_of_shape _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.hasLimitsOfShape`：∀ {R : Type u} [inst : Ring R] {J : Type v} 
[inst_1 : CategoryTheory.Category.{t, v} J] [Small.{w, v} J],   CategoryTheory.L
imits.HasLimitsO…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
The category of R-modules has all limits.
-/
lemma hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (ModuleCat.{w} R) where
  has_limits_of_shape _ := hasLimitsOfShape
/-
**ModuleCat.hasLimits** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：hasLimits : HasLimits (ModuleCat.{w} R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hasLimitsOfSize`：hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOf
Size.{t, v} (ModuleCat.{w} R) where has_limits_of_shape _
-/
instance hasLimits : HasLimits (ModuleCat.{w} R) :=
  ModuleCat.hasLimitsOfSize.{w, w, w, u}
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := high) hasLimits' : HasLimits (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u}

/-- An auxiliary declaration to speed up typechecking.
-/
/-
**ModuleCat.forget** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommGroup_preservesLimitsAux :
    IsLimit ((forget₂ (ModuleCat R) AddCommGrpCat).mapCone (limitCone F)) :=
  letI : Small.{w} (Functor.sections ((F ⋙ forget₂ _ AddCommGrpCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))
  AddCommGrpCat.limitConeIsLimit
    (F ⋙ forget₂ (ModuleCat.{w} R) _ : J ⥤ AddCommGrpCat.{w})

/-- The forgetful functor from R-modules to abelian groups preserves all limits. -/
/-
**ModuleCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from R-modules to abelian groups preserves all limits.
-/
instance forget₂AddCommGroup_preservesLimit :
    PreservesLimit F (forget₂ (ModuleCat R) AddCommGrpCat) :=
  preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (forget₂AddCommGroup_preservesLimitsAux F)

/-- The forgetful functor from R-modules to abelian groups preserves all limits.
-/
/-
**ModuleCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from R-modules to abelian groups preserves all limits.
-/
instance forget₂AddCommGroup_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v}
      (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) where
  preservesLimitsOfShape := { preservesLimit := inferInstance }
/-
**ModuleCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂AddCommGroup_preservesLimits :
    PreservesLimits (forget₂ (ModuleCat R) AddCommGrpCat.{w}) :=
  ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{w, w}

/-- The forgetful functor from R-modules to types preserves all limits.
-/
/-
**ModuleCat.forget_preservesLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：forget_preservesLimitsOfSize [UnivLE.{v, w}] : PreservesLimitsOfSize.{t, v
} (forget (ModuleCat.{w} R)) where preservesLimitsOfShape
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
The forgetful functor from R-modules to types preserves all limits.
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget (ModuleCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦ preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
        (Types.Small.limitConeIsLimit.{v} (_ ⋙ forget _)) }
/-
**ModuleCat.forget_preservesLimits** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：forget_preservesLimits : PreservesLimits (forget (ModuleCat.{w} R))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget_preservesLimits : PreservesLimits (forget (ModuleCat.{w} R)) :=
  ModuleCat.forget_preservesLimitsOfSize.{w, w}

end

/-
**ModuleCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂AddCommGroup_reflectsLimit :
    ReflectsLimit F (forget₂ (ModuleCat.{w} R) AddCommGrpCat) where
  reflects {c} hc := ⟨by
    have : HasLimit (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat) := ⟨_, hc⟩
    have : Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R))) := by
      simpa only [AddCommGrpCat.hasLimit_iff_small_sections] using! this
    have := reflectsLimit_of_reflectsIsomorphisms F (forget₂ (ModuleCat R) AddCommGrpCat)
    exact isLimitOfReflects _ hc⟩
/-
**ModuleCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂AddCommGroup_reflectsLimitOfShape :
    ReflectsLimitsOfShape J (forget₂ (ModuleCat.{w} R) AddCommGrpCat) where
/-
**ModuleCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂AddCommGroup_reflectsLimitOfSize :
    ReflectsLimitsOfSize.{t, v} (forget₂ (ModuleCat.{w} R) AddCommGrpCat) where

section DirectLimit

open Module

variable {ι : Type v}
variable [DecidableEq ι] [Preorder ι]
variable (G : ι → Type v)
variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G fun i j h ↦ f i j h]

/-- The diagram (in the sense of `CategoryTheory`) of an unbundled `directLimit` of modules. -/
@[simps]
/-
**ModuleCat.directLimitDiagram** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：directLimitDiagram : ι ⥤ ModuleCat R where obj i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram (in the sense of `CategoryTheory`) of an unbundled `directLimit` of 
modules.
-/
def directLimitDiagram : ι ⥤ ModuleCat R where
  obj i := ModuleCat.of R (G i)
  map hij := ofHom (f _ _ hij.le)
  map_id i := by
    ext
    apply Module.DirectedSystem.map_self
  map_comp hij hjk := by
    ext
    symm
    apply Module.DirectedSystem.map_map f

/-- The `Cocone` on `directLimitDiagram` corresponding to
the unbundled `directLimit` of modules.

In `directLimitIsColimit` we show that it is a colimit cocone. -/
@[simps]
/-
**ModuleCat.directLimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：directLimitCocone : Cocone (directLimitDiagram G f) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Cocone` on `directLimitDiagram` corresponding to
the unbundled `directLimit` of modules.

In `directLimitIsColimit` we show that it is a colimit cocone.
-/
def directLimitCocone : Cocone (directLimitDiagram G f) where
  pt := ModuleCat.of R <| DirectLimit G f
  ι :=
    { app := fun x => ofHom (Module.DirectLimit.of R ι G f x)
      naturality := fun _ _ hij => by
        ext
        exact DirectLimit.of_f }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unbundled `directLimit` of modules is a colimit
in the sense of `CategoryTheory`. -/
@[simps]
/-
**ModuleCat.directLimitIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：directLimitIsColimit : IsColimit (directLimitCocone G f) where desc s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unbundled `directLimit` of modules is a colimit
in the sense of `CategoryTheory`.
-/
def directLimitIsColimit : IsColimit (directLimitCocone G f) where
  desc s := ofHom <|
    Module.DirectLimit.lift R ι G f (fun i => (s.ι.app i).hom) fun i j h x => by
      simp only [Functor.const_obj_obj]
      rw [← s.w (homOfLE h)]
      rfl
  fac s i := by
    ext
    dsimp only [hom_comp, directLimitCocone, hom_ofHom, LinearMap.comp_apply]
    apply DirectLimit.lift_of
  uniq s m h := by
    have :
      s.ι.app = fun i =>
        (ofHom (DirectLimit.of R ι (fun i => G i) (fun i j H => f i j H) i)) ≫ m := by
      funext i
      rw [← h]
      rfl
    ext
    simp [this]

end DirectLimit

end ModuleCat

