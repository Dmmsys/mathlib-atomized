/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Mario Carneiro, Andrew Yang
-/
module

public import Mathlib.Topology.Category.TopCat.Adjunctions
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The category of topological spaces has all limits and colimits

Further, these limits and colimits are preserved by the forgetful functor --- that is, the
underlying types are just the limits in the category of types.
-/

@[expose] public section


open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

universe v u u' w

noncomputable section

local notation "forget" => forget TopCat

namespace TopCat

section Limits

variable {J : Type v} [Category.{w} J]

attribute [local fun_prop] continuous_subtype_val
/-- A choice of limit cone for a functor `F : J ⥤ TopCat`.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `Types.limitCone`).
-/
/-
**TopCat.limitCone** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：limitCone (F : J ⥤ TopCat.{max v u}) : Cone F where pt
参数：F : J ⥤ TopCat.{max v u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of limit cone for a functor `F : J ⥤ TopCat`.
Generally you should just use `limit.cone F`, unless you need the actual definit
ion
(which is in terms of `Types.limitCone`).
-/
def limitCone (F : J ⥤ TopCat.{max v u}) : Cone F where
  pt := TopCat.of { u : ∀ j : J, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j }
  π :=
    { app := fun j => ofHom
        { toFun := fun u => u.val j
          -- Porting note: `continuity` from the original mathlib3 proof failed here.
          continuous_toFun := Continuous.comp (continuous_apply _) (continuous_subtype_val) }
      naturality := fun X Y f => by
        ext a
        exact (a.2 f).symm }

/-- The chosen cone `TopCat.limitCone F` for a functor `F : J ⥤ TopCat` is a limit cone.
Generally you should just use `limit.isLimit F`, unless you need the actual definition
(which is in terms of `Types.limitConeIsLimit`).
-/
/-
**TopCat.limitConeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：limitConeIsLimit (F : J ⥤ TopCat.{max v u}) : IsLimit (limitCone.{v, u} F)
 where lift S
参数：F : J ⥤ TopCat.{max v u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chosen cone `TopCat.limitCone F` for a functor `F : J ⥤ TopCat` is a limit c
one.
Generally you should just use `limit.isLimit F`, unless you need the actual defi
nition
(which is in terms of `Types.limitConeIsLimit`).
-/
def limitConeIsLimit (F : J ⥤ TopCat.{max v u}) : IsLimit (limitCone.{v, u} F) where
  lift S := ofHom
    { toFun := fun x =>
        ⟨fun _ => S.π.app _ x, fun f => by
          dsimp
          rw [← S.w f]
          rfl⟩
      continuous_toFun :=
        Continuous.subtype_mk (continuous_pi fun j => (S.π.app j).hom.2) fun x i j f => by
          dsimp
          rw [← S.w f]
          rfl }
  uniq S m h := by
    ext a
    simp [← h]
    rfl

section

variable {F : J ⥤ TopCat.{u}} (c : Cone (F ⋙ forget))

/-- Given a functor `F : J ⥤ TopCat` and a cone `c : Cone (F ⋙ forget)`
of the underlying functor to types, this is the type `c.pt`
with the infimum of the induced topologies by the maps `c.π.app j`. -/
/-
**TopCat.conePtOfConeForget** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：conePtOfConeForget : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : J ⥤ TopCat` and a cone `c : Cone (F ⋙ forget)`
of the underlying functor to types, this is the type `c.pt`
with the infimum of the induced topologies by the maps `c.π.app j`.
-/
def conePtOfConeForget : Type _ := c.pt
/-
**TopCat.topologicalSpaceConePtOfConeForget** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
形式化陈述：topologicalSpaceConePtOfConeForget : TopologicalSpace (conePtOfConeForget 
c)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance topologicalSpaceConePtOfConeForget :
    TopologicalSpace (conePtOfConeForget c) :=
  (⨅ j, (F.obj j).str.induced (c.π.app j))

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a functor `F : J ⥤ TopCat` and a cone `c : Cone (F ⋙ forget)`
of the underlying functor to types, this is a cone for `F` whose point is
`c.pt` with the infimum of the induced topologies by the maps `c.π.app j`. -/
@[simps pt π_app]
/-
**TopCat.coneOfConeForget** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：coneOfConeForget : Cone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : J ⥤ TopCat` and a cone `c : Cone (F ⋙ forget)`
of the underlying functor to types, this is a cone for `F` whose point is
`c.pt` with the infimum of the induced topologies by the maps `c.π.app j`.
-/
def coneOfConeForget : Cone F where
  pt := of (conePtOfConeForget c)
  π :=
    { app j := ofHom (ContinuousMap.mk (c.π.app j) (by
        rw [continuous_iff_le_induced]
        exact iInf_le _ _ ))
      naturality j j' φ := by
        ext
        apply ConcreteCategory.congr_hom (c.π.naturality φ) }

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a functor `F : J ⥤ TopCat` and a cone `c : Cone (F ⋙ forget)`
of the underlying functor to types, the limit of `F` is `c.pt` equipped
with the infimum of the induced topologies by the maps `c.π.app j`. -/
/-
**TopCat.isLimitConeOfForget** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：isLimitConeOfForget (c : Cone (F ⋙ forget)) (hc : IsLimit c) : IsLimit (co
neOfConeForget c)
参数：c : Cone (F ⋙ forget)；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : J ⥤ TopCat` and a cone `c : Cone (F ⋙ forget)`
of the underlying functor to types, the limit of `F` is `c.pt` equipped
with the infimum of the induced topologies by the maps `c.π.app j`.
-/
def isLimitConeOfForget (c : Cone (F ⋙ forget)) (hc : IsLimit c) :
    IsLimit (coneOfConeForget c) := by
  refine IsLimit.ofFaithful forget (ht := hc)
    (fun s ↦ ofHom (ContinuousMap.mk (hc.lift ((forget).mapCone s)) ?_)) (fun _ ↦ rfl)
  rw [continuous_iff_coinduced_le]
  dsimp [topologicalSpaceConePtOfConeForget]
  rw [le_iInf_iff]
  intro j
  rw [coinduced_le_iff_le_induced, induced_compose]
  convert! continuous_iff_le_induced.1 (s.π.app j).hom.continuous
  ext x
  exact ConcreteCategory.hom_ext_iff.mp (hc.fac ((forget).mapCone s) j) x

end

section IsLimit

variable {F : J ⥤ TopCat.{u}} (c : Cone F) (hc : IsLimit c)

include hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.induced_of_isLimit** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：induced_of_isLimit : c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `TopCat.instIsRightAdjointForgetContinuousMapCarrier`：(CategoryTheory.for
get TopCat).IsRightAdjoint
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.induced_eq`：induced_eq (h : X ≃ₜ Y) : TopologicalSpace.induce
d h ‹_› = ‹_›
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `induced_iInf`：induced_iInf {ι : Sort w} {t : ι -> TopologicalSpace α} : 
(⨅ i, t i).induced g = ⨅ i, (t i).induced g
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem induced_of_isLimit :
    c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j) := by
  let c' := coneOfConeForget ((forget).mapCone c)
  let hc' : IsLimit c' := isLimitConeOfForget _ (isLimitOfPreserves forget hc)
  let e := IsLimit.conePointUniqueUpToIso hc' hc
  have he (j : J) : e.inv ≫ c'.π.app j = c.π.app j :=
    IsLimit.conePointUniqueUpToIso_inv_comp hc' hc j
  apply (homeoOfIso e.symm).induced_eq.symm.trans
  dsimp [coneOfConeForget_pt, c', topologicalSpaceConePtOfConeForget]
  conv_rhs => simp only [← he]
  simp [← induced_compose, homeoOfIso, c']

end IsLimit

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.nonempty_isLimit_iff_eq_induced** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：nonempty_isLimit_iff_eq_induced {F : J ⥤ TopCat.{u}} (c : Cone F) (hc : Is
Limit ((forget).mapCone c)) : Nonempty (IsLimit c) ↔ c.pt.str = ⨅ j, (F.obj j).s
tr.induced (c.π.app j)
参数：c : Cone F；hc : IsLimit ((forget).mapCone c)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.induced_of_isLimit`：induced_of_isLimit : c.pt.str = ⨅ j, (F.obj j
).str.induced (c.π.app j)
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma nonempty_isLimit_iff_eq_induced {F : J ⥤ TopCat.{u}} (c : Cone F)
    (hc : IsLimit ((forget).mapCone c)) :
    Nonempty (IsLimit c) ↔ c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j) := by
  refine ⟨fun ⟨hc⟩ ↦ induced_of_isLimit _ hc, fun h ↦ ⟨?_⟩⟩
  refine .ofIsoLimit (isLimitConeOfForget _ hc) (Cone.ext ?_ ?_)
  · refine TopCat.isoOfHomeo
      { toEquiv := .refl _,
        continuous_toFun := h ▸ by fun_prop,
        continuous_invFun := h ▸ by fun_prop }
  · intro; rfl

variable (F : J ⥤ TopCat.{u})
/-
**TopCat.limit_topology** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：limit_topology [HasLimit F] : (limit F).str = ⨅ j, (F.obj j).str.induced (
limit.π F j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.induced_of_isLimit`：induced_of_isLimit : c.pt.str = ⨅ j, (F.obj j
).str.induced (c.π.app j)
-/
theorem limit_topology [HasLimit F] :
    (limit F).str = ⨅ j, (F.obj j).str.induced (limit.π F j) :=
  induced_of_isLimit _ (limit.isLimit _)

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.hasLimit_iff_small_sections** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：hasLimit_iff_small_sections : HasLimit F ↔ Small.{u} ((F ⋙ forget).section
s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Types.hasLimit_iff_small_sections`：hasLimit_iff_sm
all_sections (F : J ⥤ Type u) : HasLimit F ↔ Small.{u} F.sections
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `TopCat.instIsRightAdjointForgetContinuousMapCarrier`：(CategoryTheory.for
get TopCat).IsRightAdjoint
-/
lemma hasLimit_iff_small_sections :
    HasLimit F ↔ Small.{u} ((F ⋙ forget).sections) := by
  rw [← Types.hasLimit_iff_small_sections]
  constructor <;> intro
  · infer_instance
  · exact ⟨⟨_, isLimitConeOfForget _ (limit.isLimit _)⟩⟩
/-
**TopCat.topCat_hasLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
形式化陈述：topCat_hasLimitsOfShape (J : Type v) [Category* J] [Small.{u} J] : HasLimi
tsOfShape J TopCat.{u} where has_limit
参数：J : Type v。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TopCat.hasLimit_iff_small_sections`：hasLimit_iff_small_sections : HasLim
it F ↔ Small.{u} ((F ⋙ forget).sections)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance topCat_hasLimitsOfShape (J : Type v) [Category* J] [Small.{u} J] :
    HasLimitsOfShape J TopCat.{u} where
  has_limit := fun F => by
    rw [hasLimit_iff_small_sections]
    infer_instance
/-
**TopCat.topCat_hasLimitsOfSize** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：∀ [UnivLE.{v, u}], CategoryTheory.Limits.HasLimitsOfSize.{w, v, u, u + 1} 
TopCat
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance topCat_hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} TopCat.{u} where
/-
**TopCat.topCat_hasLimits** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
形式化陈述：topCat_hasLimits : HasLimits TopCat.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.topCat_hasLimitsOfSize`：∀ [UnivLE.{v, u}], CategoryTheory.Limits.
HasLimitsOfSize.{w, v, u, u + 1} TopCat
-/
instance topCat_hasLimits : HasLimits TopCat.{u} :=
  TopCat.topCat_hasLimitsOfSize.{u, u}
/-
**TopCat.forget_preservesLimitsOfSize** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：CategoryTheory.Limits.PreservesLimitsOfSize.{w, v, u, u, u + 1, u + 1} (Ca
tegoryTheory.forget TopCat)
参数：CategoryTheory.forget TopCat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `TopCat.instIsRightAdjointForgetContinuousMapCarrier`：(CategoryTheory.for
get TopCat).IsRightAdjoint
-/
instance forget_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (forget : TopCat.{u} ⥤ _) where
/-
**TopCat.forget_preservesLimits** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget TopCat)
参数：CategoryTheory.forget TopCat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `TopCat.instIsRightAdjointForgetContinuousMapCarrier`：(CategoryTheory.for
get TopCat).IsRightAdjoint
-/
instance forget_preservesLimits : PreservesLimits (forget : TopCat.{u} ⥤ _) where

end Limits

section Colimits

variable {J : Type v} [Category.{w} J] {F : J ⥤ TopCat.{u}}

section

variable (c : Cocone (F ⋙ forget))

/-- Given a functor `F : J ⥤ TopCat` and a cocone `c : Cocone (F ⋙ forget)`
of the underlying cocone of types, this is the type `c.pt`
with the supremum of the topologies that are coinduced by the maps `c.ι.app j`. -/
/-
**TopCat.coconePtOfCoconeForget** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：coconePtOfCoconeForget : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : J ⥤ TopCat` and a cocone `c : Cocone (F ⋙ forget)`
of the underlying cocone of types, this is the type `c.pt`
with the supremum of the topologies that are coinduced by the maps `c.ι.app j`.
-/
def coconePtOfCoconeForget : Type _ := c.pt
/-
**TopCat.topologicalSpaceCoconePtOfCoconeForget** 是 Mathlib 中的一个实例，位于命名空间 `TopCa
t`。
形式化陈述：topologicalSpaceCoconePtOfCoconeForget : TopologicalSpace (coconePtOfCocon
eForget c)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance topologicalSpaceCoconePtOfCoconeForget :
    TopologicalSpace (coconePtOfCoconeForget c) :=
  (⨆ j, (F.obj j).str.coinduced (c.ι.app j))

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a functor `F : J ⥤ TopCat` and a cocone `c : Cocone (F ⋙ forget)`
of the underlying cocone of types, this is a cocone for `F` whose point is
`c.pt` with the supremum of the coinduced topologies by the maps `c.ι.app j`. -/
@[simps pt ι_app]
/-
**TopCat.coconeOfCoconeForget** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：coconeOfCoconeForget : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : J ⥤ TopCat` and a cocone `c : Cocone (F ⋙ forget)`
of the underlying cocone of types, this is a cocone for `F` whose point is
`c.pt` with the supremum of the coinduced topologies by the maps `c.ι.app j`.
-/
def coconeOfCoconeForget : Cocone F where
  pt := of (coconePtOfCoconeForget c)
  ι :=
    { app j := ofHom (ContinuousMap.mk (c.ι.app j) (by
        rw [continuous_iff_coinduced_le]
        dsimp [topologicalSpaceCoconePtOfCoconeForget]
        exact le_iSup (fun j ↦ (F.obj j).str.coinduced _) j))
      naturality j j' φ := by
        ext
        apply ConcreteCategory.congr_hom (c.ι.naturality φ) }

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a functor `F : J ⥤ TopCat` and a cocone `c : Cocone (F ⋙ forget)`
of the underlying cocone of types, the colimit of `F` is `c.pt` equipped
with the supremum of the coinduced topologies by the maps `c.ι.app j`. -/
/-
**TopCat.isColimitCoconeOfForget** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：isColimitCoconeOfForget (c : Cocone (F ⋙ forget)) (hc : IsColimit c) : IsC
olimit (coconeOfCoconeForget c)
参数：c : Cocone (F ⋙ forget)；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : J ⥤ TopCat` and a cocone `c : Cocone (F ⋙ forget)`
of the underlying cocone of types, the colimit of `F` is `c.pt` equipped
with the supremum of the coinduced topologies by the maps `c.ι.app j`.
-/
def isColimitCoconeOfForget (c : Cocone (F ⋙ forget)) (hc : IsColimit c) :
    IsColimit (coconeOfCoconeForget c) := by
  refine IsColimit.ofFaithful forget (ht := hc)
    (fun s ↦ ofHom (ContinuousMap.mk (hc.desc ((forget).mapCocone s)) ?_)) (fun _ ↦ rfl)
  rw [continuous_iff_le_induced]
  dsimp [topologicalSpaceCoconePtOfCoconeForget]
  rw [iSup_le_iff]
  intro j
  rw [coinduced_le_iff_le_induced, induced_compose]
  convert! continuous_iff_le_induced.1 (s.ι.app j).hom.continuous
  ext x
  exact ConcreteCategory.hom_ext_iff.mp (hc.fac ((forget).mapCocone s) j) x

end

section IsColimit

variable (c : Cocone F) (hc : IsColimit c)

include hc

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**TopCat.coinduced_of_isColimit** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：coinduced_of_isColimit : c.pt.str = ⨆ j, (F.obj j).str.coinduced (c.ι.app 
j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `TopCat.instIsLeftAdjointForgetContinuousMapCarrier`：(CategoryTheory.forg
et TopCat).IsLeftAdjoint
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.coinduced_eq`：coinduced_eq (h : X ≃ₜ Y) : TopologicalSpace.co
induced h ‹_› = ‹_›
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coinduced_iSup`：coinduced_iSup {ι : Sort w} {t : ι -> TopologicalSpace α
} : (⨆ i, t i).coinduced f = ⨆ i, (t i).coinduced f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem coinduced_of_isColimit :
    c.pt.str = ⨆ j, (F.obj j).str.coinduced (c.ι.app j) := by
  let c' := coconeOfCoconeForget ((forget).mapCocone c)
  let hc' : IsColimit c' := isColimitCoconeOfForget _ (isColimitOfPreserves forget hc)
  let e := IsColimit.coconePointUniqueUpToIso hc' hc
  have he (j : J) : c'.ι.app j ≫ e.hom = c.ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hc' hc j
  apply (homeoOfIso e).coinduced_eq.symm.trans
  dsimp [coconeOfCoconeForget_pt, c', topologicalSpaceCoconePtOfCoconeForget]
  simp only [coinduced_iSup]
  conv_rhs => simp only [← he]
  rfl
/-
**TopCat.isOpen_iff_of_isColimit** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：isOpen_iff_of_isColimit (X : Set c.pt) : IsOpen X ↔ forall (j : J), IsOpen
 (c.ι.app j ⁻¹' X)
参数：X : Set c.pt。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopCat.coinduced_of_isColimit`：coinduced_of_isColimit : c.pt.str = ⨆ j, 
(F.obj j).str.coinduced (c.ι.app j)
· 使用定理 `isOpen_fold`：isOpen_fold {t : TopologicalSpace X} : t.IsOpen s = IsOpen[
t] s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `isOpen_iSup_iff`：isOpen_iSup_iff {s : Set α} : IsOpen[⨆ i, t i] s ↔ fora
ll i, IsOpen[t i] s
-/
lemma isOpen_iff_of_isColimit (X : Set c.pt) :
    IsOpen X ↔ ∀ (j : J), IsOpen (c.ι.app j ⁻¹' X) := by
  trans (⨆ (j : J), (F.obj j).str.coinduced (c.ι.app j)).IsOpen X
  · rw [← coinduced_of_isColimit c hc, isOpen_fold]
  · simp only [← isOpen_coinduced]
    apply isOpen_iSup_iff

set_option backward.defeqAttrib.useBackward true in
/-
**TopCat.isClosed_iff_of_isColimit** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：isClosed_iff_of_isColimit (X : Set c.pt) : IsClosed X ↔ forall (j : J), Is
Closed (c.ι.app j ⁻¹' X)
参数：X : Set c.pt。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TopCat.isOpen_iff_of_isColimit`：isOpen_iff_of_isColimit (X : Set c.pt) :
 IsOpen X ↔ forall (j : J), IsOpen (c.ι.app j ⁻¹' X)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isClosed_iff_of_isColimit (X : Set c.pt) :
    IsClosed X ↔ ∀ (j : J), IsClosed (c.ι.app j ⁻¹' X) := by
  simp only [← isOpen_compl_iff, isOpen_iff_of_isColimit _ hc,
    Functor.const_obj_obj, Set.preimage_compl]
/-
**TopCat.continuous_iff_of_isColimit** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：continuous_iff_of_isColimit {X : Type u'} [TopologicalSpace X] (f : c.pt -
> X) : Continuous f ↔ forall (j : J), Continuous (f ∘ c.ι.app j)
参数：f : c.pt -> X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `TopCat.isOpen_iff_of_isColimit`：isOpen_iff_of_isColimit (X : Set c.pt) :
 IsOpen X ↔ forall (j : J), IsOpen (c.ι.app j ⁻¹' X)
-/
lemma continuous_iff_of_isColimit {X : Type u'} [TopologicalSpace X] (f : c.pt → X) :
    Continuous f ↔ ∀ (j : J), Continuous (f ∘ c.ι.app j) := by
  simp only [continuous_def, isOpen_iff_of_isColimit _ hc]
  tauto

end IsColimit

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.nonempty_isColimit_iff_eq_coinduced** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：nonempty_isColimit_iff_eq_coinduced (c : Cocone F) (hc : IsColimit ((forge
t).mapCocone c)) : Nonempty (IsColimit c) ↔ c.pt.str = ⨆ j, (F.obj j).str.coindu
ced (c.ι.app j)
参数：c : Cocone F；hc : IsColimit ((forget).mapCocone c)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.coinduced_of_isColimit`：coinduced_of_isColimit : c.pt.str = ⨆ j, 
(F.obj j).str.coinduced (c.ι.app j)
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma nonempty_isColimit_iff_eq_coinduced (c : Cocone F) (hc : IsColimit ((forget).mapCocone c)) :
    Nonempty (IsColimit c) ↔ c.pt.str = ⨆ j, (F.obj j).str.coinduced (c.ι.app j) := by
  refine ⟨fun ⟨hc⟩ ↦ coinduced_of_isColimit _ hc, fun h ↦ ⟨?_⟩⟩
  refine .ofIsoColimit (isColimitCoconeOfForget _ hc) (Cocone.ext ?_ ?_)
  · refine TopCat.isoOfHomeo
      { toEquiv := .refl _,
        continuous_toFun := h ▸ by fun_prop,
        continuous_invFun := h ▸ by fun_prop }
  · intro; rfl

variable (F)
/-
**TopCat.colimit_topology** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：colimit_topology (F : J ⥤ TopCat.{u}) [HasColimit F] : (colimit F).str = ⨆
 j, (F.obj j).str.coinduced (colimit.ι F j)
参数：F : J ⥤ TopCat.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.coinduced_of_isColimit`：coinduced_of_isColimit : c.pt.str = ⨆ j, 
(F.obj j).str.coinduced (c.ι.app j)
-/
theorem colimit_topology (F : J ⥤ TopCat.{u}) [HasColimit F] :
    (colimit F).str = ⨆ j, (F.obj j).str.coinduced (colimit.ι F j) :=
  coinduced_of_isColimit _ (colimit.isColimit _)
/-
**TopCat.colimit_isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：colimit_isOpen_iff (F : J ⥤ TopCat.{u}) [HasColimit F] (U : Set ((colimit 
F : _) : Type u)) : IsOpen U ↔ forall j, IsOpen (colimit.ι F j ⁻¹' U)
参数：F : J ⥤ TopCat.{u}；U : Set ((colimit F : _) : Type u)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.isOpen_iff_of_isColimit`：isOpen_iff_of_isColimit (X : Set c.pt) :
 IsOpen X ↔ forall (j : J), IsOpen (c.ι.app j ⁻¹' X)
-/
theorem colimit_isOpen_iff (F : J ⥤ TopCat.{u}) [HasColimit F]
    (U : Set ((colimit F : _) : Type u)) :
    IsOpen U ↔ ∀ j, IsOpen (colimit.ι F j ⁻¹' U) := by
  apply isOpen_iff_of_isColimit _ (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.hasColimit_iff_small_colimitType** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：hasColimit_iff_small_colimitType : HasColimit F ↔ Small.{u} (F ⋙ forget).C
olimitType
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Types.hasColimit_iff_small_colimitType`：hasColimit
_iff_small_colimitType (F : J ⥤ Type u) : HasColimit F ↔ Small.{u} F.ColimitType
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `TopCat.instIsLeftAdjointForgetContinuousMapCarrier`：(CategoryTheory.forg
et TopCat).IsLeftAdjoint
-/
lemma hasColimit_iff_small_colimitType :
    HasColimit F ↔ Small.{u} (F ⋙ forget).ColimitType := by
  rw [← Types.hasColimit_iff_small_colimitType]
  constructor <;> intro
  · infer_instance
  · exact ⟨⟨_, isColimitCoconeOfForget _ (colimit.isColimit _)⟩⟩
/-
**TopCat.topCat_hasColimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
形式化陈述：topCat_hasColimitsOfShape (J : Type v) [Category* J] [Small.{u} J] : HasCo
limitsOfShape J TopCat.{u} where has_colimit
参数：J : Type v。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TopCat.hasColimit_iff_small_colimitType`：hasColimit_iff_small_colimitTyp
e : HasColimit F ↔ Small.{u} (F ⋙ forget).ColimitType
· 使用定理 `CategoryTheory.Functor.instSmallColimitType`：∀ {J : Type v} [inst : Cate
goryTheory.Category.{w, v} J] [Small.{u, v} J] (F : CategoryTheory.Functor J (Ty
pe u)),   Small.{u, max u v} F.Co…
-/
instance topCat_hasColimitsOfShape (J : Type v) [Category* J] [Small.{u} J] :
    HasColimitsOfShape J TopCat.{u} where
  has_colimit := fun F => by
    rw [hasColimit_iff_small_colimitType]
    infer_instance
/-
**TopCat.topCat_hasColimitsOfSize** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：∀ [UnivLE.{v, u}], CategoryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1
} TopCat
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance topCat_hasColimitsOfSize [UnivLE.{v, u}] : HasColimitsOfSize.{w, v} TopCat.{u} where
/-
**TopCat.topCat_hasColimits** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
形式化陈述：topCat_hasColimits : HasColimits TopCat.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.topCat_hasColimitsOfSize`：∀ [UnivLE.{v, u}], CategoryTheory.Limit
s.HasColimitsOfSize.{w, v, u, u + 1} TopCat
-/
instance topCat_hasColimits : HasColimits TopCat.{u} :=
  TopCat.topCat_hasColimitsOfSize.{u, u}
/-
**TopCat.forget_preservesColimitsOfSize** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：CategoryTheory.Limits.PreservesColimitsOfSize.{w, v, u, u, u + 1, u + 1} (
CategoryTheory.forget TopCat)
参数：CategoryTheory.forget TopCat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `TopCat.instIsLeftAdjointForgetContinuousMapCarrier`：(CategoryTheory.forg
et TopCat).IsLeftAdjoint
-/
instance forget_preservesColimitsOfSize :
    PreservesColimitsOfSize.{w, v} (forget : TopCat.{u} ⥤ _) where
/-
**TopCat.forget_preservesColimits** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：CategoryTheory.Limits.PreservesColimits (CategoryTheory.forget TopCat)
参数：CategoryTheory.forget TopCat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `TopCat.instIsLeftAdjointForgetContinuousMapCarrier`：(CategoryTheory.forg
et TopCat).IsLeftAdjoint
-/
instance forget_preservesColimits : PreservesColimits (forget : TopCat.{u} ⥤ Type u) where

end Colimits

/-- The terminal object of `Top` is `PUnit`. -/
/-
**TopCat.isTerminalPUnit** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：isTerminalPUnit : IsTerminal (TopCat.of PUnit.{u + 1})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The terminal object of `Top` is `PUnit`.
-/
def isTerminalPUnit : IsTerminal (TopCat.of PUnit.{u + 1}) :=
  haveI : ∀ X, Unique (X ⟶ TopCat.of PUnit.{u + 1}) := fun X =>
    ⟨⟨ofHom ⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun f => by ext⟩
  Limits.IsTerminal.ofUnique _

/-- The terminal object of `Top` is `PUnit`. -/
/-
**TopCat.terminalIsoPUnit** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：terminalIsoPUnit : ⊤_ TopCat.{u} ≅ TopCat.of PUnit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The terminal object of `Top` is `PUnit`.
-/
def terminalIsoPUnit : ⊤_ TopCat.{u} ≅ TopCat.of PUnit :=
  terminalIsTerminal.uniqueUpToIso isTerminalPUnit

/-- The initial object of `Top` is `PEmpty`. -/
/-
**TopCat.isInitialPEmpty** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：isInitialPEmpty : IsInitial (TopCat.of PEmpty.{u + 1})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial object of `Top` is `PEmpty`.
-/
def isInitialPEmpty : IsInitial (TopCat.of PEmpty.{u + 1}) :=
  haveI : ∀ X, Unique (TopCat.of PEmpty.{u + 1} ⟶ X) := fun X =>
    ⟨⟨ofHom ⟨fun x => x.elim, by fun_prop⟩⟩, fun f => by ext ⟨⟩⟩
  Limits.IsInitial.ofUnique _

/-- The initial object of `Top` is `PEmpty`. -/
/-
**TopCat.initialIsoPEmpty** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：initialIsoPEmpty : ⊥_ TopCat.{u} ≅ TopCat.of PEmpty
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial object of `Top` is `PEmpty`.
-/
def initialIsoPEmpty : ⊥_ TopCat.{u} ≅ TopCat.of PEmpty :=
  initialIsInitial.uniqueUpToIso isInitialPEmpty

/-- The unique map ∅ ⟶ X is inducing. -/
/-
**TopCat.IsInducing.empty** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.IsInducing`。
形式化陈述：∀ (X : TopCat), Topology.IsInducing ⇑(CategoryTheory.ConcreteCategory.hom 
(TopCat.isInitialPEmpty.to X))
参数：X : TopCat；CategoryTheory.ConcreteCategory.hom (TopCat.isInitialPEmpty.to X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext`：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen 
= IsOpen → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instDiscreteTopologyPEmpty`：DiscreteTopology PEmpty.{u_1 + 1}
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用定理 `instSubsingletonPEmpty`：Subsingleton PEmpty.{u_1}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The unique map ∅ ⟶ X is inducing.
-/
lemma IsInducing.empty (X : TopCat) : Topology.IsInducing (TopCat.isInitialPEmpty.to X) where
  eq_induced := by ext; simp

end TopCat

