/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.HomEquiv
public import Mathlib.Logic.Small.Defs

/-!
# Shrinking morphisms in localized categories

Given a class of morphisms `W : MorphismProperty C`, and two objects `X` and `Y`,
we introduce a type-class `HasSmallLocalizedHom.{w} W X Y` which expresses
that in the localized category with respect to `W`, the type of morphisms from `X`
to `Y` is `w`-small for a certain universe `w`. Under this assumption,
we define `SmallHom.{w} W X Y : Type w` as the shrunk type. For any localization
functor `L : C ⥤ D` for `W`, we provide a bijection
`SmallHom.equiv.{w} W L : SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y)` that is compatible
with the composition of morphisms.

-/

@[expose] public section

universe w'' w w' v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Category

namespace Localization

variable {C : Type u₁} [Category.{v₁} C] (W : MorphismProperty C)
  {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D']

section

variable (L : C ⥤ D) [L.IsLocalization W] (X Y Z : C)

/-- This property holds if the type of morphisms between `X` and `Y`
in the localized category with respect to `W : MorphismProperty C`
is small. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the universe `w` would default to a
-- universe output parameter. See Note [universe output parameters and typeclass caching].
@[univ_out_params]
/-
**CategoryTheory.Localization.HasSmallLocalizedHom** 是 Mathlib 中的一个归纳类型，位于命名空间 `
CategoryTheory.Localization`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.MorphismProperty C → C → C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class HasSmallLocalizedHom : Prop where
  small : Small.{w} (W.Q.obj X ⟶ W.Q.obj Y)

attribute [instance] HasSmallLocalizedHom.small

variable {X Y Z}
/-
**CategoryTheory.Localization.hasSmallLocalizedHom_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Localization`。
形式化陈述：hasSmallLocalizedHom_iff : HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.o
bj X ⟶ L.obj Y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_map`：small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃
 β) : Small.{w} α
· 使用定理 `CategoryTheory.Localization.HasSmallLocalizedHom.small`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {W : CategoryTheory.MorphismProperty
 C} {X Y : C}   [self : CategoryTheory.Local…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma hasSmallLocalizedHom_iff :
    HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y) := by
  constructor
  · intro h
    exact small_map (homEquiv W W.Q L).symm
  · intro h
    exact ⟨small_map (homEquiv W W.Q L)⟩

include L in
/-
**CategoryTheory.Localization.hasSmallLocalizedHom_of_isLocalization** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Localization`。
形式化陈述：hasSmallLocalizedHom_of_isLocalization : HasSmallLocalizedHom.{v₂} W X Y
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.hasSmallLocalizedHom_iff`：hasSmallLocalizedH
om_iff : HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y)
-/
lemma hasSmallLocalizedHom_of_isLocalization :
    HasSmallLocalizedHom.{v₂} W X Y := by
  rw [hasSmallLocalizedHom_iff W L]
  infer_instance

variable (X Y) in
/-
**CategoryTheory.Localization.small_of_hasSmallLocalizedHom** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Localization`。
形式化陈述：small_of_hasSmallLocalizedHom [HasSmallLocalizedHom.{w} W X Y] : Small.{w}
 (L.obj X ⟶ L.obj Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Localization.hasSmallLocalizedHom_iff`：hasSmallLocalizedH
om_iff : HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y)
-/
lemma small_of_hasSmallLocalizedHom [HasSmallLocalizedHom.{w} W X Y] :
    Small.{w} (L.obj X ⟶ L.obj Y) := by
  rwa [← hasSmallLocalizedHom_iff W]
/-
**CategoryTheory.Localization.hasSmallLocalizedHom_iff_of_isos** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Localization`。
形式化陈述：hasSmallLocalizedHom_iff_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') : 
HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X' Y'
参数：e : X ≅ X'；e' : Y ≅ Y'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.hasSmallLocalizedHom_iff`：hasSmallLocalizedH
om_iff : HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y)
· 使用定理 `small_congr`：small_congr {α : Type*} {β : Type*} (e : α ≃ β) : Small.{w}
 α ↔ Small.{w} β
-/
lemma hasSmallLocalizedHom_iff_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') :
    HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X' Y' := by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (W.Q.mapIso e) (W.Q.mapIso e'))
/-
**CategoryTheory.Localization.hasSmallLocalizedHom_of_isos** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Localization`。
形式化陈述：hasSmallLocalizedHom_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') [HasSm
allLocalizedHom.{w} W X Y] : HasSmallLocalizedHom.{w} W X' Y'
参数：e : X ≅ X'；e' : Y ≅ Y'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Localization.hasSmallLocalizedHom_iff_of_isos`：hasSmallLo
calizedHom_iff_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') : HasSmallLocalize
dHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X' Y'
-/
lemma hasSmallLocalizedHom_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y')
    [HasSmallLocalizedHom.{w} W X Y] :
    HasSmallLocalizedHom.{w} W X' Y' := by
  rwa [← hasSmallLocalizedHom_iff_of_isos _ e e']

variable (X) in
/-
**CategoryTheory.Localization.hasSmallLocalizedHom_iff_target** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Localization`。
形式化陈述：hasSmallLocalizedHom_iff_target {Y Y' : C} (f : Y ⟶ Y') (hf : W f) : HasSm
allLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X Y'
参数：f : Y ⟶ Y'；hf : W f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.hasSmallLocalizedHom_iff`：hasSmallLocalizedH
om_iff : HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y)
· 使用定理 `small_congr`：small_congr {α : Type*} {β : Type*} (e : α ≃ β) : Small.{w}
 α ↔ Small.{w} β
-/
lemma hasSmallLocalizedHom_iff_target {Y Y' : C} (f : Y ⟶ Y') (hf : W f) :
    HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X Y' := by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (Iso.refl _) (Localization.isoOfHom W.Q W f hf))
/-
**CategoryTheory.Localization.hasSmallLocalizedHom_iff_source** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Localization`。
形式化陈述：hasSmallLocalizedHom_iff_source {X' : C} (f : X ⟶ X') (hf : W f) (Y : C) :
 HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X' Y
参数：f : X ⟶ X'；hf : W f；Y : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.hasSmallLocalizedHom_iff`：hasSmallLocalizedH
om_iff : HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y)
· 使用定理 `small_congr`：small_congr {α : Type*} {β : Type*} (e : α ≃ β) : Small.{w}
 α ↔ Small.{w} β
-/
lemma hasSmallLocalizedHom_iff_source {X' : C} (f : X ⟶ X') (hf : W f) (Y : C) :
    HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X' Y := by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (Localization.isoOfHom W.Q W f hf) (Iso.refl _))

end

/-- The type of morphisms from `X` to `Y` in the localized category
with respect to `W : MorphismProperty C` that is shrunk to `Type w`
when `HasSmallLocalizedHom.{w} W X Y` holds. -/
/-
**CategoryTheory.Localization.SmallHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Localization`。
形式化陈述：SmallHom (X Y : C) [HasSmallLocalizedHom.{w} W X Y] : Type w
参数：X Y : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.HasSmallLocalizedHom.small`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {W : CategoryTheory.MorphismProperty
 C} {X Y : C}   [self : CategoryTheory.Local…

--- 原说明 ---
The type of morphisms from `X` to `Y` in the localized category
with respect to `W : MorphismProperty C` that is shrunk to `Type w`
when `HasSmallLocalizedHom.{w} W X Y` holds.
-/
def SmallHom (X Y : C) [HasSmallLocalizedHom.{w} W X Y] : Type w :=
  Shrink.{w} (W.Q.obj X ⟶ W.Q.obj Y)

namespace SmallHom

/-- The canonical bijection `SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y)`
when `L` is a localization functor for `W : MorphismProperty C` and
that `HasSmallLocalizedHom.{w} W X Y` holds. -/
/-
**CategoryTheory.Localization.SmallHom.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Localization.SmallHom`。
形式化陈述：equiv (L : C ⥤ D) [L.IsLocalization W] {X Y : C} [HasSmallLocalizedHom.{w}
 W X Y] : SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y)
参数：L : C ⥤ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Localization.HasSmallLocalizedHom.small`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {W : CategoryTheory.MorphismProperty
 C} {X Y : C}   [self : CategoryTheory.Local…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The canonical bijection `SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y)`
when `L` is a localization functor for `W : MorphismProperty C` and
that `HasSmallLocalizedHom.{w} W X Y` holds.
-/
noncomputable def equiv (L : C ⥤ D) [L.IsLocalization W] {X Y : C}
    [HasSmallLocalizedHom.{w} W X Y] :
    SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y) :=
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  (equivShrink _).symm.trans (homEquiv W W.Q L)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.SmallHom.equiv_equiv_symm** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Localization.SmallHom`。
形式化陈述：equiv_equiv_symm (L : C ⥤ D) [L.IsLocalization W] (L' : C ⥤ D') [L'.IsLoca
lization W] (G : D ⥤ D') (e : L ⋙ G ≅ L') {X Y : C} [HasSmallLocalizedHom.{w} W 
X Y] (f : L.obj X ⟶ L.obj Y) : equiv W L' ((equiv W L).symm f) = e.inv.app X ≫ G
.map f ≫ e.hom.app Y
参数：L : C ⥤ D；L' : C ⥤ D'；G : D ⥤ D'；e : L ⋙ G ≅ L'；f : L.obj X ⟶ L.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Localization.HasSmallLocalizedHom.small`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {W : CategoryTheory.MorphismProperty
 C} {X Y : C}   [self : CategoryTheory.Local…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `CategoryTheory.Localization.homEquiv_trans`：homEquiv_trans (f : L₁.obj X
 ⟶ L₁.obj Y) : homEquiv W L₂ L₃ (homEquiv W L₁ L₂ f) = homEquiv W L₁ L₃ f
· 使用引理 `CategoryTheory.Localization.homEquiv_eq`：homEquiv_eq (G : D₁ ⥤ D₂) (e : 
L₁ ⋙ G ≅ L₂) (f : L₁.obj X ⟶ L₁.obj Y) : homEquiv W L₁ L₂ f = e.inv.app X ≫ G.ma
p f ≫ e.hom.app Y
-/
lemma equiv_equiv_symm (L : C ⥤ D) [L.IsLocalization W]
    (L' : C ⥤ D') [L'.IsLocalization W] (G : D ⥤ D')
    (e : L ⋙ G ≅ L') {X Y : C} [HasSmallLocalizedHom.{w} W X Y]
    (f : L.obj X ⟶ L.obj Y) :
    equiv W L' ((equiv W L).symm f) =
      e.inv.app X ≫ G.map f ≫ e.hom.app Y := by
  dsimp [equiv]
  rw [Equiv.symm_apply_apply, homEquiv_trans]
  apply homEquiv_eq

/-- The element in `SmallHom W X Y` induced by `f : X ⟶ Y`. -/
/-
**CategoryTheory.Localization.SmallHom.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Localization.SmallHom`。
形式化陈述：mk {X Y : C} [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) : SmallHom.{w} W
 X Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The element in `SmallHom W X Y` induced by `f : X ⟶ Y`.
-/
noncomputable def mk {X Y : C} [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) :
    SmallHom.{w} W X Y :=
  (equiv.{w} W W.Q).symm (W.Q.map f)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Localization.SmallHom.equiv_mk** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Localization.SmallHom`。
形式化陈述：equiv_mk (L : C ⥤ D) [L.IsLocalization W] {X Y : C} [HasSmallLocalizedHom.
{w} W X Y] (f : X ⟶ Y) : equiv.{w} W L (mk W f) = L.map f
参数：L : C ⥤ D；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Localization.HasSmallLocalizedHom.small`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {W : CategoryTheory.MorphismProperty
 C} {X Y : C}   [self : CategoryTheory.Local…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.Localization.homEquiv_refl`：homEquiv_refl (f : L₁.obj X ⟶
 L₁.obj Y) : homEquiv W L₁ L₁ f = f
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `CategoryTheory.Localization.homEquiv_map`：homEquiv_map (f : X ⟶ Y) : hom
Equiv W L₁ L₂ (L₁.map f) = L₂.map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv_mk (L : C ⥤ D) [L.IsLocalization W] {X Y : C}
    [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) :
    equiv.{w} W L (mk W f) = L.map f := by
  simp [equiv, mk]

variable {W}

/-- The formal inverse in `SmallHom W X Y` of a morphism `f : Y ⟶ X` such that `W f`. -/
/-
**CategoryTheory.Localization.SmallHom.mkInv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Localization.SmallHom`。
形式化陈述：mkInv {X Y : C} (f : Y ⟶ X) (hf : W f) [HasSmallLocalizedHom.{w} W X Y] : 
SmallHom.{w} W X Y
参数：f : Y ⟶ X；hf : W f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The formal inverse in `SmallHom W X Y` of a morphism `f : Y ⟶ X` such that `W f`
.
-/
noncomputable def mkInv {X Y : C} (f : Y ⟶ X) (hf : W f) [HasSmallLocalizedHom.{w} W X Y] :
    SmallHom.{w} W X Y :=
  (equiv.{w} W W.Q).symm (Localization.isoOfHom W.Q W f hf).inv

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Localization.SmallHom.equiv_mkInv** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Localization.SmallHom`。
形式化陈述：equiv_mkInv (L : C ⥤ D) [L.IsLocalization W] {X Y : C} (f : Y ⟶ X) (hf : W
 f) [HasSmallLocalizedHom.{w} W X Y] : equiv.{w} W L (mkInv f hf) = (Localizatio
n.isoOfHom L W f hf).inv
参数：L : C ⥤ D；f : Y ⟶ X；hf : W f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Localization.HasSmallLocalizedHom.small`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {W : CategoryTheory.MorphismProperty
 C} {X Y : C}   [self : CategoryTheory.Local…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.Localization.homEquiv_isoOfHom_inv`：homEquiv_isoOfHom_inv
 (f : Y ⟶ X) (hf : W f) : homEquiv W L₁ L₂ (isoOfHom L₁ W f hf).inv = (isoOfHom 
L₂ W f hf).inv
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv_mkInv (L : C ⥤ D) [L.IsLocalization W] {X Y : C} (f : Y ⟶ X) (hf : W f)
    [HasSmallLocalizedHom.{w} W X Y] :
    equiv.{w} W L (mkInv f hf) = (Localization.isoOfHom L W f hf).inv := by
  simp only [equiv, mkInv, Equiv.symm_trans_apply, Equiv.symm_symm, homEquiv_symm_apply,
    Equiv.trans_apply, Equiv.symm_apply_apply, homEquiv_isoOfHom_inv]

/-- The composition on `SmallHom W`. -/
/-
**CategoryTheory.Localization.SmallHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Localization.SmallHom`。
形式化陈述：comp {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w
} W Y Z] [HasSmallLocalizedHom.{w} W X Z] (α : SmallHom.{w} W X Y) (β : SmallHom
.{w} W Y Z) : SmallHom.{w} W X Z
参数：α : SmallHom.{w} W X Y；β : SmallHom.{w} W Y Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The composition on `SmallHom W`.
-/
noncomputable def comp {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y]
    [HasSmallLocalizedHom.{w} W Y Z] [HasSmallLocalizedHom.{w} W X Z]
    (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z) :
    SmallHom.{w} W X Z :=
  (equiv W W.Q).symm (equiv W W.Q α ≫ equiv W W.Q β)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.SmallHom.equiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Localization.SmallHom`。
形式化陈述：equiv_comp (L : C ⥤ D) [L.IsLocalization W] {X Y Z : C} [HasSmallLocalized
Hom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y Z] [HasSmallLocalizedHom.{w} W X Z]
 (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z) : equiv W L (α.comp β) = equi
v W L α ≫ equiv W L β
参数：L : C ⥤ D；α : SmallHom.{w} W X Y；β : SmallHom.{w} W Y Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.small_of_hasSmallLocalizedHom`：small_of_hasS
mallLocalizedHom [HasSmallLocalizedHom.{w} W X Y] : Small.{w} (L.obj X ⟶ L.obj Y
)
· 使用定理 `CategoryTheory.Localization.HasSmallLocalizedHom.small`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {W : CategoryTheory.MorphismProperty
 C} {X Y : C}   [self : CategoryTheory.Local…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Localization.homEquiv_refl`：homEquiv_refl (f : L₁.obj X ⟶
 L₁.obj Y) : homEquiv W L₁ L₁ f = f
· 使用引理 `CategoryTheory.Localization.homEquiv_comp`：homEquiv_comp (f : L₁.obj X ⟶
 L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z) : homEquiv W L₁ L₂ (f ≫ g) = homEquiv W L₁ 
L₂ f ≫ homEquiv W L₁ L₂ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv_comp (L : C ⥤ D) [L.IsLocalization W] {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y]
    [HasSmallLocalizedHom.{w} W Y Z] [HasSmallLocalizedHom.{w} W X Z]
    (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z) :
    equiv W L (α.comp β) = equiv W L α ≫ equiv W L β := by
  let := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  let := small_of_hasSmallLocalizedHom.{w} W W.Q Y Z
  obtain ⟨α, rfl⟩ := (equivShrink _).surjective α
  obtain ⟨β, rfl⟩ := (equivShrink _).surjective β
  dsimp [equiv, comp]
  rw [Equiv.symm_apply_apply]
  simp only [homEquiv_refl, homEquiv_comp]

section

variable {X Y Z T : C}

/-
**CategoryTheory.Localization.SmallHom.mk_comp_mk** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Localization.SmallHom`。
形式化陈述：mk_comp_mk [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y 
Z] [HasSmallLocalizedHom.{w} W X Z] (f : X ⟶ Y) (g : Y ⟶ Z) : (mk W f).comp (mk 
W g) = mk W (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_comp`：equiv_comp (L : C ⥤ D) 
[L.IsLocalization W] {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocal
izedHom.{w} W Y Z] [HasSmallLocalized…
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_mk`：equiv_mk (L : C ⥤ D) [L.I
sLocalization W] {X Y : C} [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) : equiv.
{w} W L (mk W f) = L.map f
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mk_comp_mk [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y Z]
    [HasSmallLocalizedHom.{w} W X Z] (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk W f).comp (mk W g) = mk W (f ≫ g) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]
/-
**CategoryTheory.Localization.SmallHom.comp_mk_id** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Localization.SmallHom`。
形式化陈述：comp_mk_id [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y 
Y] (α : SmallHom.{w} W X Y) : α.comp (mk W (𝟙 Y)) = α
参数：α : SmallHom.{w} W X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_comp`：equiv_comp (L : C ⥤ D) 
[L.IsLocalization W] {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocal
izedHom.{w} W Y Z] [HasSmallLocalized…
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_mk`：equiv_mk (L : C ⥤ D) [L.I
sLocalization W] {X Y : C} [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) : equiv.
{w} W L (mk W f) = L.map f
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_mk_id [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y Y]
    (α : SmallHom.{w} W X Y) :
    α.comp (mk W (𝟙 Y)) = α :=
  (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]
/-
**CategoryTheory.Localization.SmallHom.mk_id_comp** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Localization.SmallHom`。
形式化陈述：mk_id_comp [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W X 
X] (α : SmallHom.{w} W X Y) : (mk W (𝟙 X)).comp α = α
参数：α : SmallHom.{w} W X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_comp`：equiv_comp (L : C ⥤ D) 
[L.IsLocalization W] {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocal
izedHom.{w} W Y Z] [HasSmallLocalized…
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_mk`：equiv_mk (L : C ⥤ D) [L.I
sLocalization W] {X Y : C} [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) : equiv.
{w} W L (mk W f) = L.map f
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mk_id_comp [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W X X]
    (α : SmallHom.{w} W X Y) :
    (mk W (𝟙 X)).comp α = α :=
  (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]
/-
**CategoryTheory.Localization.SmallHom.comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Localization.SmallHom`。
形式化陈述：comp_assoc [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W X 
Z] [HasSmallLocalizedHom.{w} W X T] [HasSmallLocalizedHom.{w} W Y Z] [HasSmallLo
calizedHom.{w} W Y T] [HasSmallLocalizedHom.{w} W Z T] (α : SmallHom.{w} W X Y) 
(β : SmallHom.{w} W Y Z) (γ : SmallHom.{w} W Z T) : (α.comp β).comp γ = α.comp (
β.comp γ)
参数：α : SmallHom.{w} W X Y；β : SmallHom.{w} W Y Z；γ : SmallHom.{w} W Z T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_comp`：equiv_comp (L : C ⥤ D) 
[L.IsLocalization W] {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocal
izedHom.{w} W Y Z] [HasSmallLocalized…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_assoc [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W X Z]
    [HasSmallLocalizedHom.{w} W X T] [HasSmallLocalizedHom.{w} W Y Z]
    [HasSmallLocalizedHom.{w} W Y T] [HasSmallLocalizedHom.{w} W Z T]
    (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z) (γ : SmallHom.{w} W Z T) :
    (α.comp β).comp γ = α.comp (β.comp γ) := by
  apply (equiv W W.Q).injective
  simp only [equiv_comp, assoc]

@[simp]
/-
**CategoryTheory.Localization.SmallHom.mk_comp_mkInv** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Localization.SmallHom`。
形式化陈述：mk_comp_mkInv [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W
 Y X] [HasSmallLocalizedHom.{w} W Y Y] (f : Y ⟶ X) (hf : W f) : (mk W f).comp (m
kInv f hf) = mk W (𝟙 Y)
参数：f : Y ⟶ X；hf : W f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_comp`：equiv_comp (L : C ⥤ D) 
[L.IsLocalization W] {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocal
izedHom.{w} W Y Z] [HasSmallLocalized…
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_mk`：equiv_mk (L : C ⥤ D) [L.I
sLocalization W] {X Y : C} [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) : equiv.
{w} W L (mk W f) = L.map f
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_mkInv`：equiv_mkInv (L : C ⥤ D
) [L.IsLocalization W] {X Y : C} (f : Y ⟶ X) (hf : W f) [HasSmallLocalizedHom.{w
} W X Y] : equiv.{w} W L (mkInv f hf) …
· 使用引理 `CategoryTheory.Localization.isoOfHom_hom_inv_id`：isoOfHom_hom_inv_id {X 
Y : C} (f : X ⟶ Y) (hf : W f) : L.map f ≫ (isoOfHom L W f hf).inv = 𝟙 _
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mk_comp_mkInv [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y X]
    [HasSmallLocalizedHom.{w} W Y Y] (f : Y ⟶ X) (hf : W f) :
    (mk W f).comp (mkInv f hf) = mk W (𝟙 Y) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]
/-
**CategoryTheory.Localization.SmallHom.mkInv_comp_mk** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Localization.SmallHom`。
形式化陈述：mkInv_comp_mk [HasSmallLocalizedHom.{w} W X X] [HasSmallLocalizedHom.{w} W
 X Y] [HasSmallLocalizedHom.{w} W Y X] (f : Y ⟶ X) (hf : W f) : (mkInv f hf).com
p (mk W f) = mk W (𝟙 X)
参数：f : Y ⟶ X；hf : W f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_comp`：equiv_comp (L : C ⥤ D) 
[L.IsLocalization W] {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocal
izedHom.{w} W Y Z] [HasSmallLocalized…
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_mkInv`：equiv_mkInv (L : C ⥤ D
) [L.IsLocalization W] {X Y : C} (f : Y ⟶ X) (hf : W f) [HasSmallLocalizedHom.{w
} W X Y] : equiv.{w} W L (mkInv f hf) …
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_mk`：equiv_mk (L : C ⥤ D) [L.I
sLocalization W] {X Y : C} [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) : equiv.
{w} W L (mk W f) = L.map f
· 使用引理 `CategoryTheory.Localization.isoOfHom_inv_hom_id`：isoOfHom_inv_hom_id {X 
Y : C} (f : X ⟶ Y) (hf : W f) : (isoOfHom L W f hf).inv ≫ L.map f = 𝟙 _
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mkInv_comp_mk [HasSmallLocalizedHom.{w} W X X] [HasSmallLocalizedHom.{w} W X Y]
    [HasSmallLocalizedHom.{w} W Y X] (f : Y ⟶ X) (hf : W f) :
    (mkInv f hf).comp (mk W f) = mk W (𝟙 X) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

end

section ChangeOfUniverse

/-- Up to an equivalence, the type `SmallHom.{w} W X Y n` does not depend on the universe `w`. -/
/-
**CategoryTheory.Localization.SmallHom.chgUniv** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Localization.SmallHom`。
形式化陈述：chgUniv {X Y : C} [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{
w''} W X Y] : SmallHom.{w} W X Y ≃ SmallHom.{w''} W X Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Up to an equivalence, the type `SmallHom.{w} W X Y n` does not depend on the uni
verse `w`.
-/
noncomputable def chgUniv {X Y : C}
    [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w''} W X Y] :
    SmallHom.{w} W X Y ≃ SmallHom.{w''} W X Y :=
  (equiv.{w} W W.Q).trans (equiv.{w''} W W.Q).symm
/-
**CategoryTheory.Localization.SmallHom.equiv_chgUniv** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Localization.SmallHom`。
形式化陈述：equiv_chgUniv (L : C ⥤ D) [L.IsLocalization W] {X Y : C} [HasSmallLocalize
dHom.{w} W X Y] [HasSmallLocalizedHom.{w''} W X Y] (e : SmallHom.{w} W X Y) : eq
uiv W L (chgUniv.{w''} e) = equiv W L e
参数：L : C ⥤ D；e : SmallHom.{w} W X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_equiv_symm`：equiv_equiv_symm 
(L : C ⥤ D) [L.IsLocalization W] (L' : C ⥤ D') [L'.IsLocalization W] (G : D ⥤ D'
) (e : L ⋙ G ≅ L') {X Y : C} [HasSmallLocal…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv_chgUniv (L : C ⥤ D) [L.IsLocalization W] {X Y : C}
    [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w''} W X Y]
    (e : SmallHom.{w} W X Y) :
    equiv W L (chgUniv.{w''} e) = equiv W L e := by
  obtain ⟨f, rfl⟩ := (equiv W W.Q).symm.surjective e
  dsimp [chgUniv]
  simp only [Equiv.apply_symm_apply,
    equiv_equiv_symm W _ _ _ (Localization.compUniqFunctor W.Q L W)]

end ChangeOfUniverse

end SmallHom

end Localization

namespace LocalizerMorphism

open Localization

variable {C₁ : Type u₁} [Category.{v₁} C₁] {W₁ : MorphismProperty C₁}
  {C₂ : Type u₂} [Category.{v₂} C₂] {W₂ : MorphismProperty C₂}
  {D₁ : Type u₃} [Category.{v₃} D₁] {D₂ : Type u₄} [Category.{v₄} D₂]
  (Φ : LocalizerMorphism W₁ W₂) (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]

section

variable {X Y : C₁}

variable [HasSmallLocalizedHom.{w} W₁ X Y]
  [HasSmallLocalizedHom.{w'} W₂ (Φ.functor.obj X) (Φ.functor.obj Y)]

/-- The action of a localizer morphism on `SmallHom`. -/
/-
**CategoryTheory.LocalizerMorphism.smallHomMap** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.LocalizerMorphism`。
形式化陈述：smallHomMap (f : SmallHom.{w} W₁ X Y) : SmallHom.{w'} W₂ (Φ.functor.obj X)
 (Φ.functor.obj Y)
参数：f : SmallHom.{w} W₁ X Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The action of a localizer morphism on `SmallHom`.
-/
noncomputable def smallHomMap (f : SmallHom.{w} W₁ X Y) :
    SmallHom.{w'} W₂ (Φ.functor.obj X) (Φ.functor.obj Y) :=
  (SmallHom.equiv W₂ W₂.Q).symm
    (Iso.homCongr ((CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm.app _)
      ((CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm.app _)
      ((Φ.localizedFunctor W₁.Q W₂.Q).map ((SmallHom.equiv W₁ W₁.Q) f)))

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.LocalizerMorphism.equiv_smallHomMap** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.LocalizerMorphism`。
形式化陈述：equiv_smallHomMap (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) (f : SmallHo
m.{w} W₁ X Y) : (SmallHom.equiv W₂ L₂) (Φ.smallHomMap f) = e.hom.app X ≫ G.map (
SmallHom.equiv W₁ L₁ f) ≫ e.inv.app Y
参数：G : D₁ ⥤ D₂；e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G；f : SmallHom.{w} W₁ X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_equiv_symm`：equiv_equiv_symm 
(L : C ⥤ D) [L.IsLocalization W] (L' : C ⥤ D') [L'.IsLocalization W] (G : D ⥤ D'
) (e : L ⋙ G ≅ L') {X Y : C} [HasSmallLocal…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.instIsSplitEpiMap`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   {X Y : C} (f : X ⟶…
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
-/
lemma equiv_smallHomMap (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)
    (f : SmallHom.{w} W₁ X Y) :
    (SmallHom.equiv W₂ L₂) (Φ.smallHomMap f) =
      e.hom.app X ≫ G.map (SmallHom.equiv W₁ L₁ f) ≫ e.inv.app Y := by
  obtain ⟨g, rfl⟩ := (SmallHom.equiv W₁ W₁.Q).symm.surjective f
  simp only [smallHomMap, Equiv.apply_symm_apply]
  let G' := Φ.localizedFunctor W₁.Q W₂.Q
  let β := CatCommSq.iso Φ.functor W₁.Q W₂.Q G'
  let E₁ := (uniq W₁.Q L₁ W₁).functor
  let α₁ : W₁.Q ⋙ E₁ ≅ L₁ := compUniqFunctor W₁.Q L₁ W₁
  let E₂ := (uniq W₂.Q L₂ W₂).functor
  let α₂ : W₂.Q ⋙ E₂ ≅ L₂ := compUniqFunctor W₂.Q L₂ W₂
  rw [SmallHom.equiv_equiv_symm W₁ W₁.Q L₁ E₁ α₁,
    SmallHom.equiv_equiv_symm W₂ W₂.Q L₂ E₂ α₂]
  change α₂.inv.app _ ≫ E₂.map (β.hom.app X ≫ G'.map g ≫ β.inv.app Y) ≫ _ = _
  let γ : G' ⋙ E₂ ≅ E₁ ⋙ G := liftNatIso W₁.Q W₁ (W₁.Q ⋙ G' ⋙ E₂) (W₁.Q ⋙ E₁ ⋙ G) _ _
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight β.symm E₂ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ α₂ ≪≫ e ≪≫
      Functor.isoWhiskerRight α₁.symm G ≪≫ Functor.associator _ _ _)
  have hγ : ∀ (X : C₁), γ.hom.app (W₁.Q.obj X) =
      E₂.map (β.inv.app X) ≫ α₂.hom.app (Φ.functor.obj X) ≫
        e.hom.app X ≫ G.map (α₁.inv.app X) := fun X ↦ by
    simp [γ, id_comp, comp_id]
  simp only [Functor.map_comp, ← NatIso.naturality_1 γ, ← Functor.comp_map,
    ← cancel_epi (e.inv.app X), ← cancel_epi (G.map (α₁.hom.app X)),
    ← cancel_epi (γ.hom.app (W₁.Q.obj X)), assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, id_comp,
    Iso.hom_inv_id_app_assoc]
  simp only [hγ, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, id_comp, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app, Functor.comp_obj, comp_id]

@[simp]
/-
**CategoryTheory.LocalizerMorphism.smallHomMap_mk** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.LocalizerMorphism`。
形式化陈述：smallHomMap_mk (f : X ⟶ Y) : Φ.smallHomMap (SmallHom.mk _ f) = SmallHom.mk
 _ (Φ.functor.map f)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.equiv_smallHomMap`：equiv_smallHomMap (G
 : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) (f : SmallHom.{w} W₁ X Y) : (SmallHom.
equiv W₂ L₂) (Φ.smallHomMap f) = e.hom.a…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_mk`：equiv_mk (L : C ⥤ D) [L.I
sLocalization W] {X Y : C} [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) : equiv.
{w} W L (mk W f) = L.map f
· 使用引理 `CategoryTheory.CatCommSq.iso_inv_naturality`：iso_inv_naturality [h : Cat
CommSq T L R B] {x y : C₁} (f : x ⟶ y) : B.map (L.map f) ≫ (iso T L R B).inv.app
 y = (iso T L R B).inv.app x ≫ R.…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smallHomMap_mk (f : X ⟶ Y) :
    Φ.smallHomMap (SmallHom.mk _ f) =
      SmallHom.mk _ (Φ.functor.map f) := by
  apply (SmallHom.equiv W₂ W₂.Q).injective
  simp [Φ.equiv_smallHomMap W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) (CatCommSq.iso _ _ _ _)]

end

section

variable {X Y Z : C₁}

variable [HasSmallLocalizedHom.{w} W₁ X Y] [HasSmallLocalizedHom.{w} W₁ Y Z]
  [HasSmallLocalizedHom.{w} W₁ X Z]
  [HasSmallLocalizedHom.{w'} W₂ (Φ.functor.obj X) (Φ.functor.obj Y)]
  [HasSmallLocalizedHom.{w'} W₂ (Φ.functor.obj Y) (Φ.functor.obj Z)]
  [HasSmallLocalizedHom.{w'} W₂ (Φ.functor.obj X) (Φ.functor.obj Z)]

/-
**CategoryTheory.LocalizerMorphism.smallHomMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.LocalizerMorphism`。
形式化陈述：smallHomMap_comp (f : SmallHom.{w} W₁ X Y) (g : SmallHom.{w} W₁ Y Z) : Φ.s
mallHomMap (f.comp g) = (Φ.smallHomMap f).comp (Φ.smallHomMap g)
参数：f : SmallHom.{w} W₁ X Y；g : SmallHom.{w} W₁ Y Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.equiv_smallHomMap`：equiv_smallHomMap (G
 : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) (f : SmallHom.{w} W₁ X Y) : (SmallHom.
equiv W₂ L₂) (Φ.smallHomMap f) = e.hom.a…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_comp`：equiv_comp (L : C ⥤ D) 
[L.IsLocalization W] {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocal
izedHom.{w} W Y Z] [HasSmallLocalized…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smallHomMap_comp (f : SmallHom.{w} W₁ X Y) (g : SmallHom.{w} W₁ Y Z) :
    Φ.smallHomMap (f.comp g) = (Φ.smallHomMap f).comp (Φ.smallHomMap g) := by
  apply (SmallHom.equiv W₂ W₂.Q).injective
  simp [Φ.equiv_smallHomMap W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) (CatCommSq.iso _ _ _ _),
    SmallHom.equiv_comp]

end

section

variable {X Y : C₁} [HasSmallLocalizedHom.{w} W₁ X Y] {X' Y' : C₂}
  [HasSmallLocalizedHom.{w'} W₂ X' X']
  [HasSmallLocalizedHom.{w'} W₂ X' Y']
  [HasSmallLocalizedHom.{w'} W₂ Y' Y']
  (eX : Φ.functor.obj X ≅ X') (eY : Φ.functor.obj Y ≅ Y')

/-- The action of a localizer morphism `Φ` on `SmallHom`. In this version, we allow
the replacement of objects `Φ.functor.obj` by isomorphic objects. -/
/-
**CategoryTheory.LocalizerMorphism.smallHomMap'** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.LocalizerMorphism`。
形式化陈述：smallHomMap' (f : SmallHom.{w} W₁ X Y) : SmallHom.{w'} W₂ X' Y'
参数：f : SmallHom.{w} W₁ X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of a localizer morphism `Φ` on `SmallHom`. In this version, we allow
the replacement of objects `Φ.functor.obj` by isomorphic objects.
-/
noncomputable def smallHomMap' (f : SmallHom.{w} W₁ X Y) :
    SmallHom.{w'} W₂ X' Y' :=
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm eY.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ (Iso.refl X') eX.symm
  (SmallHom.mk _ eX.inv).comp ((Φ.smallHomMap f).comp (SmallHom.mk _ eY.hom))

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.LocalizerMorphism.equiv_smallHomMap'** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.LocalizerMorphism`。
形式化陈述：equiv_smallHomMap' (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) (f : SmallH
om.{w} W₁ X Y) : SmallHom.equiv W₂ L₂ (Φ.smallHomMap' eX eY f) = L₂.map eX.inv ≫
 e.hom.app X ≫ G.map (SmallHom.equiv W₁ L₁ f) ≫ e.inv.app Y ≫ L₂.map eY.hom
参数：G : D₁ ⥤ D₂；e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G；f : SmallHom.{w} W₁ X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.hasSmallLocalizedHom_of_isos`：hasSmallLocali
zedHom_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') [HasSmallLocalizedHom.{w} 
W X Y] : HasSmallLocalizedHom.{w} W X' Y'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_comp`：equiv_comp (L : C ⥤ D) 
[L.IsLocalization W] {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocal
izedHom.{w} W Y Z] [HasSmallLocalized…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_mk`：equiv_mk (L : C ⥤ D) [L.I
sLocalization W] {X Y : C} [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) : equiv.
{w} W L (mk W f) = L.map f
· 使用引理 `CategoryTheory.LocalizerMorphism.equiv_smallHomMap`：equiv_smallHomMap (G
 : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) (f : SmallHom.{w} W₁ X Y) : (SmallHom.
equiv W₂ L₂) (Φ.smallHomMap f) = e.hom.a…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv_smallHomMap' (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)
    (f : SmallHom.{w} W₁ X Y) :
    SmallHom.equiv W₂ L₂ (Φ.smallHomMap' eX eY f) =
      L₂.map eX.inv ≫ e.hom.app X ≫ G.map (SmallHom.equiv W₁ L₁ f) ≫
        e.inv.app Y ≫ L₂.map eY.hom := by
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  simp [smallHomMap', SmallHom.equiv_comp, Φ.equiv_smallHomMap L₁ L₂ G e]

@[simp]
/-
**CategoryTheory.LocalizerMorphism.smallHomMap'_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.LocalizerMorphism`。
形式化陈述：∀ {C₁ : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C₁] {W₁ : Catego
ryTheory.MorphismProperty C₁} {C₂ : Type u₂}   [inst_1 : CategoryTheory.Category
.{v₂, u₂} C₂] {W₂ : CategoryTheory.MorphismProperty C₂}   (Φ : CategoryTheory.Lo
calizerMorphism W₁ W₂) {X Y : C₁}   [inst_2 : CategoryTheory.Localization.HasSma
llLocalizedHom W₁ X Y] {X' Y' : C₂}   [inst_3 : CategoryTheory.Localization.HasS
mallLocalizedHom W₂ X' X']   [inst_4 : CategoryTheory.Localization.HasSmallLocal
izedHom W₂ X' Y']   [inst_5 : CategoryTheory.Localization.HasSmallLocalizedHom W
₂ Y' Y'] (eX : Φ.functor.obj X ≅ X')   (eY : Φ.functor.obj Y ≅ Y') (f : X ⟶ Y), 
  Φ.smallHomMap' eX eY (CategoryTheory.Localization.SmallHom.mk W₁ f) =     Cate
goryTheory.Localization.SmallHom.mk W₂       (CategoryTheory.CategoryStruct.comp
 eX.inv (CategoryTheory.CategoryStruct.comp (Φ.functor.map f) eY.hom))
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；eX : Φ.functor.obj X ≅ X'；eY : Φ.f
unctor.obj Y ≅ Y'；f : X ⟶ Y；CategoryTheory.Localization.SmallHom.mk W₁ f；Categor
yTheory.CategoryStruct.comp eX.inv (CategoryTheory.CategoryStruct.comp (Φ.functo
r.map f) eY.hom)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.smallHomMap_mk`：smallHomMap_mk (f : X ⟶
 Y) : Φ.smallHomMap (SmallHom.mk _ f) = SmallHom.mk _ (Φ.functor.map f)
· 使用引理 `CategoryTheory.Localization.SmallHom.mk_comp_mk`：mk_comp_mk [HasSmallLoc
alizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y Z] [HasSmallLocalizedHom.{w} 
W X Z] (f : X ⟶ Y) (g : Y ⟶ Z) : (mk …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smallHomMap'_mk (f : X ⟶ Y) :
    Φ.smallHomMap' eX eY (SmallHom.mk _ f) =
      SmallHom.mk _ (eX.inv ≫ Φ.functor.map f ≫ eY.hom) := by
  simp [smallHomMap', SmallHom.mk_comp_mk]

end

section

variable {X Y Z : C₁} [HasSmallLocalizedHom.{w} W₁ X Y] [HasSmallLocalizedHom.{w} W₁ Y Z]
  [HasSmallLocalizedHom.{w} W₁ X Z] {X' Y' Z' : C₂}
  [HasSmallLocalizedHom.{w'} W₂ X' X'] [HasSmallLocalizedHom.{w'} W₂ Y' Y']
  [HasSmallLocalizedHom.{w'} W₂ Z' Z'] [HasSmallLocalizedHom.{w'} W₂ X' Y']
  [HasSmallLocalizedHom.{w'} W₂ Y' Z'] [HasSmallLocalizedHom.{w'} W₂ X' Z']
  (eX : Φ.functor.obj X ≅ X') (eY : Φ.functor.obj Y ≅ Y') (eZ : Φ.functor.obj Z ≅ Z')

/-
**CategoryTheory.LocalizerMorphism.smallHomMap'_comp** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.LocalizerMorphism`。
形式化陈述：∀ {C₁ : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C₁] {W₁ : Catego
ryTheory.MorphismProperty C₁} {C₂ : Type u₂}   [inst_1 : CategoryTheory.Category
.{v₂, u₂} C₂] {W₂ : CategoryTheory.MorphismProperty C₂}   (Φ : CategoryTheory.Lo
calizerMorphism W₁ W₂) {X Y Z : C₁}   [inst_2 : CategoryTheory.Localization.HasS
mallLocalizedHom W₁ X Y]   [inst_3 : CategoryTheory.Localization.HasSmallLocaliz
edHom W₁ Y Z]   [inst_4 : CategoryTheory.Localization.HasSmallLocalizedHom W₁ X 
Z] {X' Y' Z' : C₂}   [inst_5 : CategoryTheory.Localization.HasSmallLocalizedHom 
W₂ X' X']   [inst_6 : CategoryTheory.Localization.HasSmallLocalizedHom W₂ Y' Y']
   [inst_7 : CategoryTheory.Localization.HasSmallLocalizedHom W₂ Z' Z']   [inst_
8 : CategoryTheory.Localization.HasSmallLocalizedHom W₂ X' Y']   [inst_9 : Categ
oryTheory.Localization.HasSmallLocalizedHom W₂ Y' Z']   [inst_10 : CategoryTheor
y.Localization.HasSmallLocalizedHom W₂ X' Z'] (eX : Φ.functor.obj X ≅ X')   (eY 
: Φ.functor.obj Y ≅ Y') (eZ : Φ.functor.obj Z ≅ Z') (f : CategoryTheory.Localiza
tion.SmallHom W₁ X Y)   (g : CategoryTheory.Localization.SmallHom W₁ Y Z),   Φ.s
mallHomMap' eX eZ (f.comp g) = (Φ.smallHomMap' eX eY f).comp (Φ.smallHomMap' eY 
eZ g)
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；eX : Φ.functor.obj X ≅ X'；eY : Φ.f
unctor.obj Y ≅ Y'；eZ : Φ.functor.obj Z ≅ Z'；f : CategoryTheory.Localization.Smal
lHom W₁ X Y；g : CategoryTheory.Localization.SmallHom W₁ Y Z；f.comp g；Φ.smallHomM
ap' eX eY f；Φ.smallHomMap' eY eZ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.hasSmallLocalizedHom_of_isos`：hasSmallLocali
zedHom_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') [HasSmallLocalizedHom.{w} 
W X Y] : HasSmallLocalizedHom.{w} W X' Y'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.LocalizerMorphism.smallHomMap_comp`：smallHomMap_comp (f :
 SmallHom.{w} W₁ X Y) (g : SmallHom.{w} W₁ Y Z) : Φ.smallHomMap (f.comp g) = (Φ.
smallHomMap f).comp (Φ.smallHomMap g)
· 使用引理 `CategoryTheory.Localization.SmallHom.comp_assoc`：comp_assoc [HasSmallLoc
alizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W X Z] [HasSmallLocalizedHom.{w} 
W X T] [HasSmallLocalizedHom.{w} W Y …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Localization.SmallHom.mk_comp_mk`：mk_comp_mk [HasSmallLoc
alizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y Z] [HasSmallLocalizedHom.{w} 
W X Z] (f : X ⟶ Y) (g : Y ⟶ Z) : (mk …
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用引理 `CategoryTheory.Localization.SmallHom.mk_id_comp`：mk_id_comp [HasSmallLoc
alizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W X X] (α : SmallHom.{w} W X Y) :
 (mk W (𝟙 X)).comp α = α
-/
lemma smallHomMap'_comp (f : SmallHom.{w} W₁ X Y) (g : SmallHom.{w} W₁ Y Z) :
    Φ.smallHomMap' eX eZ (f.comp g) =
      (Φ.smallHomMap' eX eY f).comp (Φ.smallHomMap' eY eZ g) := by
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm eY.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm (Iso.refl Z')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm eZ.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Z')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ (Iso.refl Y') eY.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm eY.symm
  simp only [smallHomMap', smallHomMap_comp, SmallHom.comp_assoc]
  congr 2
  rw [← SmallHom.comp_assoc, SmallHom.mk_comp_mk, eY.hom_inv_id, SmallHom.mk_id_comp]

end

end LocalizerMorphism

end CategoryTheory

