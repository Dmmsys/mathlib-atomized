/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.Hypercover.IsSheaf
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-!
# Continuous functors between sites.

We define the notion of continuous functor between sites: these are functors `F` such that
the precomposition with `F.op` preserves sheaves of types (and actually sheaves in any
category).

## Main definitions

* `Functor.IsContinuous`: a functor between sites is continuous if the
  precomposition with this functor preserves sheaves with values in
  the category `Type t` for a certain auxiliary universe `t`.
* `Functor.sheafPushforwardContinuous`: the induced functor
  `Sheaf K A ⥤ Sheaf J A` for a continuous functor `G : (C, J) ⥤ (D, K)`. In case this is
  part of a morphism of sites, this would be understood as the pushforward functor
  even though it goes in the opposite direction as the functor `G`. (Here, the auxiliary
  universe `t` in the assumption that `G` is continuous is the one such that morphisms
  in the category `A` are in `Type t`.)
* `Functor.PreservesOneHypercovers`: a type-class expressing that a functor preserves
  1-hypercovers of a certain size

## Main result

- `Functor.isContinuous_of_preservesOneHypercovers`: if the topology on `C` is generated
  by 1-hypercovers of size `w` and that `F : C ⥤ D` preserves 1-hypercovers of size `w`,
  then `F` is continuous (for any auxiliary universe parameter `t`).
  This is an instance for `w = max u₁ v₁` when `C : Type u₁` and `[Category.{v₁} C]`

## References
* https://stacks.math.columbia.edu/tag/00WU

-/

@[expose] public section

universe w t v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

namespace PreOneHypercover

variable {X : C} (E : PreOneHypercover X) (F : C ⥤ D)

/-- The image of a 1-pre-hypercover by a functor. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
/-
**CategoryTheory.PreOneHypercover.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
PreOneHypercover`。
形式化陈述：map : PreOneHypercover (F.obj X) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a 1-pre-hypercover by a functor.
-/
def map : PreOneHypercover (F.obj X) where
  __ := E.toPreZeroHypercover.map F
  I₁ := E.I₁
  Y _ _ j := F.obj (E.Y j)
  p₁ _ _ j := F.map (E.p₁ j)
  p₂ _ _ j := F.map (E.p₂ j)
  w _ _ j := by simpa using! F.congr_map (E.w j)

@[simp]
/-
**CategoryTheory.PreOneHypercover.map_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.PreOneHypercover`。
形式化陈述：map_id : E.map (𝟭 _) = E
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_id : E.map (𝟭 _) = E :=
  rfl
/-
**CategoryTheory.PreOneHypercover.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.PreOneHypercover`。
形式化陈述：map_comp {D' : Type*} [Category* D'] (G : D ⥤ D') : E.map (F ⋙ G) = (E.map
 F).map G
参数：G : D ⥤ D'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_comp {D' : Type*} [Category* D'] (G : D ⥤ D') : E.map (F ⋙ G) = (E.map F).map G :=
  rfl
/-
**CategoryTheory.PreOneHypercover.sieve** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.PreOneHypercover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sieve₀_map : (E.map F).sieve₀ = Sieve.functorPushforward _ E.sieve₀ := by
  rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, ← PreZeroHypercover.presieve₀,
    PreOneHypercover.map_toPreZeroHypercover, PreZeroHypercover.presieve₀_map,
    Sieve.generate_map_eq_functorPushforward]

/-- If `F : C ⥤ D`, `P : Dᵒᵖ ⥤ A` and `E` is a 1-pre-hypercover of an object of `X`,
then `(E.map F).multifork P` is a limit iff `E.multifork (F.op ⋙ P)` is a limit. -/
/-
**CategoryTheory.PreOneHypercover.isLimitMapMultiforkEquiv** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.PreOneHypercover`。
形式化陈述：isLimitMapMultiforkEquiv {A : Type u} [Category.{t} A] (P : Dᵒᵖ ⥤ A) : IsL
imit ((E.map F).multifork P) ≃ IsLimit (E.multifork (F.op ⋙ P))
参数：P : Dᵒᵖ ⥤ A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
If `F : C ⥤ D`, `P : Dᵒᵖ ⥤ A` and `E` is a 1-pre-hypercover of an object of `X`,
then `(E.map F).multifork P` is a limit iff `E.multifork (F.op ⋙ P)` is a limit.
-/
def isLimitMapMultiforkEquiv {A : Type u} [Category.{t} A] (P : Dᵒᵖ ⥤ A) :
    IsLimit ((E.map F).multifork P) ≃ IsLimit (E.multifork (F.op ⋙ P)) := by rfl

section

variable {E} {W : C} {i₁ i₂ : E.I₀} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.PreOneHypercover.functorPushforward_sieve** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.PreOneHypercover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorPushforward_sieve₁_map_le :
    Sieve.functorPushforward F (E.sieve₁ p₁ p₂) ≤ (E.map F).sieve₁ (F.map p₁) (F.map p₂) := by
  rw [Sieve.functorPushforward_le_iff_le_functorPullback]
  intro Y f ⟨k, u, hf₁, hf₂⟩
  exact ⟨k, F.map u, by simp [← Functor.map_comp, hf₁], by simp [← Functor.map_comp, hf₂]⟩

variable (i₁ i₂) in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.PreOneHypercover.functorPushforward_sieve** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.PreOneHypercover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorPushforward_sieve₁'_of_preservesLimit [HasPullback (E.f i₁) (E.f i₂)]
    [PreservesLimit (cospan (E.f i₁) (E.f i₂)) F] :
    Sieve.functorPushforward F (E.sieve₁' i₁ i₂) =
      (E.map F).sieve₁ (F.map <| pullback.fst _ _) (F.map <| pullback.snd _ _) := by
  have : HasPullback ((E.map F).f i₁) ((E.map F).f i₂) :=
    hasPullback_of_preservesPullback F (E.f i₁) (E.f i₂)
  refine le_antisymm ?_ ?_
  · rw [PreOneHypercover.sieve₁'_eq_sieve₁]
    apply PreOneHypercover.functorPushforward_sieve₁_map_le
  · rw [PreOneHypercover.sieve₁_eq_pullback_sieve₁' _ _ _
      (by simp [← Functor.map_comp, pullback.condition])]
    rintro W f ⟨Z, u, v, ⟨k⟩, h⟩
    refine ⟨E.Y k, pullback.lift (E.p₁ k) (E.p₂ k) (E.w _), u, ?_, ?_⟩
    · use E.Y k, 𝟙 _, pullback.lift (E.p₁ k) (E.p₂ k) (E.w _), ⟨k⟩
      simp
    · simp only [pullback.hom_ext_iff, Category.assoc, limit.lift_π, PullbackCone.mk_π_app] at h
      apply IsPullback.hom_ext (IsPullback.map _ (.of_hasPullback _ _)) <;>
        simp [← h.left, ← h.right, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.PreOneHypercover.functorPushforward_sieve** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.PreOneHypercover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorPushforward_sieve₁_of_preservesPullbacks (h : p₁ ≫ E.f _ = p₂ ≫ E.f _)
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F] :
    Sieve.functorPushforward F (E.sieve₁ p₁ p₂) = (E.map F).sieve₁ (F.map p₁) (F.map p₂) := by
  refine le_antisymm (PreOneHypercover.functorPushforward_sieve₁_map_le _ _ _) ?_
  have : HasPullback ((E.map F).f i₁) ((E.map F).f i₂) :=
    hasPullback_of_preservesPullback F (E.f i₁) (E.f i₂)
  rintro T f ⟨k, u, hf₁, hf₂⟩
  let l : W ⟶ pullback (E.f i₁) (E.f i₂) := pullback.lift p₁ p₂ h
  have hl₁ : l ≫ pullback.fst _ _ = p₁ := by simp [l]
  have hl₂ : l ≫ pullback.snd _ _ = p₂ := by simp [l]
  let r : E.Y k ⟶ pullback (E.f i₁) (E.f i₂) := pullback.lift (E.p₁ _) (E.p₂ _) (E.w _)
  refine ⟨pullback l r, pullback.fst _ _, IsPullback.lift
    (IsPullback.map _ (.of_hasPullback _ _)) f u ?_, ?_, ?_⟩
  · apply (IsPullback.map _ (.of_hasPullback _ _)).hom_ext <;>
      simp [l, r, ← Functor.map_comp, hf₁, hf₂]
  · refine ⟨k, pullback.snd _ _, ?_, ?_⟩ <;> simp [← hl₁, ← hl₂, pullback.condition_assoc, r]
  · simp

end

end PreOneHypercover

namespace GrothendieckTopology

namespace OneHypercover

variable {J : GrothendieckTopology C} {X : C} (E : J.OneHypercover X)

/-- A 1-hypercover in `C` is preserved by a functor `F : C ⥤ D` if the mapped 1-pre-hypercover
in `D` is a 1-hypercover for the given topology on `D`. -/
/-
**CategoryTheory.GrothendieckTopology.OneHypercover.IsPreservedBy** 是 Mathlib 中的
一个归纳类型，位于命名空间 `CategoryTheory.GrothendieckTopology.OneHypercover`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {J : Cat
egoryTheory.GrothendieckTopology C} →           {X : C} → J.OneHypercover X → Ca
tegoryTheory.Functor C D → CategoryTheory.GrothendieckTopology D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A 1-hypercover in `C` is preserved by a functor `F : C ⥤ D` if the mapped 1-pre-
hypercover
in `D` is a 1-hypercover for the given topology on `D`.
-/
class IsPreservedBy (F : C ⥤ D) (K : GrothendieckTopology D) : Prop where
  mem₀ : (E.toPreOneHypercover.map F).sieve₀ ∈ K (F.obj X)
  mem₁ (i₁ i₂ : E.I₀) ⦃W : D⦄ (p₁ : W ⟶ F.obj (E.X i₁)) (p₂ : W ⟶ F.obj (E.X i₂))
    (w : p₁ ≫ F.map (E.f i₁) = p₂ ≫ F.map (E.f i₂)) :
      (E.toPreOneHypercover.map F).sieve₁ p₁ p₂ ∈ K W

/-- Given a 1-hypercover `E : J.OneHypercover X` of an object of `C`, a functor `F : C ⥤ D`
such that `E.IsPreservedBy F K` for a Grothendieck topology `K` on `D`, this is
the image of `E` by `F`, as a 1-hypercover of `F.obj X` for `K`. -/
@[simps! toPreOneHypercover]
/-
**CategoryTheory.GrothendieckTopology.OneHypercover.map** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.GrothendieckTopology.OneHypercover`。
形式化陈述：map (F : C ⥤ D) (K : GrothendieckTopology D) [E.IsPreservedBy F K] : K.One
Hypercover (F.obj X) where toPreOneHypercover
参数：F : C ⥤ D；K : GrothendieckTopology D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.OneHypercover.IsPreservedBy.mem₀`：∀ 
{C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 
: CategoryTheory.Category.{v₂, u₂} D}   {J : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.OneHypercover.IsPreservedBy.mem₁`：∀ 
{C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 
: CategoryTheory.Category.{v₂, u₂} D}   {J : CategoryTheor…

--- 原说明 ---
Given a 1-hypercover `E : J.OneHypercover X` of an object of `C`, a functor `F :
 C ⥤ D`
such that `E.IsPreservedBy F K` for a Grothendieck topology `K` on `D`, this is
the image of `E` by `F`, as a 1-hypercover of `F.obj X` for `K`.
-/
def map (F : C ⥤ D) (K : GrothendieckTopology D) [E.IsPreservedBy F K] :
    K.OneHypercover (F.obj X) where
  toPreOneHypercover := E.toPreOneHypercover.map F
  mem₀ := IsPreservedBy.mem₀
  mem₁ _ _ _ _ _ h := IsPreservedBy.mem₁ _ _ _ _ h
/-
**CategoryTheory.GrothendieckTopology.OneHypercover.** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.GrothendieckTopology.OneHypercover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : E.IsPreservedBy (𝟭 C) J where
  mem₀ := E.mem₀
  mem₁ := E.mem₁

end OneHypercover

end GrothendieckTopology

namespace Functor

variable (F F' : C ⥤ D) (τ : F ⟶ F') (e : F ≅ F') (G : D ⥤ E)
  {F'' : C ⥤ C} (eF'' : F'' ≅ 𝟭 C) {FG : C ⥤ E} (eFG : F ⋙ G ≅ FG)
  {A : Type u} [Category.{t} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)

/-- The condition that a functor `F : C ⥤ D` sends 1-hypercovers for
`J : GrothendieckTopology C` to 1-hypercovers for `K : GrothendieckTopology D`. -/
/-
**CategoryTheory.Functor.PreservesOneHypercovers** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：PreservesOneHypercovers
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a functor `F : C ⥤ D` sends 1-hypercovers for
`J : GrothendieckTopology C` to 1-hypercovers for `K : GrothendieckTopology D`.
-/
abbrev PreservesOneHypercovers :=
  ∀ {X : C} (E : GrothendieckTopology.OneHypercover.{w} J X), E.IsPreservedBy F K

/-- A functor `F` is continuous if the precomposition with `F.op` sends sheaves of
`Type (max u₁ v₁ u₂ v₂)` to sheaves. This implies that this holds for an arbitrary
universe (see `Functor.op_comp_isSheaf_of_types`). -/
/-
**CategoryTheory.Functor.IsContinuous** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：IsContinuous : Prop where op_comp_isSheaf_of_types (G : Sheaf K (Type max 
u₁ v₁ u₂ v₂)) : Presieve.IsSheaf J (F.op ⋙ G.obj)  /-- (Implementation) Use the 
more general `Functor.W_map_of_adjunction_of_isContinuous`. -/ private lemma W_m
ap_of_adjunction_of_isContinuous_aux (F : C ⥤ D) (H : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v
₂) ⥤ (Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂)) (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj
 F.op) [Functor.IsContinuous F J K] {G G' : Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂} (f : G ⟶
 G') (hf : J.W f) : K.W (H
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` is continuous if the precomposition with `F.op` sends sheaves of
`Type (max u₁ v₁ u₂ v₂)` to sheaves. This implies that this holds for an arbitra
ry
universe (see `Functor.op_comp_isSheaf_of_types`).
-/
class IsContinuous : Prop where
  op_comp_isSheaf_of_types (G : Sheaf K (Type max u₁ v₁ u₂ v₂)) : Presieve.IsSheaf J (F.op ⋙ G.obj)

/-- (Implementation) Use the more general `Functor.W_map_of_adjunction_of_isContinuous`. -/
/-
**CategoryTheory.Functor.W_map_of_adjunction_of_isContinuous_aux** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) Use the more general `Functor.W_map_of_adjunction_of_isContinuo
us`.
-/
private lemma W_map_of_adjunction_of_isContinuous_aux (F : C ⥤ D)
    (H : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ (Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂))
    (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    [Functor.IsContinuous F J K] {G G' : Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂} (f : G ⟶ G') (hf : J.W f) :
    K.W (H.map f) := by
  intro U hU
  rw [adj.map_comp_bijective_iff]
  apply hf
  rw [isSheaf_iff_isSheaf_of_type]
  exact IsContinuous.op_comp_isSheaf_of_types (F := F) ⟨U, hU⟩

set_option backward.defeqAttrib.useBackward true in
/-- `Functor.IsContinuous` is preserved under enlarging the universe if the starting
universe is large enough. SGA 4 III 1.5. -/
/-
**CategoryTheory.Functor.isSheaf_of_isContinuous_aux** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Functor.IsContinuous` is preserved under enlarging the universe if the starting
universe is large enough. SGA 4 III 1.5.
-/
private lemma isSheaf_of_isContinuous_aux (F : C ⥤ D) [Functor.IsContinuous F J K]
    (G : Dᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂) (hG : Presieve.IsSheaf K G) :
    Presieve.IsSheaf J (F.op ⋙ G) := by
  let H : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂ := F.op.lan
  let adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  let H' : (Cᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂ := F.op.lan
  let adj' : H' ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  refine Presieve.IsSheaf.comp_of_W_map_of_adjunction _ adj' ?_ _ hG
  intro X S hS
  have hWS : J.W (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι :=
    Sieve.W_shrinkFunctor_ι_of_mem.{max u₁ v₁ u₂ v₂} _ S hS
  have : K.W _ := Functor.W_map_of_adjunction_of_isContinuous_aux (J := J) K F H adj
    (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι hWS
  let e : H ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ≅
      (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ⋙ H' :=
    uliftFunctor.{w, max (max (max u₁ u₂) v₁) v₂}.lanCompIsoOfPreserves F.op
  let iso : Arrow.mk (H'.map (Sieve.shrinkFunctor.{max w u₁ v₁ u₂ v₂} S).ι) ≅
      .mk (Functor.whiskerRight
        (H.map (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι) uliftFunctor.{w}) :=
    Arrow.isoMk' _ _
      (H'.mapIso (Sieve.shrinkFunctorUliftFunctorIso.{max u₁ v₁ u₂ v₂, w} S).symm ≪≫ (e.app _).symm)
      (H'.mapIso (shrinkYonedaUliftFunctorIso.{max u₁ v₁ u₂ v₂}.app _).symm ≪≫ (e.app _).symm) <| by
        simp only [Functor.mapIso_symm, Functor.comp_obj, Functor.whiskeringRight_obj_obj,
          Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
        rw [← Functor.map_comp_assoc, ← dsimp% e.inv.naturality, ← Functor.map_comp_assoc,
          Sieve.shrinkFunctorUliftFunctorIso_inv_ι]
  rw [K.W.arrow_mk_iso_iff iso]
  apply GrothendieckTopology.W_of_preservesSheafification
  exact F.W_map_of_adjunction_of_isContinuous_aux J K H adj
    (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι hWS

/-- If `F` is continuous, any sheaf (in an arbitrary universe) remains a sheaf when
precomposing with `F.op` (SGA 4 III 1.5). -/
/-
**CategoryTheory.Functor.op_comp_isSheaf_of_types** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：op_comp_isSheaf_of_types [Functor.IsContinuous F J K] (G : Sheaf K (Type t
)) : Presieve.IsSheaf J (F.op ⋙ G.obj)
参数：G : Sheaf K (Type t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.isSheaf_comp_uliftFunctor_iff`：isSheaf_comp_ulif
tFunctor_iff : IsSheaf J (P ⋙ uliftFunctor.{w'}) ↔ IsSheaf J P
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.Presheaf.isSheaf_of_iso_iff`：isSheaf_of_iso_iff {P P' : C
ᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P'
· 使用定理 `_private.Mathlib.CategoryTheory.Sites.Continuous.0.CategoryTheory.Functo
r.isSheaf_of_isContinuous_aux`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{
v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (J : Ca
tegoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj

--- 原说明 ---
If `F` is continuous, any sheaf (in an arbitrary universe) remains a sheaf when
precomposing with `F.op` (SGA 4 III 1.5).
-/
lemma op_comp_isSheaf_of_types [Functor.IsContinuous F J K] (G : Sheaf K (Type t)) :
    Presieve.IsSheaf J (F.op ⋙ G.obj) := by
  rw [← Presieve.isSheaf_comp_uliftFunctor_iff.{t, max u₁ v₁ u₂ v₂}, ← isSheaf_iff_isSheaf_of_type,
    Presheaf.isSheaf_of_iso_iff (Functor.associator _ _ _), isSheaf_iff_isSheaf_of_type]
  apply isSheaf_of_isContinuous_aux.{t} J K
  rw [Presieve.isSheaf_comp_uliftFunctor_iff, ← isSheaf_iff_isSheaf_of_type]
  exact G.property
/-
**CategoryTheory.Functor.op_comp_isSheaf** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：op_comp_isSheaf [Functor.IsContinuous F J K] (G : Sheaf K A) : Presheaf.Is
Sheaf J (F.op ⋙ G.obj)
参数：G : Sheaf K A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf_of_types`：op_comp_isSheaf_of_type
s [Functor.IsContinuous F J K] (G : Sheaf K (Type t)) : Presieve.IsSheaf J (F.op
 ⋙ G.obj)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
lemma op_comp_isSheaf [Functor.IsContinuous F J K] (G : Sheaf K A) :
    Presheaf.IsSheaf J (F.op ⋙ G.obj) :=
  fun T => F.op_comp_isSheaf_of_types J K ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (G.property T)⟩
/-
**CategoryTheory.Functor.op_comp_isSheaf_of_isSheaf** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：op_comp_isSheaf_of_isSheaf [IsContinuous F J K] (P : Dᵒᵖ ⥤ A) (h : Preshea
f.IsSheaf K P) : Presheaf.IsSheaf J (F.op ⋙ P)
参数：P : Dᵒᵖ ⥤ A；h : Presheaf.IsSheaf K P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf`：op_comp_isSheaf [Functor.IsConti
nuous F J K] (G : Sheaf K A) : Presheaf.IsSheaf J (F.op ⋙ G.obj)
-/
lemma op_comp_isSheaf_of_isSheaf [IsContinuous F J K] (P : Dᵒᵖ ⥤ A) (h : Presheaf.IsSheaf K P) :
    Presheaf.IsSheaf J (F.op ⋙ P) :=
  F.op_comp_isSheaf J K ⟨P, h⟩

variable {K} in
/-
**CategoryTheory.Functor.op_comp_isSheaf_of_isSheaf_type** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：op_comp_isSheaf_of_isSheaf_type [F.IsContinuous J K] {G : Dᵒᵖ ⥤ Type*} (h 
: Presieve.IsSheaf K G) : Presieve.IsSheaf J (F.op ⋙ G)
参数：h : Presieve.IsSheaf K G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf_of_isSheaf`：op_comp_isSheaf_of_is
Sheaf [IsContinuous F J K] (P : Dᵒᵖ ⥤ A) (h : Presheaf.IsSheaf K P) : Presheaf.I
sSheaf J (F.op ⋙ P)
-/
lemma op_comp_isSheaf_of_isSheaf_type [F.IsContinuous J K] {G : Dᵒᵖ ⥤ Type*}
    (h : Presieve.IsSheaf K G) :
    Presieve.IsSheaf J (F.op ⋙ G) := by
  rw [← isSheaf_iff_isSheaf_of_type] at h ⊢
  exact F.op_comp_isSheaf_of_isSheaf _ _ _ h

/-- SGA 4 III 1.2 (i) => (iii) -/
/-
**CategoryTheory.Functor.W_map_of_adjunction_of_isContinuous** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：W_map_of_adjunction_of_isContinuous (F : C ⥤ D) (H : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)
) (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op) [Functor.IsContinuous F J 
K] {G G' : Cᵒᵖ ⥤ A} (f : G ⟶ G') (hf : J.W f) : K.W (H.map f)
参数：F : C ⥤ D；H : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)；adj : H ⊣ (Functor.whiskeringLeft _ _ _).
obj F.op；f : G ⟶ G'；hf : J.W f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.map_comp_bijective_iff`：map_comp_bijective_iff
 (adj : F ⊣ G) {X Y : C} (f : X ⟶ Y) (Z : D) : Function.Bijective (fun (g : F.ob
j Y ⟶ Z) => F.map f ≫ g) ↔ Function.Bi…
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf_of_isSheaf`：op_comp_isSheaf_of_is
Sheaf [IsContinuous F J K] (P : Dᵒᵖ ⥤ A) (h : Presheaf.IsSheaf K P) : Presheaf.I
sSheaf J (F.op ⋙ P)

--- 原说明 ---
SGA 4 III 1.2 (i) => (iii)
-/
lemma W_map_of_adjunction_of_isContinuous (F : C ⥤ D) (H : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A))
    (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    [Functor.IsContinuous F J K] {G G' : Cᵒᵖ ⥤ A} (f : G ⟶ G') (hf : J.W f) :
    K.W (H.map f) := by
  intro U hU
  rw [adj.map_comp_bijective_iff]
  exact hf _ (F.op_comp_isSheaf_of_isSheaf _ _ _ hU)
/-
**CategoryTheory.Functor.isContinuous_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：isContinuous_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) (J : GrothendieckTopolog
y C) (K : GrothendieckTopology D) [Functor.IsContinuous F₁ J K] : Functor.IsCont
inuous F₂ J K where op_comp_isSheaf_of_types G
参数：e : F₁ ≅ F₂；J : GrothendieckTopology C；K : GrothendieckTopology D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.isSheaf_iso`：isSheaf_iso {P' : Cᵒᵖ ⥤ Type w} (i 
: P ≅ P') (h : IsSheaf J P) : IsSheaf J P'
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf_of_types`：op_comp_isSheaf_of_type
s [Functor.IsContinuous F J K] (G : Sheaf K (Type t)) : Presieve.IsSheaf J (F.op
 ⋙ G.obj)
-/
lemma isContinuous_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous F₁ J K] : Functor.IsContinuous F₂ J K where
  op_comp_isSheaf_of_types G :=
    Presieve.isSheaf_iso J (isoWhiskerRight (NatIso.op e.symm) _)
      (F₁.op_comp_isSheaf_of_types J K G)
/-
**CategoryTheory.Functor.isContinuous_id** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：isContinuous_id : Functor.IsContinuous (𝟭 C) J J where op_comp_isSheaf_of_
types G
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
instance isContinuous_id : Functor.IsContinuous (𝟭 C) J J where
  op_comp_isSheaf_of_types G := (isSheaf_iff_isSheaf_of_type _ _).1 G.2
/-
**CategoryTheory.Functor.isContinuous_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：isContinuous_comp (F₁ : C ⥤ D) (F₂ : D ⥤ E) (J : GrothendieckTopology C) (
K : GrothendieckTopology D) (L : GrothendieckTopology E) [Functor.IsContinuous F
₁ J K] [Functor.IsContinuous F₂ K L] : Functor.IsContinuous (F₁ ⋙ F₂) J L where 
op_comp_isSheaf_of_types G
参数：F₁ : C ⥤ D；F₂ : D ⥤ E；J : GrothendieckTopology C；K : GrothendieckTopology D；L
 : GrothendieckTopology E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf_of_types`：op_comp_isSheaf_of_type
s [Functor.IsContinuous F J K] (G : Sheaf K (Type t)) : Presieve.IsSheaf J (F.op
 ⋙ G.obj)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
-/
lemma isContinuous_comp (F₁ : C ⥤ D) (F₂ : D ⥤ E) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [Functor.IsContinuous F₁ J K] [Functor.IsContinuous F₂ K L] :
    Functor.IsContinuous (F₁ ⋙ F₂) J L where
  op_comp_isSheaf_of_types G :=
    F₁.op_comp_isSheaf_of_types J K
      ⟨_,(isSheaf_iff_isSheaf_of_type _ _).2 (F₂.op_comp_isSheaf_of_types K L G)⟩
/-
**CategoryTheory.Functor.isContinuous_comp'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：isContinuous_comp' {F₁ : C ⥤ D} {F₂ : D ⥤ E} {F₁₂ : C ⥤ E} (e : F₁ ⋙ F₂ ≅ 
F₁₂) (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : Grothendieck
Topology E) [Functor.IsContinuous F₁ J K] [Functor.IsContinuous F₂ K L] : Functo
r.IsContinuous F₁₂ J L
参数：e : F₁ ⋙ F₂ ≅ F₁₂；J : GrothendieckTopology C；K : GrothendieckTopology D；L : G
rothendieckTopology E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isContinuous_comp`：isContinuous_comp (F₁ : C ⥤ D)
 (F₂ : D ⥤ E) (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : Gro
thendieckTopology E) [Functor.…
· 使用引理 `CategoryTheory.Functor.isContinuous_of_iso`：isContinuous_of_iso {F₁ F₂ :
 C ⥤ D} (e : F₁ ≅ F₂) (J : GrothendieckTopology C) (K : GrothendieckTopology D) 
[Functor.IsContinuous F₁ J K] : …
-/
lemma isContinuous_comp' {F₁ : C ⥤ D} {F₂ : D ⥤ E} {F₁₂ : C ⥤ E}
    (e : F₁ ⋙ F₂ ≅ F₁₂) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [Functor.IsContinuous F₁ J K] [Functor.IsContinuous F₂ K L] :
    Functor.IsContinuous F₁₂ J L := by
  have := Functor.isContinuous_comp F₁ F₂ J K L
  apply Functor.isContinuous_of_iso e
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Functor.IsContinuous F J K] :
    Functor.IsContinuous (F ⋙ 𝟭 D) J K := by
  assumption
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Functor.IsContinuous F J K] :
    Functor.IsContinuous (𝟭 C ⋙ F) J K := by
  assumption

/-- To show a functor `F : C ⥤ D` is continuous for the topologies generated by
  precoverage `J` and `K`, it suffices to show that the image of every `J`-covering
  is a `K`-covering, if `F` preserves pairwise pullbacks of `J`-coverings. -/
/-
**CategoryTheory.Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isContinuous_toGrothendieck_of_pullbacksPreservedBy (J : Precoverage C) (K
 : Precoverage D) [J.IsStableUnderBaseChange] [J.HasPullbacks] [K.IsStableUnderB
aseChange] [K.HasPullbacks] [J.PullbacksPreservedBy F] (h : J <= K.comap F) : Fu
nctor.IsContinuous F J.toGrothendieck K.toGrothendieck where op_comp_isSheaf_of_
types
参数：J : Precoverage C；K : Precoverage D；h : J <= K.comap F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Precoverage.toGrothendieck_toCoverage`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] {J : CategoryTheory.Precoverage C} 
  [inst_1 : J.HasPullbacks] [inst_2 : J.Is…
· 使用定理 `CategoryTheory.Presieve.isSheaf_coverage`：isSheaf_coverage (K : Coverage
 C) (P : Cᵒᵖ ⥤ Type*) : Presieve.IsSheaf K.toGrothendieck P ↔ (forall {X : C} (R
 : Presieve X), R in K X -> Pr…
· 使用定理 `CategoryTheory.Precoverage.preservesPairwisePullbacks_of_mem`：∀ {C : Typ
e u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : 
CategoryTheory.Category.{v_2, u_2} D} {J : Categor…
· 使用引理 `CategoryTheory.Precoverage.hasPairwisePullbacks_of_mem`：hasPairwisePullb
acks_of_mem (J : Precoverage C) [J.HasPullbacks] {X : C} {R : Presieve X} (hR : 
R in J X) : R.HasPairwisePullbacks where has…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullback
s`：∀ {C : Type u_4} [inst : CategoryTheory.Category.{u_3, u_4} C] {D : Type u_1}
   [inst_1 : CategoryTheory.Category.{v_1, u_1} D] (F : Categor…
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P

--- 原说明 ---
To show a functor `F : C ⥤ D` is continuous for the topologies generated by
  precoverage `J` and `K`, it suffices to show that the image of every `J`-cover
ing
  is a `K`-covering, if `F` preserves pairwise pullbacks of `J`-coverings.
-/
lemma isContinuous_toGrothendieck_of_pullbacksPreservedBy (J : Precoverage C)
    (K : Precoverage D) [J.IsStableUnderBaseChange] [J.HasPullbacks] [K.IsStableUnderBaseChange]
    [K.HasPullbacks] [J.PullbacksPreservedBy F] (h : J ≤ K.comap F) :
    Functor.IsContinuous F J.toGrothendieck K.toGrothendieck where
  op_comp_isSheaf_of_types := fun ⟨G, H⟩ ↦ by
    rw [isSheaf_iff_isSheaf_of_type] at H
    rw [← Precoverage.toGrothendieck_toCoverage, Presieve.isSheaf_coverage] at H ⊢
    intro X R hR
    have : F.PreservesPairwisePullbacks R := J.preservesPairwisePullbacks_of_mem hR
    have : R.HasPairwisePullbacks := J.hasPairwisePullbacks_of_mem hR
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
    exact H _ (h _ hR)

section

/-
**CategoryTheory.Functor.op_comp_isSheaf_of_preservesOneHypercovers** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：op_comp_isSheaf_of_preservesOneHypercovers [PreservesOneHypercovers.{w} F 
J K] [GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J] (P : Dᵒᵖ ⥤ A) (hP 
: Presheaf.IsSheaf K P) : Presheaf.IsSheaf J (F.op ⋙ P)
参数：P : Dᵒᵖ ⥤ A；hP : Presheaf.IsSheaf K P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presheaf.isSheaf_iff_of_isGeneratedByOneHypercovers`：isSh
eaf_iff_of_isGeneratedByOneHypercovers [GrothendieckTopology.IsGeneratedByOneHyp
ercovers.{w} J] (P : Cᵒᵖ ⥤ A) : IsSheaf J P ↔ forall ⦃X …
-/
lemma op_comp_isSheaf_of_preservesOneHypercovers
    [PreservesOneHypercovers.{w} F J K] [GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J]
    (P : Dᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf K P) :
    Presheaf.IsSheaf J (F.op ⋙ P) := by
  rw [Presheaf.isSheaf_iff_of_isGeneratedByOneHypercovers.{w}]
  intro X E
  exact ⟨(E.toPreOneHypercover.isLimitMapMultiforkEquiv F P)
    ((E.map F K).isLimitMultifork ⟨P, hP⟩)⟩
/-
**CategoryTheory.Functor.isContinuous_of_preservesOneHypercovers** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isContinuous_of_preservesOneHypercovers [PreservesOneHypercovers.{w} F J K
] [GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J] : IsContinuous F J K 
where op_comp_isSheaf_of_types
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf_of_preservesOneHypercovers`：op_co
mp_isSheaf_of_preservesOneHypercovers [PreservesOneHypercovers.{w} F J K] [Groth
endieckTopology.IsGeneratedByOneHypercovers.{w} J] (P :…
-/
lemma isContinuous_of_preservesOneHypercovers
    [PreservesOneHypercovers.{w} F J K] [GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J] :
    IsContinuous F J K where
  op_comp_isSheaf_of_types := by
    rintro ⟨P, hP⟩
    rw [← isSheaf_iff_isSheaf_of_type]
    exact F.op_comp_isSheaf_of_preservesOneHypercovers J K P hP

end

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PreservesOneHypercovers.{max u₁ v₁} F J K] :
    IsContinuous F J K :=
  isContinuous_of_preservesOneHypercovers.{max u₁ v₁} F J K

variable (A)
variable [Functor.IsContinuous F J K]

/-- The induced functor `Sheaf K A ⥤ Sheaf J A` given by `F.op ⋙ _`
if `F` is a continuous functor.
-/
@[simps!]
/-
**CategoryTheory.Functor.sheafPushforwardContinuous** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：sheafPushforwardContinuous : Sheaf K A ⥤ Sheaf J A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf`：op_comp_isSheaf [Functor.IsConti
nuous F J K] (G : Sheaf K A) : Presheaf.IsSheaf J (F.op ⋙ G.obj)

--- 原说明 ---
The induced functor `Sheaf K A ⥤ Sheaf J A` given by `F.op ⋙ _`
if `F` is a continuous functor.
-/
def sheafPushforwardContinuous : Sheaf K A ⥤ Sheaf J A :=
  ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (whiskeringLeft _ _ _).obj F.op)
    (F.op_comp_isSheaf J K)

/-- The functor `F.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A`
is induced by the precomposition with `F.op`. -/
@[simps!]
/-
**CategoryTheory.Functor.sheafPushforwardContinuousCompSheafToPresheafIso** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：sheafPushforwardContinuousCompSheafToPresheafIso : F.sheafPushforwardConti
nuous A J K ⋙ sheafToPresheaf J A ≅ sheafToPresheaf K A ⋙ (whiskeringLeft _ _ _)
.obj F.op
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `F.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A`
is induced by the precomposition with `F.op`.
-/
def sheafPushforwardContinuousCompSheafToPresheafIso :
    F.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A ≅
      sheafToPresheaf K A ⋙ (whiskeringLeft _ _ _).obj F.op := Iso.refl _

/-- The functor `sheafPushforwardContinuous` corresponding to the identity functor
identifies to the identity functor. -/
@[simps!]
/-
**CategoryTheory.Functor.sheafPushforwardContinuousId** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：sheafPushforwardContinuousId : sheafPushforwardContinuous (𝟭 C) A J J ≅ 𝟭 
_
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `sheafPushforwardContinuous` corresponding to the identity functor
identifies to the identity functor.
-/
def sheafPushforwardContinuousId :
    sheafPushforwardContinuous (𝟭 C) A J J ≅ 𝟭 _ := Iso.refl _

/-- The composition of two pushforward functors on sheaves identifies to
the pushforward for the composition of the two functors. -/
@[simps!]
/-
**CategoryTheory.Functor.sheafPushforwardContinuousComp** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：sheafPushforwardContinuousComp [IsContinuous G K L] : letI
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two pushforward functors on sheaves identifies to
the pushforward for the composition of the two functors.
-/
def sheafPushforwardContinuousComp [IsContinuous G K L] :
    letI := isContinuous_comp F G J K L
    sheafPushforwardContinuous G A K L ⋙ sheafPushforwardContinuous F A J K ≅
    sheafPushforwardContinuous (F ⋙ G) A J L := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {F F'} in
/-- The action of a natural transformation on pushforward functors of sheaves. -/
@[simps]
/-
**CategoryTheory.Functor.sheafPushforwardContinuousNatTrans** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：sheafPushforwardContinuousNatTrans [IsContinuous F' J K] : sheafPushforwar
dContinuous F' A J K ⟶ sheafPushforwardContinuous F A J K where app M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of a natural transformation on pushforward functors of sheaves.
-/
def sheafPushforwardContinuousNatTrans [IsContinuous F' J K] :
    sheafPushforwardContinuous F' A J K ⟶ sheafPushforwardContinuous F A J K where
  app M := ⟨whiskerRight (NatTrans.op τ) _⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {F F'} in
/-- The action of a natural isomorphism on pushforward functors of sheaves. -/
@[simps]
/-
**CategoryTheory.Functor.sheafPushforwardContinuousIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：sheafPushforwardContinuousIso [IsContinuous F' J K] : sheafPushforwardCont
inuous F A J K ≅ sheafPushforwardContinuous F' A J K where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of a natural isomorphism on pushforward functors of sheaves.
-/
def sheafPushforwardContinuousIso [IsContinuous F' J K] :
    sheafPushforwardContinuous F A J K ≅ sheafPushforwardContinuous F' A J K where
  hom := sheafPushforwardContinuousNatTrans e.inv _ _ _
  inv := sheafPushforwardContinuousNatTrans e.hom _ _ _
  hom_inv_id := by ext; simp [← Functor.map_comp, ← op_comp]
  inv_hom_id := by ext; simp [← Functor.map_comp, ← op_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-- If a continuous functor between sites is isomorphic to the identity functor,
then the corresponding pushforward functor on sheaves identifies to the
identity functor. -/
@[simps!]
/-
**CategoryTheory.Functor.sheafPushforwardContinuousId'** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：sheafPushforwardContinuousId' [IsContinuous F'' J J] : sheafPushforwardCon
tinuous F'' A J J ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a continuous functor between sites is isomorphic to the identity functor,
then the corresponding pushforward functor on sheaves identifies to the
identity functor.
-/
def sheafPushforwardContinuousId' [IsContinuous F'' J J] :
    sheafPushforwardContinuous F'' A J J ≅ 𝟭 _ :=
  sheafPushforwardContinuousIso eF'' _ _ _ ≪≫ sheafPushforwardContinuousId _ _

set_option backward.isDefEq.respectTransparency.types false in
variable {F G} in
/-- When we have an isomorphism `F ⋙ G ≅ FG` between continuous functors
between sites, the composition of the pushforward functors for
`G` and `F` identifies to the pushforward functor for `FG`. -/
@[simps!]
/-
**CategoryTheory.Functor.sheafPushforwardContinuousComp'** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：sheafPushforwardContinuousComp' [IsContinuous G K L] [IsContinuous FG J L]
 : sheafPushforwardContinuous G A K L ⋙ sheafPushforwardContinuous F A J K ≅ she
afPushforwardContinuous FG A J L
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isContinuous_comp`：isContinuous_comp (F₁ : C ⥤ D)
 (F₂ : D ⥤ E) (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : Gro
thendieckTopology E) [Functor.…

--- 原说明 ---
When we have an isomorphism `F ⋙ G ≅ FG` between continuous functors
between sites, the composition of the pushforward functors for
`G` and `F` identifies to the pushforward functor for `FG`.
-/
def sheafPushforwardContinuousComp'
    [IsContinuous G K L] [IsContinuous FG J L] :
    sheafPushforwardContinuous G A K L ⋙ sheafPushforwardContinuous F A J K ≅
    sheafPushforwardContinuous FG A J L :=
  letI := isContinuous_comp F G J K L
  sheafPushforwardContinuousComp _ _ _ _ _ _ ≪≫ sheafPushforwardContinuousIso eFG _ _ _

end Functor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F ⊣ G` is an adjunction between continuous functors, the associated
pushforwards on sheaves are adjoint. -/
@[simps!]
/-
**CategoryTheory.Adjunction.sheafPushforwardContinuous** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Adjunction`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {E : Typ
e u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} E] →             {F
 : CategoryTheory.Functor C D} →               {G : CategoryTheory.Functor D C} 
→                 (F ⊣ G) →                   (J : CategoryTheory.GrothendieckTo
pology C) →                     (K : CategoryTheory.GrothendieckTopology D) →   
                    [inst_3 : F.IsContinuous J K] →                         [ins
t_4 : G.IsContinuous K J] →                           F.sheafPushforwardContinuo
us E J K ⊣ G.sheafPushforwardContinuous E K J
参数：F ⊣ G；J : CategoryTheory.GrothendieckTopology C；K : CategoryTheory.Grothendie
ckTopology D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F ⊣ G` is an adjunction between continuous functors, the associated
pushforwards on sheaves are adjoint.
-/
def Adjunction.sheafPushforwardContinuous {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
    [G.IsContinuous K J] :
    F.sheafPushforwardContinuous E J K ⊣ G.sheafPushforwardContinuous E K J where
  unit.app P := { hom := (adj.op.whiskerLeft _).unit.app P.obj }
  counit.app P := { hom := (adj.op.whiskerLeft _).counit.app P.obj }
  left_triangle_components P := by
    ext : 1
    exact (adj.op.whiskerLeft _).left_triangle_components P.obj
  right_triangle_components P := by
    ext : 1
    exact (adj.op.whiskerLeft _).right_triangle_components P.obj

end CategoryTheory

