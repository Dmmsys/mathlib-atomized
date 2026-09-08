/-
Copyright (c) 2026 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!

# Weakly étale morphisms

A morphism of schemes is weakly étale if it is flat and its diagonal is flat. As
the name suggests any étale morphism is weakly étale and every weakly étale
morphism of finite presentation is étale.

## Main definitions

- `AlgebraicGeometry.WeaklyEtale`: The class of weakly étale morphisms.

## TODOs

- When weakly étale ring homomorphisms are in mathlib, show
  `HasRingHomProperty WeaklyEtale RingHom.WeaklyEtale` (@chrisflav).
- Deduce from this that weakly étale morphisms of finite presentation are étale (@chrisflav).

-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {W X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism is weakly étale if it is flat and the diagonal map is flat. -/
@[mk_iff, stacks 094P]
/-
**AlgebraicGeometry.WeaklyEtale** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeometry`。
形式化陈述：WeaklyEtale : Prop where flat : Flat f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism is weakly étale if it is flat and the diagonal map is flat.
-/
class WeaklyEtale : Prop where
  flat : Flat f := by infer_instance
  flat_diagonal : Flat (pullback.diagonal f) := by infer_instance

namespace WeaklyEtale

attribute [instance] flat flat_diagonal

/-
**AlgebraicGeometry.WeaklyEtale.weaklyEtale_eq_flat_inf_diagonal_flat** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicGeometry.WeaklyEtale`。
形式化陈述：weaklyEtale_eq_flat_inf_diagonal_flat : @WeaklyEtale = (@Flat ⊓ MorphismPr
operty.diagonal @Flat : MorphismProperty Scheme.{u})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.weaklyEtale_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f
 : X ⟶ Y),   AlgebraicGeometry.WeaklyEtale f ↔     autoParam (AlgebraicGeometry.
Flat f) AlgebraicGeomet…
-/
theorem weaklyEtale_eq_flat_inf_diagonal_flat :
    @WeaklyEtale = (@Flat ⊓ MorphismProperty.diagonal @Flat : MorphismProperty Scheme.{u}) := by
  ext
  exact weaklyEtale_iff _

/-- Etale morphisms are weakly étale. -/
/-
**AlgebraicGeometry.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.We
aklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Etale morphisms are weakly étale.
-/
instance (priority := 900) [Etale f] : WeaklyEtale f where

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.We
aklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.RespectsIso @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.We
aklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.We
aklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WeaklyEtale f] [WeaklyEtale g] : WeaklyEtale (f ≫ g) :=
  MorphismProperty.comp_mem _ f g inferInstance inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.We
aklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsStableUnderBaseChange @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.We
aklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtSource @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.We
aklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtTarget @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.We
aklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [WeaklyEtale g] :
    WeaklyEtale (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.We
aklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [WeaklyEtale f] :
    WeaklyEtale (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance
/-
**AlgebraicGeometry.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.We
aklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [WeaklyEtale f] : WeaklyEtale (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V
/-
**AlgebraicGeometry.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.We
aklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [WeaklyEtale f] :
    WeaklyEtale (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

/-- This proof is by `inferInstance` and the argument goes through
`IsImmersion (diagonal f) → Mono (diagonal f) → IsIso (diagonal (diagonal f))`. -/
/-
**AlgebraicGeometry.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.We
aklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This proof is by `inferInstance` and the argument goes through
`IsImmersion (diagonal f) → Mono (diagonal f) → IsIso (diagonal (diagonal f))`.
-/
instance (f : X ⟶ Y) [WeaklyEtale f] : WeaklyEtale (pullback.diagonal f) where

set_option backward.isDefEq.respectTransparency.types false in
@[stacks 0951]
/-
**AlgebraicGeometry.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.We
aklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty @WeaklyEtale @WeaklyEtale := by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f hf
  exact inferInstanceAs <| WeaklyEtale (pullback.diagonal f)
/-
**AlgebraicGeometry.WeaklyEtale.of_comp** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.WeaklyEtale`。
形式化陈述：of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [WeaklyEtale (f ≫ g)] [WeaklyEtale g] : We
aklyEtale f
参数：f : X ⟶ Y；g : Y ⟶ Z；f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `AlgebraicGeometry.WeaklyEtale.instHasOfPostcompPropertyScheme`：CategoryT
heory.MorphismProperty.HasOfPostcompProperty @AlgebraicGeometry.WeaklyEtale @Alg
ebraicGeometry.WeaklyEtale
-/
lemma of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [WeaklyEtale (f ≫ g)] [WeaklyEtale g] : WeaklyEtale f :=
  MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

end WeaklyEtale

/-
**AlgebraicGeometry.etale_le_weaklyEtale** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：etale_le_weaklyEtale : @Etale <= @WeaklyEtale
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.WeaklyEtale.instOfEtale`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.Etale f], AlgebraicGeometry.WeaklyEtale f
-/
lemma etale_le_weaklyEtale : @Etale ≤ @WeaklyEtale :=
  fun _ _ _ _ ↦ inferInstance

end AlgebraicGeometry

