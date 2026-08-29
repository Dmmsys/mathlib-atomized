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
/--
Definition of `WeaklyEtale` / `WeaklyEtale` 的定义

English:
class WeaklyEtale
  parameters: : Prop where
  axioms and operations (2):
    - flat : Flat f  [default: by infer_instance]
    - flat_diagonal : Flat (pullback.diagonal f)  [default: by infer_instance]

中文:
类 WeaklyEtale
  参数: : 命题 where
  公理与运算 (2 个):
    - flat : Flat f  [默认: by infer_instance]
    - flat_diagonal : Flat (pullback.diagonal f)  [默认: by infer_instance]

Depends on / 依赖: diagonal, flat_diagonal, infer_instance, pullback, pullback.diagonal
-/
class WeaklyEtale : Prop where
  flat : Flat f := by infer_instance
  flat_diagonal : Flat (pullback.diagonal f) := by infer_instance

namespace WeaklyEtale

attribute [instance] flat flat_diagonal

/--
theorem `weaklyEtale_eq_flat_inf_diagonal_flat` / 定理 `weaklyEtale_eq_flat_inf_diagonal_flat`

English:
theorem weaklyEtale_eq_flat_inf_diagonal_flat
  proof: by
  ext
  exact weaklyEtale_iff _

中文:
定理 weaklyEtale_eq_flat_inf_diagonal_flat
  证明: by
  ext
  exact weaklyEtale_iff _

Depends on / 依赖: weaklyEtale_iff
-/
theorem weaklyEtale_eq_flat_inf_diagonal_flat :
    @WeaklyEtale = (@Flat ⊓ MorphismProperty.diagonal @Flat : MorphismProperty Scheme.{u}) := by
  ext
  exact weaklyEtale_iff _

/-- Etale morphisms are weakly étale. -/
instance (priority := 900) [Etale f] : WeaklyEtale f where

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.RespectsIso @WeaklyEtale
  body: by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

中文:
实例 :
  签名: Morphism命题erty.RespectsIso @WeaklyEtale
  定义体: by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

Depends on / 依赖: infer_instance, weaklyEtale_eq_flat_inf_diagonal_flat
-/
instance : MorphismProperty.RespectsIso @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @WeaklyEtale
  body: by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

中文:
实例 :
  签名: Morphism命题erty.IsMultiplicative @WeaklyEtale
  定义体: by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

Depends on / 依赖: infer_instance, weaklyEtale_eq_flat_inf_diagonal_flat
-/
instance : MorphismProperty.IsMultiplicative @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WeaklyEtale
  signature: f] [WeaklyEtale g] : WeaklyEtale (f ≫ g)
  body: MorphismProperty.comp_mem _ f g inferInstance inferInstance

中文:
实例 [WeaklyEtale
  签名: f] [WeaklyEtale g] : WeaklyEtale (f ≫ g)
  定义体: MorphismProperty.comp_mem _ f g inferInstance inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.comp_mem, comp_mem
-/
instance [WeaklyEtale f] [WeaklyEtale g] : WeaklyEtale (f ≫ g) :=
  MorphismProperty.comp_mem _ f g inferInstance inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsStableUnderBaseChange @WeaklyEtale
  body: by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

中文:
实例 :
  签名: Morphism命题erty.IsStableUnderBaseChange @WeaklyEtale
  定义体: by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

Depends on / 依赖: infer_instance, weaklyEtale_eq_flat_inf_diagonal_flat
-/
instance : MorphismProperty.IsStableUnderBaseChange @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtSource @WeaklyEtale
  body: by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

中文:
实例 :
  签名: IsZariskiLocalAtSource @WeaklyEtale
  定义体: by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

Depends on / 依赖: infer_instance, weaklyEtale_eq_flat_inf_diagonal_flat
-/
instance : IsZariskiLocalAtSource @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtTarget @WeaklyEtale
  body: by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

中文:
实例 :
  签名: IsZariskiLocalAtTarget @WeaklyEtale
  定义体: by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

Depends on / 依赖: infer_instance, weaklyEtale_eq_flat_inf_diagonal_flat
-/
instance : IsZariskiLocalAtTarget @WeaklyEtale := by
  rw [weaklyEtale_eq_flat_inf_diagonal_flat]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [WeaklyEtale g] :
    WeaklyEtale (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [WeaklyEtale f] :
    WeaklyEtale (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [WeaklyEtale f] : WeaklyEtale (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [WeaklyEtale f] :
    WeaklyEtale (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

/-- This proof is by `inferInstance` and the argument goes through
`IsImmersion (diagonal f) → Mono (diagonal f) → IsIso (diagonal (diagonal f))`. -/
instance (f : X ⟶ Y) [WeaklyEtale f] : WeaklyEtale (pullback.diagonal f) where

set_option backward.isDefEq.respectTransparency.types false in
@[stacks 0951]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty @WeaklyEtale @WeaklyEtale
  body: by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f hf
exact inferInstanceAs WeaklyEtale (pullback.diagonal f)

中文:
实例 :
  签名: Morphism命题erty.HasOfPostcomp命题erty @WeaklyEtale @WeaklyEtale
  定义体: by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f hf
exact inferInstanceAs WeaklyEtale (pullback.diagonal f)

Depends on / 依赖: MorphismProperty, MorphismProperty.hasOfPostcompProperty_iff_le_diagonal, WeaklyEtale, diagonal, hasOfPostcompProperty_iff_le_diagonal, pullback, pullback.diagonal, truncation
-/
instance : MorphismProperty.HasOfPostcompProperty @WeaklyEtale @WeaklyEtale := by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f hf
exact inferInstanceAs WeaklyEtale (pullback.diagonal f)

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  given: (f : X ⟶ Y) (g : Y ⟶ Z) [WeaklyEtale (f ≫ g)] [WeaklyEtale g]
  statement: WeaklyEtale f
  proof: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

中文:
引理 of_comp
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) [WeaklyEtale (f ≫ g)] [WeaklyEtale g]
  结论: WeaklyEtale f
  证明: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

Depends on / 依赖: MorphismProperty, MorphismProperty.of_postcomp, of_postcomp
-/
lemma of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [WeaklyEtale (f ≫ g)] [WeaklyEtale g] : WeaklyEtale f :=
  MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

end WeaklyEtale

/--
lemma `etale_le_weaklyEtale` / 引理 `etale_le_weaklyEtale`

English:
lemma etale_le_weaklyEtale
  statement: @Etale <= @WeaklyEtale
  proof: fun _ _ _ _ => inferInstance

中文:
引理 etale_le_weaklyEtale
  结论: @Etale <= @WeaklyEtale
  证明: fun _ _ _ _ => inferInstance
-/
lemma etale_le_weaklyEtale : @Etale <= @WeaklyEtale :=
  fun _ _ _ _ => inferInstance

end AlgebraicGeometry
