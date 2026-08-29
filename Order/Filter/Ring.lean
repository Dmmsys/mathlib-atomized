/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.Germ.OrderedMonoid
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Lemmas about filters and ordered rings.
-/

public section
namespace Filter

open Function Filter

universe u v

variable {α : Type u} {β : Type v}

/--
theorem `EventuallyLE.mul_le_mul` / 定理 `EventuallyLE.mul_le_mul`

English:
theorem EventuallyLE.mul_le_mul
  statement: [MulZeroClass β] [Preorder β] [PosMulMono β] [MulPosMono β]
  proof: by
  filter_upwards [hf, hg, hg₀, hf₀] with x using _root_.mul_le_mul

@[to_additive EventuallyLE.add_le_add]

中文:
定理 EventuallyLE.mul_le_mul
  结论: [乘零类 β] [预序 β] [正乘递增 β] [乘正递增 β]
  证明: by
  filter_upwards [hf, hg, hg₀, hf₀] with x using _root_.mul_le_mul

@[to_additive EventuallyLE.add_le_add]

Depends on / 依赖: _root_, _root_.mul_le_mul, filter_upwards, mul_le_mul
-/
theorem EventuallyLE.mul_le_mul [MulZeroClass β] [Preorder β] [PosMulMono β] [MulPosMono β]
    {l : Filter α} {f₁ f₂ g₁ g₂ : α -> β} (hf : f₁ <=ᶠ[l] f₂) (hg : g₁ <=ᶠ[l] g₂) (hg₀ : 0 <=ᶠ[l] g₁)
    (hf₀ : 0 <=ᶠ[l] f₂) : f₁ * g₁ <=ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg, hg₀, hf₀] with x using _root_.mul_le_mul

@[to_additive EventuallyLE.add_le_add]
/--
theorem `EventuallyLE.mul_le_mul'` / 定理 `EventuallyLE.mul_le_mul'`

English:
theorem EventuallyLE.mul_le_mul'
  statement: [Mul β] [Preorder β] [MulLeftMono β]
  proof: by
  filter_upwards [hf, hg] with x hfx hgx using _root_.mul_le_mul' hfx hgx

中文:
定理 EventuallyLE.mul_le_mul'
  结论: [乘法 β] [预序 β] [MulLeftMono β]
  证明: by
  filter_upwards [hf, hg] with x hfx hgx using _root_.mul_le_mul' hfx hgx

Depends on / 依赖: _root_, _root_.mul_le_mul, filter_upwards, mul_le_mul
-/
theorem EventuallyLE.mul_le_mul' [Mul β] [Preorder β] [MulLeftMono β]
    [MulRightMono β] {l : Filter α} {f₁ f₂ g₁ g₂ : α -> β}
    (hf : f₁ <=ᶠ[l] f₂) (hg : g₁ <=ᶠ[l] g₂) : f₁ * g₁ <=ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg] with x hfx hgx using _root_.mul_le_mul' hfx hgx

/--
theorem `EventuallyLE.mul_nonneg` / 定理 `EventuallyLE.mul_nonneg`

English:
theorem EventuallyLE.mul_nonneg
  statement: [Semiring β] [PartialOrder β] [IsOrderedRing β]
  proof: by filter_upwards [hf, hg] with x using _root_.mul_nonneg

中文:
定理 EventuallyLE.mul_nonneg
  结论: [半环 β] [偏序 β] [是Ordered环 β]
  证明: by filter_upwards [hf, hg] with x using _root_.mul_nonneg

Depends on / 依赖: _root_, _root_.mul_nonneg, filter_upwards, mul_nonneg
-/
theorem EventuallyLE.mul_nonneg [Semiring β] [PartialOrder β] [IsOrderedRing β]
    {l : Filter α} {f g : α -> β} (hf : 0 <=ᶠ[l] f)
    (hg : 0 <=ᶠ[l] g) : 0 <=ᶠ[l] f * g := by filter_upwards [hf, hg] with x using _root_.mul_nonneg

/--
theorem `eventually_sub_nonneg` / 定理 `eventually_sub_nonneg`

English:
theorem eventually_sub_nonneg
  statement: [AddGroup β] [LE β] [AddRightMono β]
  proof: eventually_congr Eventually.of_forall fun _ => sub_nonneg

中文:
定理 eventually_sub_nonneg
  结论: [加法群 β] [LE β] [AddRightMono β]
  证明: eventually_congr Eventually.of_forall fun _ => sub_nonneg

Depends on / 依赖: Eventually, Eventually.of_forall, eventually_congr, of_forall, sub_nonneg
-/
theorem eventually_sub_nonneg [AddGroup β] [LE β] [AddRightMono β]
    {l : Filter α} {f g : α -> β} :
    0 <=ᶠ[l] g - f ↔ f <=ᶠ[l] g :=
eventually_congr Eventually.of_forall fun _ => sub_nonneg

namespace Germ

variable {l : Filter α}

/--
Instance `instIsOrderedRing` / 实例 `instIsOrderedRing`

English:
instance instIsOrderedRing
  signature: [Semiring β] [PartialOrder β] [IsOrderedRing β]
  body: const_le zero_le_one
  mul_le_mul_of_nonneg_left x :=
inductionOn x fun _f hx y z => inductionOn₂ y z fun _g _h hfg => hx.mp hfg.mono
      fun _a => mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right x :=
inductionOn x fun _f hx y z => inductionOn₂ y z fun _g _h hfg => hx.mp hfg.mono
      fun 

中文:
实例 instIsOrderedRing
  签名: [半环 β] [偏序 β] [是Ordered环 β]
  定义体: const_le zero_le_one
  mul_le_mul_of_nonneg_left x :=
inductionOn x fun _f hx y z => inductionOn₂ y z fun _g _h hfg => hx.mp hfg.mono
      fun _a => mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right x :=
inductionOn x fun _f hx y z => inductionOn₂ y z fun _g _h hfg => hx.mp hfg.mono
      fun 

Depends on / 依赖: const_le, zero_le_one
-/
instance instIsOrderedRing [Semiring β] [PartialOrder β] [IsOrderedRing β] :
    IsOrderedRing (Germ l β) where
  zero_le_one := const_le zero_le_one
  mul_le_mul_of_nonneg_left x :=
inductionOn x fun _f hx y z => inductionOn₂ y z fun _g _h hfg => hx.mp hfg.mono
      fun _a => mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right x :=
inductionOn x fun _f hx y z => inductionOn₂ y z fun _g _h hfg => hx.mp hfg.mono
      fun _a => mul_le_mul_of_nonneg_right

end Germ

end Filter
