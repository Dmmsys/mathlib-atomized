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

/-
**Filter.EventuallyLE.mul_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`
。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : MulZeroClass β] [inst_1 : Preorder β] 
[PosMulMono β] [MulPosMono β] {l : Filter α}   {f₁ f₂ g₁ g₂ : α → β}, f₁ ≤ᶠ[l] f
₂ → g₁ ≤ᶠ[l] g₂ → 0 ≤ᶠ[l] g₁ → 0 ≤ᶠ[l] f₂ → f₁ * g₁ ≤ᶠ[l] f₂ * g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
-/
theorem EventuallyLE.mul_le_mul [MulZeroClass β] [Preorder β] [PosMulMono β] [MulPosMono β]
    {l : Filter α} {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) (hg₀ : 0 ≤ᶠ[l] g₁)
    (hf₀ : 0 ≤ᶠ[l] f₂) : f₁ * g₁ ≤ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg, hg₀, hf₀] with x using _root_.mul_le_mul

@[to_additive EventuallyLE.add_le_add]
/-
**Filter.EventuallyLE.mul_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE
`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Mul β] [inst_1 : Preorder β] [MulLeftM
ono β] [MulRightMono β] {l : Filter α}   {f₁ f₂ g₁ g₂ : α → β}, f₁ ≤ᶠ[l] f₂ → g₁
 ≤ᶠ[l] g₂ → f₁ * g₁ ≤ᶠ[l] f₂ * g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
-/
theorem EventuallyLE.mul_le_mul' [Mul β] [Preorder β] [MulLeftMono β]
    [MulRightMono β] {l : Filter α} {f₁ f₂ g₁ g₂ : α → β}
    (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) : f₁ * g₁ ≤ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg] with x hfx hgx using _root_.mul_le_mul' hfx hgx
/-
**Filter.EventuallyLE.mul_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`
。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Semiring β] [inst_1 : PartialOrder β] 
[IsOrderedRing β] {l : Filter α}   {f g : α → β}, 0 ≤ᶠ[l] f → 0 ≤ᶠ[l] g → 0 ≤ᶠ[l
] f * g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem EventuallyLE.mul_nonneg [Semiring β] [PartialOrder β] [IsOrderedRing β]
    {l : Filter α} {f g : α → β} (hf : 0 ≤ᶠ[l] f)
    (hg : 0 ≤ᶠ[l] g) : 0 ≤ᶠ[l] f * g := by filter_upwards [hf, hg] with x using _root_.mul_nonneg
/-
**Filter.eventually_sub_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_sub_nonneg [AddGroup β] [LE β] [AddRightMono β] {l : Filter α} 
{f g : α -> β} : 0 <=ᶠ[l] g - f ↔ f <=ᶠ[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
-/
theorem eventually_sub_nonneg [AddGroup β] [LE β] [AddRightMono β]
    {l : Filter α} {f g : α → β} :
    0 ≤ᶠ[l] g - f ↔ f ≤ᶠ[l] g :=
  eventually_congr <| Eventually.of_forall fun _ => sub_nonneg

namespace Germ

variable {l : Filter α}

/-
**Filter.Germ.instIsOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instIsOrderedRing [Semiring β] [PartialOrder β] [IsOrderedRing β] : IsOrde
redRing (Germ l β) where zero_le_one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.instIsOrderedAddMonoid`：∀ {α : Type u_1} {β : Type u_2} {l :
 Filter α} [inst : AddCommMonoid β] [inst_1 : Preorder β] [IsOrderedAddMonoid β]
,   IsOrderedAddMonoid (…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Filter.Germ.const_le`：const_le [LE β] {x y : β} : x <= y -> (↑x : Germ l
 β) <= ↑y
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Filter.Germ.inductionOn`：inductionOn (f : Germ l β) {p : Germ l β -> Pro
p} (h : forall f : α -> β, p f) : p f
· 使用定理 `Filter.Germ.inductionOn₂`：inductionOn₂ (f : Germ l β) (g : Germ l γ) {p 
: Germ l β -> Germ l γ -> Prop} (h : forall (f : α -> β) (g : α -> γ), p f g) : 
p f g
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
-/
instance instIsOrderedRing [Semiring β] [PartialOrder β] [IsOrderedRing β] :
    IsOrderedRing (Germ l β) where
  zero_le_one := const_le zero_le_one
  mul_le_mul_of_nonneg_left x :=
    inductionOn x fun _f hx y z ↦ inductionOn₂ y z fun _g _h hfg ↦ hx.mp <| hfg.mono
      fun _a ↦ mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right x :=
    inductionOn x fun _f hx y z ↦ inductionOn₂ y z fun _g _h hfg ↦ hx.mp <| hfg.mono
      fun _a ↦ mul_le_mul_of_nonneg_right

end Germ

end Filter

