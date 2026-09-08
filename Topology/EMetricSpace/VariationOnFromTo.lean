/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Signed variation

We define `variationOnFromTo f s a b : ℝ` as the signed variation of `f` between `a` and `b`, i.e.,
its variation if `a ≤ b`, and its opposite otherwise. We establish basic properties of this notion,
and use it to show that a bounded variation real function is the difference of two monotone
functions.
 -/

@[expose] public section

open scoped ENNReal Topology
open Set Filter

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]

/-- The **signed** variation of `f` on the interval `Icc a b` intersected with the set `s`,
squashed to a real (therefore only really meaningful if the variation is finite)
-/
/-
**variationOnFromTo** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：variationOnFromTo (f : α -> E) (s : Set α) (a b : α) : Real
参数：f : α -> E；s : Set α；a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **signed** variation of `f` on the interval `Icc a b` intersected with the s
et `s`,
squashed to a real (therefore only really meaningful if the variation is finite)
-/
noncomputable def variationOnFromTo (f : α → E) (s : Set α) (a b : α) : ℝ :=
  if a ≤ b then (eVariationOn f (s ∩ Icc a b)).toReal else -(eVariationOn f (s ∩ Icc b a)).toReal

namespace variationOnFromTo

variable (f : α → E) (s : Set α)

/-
**variationOnFromTo.self** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] (f : α → E) (s : Set α) (a : α),   variationOnFromTo f s a a = 0
参数：f : α → E；s : Set α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_zero`：ENNReal.toReal 0 = 0
-/
protected theorem self (a : α) : variationOnFromTo f s a a = 0 := by
  dsimp only [variationOnFromTo]
  rw [if_pos le_rfl, Icc_self, eVariationOn.subsingleton, ENNReal.toReal_zero]
  exact fun x hx y hy => hx.2.trans hy.2.symm
/-
**variationOnFromTo.nonneg_of_le** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] (f : α → E) (s : Set α)   {a b : α}, a ≤ b → 0 ≤ variationOnFromTo 
f s a b
参数：f : α → E；s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
protected theorem nonneg_of_le {a b : α} (h : a ≤ b) : 0 ≤ variationOnFromTo f s a b := by
  simp only [variationOnFromTo, if_pos h, ENNReal.toReal_nonneg]
/-
**variationOnFromTo.eq_neg_swap** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] (f : α → E) (s : Set α)   (a b : α), variationOnFromTo f s a b = -v
ariationOnFromTo f s b a
参数：f : α → E；s : Set α；a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `variationOnFromTo.self`：∀ {α : Type u_1} [inst : LinearOrder α] {E : Typ
e u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α) (a : α),   variat
ionOnFromTo …
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
protected theorem eq_neg_swap (a b : α) :
    variationOnFromTo f s a b = -variationOnFromTo f s b a := by
  rcases lt_trichotomy a b with (ab | rfl | ba)
  · simp only [variationOnFromTo, if_pos ab.le, if_neg ab.not_ge, neg_neg]
  · simp only [variationOnFromTo.self, neg_zero]
  · simp only [variationOnFromTo, if_pos ba.le, if_neg ba.not_ge]
/-
**variationOnFromTo.nonpos_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] (f : α → E) (s : Set α)   {a b : α}, b ≤ a → variationOnFromTo f s 
a b ≤ 0
参数：f : α → E；s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `variationOnFromTo.eq_neg_swap`：∀ {α : Type u_1} [inst : LinearOrder α] {
E : Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   (a b : α
), variationOnFromT…
· 使用定理 `neg_nonpos_of_nonneg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : P
artialOrder α] [IsOrderedAddMonoid α] {a : α}, 0 ≤ a → -a ≤ 0
· 使用定理 `variationOnFromTo.nonneg_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] 
{E : Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : 
α}, a ≤ b → 0 ≤ vari…
-/
protected theorem nonpos_of_ge {a b : α} (h : b ≤ a) : variationOnFromTo f s a b ≤ 0 := by
  rw [variationOnFromTo.eq_neg_swap]
  exact neg_nonpos_of_nonneg (variationOnFromTo.nonneg_of_le f s h)

variable {f s} in
/-
**variationOnFromTo.abs_le_eVariationOn** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFr
omTo`。
形式化陈述：abs_le_eVariationOn (hf : BoundedVariationOn f s) {a b : α} : |variationOn
FromTo f s a b| <= (eVariationOn f s).toReal
参数：hf : BoundedVariationOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.abs_toReal`：abs_toReal {x : Real>=0∞} : |x.toReal| = x.toReal
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `eVariationOn.mono`：mono (f : α -> E) {s t : Set α} (hst : t subseteq s) 
: eVariationOn f t <= eVariationOn f s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
theorem abs_le_eVariationOn (hf : BoundedVariationOn f s) {a b : α} :
    |variationOnFromTo f s a b| ≤ (eVariationOn f s).toReal := by
  by_cases hab : a ≤ b
  · simp only [variationOnFromTo, hab, ↓reduceIte, ENNReal.abs_toReal]
    exact ENNReal.toReal_mono hf (eVariationOn.mono _ inter_subset_left)
  · simp only [variationOnFromTo, hab, ↓reduceIte, abs_neg, ENNReal.abs_toReal]
    exact ENNReal.toReal_mono hf (eVariationOn.mono _ inter_subset_left)
/-
**variationOnFromTo.eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] (f : α → E) (s : Set α)   {a b : α}, a ≤ b → variationOnFromTo f s 
a b = (eVariationOn f (s ∩ Set.Icc a b)).toReal
参数：f : α → E；s : Set α；eVariationOn f (s ∩ Set.Icc a b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
protected theorem eq_of_le {a b : α} (h : a ≤ b) :
    variationOnFromTo f s a b = (eVariationOn f (s ∩ Icc a b)).toReal :=
  if_pos h
/-
**variationOnFromTo.eq_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] (f : α → E) (s : Set α)   {a b : α}, b ≤ a → variationOnFromTo f s 
a b = -(eVariationOn f (s ∩ Set.Icc b a)).toReal
参数：f : α → E；s : Set α；eVariationOn f (s ∩ Set.Icc b a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `variationOnFromTo.eq_neg_swap`：∀ {α : Type u_1} [inst : LinearOrder α] {
E : Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   (a b : α
), variationOnFromT…
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `variationOnFromTo.eq_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {E :
 Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : α}, 
a ≤ b → variatio…
-/
protected theorem eq_of_ge {a b : α} (h : b ≤ a) :
    variationOnFromTo f s a b = -(eVariationOn f (s ∩ Icc b a)).toReal := by
  rw [variationOnFromTo.eq_neg_swap, neg_inj, variationOnFromTo.eq_of_le f s h]
/-
**variationOnFromTo.add** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] {f : α → E} {s : Set α},   LocallyBoundedVariationOn f s →     ∀ {a
 b c : α},       a ∈ s → b ∈ s → c ∈ s → variationOnFromTo f s a b + variationOn
FromTo f s b c = variationOnFromTo f s a c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `additive_of_total`：∀ {α : Type u_1} {β : Type u_2} [inst : AddMonoid β] 
(r : α → α → Prop) [Std.Total r] (f : α → α → β) (p : α → Prop),   (∀ {a b : α},
 p a → …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `variationOnFromTo.eq_neg_swap`：∀ {α : Type u_1} [inst : LinearOrder α] {
E : Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   (a b : α
), variationOnFromT…
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `variationOnFromTo.eq_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {E :
 Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : α}, 
a ≤ b → variatio…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `eVariationOn.Icc_add_Icc`：Icc_add_Icc (f : α -> E) {s : Set α} {a b c : 
α} (hab : a <= b) (hbc : b <= c) (hb : b in s) : eVariationOn f (s inter Icc a b
) + eVariation…
-/
protected theorem add {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    variationOnFromTo f s a b + variationOnFromTo f s b c = variationOnFromTo f s a c := by
  symm
  refine additive_of_total (· ≤ · : α → α → Prop) (variationOnFromTo f s) (· ∈ s) ?_ ?_ ha hb hc
  · rintro x y _xs _ys
    simp only [variationOnFromTo.eq_neg_swap f s y x, add_neg_cancel]
  · rintro x y z xy yz xs ys zs
    rw [variationOnFromTo.eq_of_le f s xy, variationOnFromTo.eq_of_le f s yz,
      variationOnFromTo.eq_of_le f s (xy.trans yz),
      ← ENNReal.toReal_add (hf x y xs ys) (hf y z ys zs), eVariationOn.Icc_add_Icc f xy yz ys]
/-
**variationOnFromTo.sub_right** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] {f : α → E} {s : Set α},   LocallyBoundedVariationOn f s →     ∀ {a
 b c : α},       a ∈ s → b ∈ s → c ∈ s → variationOnFromTo f s a b - variationOn
FromTo f s a c = variationOnFromTo f s c b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `variationOnFromTo.add`：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type
 u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   LocallyBoundedV
ariationOn …
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
protected theorem sub_right {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    variationOnFromTo f s a b - variationOnFromTo f s a c = variationOnFromTo f s c b := by
  rw [← variationOnFromTo.add hf ha hc hb, add_sub_cancel_left]
/-
**variationOnFromTo.sub_left** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] {f : α → E} {s : Set α},   LocallyBoundedVariationOn f s →     ∀ {a
 b c : α},       a ∈ s → b ∈ s → c ∈ s → variationOnFromTo f s a b - variationOn
FromTo f s c b = variationOnFromTo f s a c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `variationOnFromTo.add`：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type
 u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   LocallyBoundedV
ariationOn …
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
protected theorem sub_left {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    variationOnFromTo f s a b - variationOnFromTo f s c b = variationOnFromTo f s a c := by
  rw [← variationOnFromTo.add hf ha hc hb, add_sub_cancel_right]

variable {f s} in
/-
**variationOnFromTo.edist_zero_of_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `variationOn
FromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] {f : α → E} {s : Set α},   LocallyBoundedVariationOn f s → ∀ {a b :
 α}, a ∈ s → b ∈ s → variationOnFromTo f s a b = 0 → edist (f a) (f b) = 0
参数：f a；f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `variationOnFromTo.eq_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {E :
 Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : α}, 
a ≤ b → variatio…
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `eVariationOn.edist_le`：edist_le (f : α -> E) {s : Set α} {x y : α} (hx :
 x in s) (hy : y in s) : edist (f x) (f y) <= eVariationOn f s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `variationOnFromTo.eq_neg_swap`：∀ {α : Type u_1} [inst : LinearOrder α] {
E : Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   (a b : α
), variationOnFromT…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
protected theorem edist_zero_of_eq_zero (hf : LocallyBoundedVariationOn f s)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : variationOnFromTo f s a b = 0) :
    edist (f a) (f b) = 0 := by
  wlog h' : a ≤ b
  · rw [edist_comm]
    apply this hf hb ha _ (le_of_not_ge h')
    rw [variationOnFromTo.eq_neg_swap, h, neg_zero]
  · rw [← nonpos_iff_eq_zero, ← ENNReal.ofReal_zero, ← h, variationOnFromTo.eq_of_le f s h',
      ENNReal.ofReal_toReal (hf a b ha hb)]
    apply eVariationOn.edist_le
    exacts [⟨ha, ⟨le_rfl, h'⟩⟩, ⟨hb, ⟨h', le_rfl⟩⟩]
/-
**variationOnFromTo.eq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] {f : α → E} {s : Set α},   LocallyBoundedVariationOn f s →     ∀ {a
 b c : α},       a ∈ s → b ∈ s → c ∈ s → (variationOnFromTo f s a b = variationO
nFromTo f s a c ↔ variationOnFromTo f s b c = 0)
参数：variationOnFromTo f s a b = variationOnFromTo f s a c ↔ variationOnFromTo f s
 b c = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `variationOnFromTo.add`：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type
 u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   LocallyBoundedV
ariationOn …
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem eq_left_iff {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b c : α} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    variationOnFromTo f s a b = variationOnFromTo f s a c ↔ variationOnFromTo f s b c = 0 := by
  simp only [← variationOnFromTo.add hf ha hb hc, left_eq_add]
/-
**variationOnFromTo.eq_zero_iff_of_le** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFrom
To`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] {f : α → E} {s : Set α},   LocallyBoundedVariationOn f s →     ∀ {a
 b : α},       a ∈ s →         b ∈ s →           a ≤ b →             (variationO
nFromTo f s a b = 0 ↔               ∀ ⦃x : α⦄, x ∈ s ∩ Set.Icc a b → ∀ ⦃y : α⦄, 
y ∈ s ∩ Set.Icc a b → edist (f x) (f y) = 0)
参数：variationOnFromTo f s a b = 0 ↔               ∀ ⦃x : α⦄, x ∈ s ∩ Set.Icc a b 
→ ∀ ⦃y : α⦄, y ∈ s ∩ Set.Icc a b → edist (f x) (f y) = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `variationOnFromTo.eq_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {E :
 Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : α}, 
a ≤ b → variatio…
· 使用定理 `ENNReal.toReal_eq_zero_iff`：toReal_eq_zero_iff (x : Real>=0∞) : x.toReal
 = 0 ↔ x = 0 ∨ x = ∞
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `eVariationOn.eq_zero_iff`：eq_zero_iff (f : α -> E) {s : Set α} : eVariat
ionOn f s = 0 ↔ forall x in s, forall y in s, edist (f x) (f y) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem eq_zero_iff_of_le {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (ab : a ≤ b) :
    variationOnFromTo f s a b = 0 ↔
      ∀ ⦃x⦄ (_hx : x ∈ s ∩ Icc a b) ⦃y⦄ (_hy : y ∈ s ∩ Icc a b), edist (f x) (f y) = 0 := by
  rw [variationOnFromTo.eq_of_le _ _ ab, ENNReal.toReal_eq_zero_iff, or_iff_left (hf a b ha hb),
    eVariationOn.eq_zero_iff]
/-
**variationOnFromTo.eq_zero_iff_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFrom
To`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] {f : α → E} {s : Set α},   LocallyBoundedVariationOn f s →     ∀ {a
 b : α},       a ∈ s →         b ∈ s →           b ≤ a →             (variationO
nFromTo f s a b = 0 ↔               ∀ ⦃x : α⦄, x ∈ s ∩ Set.Icc b a → ∀ ⦃y : α⦄, 
y ∈ s ∩ Set.Icc b a → edist (f x) (f y) = 0)
参数：variationOnFromTo f s a b = 0 ↔               ∀ ⦃x : α⦄, x ∈ s ∩ Set.Icc b a 
→ ∀ ⦃y : α⦄, y ∈ s ∩ Set.Icc b a → edist (f x) (f y) = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `variationOnFromTo.eq_of_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {E :
 Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : α}, 
b ≤ a → variatio…
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `ENNReal.toReal_eq_zero_iff`：toReal_eq_zero_iff (x : Real>=0∞) : x.toReal
 = 0 ↔ x = 0 ∨ x = ∞
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `eVariationOn.eq_zero_iff`：eq_zero_iff (f : α -> E) {s : Set α} : eVariat
ionOn f s = 0 ↔ forall x in s, forall y in s, edist (f x) (f y) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem eq_zero_iff_of_ge {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (ba : b ≤ a) :
    variationOnFromTo f s a b = 0 ↔
      ∀ ⦃x⦄ (_hx : x ∈ s ∩ Icc b a) ⦃y⦄ (_hy : y ∈ s ∩ Icc b a), edist (f x) (f y) = 0 := by
  rw [variationOnFromTo.eq_of_ge _ _ ba, neg_eq_zero, ENNReal.toReal_eq_zero_iff,
    or_iff_left (hf b a hb ha), eVariationOn.eq_zero_iff]
/-
**variationOnFromTo.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] {f : α → E} {s : Set α},   LocallyBoundedVariationOn f s →     ∀ {a
 b : α},       a ∈ s →         b ∈ s →           (variationOnFromTo f s a b = 0 
↔             ∀ ⦃x : α⦄, x ∈ s ∩ Set.uIcc a b → ∀ ⦃y : α⦄, y ∈ s ∩ Set.uIcc a b 
→ edist (f x) (f y) = 0)
参数：variationOnFromTo f s a b = 0 ↔             ∀ ⦃x : α⦄, x ∈ s ∩ Set.uIcc a b →
 ∀ ⦃y : α⦄, y ∈ s ∩ Set.uIcc a b → edist (f x) (f y) = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `variationOnFromTo.eq_zero_iff_of_le`：∀ {α : Type u_1} [inst : LinearOrde
r α] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   L
ocallyBoundedVariationOn …
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
· 使用定理 `variationOnFromTo.eq_zero_iff_of_ge`：∀ {α : Type u_1} [inst : LinearOrde
r α] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   L
ocallyBoundedVariationOn …
-/
protected theorem eq_zero_iff {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) :
    variationOnFromTo f s a b = 0 ↔
      ∀ ⦃x⦄ (_hx : x ∈ s ∩ uIcc a b) ⦃y⦄ (_hy : y ∈ s ∩ uIcc a b), edist (f x) (f y) = 0 := by
  rcases le_total a b with (ab | ba)
  · rw [uIcc_of_le ab]
    exact variationOnFromTo.eq_zero_iff_of_le hf ha hb ab
  · rw [uIcc_of_ge ba]
    exact variationOnFromTo.eq_zero_iff_of_ge hf ha hb ba

variable {f} {s}
/-
**variationOnFromTo.monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] {f : α → E} {s : Set α},   LocallyBoundedVariationOn f s → ∀ {a : α
}, a ∈ s → MonotoneOn (variationOnFromTo f s a) s
参数：variationOnFromTo f s a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `variationOnFromTo.add`：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type
 u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   LocallyBoundedV
ariationOn …
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `variationOnFromTo.nonneg_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] 
{E : Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : 
α}, a ≤ b → 0 ≤ vari…
-/
protected theorem monotoneOn (hf : LocallyBoundedVariationOn f s) {a : α} (as : a ∈ s) :
    MonotoneOn (variationOnFromTo f s a) s := by
  rintro b bs c cs bc
  rw [← variationOnFromTo.add hf as bs cs]
  exact le_add_of_nonneg_right (variationOnFromTo.nonneg_of_le f s bc)
/-
**variationOnFromTo.antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] {f : α → E} {s : Set α},   LocallyBoundedVariationOn f s → ∀ {b : α
}, b ∈ s → AntitoneOn (fun a => variationOnFromTo f s a b) s
参数：fun a => variationOnFromTo f s a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `variationOnFromTo.add`：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type
 u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   LocallyBoundedV
ariationOn …
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `variationOnFromTo.nonneg_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] 
{E : Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : 
α}, a ≤ b → 0 ≤ vari…
-/
protected theorem antitoneOn (hf : LocallyBoundedVariationOn f s) {b : α} (bs : b ∈ s) :
    AntitoneOn (fun a => variationOnFromTo f s a b) s := by
  rintro a as c cs ac
  dsimp only
  rw [← variationOnFromTo.add hf as cs bs]
  exact le_add_of_nonneg_left (variationOnFromTo.nonneg_of_le f s ac)
/-
**variationOnFromTo.abs_sub_le_sub_of_le** 是 Mathlib 中的一个引理，位于命名空间 `variationOnF
romTo`。
形式化陈述：abs_sub_le_sub_of_le {f : α -> Real} {s : Set α} (hf : LocallyBoundedVaria
tionOn f s) {a b c : α} (as : a in s) (bs : b in s) (cs : c in s) (bc : b <= c) 
: |f c - f b| <= variationOnFromTo f s a c - variationOnFromTo f s a b
参数：hf : LocallyBoundedVariationOn f s；as : a in s；bs : b in s；cs : c in s；bc : b
 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
· 使用定理 `variationOnFromTo.eq_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {E :
 Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : α}, 
a ≤ b → variatio…
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `eVariationOn.edist_le`：edist_le (f : α -> E) {s : Set α} {x y : α} (hx :
 x in s) (hy : y in s) : edist (f x) (f y) <= eVariationOn f s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `variationOnFromTo.add`：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type
 u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   LocallyBoundedV
ariationOn …
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
lemma abs_sub_le_sub_of_le {f : α → ℝ} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b c : α} (as : a ∈ s) (bs : b ∈ s) (cs : c ∈ s) (bc : b ≤ c) :
    |f c - f b| ≤ variationOnFromTo f s a c - variationOnFromTo f s a b := calc
  _ = dist (f b) (f c) := by rw [dist_comm, Real.dist_eq]
  _ ≤ variationOnFromTo f s b c := by
    rw [variationOnFromTo.eq_of_le f s bc, dist_edist]
    apply ENNReal.toReal_mono (hf b c bs cs)
    apply eVariationOn.edist_le f
    exacts [⟨bs, le_rfl, bc⟩, ⟨cs, bc, le_rfl⟩]
  _ = variationOnFromTo f s a c - variationOnFromTo f s a b := by
    rw [← variationOnFromTo.add hf as bs cs, add_sub_cancel_left]
/-
**variationOnFromTo.add_self_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFr
omTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {f : α → ℝ} {s : Set α},   Locally
BoundedVariationOn f s → ∀ {a : α}, a ∈ s → MonotoneOn (variationOnFromTo f s a 
+ f) s
参数：variationOnFromTo f s a + f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
· 使用引理 `variationOnFromTo.abs_sub_le_sub_of_le`：abs_sub_le_sub_of_le {f : α -> R
eal} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α} (as : a in s) 
(bs : b in s) (cs : c in s) …
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 37 条，此处仅展示前 30 条）
-/
protected theorem add_self_monotoneOn {f : α → ℝ} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a : α} (as : a ∈ s) : MonotoneOn (variationOnFromTo f s a + f) s := by
  rintro b bs c cs bc
  suffices f b - f c ≤ variationOnFromTo f s a c - variationOnFromTo f s a b by simp; linarith
  calc
    f b - f c ≤ |f c - f b| := by grw [le_abs_self (f b - f c), abs_sub_comm (f b) (f c)]
    _ ≤ variationOnFromTo f s a c - variationOnFromTo f s a b := abs_sub_le_sub_of_le hf as bs cs bc
/-
**variationOnFromTo.sub_self_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFr
omTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {f : α → ℝ} {s : Set α},   Locally
BoundedVariationOn f s → ∀ {a : α}, a ∈ s → MonotoneOn (variationOnFromTo f s a 
- f) s
参数：variationOnFromTo f s a - f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用定理 `le_sub_iff_add_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a ≤ c - b ↔ a + b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_comm_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c :
 α), a - b + c = a + (c - b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_sub_iff_add_le'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, b ≤ c - a ↔ a + b ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用引理 `variationOnFromTo.abs_sub_le_sub_of_le`：abs_sub_le_sub_of_le {f : α -> R
eal} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α} (as : a in s) 
(bs : b in s) (cs : c in s) …
-/
protected theorem sub_self_monotoneOn {f : α → ℝ} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a : α} (as : a ∈ s) : MonotoneOn (variationOnFromTo f s a - f) s := by
  rintro b bs c cs bc
  rw [Pi.sub_apply, Pi.sub_apply, le_sub_iff_add_le, add_comm_sub, ← le_sub_iff_add_le']
  calc
    f c - f b ≤ |f c - f b| := le_abs_self _
    _ ≤ variationOnFromTo f s a c - variationOnFromTo f s a b := abs_sub_le_sub_of_le hf as bs cs bc
/-
**variationOnFromTo.comp_eq_of_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `variationOn
FromTo`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] {β : Type u_3}   [inst_2 : LinearOrder β] (f : α → E) {t : Set β} (
φ : β → α),   MonotoneOn φ t →     ∀ {x y : β}, x ∈ t → y ∈ t → variationOnFromT
o (f ∘ φ) t x y = variationOnFromTo f (φ '' t) (φ x) (φ y)
参数：f : α → E；φ : β → α；f ∘ φ；φ '' t；φ x；φ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `variationOnFromTo.eq_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {E :
 Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : α}, 
a ≤ b → variatio…
· 使用定理 `eVariationOn.comp_inter_Icc_eq_of_monotoneOn`：comp_inter_Icc_eq_of_monot
oneOn (f : α -> E) {t : Set β} (φ : β -> α) (hφ : MonotoneOn φ t) {x y : β} (hx 
: x in t) (hy : y in t) : eVariati…
· 使用定理 `variationOnFromTo.eq_of_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {E :
 Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : α}, 
b ≤ a → variatio…
-/
protected theorem comp_eq_of_monotoneOn {β : Type*} [LinearOrder β] (f : α → E) {t : Set β}
    (φ : β → α) (hφ : MonotoneOn φ t) {x y : β} (hx : x ∈ t) (hy : y ∈ t) :
    variationOnFromTo (f ∘ φ) t x y = variationOnFromTo f (φ '' t) (φ x) (φ y) := by
  rcases le_total x y with (h | h)
  · rw [variationOnFromTo.eq_of_le _ _ h, variationOnFromTo.eq_of_le _ _ (hφ hx hy h),
      eVariationOn.comp_inter_Icc_eq_of_monotoneOn f φ hφ hx hy]
  · rw [variationOnFromTo.eq_of_ge _ _ h, variationOnFromTo.eq_of_ge _ _ (hφ hy hx h),
      eVariationOn.comp_inter_Icc_eq_of_monotoneOn f φ hφ hy hx]

/-- The jump of `variationOnFromTo` on the left of a point is given by the distance between the
left limit and the value of the function. -/
/-
**variationOnFromTo.tendsto_left** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：tendsto_left {E : Type*} [PseudoMetricSpace E] [TopologicalSpace α] [Order
Topology α] {f : α -> E} {l : E} {a b : α} (ha : a in s) (hb : b in s) (hf : Loc
allyBoundedVariationOn f s) (h'f : Tendsto f (𝓝[s inter Iio b] b) (𝓝 l)) : Tends
to (variationOnFromTo f s a) (𝓝[s inter Iio b] b) (𝓝 (variationOnFromTo f s a b 
- dist (f b) l))
参数：ha : a in s；hb : b in s；hf : LocallyBoundedVariationOn f s；h'f : Tendsto f (𝓝
[s inter Iio b] b) (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.const_sub`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] (b : G) {c : G} {f : α → G}   {l : 
Filter α}, Fil…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ENNReal.tendsto_toReal`：tendsto_toReal {a : Real>=0∞} (ha : a != ∞) : Te
ndsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_left`：∀ {α : Type u_1
} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] [inst_2 
: TopologicalSpace α]   [OrderTopology α] {f …
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `variationOnFromTo.sub_left`：∀ {α : Type u_1} [inst : LinearOrder α] {E :
 Type u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   LocallyBou
ndedVariationOn …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
The jump of `variationOnFromTo` on the left of a point is given by the distance 
between the
left limit and the value of the function.
-/
theorem tendsto_left {E : Type*} [PseudoMetricSpace E] [TopologicalSpace α] [OrderTopology α]
    {f : α → E} {l : E} {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hf : LocallyBoundedVariationOn f s) (h'f : Tendsto f (𝓝[s ∩ Iio b] b) (𝓝 l)) :
    Tendsto (variationOnFromTo f s a) (𝓝[s ∩ Iio b] b)
      (𝓝 (variationOnFromTo f s a b - dist (f b) l)) := by
  suffices H : Tendsto (fun x ↦ variationOnFromTo f s a b - variationOnFromTo f s x b)
      (𝓝[s ∩ Iio b] b) (𝓝 (variationOnFromTo f s a b - dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [variationOnFromTo.sub_left hf ha hb hx.1]
  apply Tendsto.const_sub
  suffices H : Tendsto (fun x ↦ (eVariationOn f (s ∩ Icc x b)).toReal) (𝓝[s ∩ Iio b] b)
      (𝓝 (dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx using by simp [variationOnFromTo, hx.2.le]
  rw [dist_edist]
  exact (ENNReal.tendsto_toReal (by simp)).comp (hf.tendsto_eVariationOn_Icc_left h'f hb)

/-- The jump of `variationOnFromTo` on the right of a point is given by the distance between the
right limit and the value of the function. -/
/-
**variationOnFromTo.tendsto_right** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：tendsto_right {E : Type*} [PseudoMetricSpace E] [TopologicalSpace α] [Orde
rTopology α] {f : α -> E} {l : E} {a b : α} (ha : a in s) (hb : b in s) (hf : Lo
callyBoundedVariationOn f s) (h'f : Tendsto f (𝓝[s inter Ioi b] b) (𝓝 l)) : Tend
sto (variationOnFromTo f s a) (𝓝[s inter Ioi b] b) (𝓝 (variationOnFromTo f s a b
 + dist (f b) l))
参数：ha : a in s；hb : b in s；hf : LocallyBoundedVariationOn f s；h'f : Tendsto f (𝓝
[s inter Ioi b] b) (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [
inst_1 : Add M] [SeparatelyContinuousAdd M] {α : Type u_2} {f : α → M}   {x : Fi
lter α} {a : M…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ENNReal.tendsto_toReal`：tendsto_toReal {a : Real>=0∞} (ha : a != ∞) : Te
ndsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_right`：∀ {α : Type u_
1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] [inst_2
 : TopologicalSpace α]   [OrderTopology α] {f …
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `variationOnFromTo.add`：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type
 u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   LocallyBoundedV
ariationOn …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
The jump of `variationOnFromTo` on the right of a point is given by the distance
 between the
right limit and the value of the function.
-/
theorem tendsto_right {E : Type*} [PseudoMetricSpace E] [TopologicalSpace α] [OrderTopology α]
    {f : α → E} {l : E} {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hf : LocallyBoundedVariationOn f s) (h'f : Tendsto f (𝓝[s ∩ Ioi b] b) (𝓝 l)) :
    Tendsto (variationOnFromTo f s a) (𝓝[s ∩ Ioi b] b)
      (𝓝 (variationOnFromTo f s a b + dist (f b) l)) := by
  suffices H : Tendsto (fun x ↦ variationOnFromTo f s a b + variationOnFromTo f s b x)
      (𝓝[s ∩ Ioi b] b) (𝓝 (variationOnFromTo f s a b + dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [variationOnFromTo.add hf ha hb hx.1]
  apply Tendsto.const_add
  suffices H : Tendsto (fun x ↦ (eVariationOn f (s ∩ Icc b x)).toReal) (𝓝[s ∩ Ioi b] b)
      (𝓝 (dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx using by simp [variationOnFromTo, hx.2.le]
  rw [dist_edist]
  exact (ENNReal.tendsto_toReal (by simp)).comp (hf.tendsto_eVariationOn_Icc_right h'f hb)

/-- The jump of `variationOnFromTo` on the left of a point is given by the distance between the
left limit and the value of the function. -/
/-
**variationOnFromTo.leftLim_eq** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：leftLim_eq {E : Type*} [PseudoMetricSpace E] [CompleteSpace E] {f : α -> E
} {a b : α} (hf : BoundedVariationOn f univ) : (variationOnFromTo f univ a).left
Lim b = variationOnFromTo f univ a b - dist (f b) (f.leftLim b)
参数：hf : BoundedVariationOn f univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `leftLim_eq_of_eq_bot`：leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'
α : OrderTopology α] (f : α -> β) {a : α} (h : 𝓝[<] a = ⊥) : leftLim f a = f a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `leftLim_eq_of_tendsto`：leftLim_eq_of_tendsto [hα : TopologicalSpace α] [
h'α : OrderTopology α] [T2Space β] {f : α -> β} {a : α} {y : β} [h : (𝓝[<] a).Ne
Bot] (h' : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `variationOnFromTo.tendsto_left`：tendsto_left {E : Type*} [PseudoMetricSp
ace E] [TopologicalSpace α] [OrderTopology α] {f : α -> E} {l : E} {a b : α} (ha
 : a in s) (hb : b i…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `BoundedVariationOn.locallyBoundedVariationOn`：∀ {α : Type u_1} [inst : L
inearOrder α] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Se
t α},   BoundedVariationOn f s → L…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `BoundedVariationOn.tendsto_leftLim`：∀ {α : Type u_1} [inst : LinearOrder
 α] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] [CompleteSpace E]   [inst_3 :
 TopologicalSpace α] [Or…

--- 原说明 ---
The jump of `variationOnFromTo` on the left of a point is given by the distance 
between the
left limit and the value of the function.
-/
theorem leftLim_eq {E : Type*} [PseudoMetricSpace E] [CompleteSpace E]
    {f : α → E} {a b : α} (hf : BoundedVariationOn f univ) :
    (variationOnFromTo f univ a).leftLim b =
      variationOnFromTo f univ a b - dist (f b) (f.leftLim b) := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] b) with hb | hb
  · simp [leftLim_eq_of_eq_bot _ hb]
  apply leftLim_eq_of_tendsto
  have := variationOnFromTo.tendsto_left (f := f) (l := f.leftLim b) (mem_univ a) (mem_univ b)
    hf.locallyBoundedVariationOn
  simp only [univ_inter] at this
  exact this (hf.tendsto_leftLim _)

/-- The jump of `variationOnFromTo` on the right of a point is given by the distance between the
right limit and the value of the function. -/
/-
**variationOnFromTo.rightLim_eq** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
形式化陈述：rightLim_eq {E : Type*} [PseudoMetricSpace E] [CompleteSpace E] {f : α -> 
E} {a b : α} (hf : BoundedVariationOn f univ) : (variationOnFromTo f univ a).rig
htLim b = variationOnFromTo f univ a b + dist (f b) (f.rightLim b)
参数：hf : BoundedVariationOn f univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rightLim_eq_of_eq_bot`：rightLim_eq_of_eq_bot [TopologicalSpace α] [Order
Topology α] (f : α -> β) {a : α} (h : 𝓝[>] a = ⊥) : rightLim f a = f a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `rightLim_eq_of_tendsto`：rightLim_eq_of_tendsto [TopologicalSpace α] [Ord
erTopology α] [T2Space β] {f : α -> β} {a : α} {y : β} [h : (𝓝[>] a).NeBot] (h' 
: Tendsto f …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `variationOnFromTo.tendsto_right`：tendsto_right {E : Type*} [PseudoMetric
Space E] [TopologicalSpace α] [OrderTopology α] {f : α -> E} {l : E} {a b : α} (
ha : a in s) (hb : b …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `BoundedVariationOn.locallyBoundedVariationOn`：∀ {α : Type u_1} [inst : L
inearOrder α] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Se
t α},   BoundedVariationOn f s → L…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `BoundedVariationOn.tendsto_rightLim`：∀ {α : Type u_1} [inst : LinearOrde
r α] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] [CompleteSpace E]   [inst_3 
: TopologicalSpace α] [Or…

--- 原说明 ---
The jump of `variationOnFromTo` on the right of a point is given by the distance
 between the
right limit and the value of the function.
-/
theorem rightLim_eq {E : Type*} [PseudoMetricSpace E] [CompleteSpace E]
    {f : α → E} {a b : α} (hf : BoundedVariationOn f univ) :
    (variationOnFromTo f univ a).rightLim b =
      variationOnFromTo f univ a b + dist (f b) (f.rightLim b) := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[>] b) with hb | hb
  · simp [rightLim_eq_of_eq_bot _ hb]
  apply rightLim_eq_of_tendsto
  have := variationOnFromTo.tendsto_right (f := f) (l := f.rightLim b) (mem_univ a) (mem_univ b)
    hf.locallyBoundedVariationOn
  simp only [univ_inter] at this
  exact this (hf.tendsto_rightLim _)
/-
**variationOnFromTo._root_.BoundedVariationOn.continuousWithinAt_variationOnFrom
To_Ici** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_Ici
    [TopologicalSpace α] [OrderTopology α] (hf : BoundedVariationOn f univ) {a x : α}
    (hx : ContinuousWithinAt f (Ici x) x) :
    ContinuousWithinAt (variationOnFromTo f univ a) (Ici x) x := by
  have : variationOnFromTo f univ a =
      fun y ↦ variationOnFromTo f univ a x + variationOnFromTo f univ x y := by
    ext y
    rw [variationOnFromTo.add hf.locallyBoundedVariationOn (mem_univ _) (mem_univ _) (mem_univ _)]
  rw [this]
  apply continuousWithinAt_const.add
  suffices H : ContinuousWithinAt (fun y ↦ (eVariationOn f (univ ∩ Icc x y)).toReal) (Ici x) x from
    H.congr_of_mem (fun y hy ↦ by grind [variationOnFromTo]) self_mem_Iic
  simp only [ContinuousWithinAt, Icc_self]
  rw [eVariationOn.subsingleton _ (by grind [Set.Subsingleton])]
  apply (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
  apply Tendsto.mono_left _ (nhdsWithin_mono _ (subset_univ _))
  exact hf.tendsto_eVariationOn_Icc_zero_right _ (by simpa using hx)
/-
**variationOnFromTo._root_.BoundedVariationOn.continuousWithinAt_variationOnFrom
To_rightLim_Ici** 是 Mathlib 中的一个定理，位于命名空间 `variationOnFromTo`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_rightLim_Ici
    [TopologicalSpace α] [OrderTopology α] [T3Space E] [CompleteSpace E]
    (hf : BoundedVariationOn f univ) {a x : α} :
    ContinuousWithinAt (variationOnFromTo f.rightLim univ a) (Ici x) x :=
  hf.rightLim.continuousWithinAt_variationOnFromTo_Ici hf.continuousWithinAt_rightLim

end variationOnFromTo

/-- If a real-valued function has bounded variation on a set, then it is a difference of monotone
functions there. Moreover, one can make sure that the two monotone functions add up to the
variation of `f`. -/
/-
**LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn'** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn' {f : α -> Real
} {s : Set α} (h : LocallyBoundedVariationOn f s) : exists p q : α -> Real, Mono
toneOn p s ∧ MonotoneOn q s ∧ f = p - q ∧ forall x in s, forall y in s, (p y - p
 x) + (q y - q x) = variationOnFromTo f s x y
参数：h : LocallyBoundedVariationOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Set.Subsingleton.monotoneOn`：∀ {α : Type u} {β : Type v} {s : Set α} [in
st : Preorder α] [inst_1 : Preorder β] (f : α → β),   s.Subsingleton → MonotoneO
n f s
· 使用定理 `Set.subsingleton_empty`：subsingleton_empty : (∅ : Set α).Subsingleton
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `variationOnFromTo.add_self_monotoneOn`：∀ {α : Type u_1} [inst : LinearOr
der α] {f : α → ℝ} {s : Set α},   LocallyBoundedVariationOn f s → ∀ {a : α}, a ∈
 s → MonotoneOn (variationO…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `variationOnFromTo.sub_self_monotoneOn`：∀ {α : Type u_1} [inst : LinearOr
der α] {f : α → ℝ} {s : Set α},   LocallyBoundedVariationOn f s → ∀ {a : α}, a ∈
 s → MonotoneOn (variationO…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 76 条，此处仅展示前 30 条）

--- 原说明 ---
If a real-valued function has bounded variation on a set, then it is a differenc
e of monotone
functions there. Moreover, one can make sure that the two monotone functions add
 up to the
variation of `f`.
-/
theorem LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn' {f : α → ℝ} {s : Set α}
    (h : LocallyBoundedVariationOn f s) :
    ∃ p q : α → ℝ, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q ∧
      ∀ x ∈ s, ∀ y ∈ s, (p y - p x) + (q y - q x) = variationOnFromTo f s x y := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨c, cs⟩)
  · refine ⟨f, 0, subsingleton_empty.monotoneOn _, subsingleton_empty.monotoneOn _,
      (sub_zero f).symm, fun x hx y hy ↦ by simp at hx⟩
  refine ⟨fun x ↦ (variationOnFromTo f s c x + f x) / 2,
    fun x ↦ (variationOnFromTo f s c x - f x) / 2, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    dsimp
    gcongr 1
    simpa using variationOnFromTo.add_self_monotoneOn h cs hx hy hxy
  · intro x hx y hy hxy
    dsimp
    gcongr 1
    simpa using variationOnFromTo.sub_self_monotoneOn h cs hx hy hxy
  · ext
    simp
    ring
  · intro x hx y hy
    rw [← variationOnFromTo.add h hx cs hy, variationOnFromTo.eq_neg_swap]
    ring

/-- If a real-valued function has bounded variation on a set, then it is a difference of monotone
functions there. -/
/-
**LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn {f : α -> Real}
 {s : Set α} (h : LocallyBoundedVariationOn f s) : exists p q : α -> Real, Monot
oneOn p s ∧ MonotoneOn q s ∧ f = p - q
参数：h : LocallyBoundedVariationOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn'`：LocallyBoun
dedVariationOn.exists_monotoneOn_sub_monotoneOn' {f : α -> Real} {s : Set α} (h 
: LocallyBoundedVariationOn f s) : exists p q : α…

--- 原说明 ---
If a real-valued function has bounded variation on a set, then it is a differenc
e of monotone
functions there.
-/
theorem LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn {f : α → ℝ} {s : Set α}
    (h : LocallyBoundedVariationOn f s) :
    ∃ p q : α → ℝ, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q := by
  rcases h.exists_monotoneOn_sub_monotoneOn' with ⟨p, q, hp, hq, h'f, -⟩
  exact ⟨p, q, hp, hq, h'f⟩
