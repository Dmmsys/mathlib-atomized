/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Notation.Indicator

/-!
# Indicator functions and support of a function in groups with zero
-/

public section

assert_not_exists Ring

open Set

variable {ι κ G₀ M₀ R : Type*}

namespace Set
section MulZeroClass
variable [MulZeroClass M₀] {s t : Set ι} {i : ι}

/-
**Set.indicator_mul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_mul (s : Set ι) (f g : ι -> M₀) : indicator s (fun i => f i * g 
i) = fun i => indicator s f i * indicator s g i
参数：s : Set ι；f g : ι -> M₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma indicator_mul (s : Set ι) (f g : ι → M₀) :
    indicator s (fun i ↦ f i * g i) = fun i ↦ indicator s f i * indicator s g i := by
  funext
  simp only [indicator]
  split_ifs
  · rfl
  rw [mul_zero]
/-
**Set.indicator_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_mul_left (s : Set ι) (f g : ι -> M₀) : indicator s (fun j => f j
 * g j) i = indicator s f i * g i
参数：s : Set ι；f g : ι -> M₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
lemma indicator_mul_left (s : Set ι) (f g : ι → M₀) :
    indicator s (fun j ↦ f j * g j) i = indicator s f i * g i := by
  simp only [indicator]
  split_ifs
  · rfl
  · rw [zero_mul]
/-
**Set.indicator_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_mul_right (s : Set ι) (f g : ι -> M₀) : indicator s (fun j => f 
j * g j) i = f i * indicator s g i
参数：s : Set ι；f g : ι -> M₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma indicator_mul_right (s : Set ι) (f g : ι → M₀) :
    indicator s (fun j ↦ f j * g j) i = f i * indicator s g i := by
  simp only [indicator]
  split_ifs
  · rfl
  · rw [mul_zero]
/-
**Set.indicator_mul_const** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_mul_const (s : Set ι) (f : ι -> M₀) (a : M₀) (i : ι) : s.indicat
or (f · * a) i = s.indicator f i * a
参数：s : Set ι；f : ι -> M₀；a : M₀；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.indicator_mul_left`：indicator_mul_left (s : Set ι) (f g : ι -> M₀) :
 indicator s (fun j => f j * g j) i = indicator s f i * g i
-/
lemma indicator_mul_const (s : Set ι) (f : ι → M₀) (a : M₀) (i : ι) :
    s.indicator (f · * a) i = s.indicator f i * a := by rw [indicator_mul_left]
/-
**Set.indicator_const_mul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_const_mul (s : Set ι) (f : ι -> M₀) (a : M₀) (i : ι) : s.indicat
or (a * f ·) i = a * s.indicator f i
参数：s : Set ι；f : ι -> M₀；a : M₀；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.indicator_mul_right`：indicator_mul_right (s : Set ι) (f g : ι -> M₀)
 : indicator s (fun j => f j * g j) i = f i * indicator s g i
-/
lemma indicator_const_mul (s : Set ι) (f : ι → M₀) (a : M₀) (i : ι) :
    s.indicator (a * f ·) i = a * s.indicator f i := by rw [indicator_mul_right]
/-
**Set.inter_indicator_mul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inter_indicator_mul (f g : ι -> M₀) (i : ι) : (s inter t).indicator (fun j
 => f j * g j) i = s.indicator f i * t.indicator g i
参数：f g : ι -> M₀；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.indicator_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 (s t : Set α) (f : α → M),   s.indicator (t.indicator f) = (s ∩ t).indicator f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
lemma inter_indicator_mul (f g : ι → M₀) (i : ι) :
    (s ∩ t).indicator (fun j ↦ f j * g j) i = s.indicator f i * t.indicator g i := by
  rw [← Set.indicator_indicator]
  simp_rw [indicator]
  split_ifs <;> simp

end MulZeroClass

section MulZeroOneClass
variable [MulZeroOneClass M₀] {s t : Set ι} {i : ι}

/-
**Set.inter_indicator_one** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inter_indicator_one : (s inter t).indicator (1 : ι -> M₀) = s.indicator 1 
* t.indicator 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma inter_indicator_one : (s ∩ t).indicator (1 : ι → M₀) = s.indicator 1 * t.indicator 1 :=
  funext fun _ ↦ by simp only [← inter_indicator_mul, Pi.mul_apply, Pi.one_apply, one_mul]; congr

set_option backward.isDefEq.respectTransparency false in
/-
**Set.indicator_prod_one** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_prod_one {t : Set κ} {j : κ} : (s ×ˢ t).indicator (1 : ι × κ -> 
M₀) (i, j) = s.indicator 1 i * t.indicator 1 j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
lemma indicator_prod_one {t : Set κ} {j : κ} :
    (s ×ˢ t).indicator (1 : ι × κ → M₀) (i, j) = s.indicator 1 i * t.indicator 1 j := by
  simp_rw [indicator, mem_prod_eq]
  split_ifs with h₀ <;> simp only [Pi.one_apply, mul_one, mul_zero] <;> tauto

variable (M₀) [Nontrivial M₀]
/-
**Set.indicator_eq_zero_iff_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_eq_zero_iff_notMem : indicator s 1 i = (0 : M₀) ↔ i ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma indicator_eq_zero_iff_notMem : indicator s 1 i = (0 : M₀) ↔ i ∉ s := by
  simp
/-
**Set.indicator_eq_one_iff_mem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_eq_one_iff_mem : indicator s 1 i = (1 : M₀) ↔ i in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma indicator_eq_one_iff_mem : indicator s 1 i = (1 : M₀) ↔ i ∈ s := by
  classical simp [indicator_apply, imp_false]
/-
**Set.indicator_one_inj** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_one_inj (h : indicator s (1 : ι -> M₀) = indicator t 1) : s = t
参数：h : indicator s (1 : ι -> M₀) = indicator t 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.indicator_eq_one_iff_mem`：indicator_eq_one_iff_mem : indicator s 1 i
 = (1 : M₀) ↔ i in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma indicator_one_inj (h : indicator s (1 : ι → M₀) = indicator t 1) : s = t := by
  ext; simp_rw [← indicator_eq_one_iff_mem M₀, h]

end MulZeroOneClass
end Set

namespace Function
section ZeroOne
variable (R) [Zero R] [One R] [NeZero (1 : R)]

/-
**Function.support_one** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Type u_1} (R : Type u_5) [inst : Zero R] [inst_1 : One R] [NeZero 1
], Function.support 1 = Set.univ
参数：R : Type u_5。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.support_const`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] 
{c : M}, c ≠ 0 → (Function.support fun x => c) = Set.univ
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
@[simp] lemma support_one : support (1 : ι → R) = univ := support_const one_ne_zero
/-
**Function.mulSupport_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Type u_1} (R : Type u_5) [inst : Zero R] [inst_1 : One R] [NeZero 1
], Function.mulSupport 0 = Set.univ
参数：R : Type u_5。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_const`：mulSupport_const {c : M} (hc : c != 1) : (mul
Support fun _ : ι => c) = Set.univ
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
-/
@[simp] lemma mulSupport_zero : mulSupport (0 : ι → R) = univ := mulSupport_const zero_ne_one

end ZeroOne

section MulZeroClass
variable [MulZeroClass M₀]

/-
**Function.support_mul_subset_left** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：support_mul_subset_left (f g : ι -> M₀) : support (fun x => f x * g x) sub
seteq support f
参数：f g : ι -> M₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma support_mul_subset_left (f g : ι → M₀) : support (fun x ↦ f x * g x) ⊆ support f :=
  fun x hfg hf ↦ hfg <| by simp only [hf, zero_mul]
/-
**Function.support_mul_subset_right** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：support_mul_subset_right (f g : ι -> M₀) : support (fun x => f x * g x) su
bseteq support g
参数：f g : ι -> M₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma support_mul_subset_right (f g : ι → M₀) : support (fun x ↦ f x * g x) ⊆ support g :=
  fun x hfg hg => hfg <| by simp only [hg, mul_zero]

variable [NoZeroDivisors M₀]
/-
**Function.support_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MulZeroClass M₀] [NoZeroDivisors 
M₀] (f g : ι → M₀),   (Function.support fun x => f x * g x) = Function.support f
 ∩ Function.support g
参数：f g : ι → M₀；Function.support fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma support_mul (f g : ι → M₀) : support (fun x ↦ f x * g x) = support f ∩ support g :=
  ext fun x ↦ by simp [not_or]
/-
**Function.support_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MulZeroClass M₀] [NoZeroDivisors 
M₀] (f g : ι → M₀),   Function.support (f * g) = Function.support f ∩ Function.s
upport g
参数：f g : ι → M₀；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.support_mul`：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MulZeroCl
ass M₀] [NoZeroDivisors M₀] (f g : ι → M₀),   (Function.support fun x => f x * g
 x) = Func…
-/
@[simp] lemma support_mul' (f g : ι → M₀) : support (f * g) = support f ∩ support g :=
  support_mul _ _

/-- If `f` is everywhere nonzero, then `support (f * g) = support g`. -/
/-
**Function.support_mul_of_ne_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：support_mul_of_ne_zero_left {f : ι -> M₀} (hf : forall x, f x != 0) (g : ι
 -> M₀) : support (fun x => f x * g x) = support g
参数：hf : forall x, f x != 0；g : ι -> M₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.support_mul`：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MulZeroCl
ass M₀] [NoZeroDivisors M₀] (f g : ι → M₀),   (Function.support fun x => f x * g
 x) = Func…
· 使用定理 `Function.support_eq_univ`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M
] {f : ι → M}, (∀ (x : ι), f x ≠ 0) → Function.support f = Set.univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` is everywhere nonzero, then `support (f * g) = support g`.
-/
lemma support_mul_of_ne_zero_left {f : ι → M₀} (hf : ∀ x, f x ≠ 0) (g : ι → M₀) :
    support (fun x => f x * g x) = support g := by simp [support_eq_univ hf]

/-- If `g` is everywhere nonzero, then `support (f * g) = support f`. -/
/-
**Function.support_mul_of_ne_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：support_mul_of_ne_zero_right (f : ι -> M₀) {g : ι -> M₀} (hg : forall x, g
 x != 0) : support (fun x => f x * g x) = support f
参数：f : ι -> M₀；hg : forall x, g x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.support_mul`：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MulZeroCl
ass M₀] [NoZeroDivisors M₀] (f g : ι → M₀),   (Function.support fun x => f x * g
 x) = Func…
· 使用定理 `Function.support_eq_univ`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M
] {f : ι → M}, (∀ (x : ι), f x ≠ 0) → Function.support f = Set.univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `g` is everywhere nonzero, then `support (f * g) = support f`.
-/
lemma support_mul_of_ne_zero_right (f : ι → M₀) {g : ι → M₀} (hg : ∀ x, g x ≠ 0) :
    support (fun x => f x * g x) = support f := by simp [support_eq_univ hg]

end MulZeroClass

section MonoidWithZero
variable [MonoidWithZero M₀] [IsReduced M₀] {n : ℕ}

/-
**Function.support_pow** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MonoidWithZero M₀] [IsReduced M₀]
 {n : ℕ} (f : ι → M₀),   n ≠ 0 → (Function.support fun a => f a ^ n) = Function.
support f
参数：f : ι → M₀；Function.support fun a => f a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `pow_eq_zero_iff`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} {
n : ℕ} [IsReduced M₀], n ≠ 0 → (a ^ n = 0 ↔ a = 0)
-/
@[simp] lemma support_pow (f : ι → M₀) (hn : n ≠ 0) : support (fun a ↦ f a ^ n) = support f := by
  ext; exact (pow_eq_zero_iff hn).not
/-
**Function.support_pow'** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MonoidWithZero M₀] [IsReduced M₀]
 {n : ℕ} (f : ι → M₀),   n ≠ 0 → Function.support (f ^ n) = Function.support f
参数：f : ι → M₀；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.support_pow`：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MonoidWit
hZero M₀] [IsReduced M₀] {n : ℕ} (f : ι → M₀),   n ≠ 0 → (Function.support fun a
 => f a ^ …
-/
@[simp] lemma support_pow' (f : ι → M₀) (hn : n ≠ 0) : support (f ^ n) = support f :=
  support_pow _ hn

end MonoidWithZero

section GroupWithZero
variable [GroupWithZero G₀]

/-
**Function.support_inv** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Type u_1} {G₀ : Type u_3} [inst : GroupWithZero G₀] (f : ι → G₀),  
 (Function.support fun a => (f a)⁻¹) = Function.support f
参数：f : ι → G₀；Function.support fun a => (f a)⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `inv_eq_zero`：inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0
-/
@[simp] lemma support_inv (f : ι → G₀) : support (fun a ↦ (f a)⁻¹) = support f :=
  Set.ext fun _ ↦ not_congr inv_eq_zero
/-
**Function.support_inv'** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Type u_1} {G₀ : Type u_3} [inst : GroupWithZero G₀] (f : ι → G₀), F
unction.support f⁻¹ = Function.support f
参数：f : ι → G₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.support_inv`：∀ {ι : Type u_1} {G₀ : Type u_3} [inst : GroupWith
Zero G₀] (f : ι → G₀),   (Function.support fun a => (f a)⁻¹) = Function.support 
f
-/
@[simp] lemma support_inv' (f : ι → G₀) : support f⁻¹ = support f := support_inv _
/-
**Function.support_div** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Type u_1} {G₀ : Type u_3} [inst : GroupWithZero G₀] (f g : ι → G₀),
   (Function.support fun a => f a / g a) = Function.support f ∩ Function.support
 g
参数：f g : ι → G₀；Function.support fun a => f a / g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Function.support_mul`：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MulZeroCl
ass M₀] [NoZeroDivisors M₀] (f g : ι → M₀),   (Function.support fun x => f x * g
 x) = Func…
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Function.support_inv`：∀ {ι : Type u_1} {G₀ : Type u_3} [inst : GroupWith
Zero G₀] (f : ι → G₀),   (Function.support fun a => (f a)⁻¹) = Function.support 
f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma support_div (f g : ι → G₀) : support (fun a ↦ f a / g a) = support f ∩ support g := by
  simp [div_eq_mul_inv]
/-
**Function.support_div'** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Type u_1} {G₀ : Type u_3} [inst : GroupWithZero G₀] (f g : ι → G₀),
   Function.support (f / g) = Function.support f ∩ Function.support g
参数：f g : ι → G₀；f / g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.support_div`：∀ {ι : Type u_1} {G₀ : Type u_3} [inst : GroupWith
Zero G₀] (f g : ι → G₀),   (Function.support fun a => f a / g a) = Function.supp
ort f ∩ Fu…
-/
@[simp] lemma support_div' (f g : ι → G₀) : support (f / g) = support f ∩ support g :=
  support_div _ _

end GroupWithZero

variable [One R]

/-
**Function.mulSupport_one_add** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_one_add [AddLeftCancelMonoid R] (f : ι -> R) : mulSupport (fun 
x => 1 + f x) = support f
参数：f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
lemma mulSupport_one_add [AddLeftCancelMonoid R] (f : ι → R) :
    mulSupport (fun x ↦ 1 + f x) = support f :=
  Set.ext fun _ ↦ not_congr add_eq_left
/-
**Function.mulSupport_one_add'** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_one_add' [AddLeftCancelMonoid R] (f : ι -> R) : mulSupport (1 +
 f) = support f
参数：f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_one_add`：mulSupport_one_add [AddLeftCancelMonoid R] 
(f : ι -> R) : mulSupport (fun x => 1 + f x) = support f
-/
lemma mulSupport_one_add' [AddLeftCancelMonoid R] (f : ι → R) : mulSupport (1 + f) = support f :=
  mulSupport_one_add f
/-
**Function.mulSupport_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_add_one [AddRightCancelMonoid R] (f : ι -> R) : mulSupport (fun
 x => f x + 1) = support f
参数：f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `add_eq_right`：∀ {M : Type u_4} [inst : AddMonoid M] [IsRightCancelAdd M]
 {a b : M}, a + b = b ↔ a = 0
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma mulSupport_add_one [AddRightCancelMonoid R] (f : ι → R) :
    mulSupport (fun x ↦ f x + 1) = support f := Set.ext fun _ ↦ not_congr add_eq_right
/-
**Function.mulSupport_add_one'** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_add_one' [AddRightCancelMonoid R] (f : ι -> R) : mulSupport (f 
+ 1) = support f
参数：f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_add_one`：mulSupport_add_one [AddRightCancelMonoid R]
 (f : ι -> R) : mulSupport (fun x => f x + 1) = support f
-/
lemma mulSupport_add_one' [AddRightCancelMonoid R] (f : ι → R) : mulSupport (f + 1) = support f :=
  mulSupport_add_one f
/-
**Function.mulSupport_one_sub'** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_one_sub' [AddGroup R] (f : ι -> R) : mulSupport (1 - f) = suppo
rt f
参数：f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `Function.mulSupport_one_add'`：mulSupport_one_add' [AddLeftCancelMonoid R
] (f : ι -> R) : mulSupport (1 + f) = support f
· 使用定理 `Function.support_neg`：∀ {α : Type u_1} {G : Type u_3} [inst : Subtractio
nMonoid G] (f : α → G), Function.support (-f) = Function.support f
-/
lemma mulSupport_one_sub' [AddGroup R] (f : ι → R) : mulSupport (1 - f) = support f := by
  rw [sub_eq_add_neg, mulSupport_one_add', support_neg]
/-
**Function.mulSupport_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_one_sub [AddGroup R] (f : ι -> R) : mulSupport (fun x => 1 - f 
x) = support f
参数：f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_one_sub'`：mulSupport_one_sub' [AddGroup R] (f : ι ->
 R) : mulSupport (1 - f) = support f
-/
lemma mulSupport_one_sub [AddGroup R] (f : ι → R) :
    mulSupport (fun x ↦ 1 - f x) = support f := mulSupport_one_sub' f

end Function

