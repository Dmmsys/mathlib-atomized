/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Data.EReal.Basic
public import Batteries.Util.ProofWanted

/-!
# Addition, negation, subtraction and multiplication on extended real numbers

Addition and multiplication in `EReal` are problematic in the presence of `±∞`, but negation has
a natural definition and satisfies the usual properties. In particular, it is an order-reversing
isomorphism.

The construction of `EReal` as `WithBot (WithTop ℝ)` endows a `LinearOrderedAddCommMonoid` structure
on it. However, addition is badly behaved at `(⊥, ⊤)` and `(⊤, ⊥)`, so this cannot be upgraded to a
group structure. Our choice is that `⊥ + ⊤ = ⊤ + ⊥ = ⊥`, to make sure that the exponential and
logarithm between `EReal` and `ℝ≥0∞` respect the operations. Note that the convention `0 * ∞ = 0`
on `ℝ≥0∞` is enforced by measure theory. Subtraction, defined as `x - y = x + (-y)`, does not have
nice properties but is sometimes convenient to have.

There is also a `CommMonoidWithZero` structure on `EReal`, but `Mathlib/Data/EReal/Basic.lean` only
provides `MulZeroOneClass` because a proof of associativity by hand would have 125 cases.
The `CommMonoidWithZero` instance is instead delivered in `Mathlib/Data/EReal/Inv.lean`.

We define `0 * x = x * 0 = 0` for any `x`, with the other cases defined non-ambiguously.
This does not distribute with addition, as `⊥ = ⊥ + ⊤ = 1 * ⊥ + (-1) * ⊥ ≠ (1 - 1) * ⊥ = 0 * ⊥ = 0`.
Distributivity `x * (y + z) = x * y + x * z` is recovered in the case where either `0 ≤ x < ⊤`,
see `EReal.left_distrib_of_nonneg_of_ne_top`, or `0 ≤ y, z`. See `EReal.left_distrib_of_nonneg`
(similarly for right distributivity).
-/

@[expose] public section

open ENNReal NNReal

noncomputable section

namespace EReal

/-! ### Addition -/

@[simp]
/-
**EReal.add_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：add_bot (x : EReal) : x + ⊥ = ⊥
参数：x : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥

--- 原说明 ---
### Addition
-/
theorem add_bot (x : EReal) : x + ⊥ = ⊥ :=
  WithBot.add_bot _

@[simp]
/-
**EReal.bot_add** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：bot_add (x : EReal) : ⊥ + x = ⊥
参数：x : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.bot_add`：∀ {α : Type u} [inst : Add α] (x : WithBot α), ⊥ + x = 
⊥
-/
theorem bot_add (x : EReal) : ⊥ + x = ⊥ :=
  WithBot.bot_add _

@[simp]
/-
**EReal.add_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：add_eq_bot_iff {x y : EReal} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.add_eq_bot`：∀ {α : Type u} [inst : Add α] {x y : WithBot α}, x +
 y = ⊥ ↔ x = ⊥ ∨ y = ⊥
-/
theorem add_eq_bot_iff {x y : EReal} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ :=
  WithBot.add_eq_bot
/-
**EReal.add_ne_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：add_ne_bot_iff {x y : EReal} : x + y != ⊥ ↔ x != ⊥ ∧ y != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.add_ne_bot`：add_ne_bot : x + y != ⊥ ↔ x != ⊥ ∧ y != ⊥
-/
lemma add_ne_bot_iff {x y : EReal} : x + y ≠ ⊥ ↔ x ≠ ⊥ ∧ y ≠ ⊥ := WithBot.add_ne_bot

@[simp]
/-
**EReal.bot_lt_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：bot_lt_add_iff {x y : EReal} : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem bot_lt_add_iff {x y : EReal} : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp [bot_lt_iff_ne_bot]

@[simp]
/-
**EReal.top_add_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：top_add_top : (⊤ : EReal) + ⊤ = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_add_top : (⊤ : EReal) + ⊤ = ⊤ :=
  rfl

@[simp]
/-
**EReal.top_add_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：top_add_coe (x : Real) : (⊤ : EReal) + x = ⊤
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_add_coe (x : ℝ) : (⊤ : EReal) + x = ⊤ :=
  rfl

/-- For any extended real number `x` which is not `⊥`, the sum of `⊤` and `x` is equal to `⊤`. -/
@[simp]
/-
**EReal.top_add_of_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：top_add_of_ne_bot {x : EReal} (h : x != ⊥) : ⊤ + x = ⊤
参数：h : x != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.top_add_coe`：top_add_coe (x : Real) : (⊤ : EReal) + x = ⊤
· 使用定理 `EReal.top_add_top`：top_add_top : (⊤ : EReal) + ⊤ = ⊤

--- 原说明 ---
For any extended real number `x` which is not `⊥`, the sum of `⊤` and `x` is equ
al to `⊤`.
-/
theorem top_add_of_ne_bot {x : EReal} (h : x ≠ ⊥) : ⊤ + x = ⊤ := by
  induction x
  · exfalso; exact h (Eq.refl ⊥)
  · exact top_add_coe _
  · exact top_add_top

/-- For any extended real number `x`, the sum of `⊤` and `x` is equal to `⊤`
if and only if `x` is not `⊥`. -/
/-
**EReal.top_add_iff_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：top_add_iff_ne_bot {x : EReal} : ⊤ + x = ⊤ ↔ x != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.add_bot`：add_bot (x : EReal) : x + ⊥ = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.top_add_of_ne_bot`：top_add_of_ne_bot {x : EReal} (h : x != ⊥) : ⊤ 
+ x = ⊤

--- 原说明 ---
For any extended real number `x`, the sum of `⊤` and `x` is equal to `⊤`
if and only if `x` is not `⊥`.
-/
theorem top_add_iff_ne_bot {x : EReal} : ⊤ + x = ⊤ ↔ x ≠ ⊥ := by
  constructor <;> intro h
  · rintro rfl
    rw [add_bot] at h
    exact bot_ne_top h
  · cases x with
    | bot => contradiction
    | top => rfl
    | coe r => exact top_add_of_ne_bot h

/-- For any extended real number `x` which is not `⊥`, the sum of `x` and `⊤` is equal to `⊤`. -/
@[simp]
/-
**EReal.add_top_of_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：add_top_of_ne_bot {x : EReal} (h : x != ⊥) : x + ⊤ = ⊤
参数：h : x != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `EReal.top_add_of_ne_bot`：top_add_of_ne_bot {x : EReal} (h : x != ⊥) : ⊤ 
+ x = ⊤

--- 原说明 ---
For any extended real number `x` which is not `⊥`, the sum of `x` and `⊤` is equ
al to `⊤`.
-/
theorem add_top_of_ne_bot {x : EReal} (h : x ≠ ⊥) : x + ⊤ = ⊤ := by
  rw [add_comm, top_add_of_ne_bot h]

/-- For any extended real number `x`, the sum of `x` and `⊤` is equal to `⊤`
if and only if `x` is not `⊥`. -/
/-
**EReal.add_top_iff_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：add_top_iff_ne_bot {x : EReal} : x + ⊤ = ⊤ ↔ x != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `EReal.top_add_iff_ne_bot`：top_add_iff_ne_bot {x : EReal} : ⊤ + x = ⊤ ↔ x
 != ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
For any extended real number `x`, the sum of `x` and `⊤` is equal to `⊤`
if and only if `x` is not `⊥`.
-/
theorem add_top_iff_ne_bot {x : EReal} : x + ⊤ = ⊤ ↔ x ≠ ⊥ := by rw [add_comm, top_add_iff_ne_bot]
/-
**EReal.add_pos_of_pos_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, 0 < a → 0 ≤ b → 0 < a + b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected theorem add_pos_of_pos_of_nonneg {a b : EReal} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
  add_comm a b ▸ Right.add_pos_of_nonneg_of_pos hb ha

/-- For any two extended real numbers `a` and `b`, if both `a` and `b` are greater than `0`,
then their sum is also greater than `0`. -/
/-
**EReal.add_pos** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, 0 < a → 0 < b → 0 < a + b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
For any two extended real numbers `a` and `b`, if both `a` and `b` are greater t
han `0`,
then their sum is also greater than `0`.
-/
protected theorem add_pos {a b : EReal} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  Right.add_pos_of_nonneg_of_pos ha.le hb

@[simp]
/-
**EReal.coe_add_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_add_top (x : Real) : (x : EReal) + ⊤ = ⊤
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add_top (x : ℝ) : (x : EReal) + ⊤ = ⊤ :=
  rfl
/-
**EReal.toReal_add** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：toReal_add {x y : EReal} (hx : x != ⊤) (h'x : x != ⊥) (hy : y != ⊤) (h'y :
 y != ⊥) : toReal (x + y) = toReal x + toReal y
参数：hx : x != ⊤；h'x : x != ⊥；hy : y != ⊤；h'y : y != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
-/
theorem toReal_add {x y : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toReal (x + y) = toReal x + toReal y := by
  lift x to ℝ using ⟨hx, h'x⟩
  lift y to ℝ using ⟨hy, h'y⟩
  rfl
/-
**EReal.toENNReal_add** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_add {x y : EReal} (hx : 0 <= x) (hy : 0 <= y) : (x + y).toENNRea
l = x.toENNReal + y.toENNReal
参数：hx : 0 <= x；hy : 0 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `EReal.add_top_of_ne_bot`：add_top_of_ne_bot {x : EReal} (h : x != ⊥) : x 
+ ⊤ = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `EReal.toENNReal_of_ne_top`：toENNReal_of_ne_top {x : EReal} (hx : x != ⊤)
 : x.toENNReal = ENNReal.ofReal x.toReal
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `EReal.top_add_of_ne_bot`：top_add_of_ne_bot {x : EReal} (h : x != ⊥) : ⊤ 
+ x = ⊤
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
-/
lemma toENNReal_add {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y).toENNReal = x.toENNReal + y.toENNReal := by
  induction x <;> induction y <;> try {· simp_all}
  norm_cast
  simp_rw [real_coe_toENNReal]
  simp_all [ENNReal.ofReal_add]
/-
**EReal.toENNReal_add_le** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_add_le {x y : EReal} : (x + y).toENNReal <= x.toENNReal + y.toEN
NReal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.add_bot`：add_bot (x : EReal) : x + ⊥ = ⊥
· 使用引理 `EReal.toENNReal_of_ne_top`：toENNReal_of_ne_top {x : EReal} (hx : x != ⊤)
 : x.toENNReal = ENNReal.ofReal x.toReal
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `ENNReal.ofReal_add_le`：ofReal_add_le {p q : Real} : ENNReal.ofReal (p + 
q) <= ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `EReal.add_top_of_ne_bot`：add_top_of_ne_bot {x : EReal} (h : x != ⊥) : x 
+ ⊤ = ⊤
· 使用定理 `EReal.top_add_of_ne_bot`：top_add_of_ne_bot {x : EReal} (h : x != ⊥) : ⊤ 
+ x = ⊤
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
-/
lemma toENNReal_add_le {x y : EReal} : (x + y).toENNReal ≤ x.toENNReal + y.toENNReal := by
  induction x <;> induction y <;> try {· simp}
  exact ENNReal.ofReal_add_le
/-
**EReal.addLECancellable_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x : ℝ), AddLECancellable ↑x
参数：x : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.add_bot`：add_bot (x : EReal) : x + ⊥ = ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
-/
theorem addLECancellable_coe (x : ℝ) : AddLECancellable (x : EReal)
  | _, ⊤, _ => le_top
  | ⊥, _, _ => bot_le
  | ⊤, (z : ℝ), h => by simp only [coe_add_top, ← coe_add, top_le_iff, coe_ne_top] at h
  | _, ⊥, h => by simpa using h
  | (y : ℝ), (z : ℝ), h => by
    simpa only [← coe_add, EReal.coe_le_coe_iff, add_le_add_iff_left] using h

-- TODO: add `MulLECancellable.strictMono*` etc
/-
**EReal.add_lt_add_right_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：add_lt_add_right_coe {x y : EReal} (h : x < y) (z : Real) : x + z < y + z
参数：h : x < y；z : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `AddLECancellable.add_le_add_iff_right`：∀ {α : Type u_1} [inst : LE α] [i
nst_1 : Add α] [IsAddCommutative α] [AddLeftMono α] {a b c : α},   AddLECancella
ble a → (b + a ≤ c + a ↔ b …
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `EReal.addLECancellable_coe`：∀ (x : ℝ), AddLECancellable ↑x
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem add_lt_add_right_coe {x y : EReal} (h : x < y) (z : ℝ) : x + z < y + z :=
  not_le.1 <| mt (addLECancellable_coe z).add_le_add_iff_right.1 h.not_ge
/-
**EReal.add_lt_add_left_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：add_lt_add_left_coe {x y : EReal} (h : x < y) (z : Real) : (z : EReal) + x
 < z + y
参数：h : x < y；z : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `EReal.add_lt_add_right_coe`：add_lt_add_right_coe {x y : EReal} (h : x < 
y) (z : Real) : x + z < y + z
-/
theorem add_lt_add_left_coe {x y : EReal} (h : x < y) (z : ℝ) : (z : EReal) + x < z + y := by
  simpa [add_comm] using add_lt_add_right_coe h z
/-
**EReal.add_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t) : x + z < y + t
参数：h1 : x < y；h2 : z < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `EReal.add_lt_add_left_coe`：add_lt_add_left_coe {x y : EReal} (h : x < y)
 (z : Real) : (z : EReal) + x < z + y
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t) : x + z < y + t := by
  rcases eq_or_ne x ⊥ with (rfl | hx)
  · simp [h1, bot_le.trans_lt h2]
  · lift x to ℝ using ⟨h1.ne_top, hx⟩
    calc (x : EReal) + z < x + t := add_lt_add_left_coe h2 _
    _ ≤ y + t := by gcongr
/-
**EReal.add_lt_add_of_lt_of_le'** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：add_lt_add_of_lt_of_le' {x y z t : EReal} (h : x < y) (h' : z <= t) (hbot 
: t != ⊥) (htop : t = ⊤ -> z = ⊤ -> x = ⊥) : x + z < y + t
参数：h : x < y；h' : z <= t；hbot : t != ⊥；htop : t = ⊤ -> z = ⊤ -> x = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `EReal.add_lt_add_right_coe`：add_lt_add_right_coe {x y : EReal} (h : x < 
y) (z : Real) : x + z < y + z
· 使用定理 `EReal.add_lt_add`：add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t)
 : x + z < y + t
-/
theorem add_lt_add_of_lt_of_le' {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hbot : t ≠ ⊥)
    (htop : t = ⊤ → z = ⊤ → x = ⊥) : x + z < y + t := by
  rcases h'.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne z ⊤ with (rfl | hz)
    · obtain rfl := htop rfl rfl
      simpa
    lift z to ℝ using ⟨hz, hbot⟩
    exact add_lt_add_right_coe h z
  · exact add_lt_add h hlt

/-- See also `EReal.add_lt_add_of_lt_of_le'` for a version with weaker but less convenient
assumptions. -/
/-
**EReal.add_lt_add_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：add_lt_add_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z <= t) (hz : z
 != ⊥) (ht : t != ⊤) : x + z < y + t
参数：h : x < y；h' : z <= t；hz : z != ⊥；ht : t != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.add_lt_add_of_lt_of_le'`：add_lt_add_of_lt_of_le' {x y z t : EReal}
 (h : x < y) (h' : z <= t) (hbot : t != ⊥) (htop : t = ⊤ -> z = ⊤ -> x = ⊥) : x 
+ z < y + t
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥

--- 原说明 ---
See also `EReal.add_lt_add_of_lt_of_le'` for a version with weaker but less conv
enient
assumptions.
-/
theorem add_lt_add_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x + z < y + t :=
  add_lt_add_of_lt_of_le' h h' (ne_bot_of_le_ne_bot hz h') fun ht' => (ht ht').elim
/-
**EReal.add_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：add_lt_top {x y : EReal} (hx : x != ⊤) (hy : y != ⊤) : x + y < ⊤
参数：hx : x != ⊤；hy : y != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.add_lt_add`：add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t)
 : x + z < y + t
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem add_lt_top {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y < ⊤ :=
  add_lt_add hx.lt_top hy.lt_top
/-
**EReal.add_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：add_ne_top {x y : EReal} (hx : x != ⊤) (hy : y != ⊤) : x + y != ⊤
参数：hx : x != ⊤；hy : y != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `EReal.add_lt_top`：add_lt_top {x y : EReal} (hx : x != ⊤) (hy : y != ⊤) :
 x + y < ⊤
-/
lemma add_ne_top {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y ≠ ⊤ :=
  lt_top_iff_ne_top.mp <| add_lt_top hx hy
/-
**EReal.add_ne_top_iff_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_ne_top_iff_ne_top₂ {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ := by
  refine ⟨?_, fun h ↦ add_ne_top h.1 h.2⟩
  cases x <;> simp_all only [ne_eq, not_false_eq_true, top_add_of_ne_bot, not_true_eq_false,
    IsEmpty.forall_iff]
  cases y <;> simp_all only [not_false_eq_true, ne_eq, add_top_of_ne_bot, not_true_eq_false,
    coe_ne_top, and_self, implies_true]
/-
**EReal.add_ne_top_iff_ne_top_left** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：add_ne_top_iff_ne_top_left {x y : EReal} (hy : y != ⊥) (hy' : y != ⊤) : x 
+ y != ⊤ ↔ x != ⊤
参数：hy : y != ⊥；hy' : y != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `EReal.top_add_of_ne_bot`：top_add_of_ne_bot {x : EReal} (h : x != ⊥) : ⊤ 
+ x = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma add_ne_top_iff_ne_top_left {x y : EReal} (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ := by
  cases x <;> simp [add_ne_top_iff_ne_top₂, hy, hy']
/-
**EReal.add_ne_top_iff_ne_top_right** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：add_ne_top_iff_ne_top_right {x y : EReal} (hx : x != ⊥) (hx' : x != ⊤) : x
 + y != ⊤ ↔ y != ⊤
参数：hx : x != ⊥；hx' : x != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.add_ne_top_iff_ne_top_left`：add_ne_top_iff_ne_top_left {x y : ERea
l} (hy : y != ⊥) (hy' : y != ⊤) : x + y != ⊤ ↔ x != ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma add_ne_top_iff_ne_top_right {x y : EReal} (hx : x ≠ ⊥) (hx' : x ≠ ⊤) :
    x + y ≠ ⊤ ↔ y ≠ ⊤ := add_comm x y ▸ add_ne_top_iff_ne_top_left hx hx'
/-
**EReal.add_ne_top_iff_of_ne_bot_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：add_ne_top_iff_of_ne_bot_of_ne_top {x y : EReal} (hy : y != ⊥) (hy' : y !=
 ⊤) : x + y != ⊤ ↔ x != ⊤
参数：hy : y != ⊥；hy' : y != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `EReal.top_add_of_ne_bot`：top_add_of_ne_bot {x : EReal} (h : x != ⊥) : ⊤ 
+ x = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma add_ne_top_iff_of_ne_bot_of_ne_top {x y : EReal} (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ := by
  induction x <;> simp [EReal.add_ne_top_iff_ne_top₂, hy, hy']

/-! ### Negation -/

/-- negation on `EReal` -/
/-
**EReal.neg** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
形式化陈述：EReal → EReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
negation on `EReal`
-/
protected def neg : EReal → EReal
  | ⊥ => ⊤
  | ⊤ => ⊥
  | (x : ℝ) => (-x : ℝ)
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg EReal := ⟨EReal.neg⟩
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubNegZeroMonoid EReal where
  neg_zero := congr_arg Real.toEReal neg_zero
  zsmul := zsmulRec

@[simp]
/-
**EReal.neg_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：neg_top : -(⊤ : EReal) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_top : -(⊤ : EReal) = ⊥ :=
  rfl

@[simp]
/-
**EReal.neg_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：neg_bot : -(⊥ : EReal) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_bot : -(⊥ : EReal) = ⊤ :=
  rfl
/-
**EReal.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x : ℝ), ↑(-x) = -↑x
参数：x : ℝ；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem coe_neg (x : ℝ) : (↑(-x) : EReal) = -↑x := rfl
/-
**EReal.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x y : ℝ), ↑(x - y) = ↑x - ↑y
参数：x y : ℝ；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem coe_sub (x y : ℝ) : (↑(x - y) : EReal) = x - y := rfl

@[norm_cast]
/-
**EReal.coe_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_zsmul (n : Int) (x : Real) : (↑(n • x) : EReal) = n • (x : EReal)
参数：n : Int；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zsmul'`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLi
ke F G H] [inst_1 : SubNegMonoid G]   [inst_2 : SubNegMonoid H] [AddMonoidHomCla
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `EReal.coe_zero`：coe_zero : ((0 : Real) : EReal) = 0
· 使用定理 `EReal.coe_add`：coe_add (x y : Real) : (↑(x + y) : EReal) = x + y
· 使用定理 `EReal.coe_neg`：∀ (x : ℝ), ↑(-x) = -↑x
-/
theorem coe_zsmul (n : ℤ) (x : ℝ) : (↑(n • x) : EReal) = n • (x : EReal) :=
  map_zsmul' (⟨⟨(↑), coe_zero⟩, coe_add⟩ : ℝ →+ EReal) coe_neg _ _
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InvolutiveNeg EReal where
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : ℝ) => congr_arg Real.toEReal (neg_neg a)

@[simp]
/-
**EReal.toReal_neg_eq** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a : EReal}, (-a).toReal = -a.toReal
参数：-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toReal_neg_eq : ∀ {a : EReal}, toReal (-a) = -toReal a
  | ⊤ => by simp
  | ⊥ => by simp
  | (x : ℝ) => rfl

@[simp]
/-
**EReal.neg_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：neg_eq_top_iff {x : EReal} : -x = ⊤ ↔ x = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
-/
theorem neg_eq_top_iff {x : EReal} : -x = ⊤ ↔ x = ⊥ :=
  neg_injective.eq_iff' rfl

@[simp]
/-
**EReal.neg_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：neg_eq_bot_iff {x : EReal} : -x = ⊥ ↔ x = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
-/
theorem neg_eq_bot_iff {x : EReal} : -x = ⊥ ↔ x = ⊤ :=
  neg_injective.eq_iff' rfl

@[simp]
/-
**EReal.neg_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：neg_eq_zero_iff {x : EReal} : -x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem neg_eq_zero_iff {x : EReal} : -x = 0 ↔ x = 0 :=
  neg_injective.eq_iff' neg_zero
/-
**EReal.neg_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：neg_strictAnti : StrictAnti (- · : EReal -> EReal)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithBot.strictAnti_iff`：strictAnti_iff {f : WithBot α -> β} : StrictAnti
 f ↔ StrictAnti (fun a => f a : α -> β) ∧ forall x : α, f x < f ⊥
· 使用定理 `WithTop.strictAnti_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder
 α] [inst_1 : Preorder β] {f : WithTop α → β},   StrictAnti f ↔ (StrictAnti fun 
a => f ↑a) ∧…
· 使用定理 `StrictMono.comp_strictAnti`：StrictMono.comp_strictAnti (hg : StrictMono 
g) (hf : StrictAnti f) : StrictAnti (g ∘ f)
· 使用定理 `EReal.coe_strictMono`：coe_strictMono : StrictMono Real.toEReal
· 使用定理 `neg_lt_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a < b → -b < -a
· 使用定理 `EReal.bot_lt_coe`：bot_lt_coe (x : Real) : (⊥ : EReal) < x
· 使用定理 `WithTop.forall`：∀ {α : Type u_1} {p : WithTop α → Prop}, (∀ (x : WithTop
 α), p x) ↔ p ⊤ ∧ ∀ (x : α), p ↑x
· 使用定理 `bot_lt_top`：bot_lt_top : (⊥ : α) < ⊤
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤
-/
theorem neg_strictAnti : StrictAnti (- · : EReal → EReal) :=
  WithBot.strictAnti_iff.2 ⟨WithTop.strictAnti_iff.2
    ⟨coe_strictMono.comp_strictAnti fun _ _ => neg_lt_neg, fun _ => bot_lt_coe _⟩,
      WithTop.forall.2 ⟨bot_lt_top, fun _ => coe_lt_top _⟩⟩
/-
**EReal.neg_le_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, -a ≤ -b ↔ b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.le_iff_ge`：StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α}
 : f a <= f b ↔ b <= a
· 使用定理 `EReal.neg_strictAnti`：neg_strictAnti : StrictAnti (- · : EReal -> EReal)
-/
@[simp] theorem neg_le_neg_iff {a b : EReal} : -a ≤ -b ↔ b ≤ a := neg_strictAnti.le_iff_ge
/-
**EReal.neg_lt_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, -a < -b ↔ b < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.lt_iff_gt`：StrictAnti.lt_iff_gt (hf : StrictAnti f) {a b : α}
 : f a < f b ↔ b < a
· 使用定理 `EReal.neg_strictAnti`：neg_strictAnti : StrictAnti (- · : EReal -> EReal)
-/
@[simp] theorem neg_lt_neg_iff {a b : EReal} : -a < -b ↔ b < a := neg_strictAnti.lt_iff_gt

/-- `-a ≤ b` if and only if `-b ≤ a` on `EReal`. -/
/-
**EReal.neg_le** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, -a ≤ b ↔ -b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.neg_le_neg_iff`：∀ {a b : EReal}, -a ≤ -b ↔ b ≤ a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`-a ≤ b` if and only if `-b ≤ a` on `EReal`.
-/
protected theorem neg_le {a b : EReal} : -a ≤ b ↔ -b ≤ a := by
  rw [← neg_le_neg_iff, neg_neg]

/-- If `-a ≤ b` then `-b ≤ a` on `EReal`. -/
/-
**EReal.neg_le_of_neg_le** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, -a ≤ b → -b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.neg_le`：∀ {a b : EReal}, -a ≤ b ↔ -b ≤ a

--- 原说明 ---
If `-a ≤ b` then `-b ≤ a` on `EReal`.
-/
protected theorem neg_le_of_neg_le {a b : EReal} (h : -a ≤ b) : -b ≤ a := EReal.neg_le.mp h

/-- `a ≤ -b` if and only if `b ≤ -a` on `EReal`. -/
/-
**EReal.le_neg** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, a ≤ -b ↔ b ≤ -a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.neg_le_neg_iff`：∀ {a b : EReal}, -a ≤ -b ↔ b ≤ a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`a ≤ -b` if and only if `b ≤ -a` on `EReal`.
-/
protected theorem le_neg {a b : EReal} : a ≤ -b ↔ b ≤ -a := by
  rw [← neg_le_neg_iff, neg_neg]

/-- If `a ≤ -b` then `b ≤ -a` on `EReal`. -/
/-
**EReal.le_neg_of_le_neg** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, a ≤ -b → b ≤ -a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.le_neg`：∀ {a b : EReal}, a ≤ -b ↔ b ≤ -a

--- 原说明 ---
If `a ≤ -b` then `b ≤ -a` on `EReal`.
-/
protected theorem le_neg_of_le_neg {a b : EReal} (h : a ≤ -b) : b ≤ -a := EReal.le_neg.mp h

/-- `-a < b` if and only if `-b < a` on `EReal`. -/
/-
**EReal.neg_lt_comm** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：neg_lt_comm {a b : EReal} : -a < b ↔ -b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.neg_lt_neg_iff`：∀ {a b : EReal}, -a < -b ↔ b < a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`-a < b` if and only if `-b < a` on `EReal`.
-/
theorem neg_lt_comm {a b : EReal} : -a < b ↔ -b < a := by rw [← neg_lt_neg_iff, neg_neg]

/-- If `-a < b` then `-b < a` on `EReal`. -/
/-
**EReal.neg_lt_of_neg_lt** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, -a < b → -b < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.neg_lt_comm`：neg_lt_comm {a b : EReal} : -a < b ↔ -b < a

--- 原说明 ---
If `-a < b` then `-b < a` on `EReal`.
-/
protected theorem neg_lt_of_neg_lt {a b : EReal} (h : -a < b) : -b < a := neg_lt_comm.mp h

/-- `-a < b` if and only if `-b < a` on `EReal`. -/
/-
**EReal.lt_neg_comm** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：lt_neg_comm {a b : EReal} : a < -b ↔ b < -a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.neg_lt_neg_iff`：∀ {a b : EReal}, -a < -b ↔ b < a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`-a < b` if and only if `-b < a` on `EReal`.
-/
theorem lt_neg_comm {a b : EReal} : a < -b ↔ b < -a := by
  rw [← neg_lt_neg_iff, neg_neg]
/-
**EReal.neg_lt_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a : EReal}, -a < 0 ↔ 0 < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.neg_lt_comm`：neg_lt_comm {a b : EReal} : -a < b ↔ -b < a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] protected theorem neg_lt_zero {a : EReal} : -a < 0 ↔ 0 < a := by rw [neg_lt_comm, neg_zero]
/-
**EReal.neg_le_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a : EReal}, -a ≤ 0 ↔ 0 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.neg_le`：∀ {a b : EReal}, -a ≤ b ↔ -b ≤ a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] protected theorem neg_le_zero {a : EReal} : -a ≤ 0 ↔ 0 ≤ a := by rw [EReal.neg_le, neg_zero]
/-
**EReal.neg_pos** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a : EReal}, 0 < -a ↔ a < 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.lt_neg_comm`：lt_neg_comm {a b : EReal} : a < -b ↔ b < -a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] protected theorem neg_pos {a : EReal} : 0 < -a ↔ a < 0 := by rw [lt_neg_comm, neg_zero]
/-
**EReal.neg_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a : EReal}, 0 ≤ -a ↔ a ≤ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.le_neg`：∀ {a b : EReal}, a ≤ -b ↔ b ≤ -a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] protected theorem neg_nonneg {a : EReal} : 0 ≤ -a ↔ a ≤ 0 := by rw [EReal.le_neg, neg_zero]

/-- If `a < -b` then `b < -a` on `EReal`. -/
/-
**EReal.lt_neg_of_lt_neg** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, a < -b → b < -a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.lt_neg_comm`：lt_neg_comm {a b : EReal} : a < -b ↔ b < -a

--- 原说明 ---
If `a < -b` then `b < -a` on `EReal`.
-/
protected theorem lt_neg_of_lt_neg {a b : EReal} (h : a < -b) : b < -a := lt_neg_comm.mp h

/-- Negation as an order reversing isomorphism on `EReal`. -/
/-
**EReal.negOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
形式化陈述：negOrderIso : EReal ≃o ERealᵒᵈ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `EReal.neg_le_neg_iff`：∀ {a b : EReal}, -a ≤ -b ↔ b ≤ a

--- 原说明 ---
Negation as an order reversing isomorphism on `EReal`.
-/
def negOrderIso : EReal ≃o ERealᵒᵈ :=
  { Equiv.neg EReal with
    toFun := fun x => OrderDual.toDual (-x)
    invFun := fun x => -OrderDual.ofDual x
    map_rel_iff' := neg_le_neg_iff }
/-
**EReal.neg_add** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：neg_add {x y : EReal} (h1 : x != ⊥ ∨ y != ⊤) (h2 : x != ⊤ ∨ y != ⊥) : -(x 
+ y) = -x - y
参数：h1 : x != ⊥ ∨ y != ⊤；h2 : x != ⊤ ∨ y != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_add`：coe_add (x y : Real) : (↑(x + y) : EReal) = x + y
· 使用定理 `EReal.coe_neg`：∀ (x : ℝ), ↑(-x) = -↑x
· 使用定理 `EReal.coe_sub`：∀ (x y : ℝ), ↑(x - y) = ↑x - ↑y
· 使用定理 `neg_add'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a + b) = -a - b
-/
lemma neg_add {x y : EReal} (h1 : x ≠ ⊥ ∨ y ≠ ⊤) (h2 : x ≠ ⊤ ∨ y ≠ ⊥) :
    -(x + y) = -x - y := by
  induction x <;> induction y <;> try tauto
  rw [← coe_add, ← coe_neg, ← coe_neg, ← coe_sub, neg_add']
/-
**EReal.neg_sub** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：neg_sub {x y : EReal} (h1 : x != ⊥ ∨ y != ⊥) (h2 : x != ⊤ ∨ y != ⊤) : -(x 
- y) = -x + y
参数：h1 : x != ⊥ ∨ y != ⊥；h2 : x != ⊤ ∨ y != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `EReal.neg_add`：neg_add {x y : EReal} (h1 : x != ⊥ ∨ y != ⊤) (h2 : x != ⊤
 ∨ y != ⊥) : -(x + y) = -x - y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma neg_sub {x y : EReal} (h1 : x ≠ ⊥ ∨ y ≠ ⊥) (h2 : x ≠ ⊤ ∨ y ≠ ⊤) :
    -(x - y) = -x + y := by
  rw [sub_eq_add_neg, neg_add _ _, sub_eq_add_neg, neg_neg] <;> simp_all

/-- Induction principle for `EReal`s splitting into cases `↑(x : ℝ≥0∞)` and `-↑(x : ℝ≥0∞)`.
In the latter case, we additionally assume `0 < x`. -/
@[elab_as_elim]
/-
**EReal.recENNReal** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
形式化陈述：recENNReal {motive : EReal -> Sort*} (coe : forall x : Real>=0∞, motive x)
 (neg_coe : forall x : Real>=0∞, 0 < x -> motive (-x)) (x : EReal) : motive x
参数：coe : forall x : Real>=0∞, motive x；neg_coe : forall x : Real>=0∞, 0 < x -> m
otive (-x)；x : EReal。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.coe_toENNReal`：coe_toENNReal {x : EReal} (hx : 0 <= x) : (x.toENNR
eal : EReal) = x

--- 原说明 ---
Induction principle for `EReal`s splitting into cases `↑(x : ℝ≥0∞)` and `-↑(x : 
ℝ≥0∞)`.
In the latter case, we additionally assume `0 < x`.
-/
def recENNReal {motive : EReal → Sort*} (coe : ∀ x : ℝ≥0∞, motive x)
    (neg_coe : ∀ x : ℝ≥0∞, 0 < x → motive (-x)) (x : EReal) : motive x :=
  if hx : 0 ≤ x then coe_toENNReal hx ▸ coe _
  else
    haveI H₁ : 0 < -x := by simpa using hx
    haveI H₂ : x = -(-x).toENNReal := by rw [coe_toENNReal H₁.le, neg_neg]
    H₂ ▸ neg_coe _ <| by positivity

@[simp]
/-
**EReal.recENNReal_coe_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：recENNReal_coe_ennreal {motive : EReal -> Sort*} (coe : forall x : Real>=0
∞, motive x) (neg_coe : forall x : Real>=0∞, 0 < x -> motive (-x)) (x : Real>=0∞
) : recENNReal coe neg_coe x = coe x
参数：coe : forall x : Real>=0∞, motive x；neg_coe : forall x : Real>=0∞, 0 < x -> m
otive (-x)；x : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_ennreal_nonneg`：coe_ennreal_nonneg (x : Real>=0∞) : (0 : EReal
) <= x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `EReal.coe_toENNReal`：coe_toENNReal {x : EReal} (hx : 0 <= x) : (x.toENNR
eal : EReal) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.toENNReal_coe`：toENNReal_coe {x : Real>=0∞} : (x : EReal).toENNRea
l = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `heq_iff_eq`：∀ {α : Sort u_1} {a b : α}, a ≍ b ↔ a = b
-/
theorem recENNReal_coe_ennreal {motive : EReal → Sort*} (coe : ∀ x : ℝ≥0∞, motive x)
    (neg_coe : ∀ x : ℝ≥0∞, 0 < x → motive (-x)) (x : ℝ≥0∞) : recENNReal coe neg_coe x = coe x := by
  suffices ∀ y : EReal, x = y → (recENNReal coe neg_coe y : motive y) ≍ coe x from
    heq_iff_eq.mp (this x rfl)
  intro y hy
  have H₁ : 0 ≤ y := hy ▸ coe_ennreal_nonneg x
  obtain rfl : y.toENNReal = x := by simp [← hy]
  simp [recENNReal, H₁]

proof_wanted recENNReal_neg_coe_ennreal {motive : EReal → Sort*} (coe : ∀ x : ℝ≥0∞, motive x)
    (neg_coe : ∀ x : ℝ≥0∞, 0 < x → motive (-x)) {x : ℝ≥0∞} (hx : 0 < x) :
    recENNReal coe neg_coe (-x) = neg_coe x hx

/-!
### Subtraction

Subtraction on `EReal` is defined by `x - y = x + (-y)`. Since addition is badly behaved at some
points, so is subtraction. There is no standard algebraic typeclass involving subtraction that is
registered on `EReal`, beyond `SubNegZeroMonoid`, because of this bad behavior.
-/

@[simp]
/-
**EReal.bot_sub** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：bot_sub (x : EReal) : ⊥ - x = ⊥
参数：x : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥

--- 原说明 ---
### Subtraction

Subtraction on `EReal` is defined by `x - y = x + (-y)`. Since addition is badly
 behaved at some
points, so is subtraction. There is no standard algebraic typeclass involving su
btraction that is
registered on `EReal`, beyond `SubNegZeroMonoid`, because of this bad behavior.
-/
theorem bot_sub (x : EReal) : ⊥ - x = ⊥ :=
  bot_add x

@[simp]
/-
**EReal.sub_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：sub_top (x : EReal) : x - ⊤ = ⊥
参数：x : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.add_bot`：add_bot (x : EReal) : x + ⊥ = ⊥
-/
theorem sub_top (x : EReal) : x - ⊤ = ⊥ :=
  add_bot x

@[simp]
/-
**EReal.top_sub_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：top_sub_bot : (⊤ : EReal) - ⊥ = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_sub_bot : (⊤ : EReal) - ⊥ = ⊤ :=
  rfl

@[simp]
/-
**EReal.top_sub_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：top_sub_coe (x : Real) : (⊤ : EReal) - x = ⊤
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_sub_coe (x : ℝ) : (⊤ : EReal) - x = ⊤ :=
  rfl

@[simp]
/-
**EReal.coe_sub_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_sub_bot (x : Real) : (x : EReal) - ⊥ = ⊤
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub_bot (x : ℝ) : (x : EReal) - ⊥ = ⊤ :=
  rfl

@[simp]
/-
**EReal.sub_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_bot {x : EReal} (h : x != ⊥) : x - ⊥ = ⊤
参数：h : x != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma sub_bot {x : EReal} (h : x ≠ ⊥) : x - ⊥ = ⊤ := by
  cases x <;> tauto

@[simp]
/-
**EReal.top_sub** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：top_sub {x : EReal} (hx : x != ⊤) : ⊤ - x = ⊤
参数：hx : x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma top_sub {x : EReal} (hx : x ≠ ⊤) : ⊤ - x = ⊤ := by
  cases x <;> tauto

@[simp]
/-
**EReal.sub_self** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_self {x : EReal} (h_top : x != ⊤) (h_bot : x != ⊥) : x - x = 0
参数：h_top : x != ⊤；h_bot : x != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma sub_self {x : EReal} (h_top : x ≠ ⊤) (h_bot : x ≠ ⊥) : x - x = 0 := by
  cases x <;> simp_all [← coe_sub]
/-
**EReal.sub_self_le_zero** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_self_le_zero {x : EReal} : x - x <= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.bot_sub`：bot_sub (x : EReal) : ⊥ - x = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.sub_self`：sub_self {x : EReal} (h_top : x != ⊤) (h_bot : x != ⊥) :
 x - x = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `EReal.sub_top`：sub_top (x : EReal) : x - ⊤ = ⊥
-/
lemma sub_self_le_zero {x : EReal} : x - x ≤ 0 := by
  cases x <;> simp
/-
**EReal.sub_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_nonneg {x y : EReal} (h_top : x != ⊤ ∨ y != ⊤) (h_bot : x != ⊥ ∨ y != 
⊥) : 0 <= x - y ↔ y <= x
参数：h_top : x != ⊤ ∨ y != ⊤；h_bot : x != ⊥ ∨ y != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `EReal.bot_sub`：bot_sub (x : EReal) : ⊥ - x = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `EReal.sub_top`：sub_top (x : EReal) : x - ⊤ = ⊥
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用引理 `EReal.sub_bot`：sub_bot {x : EReal} (h : x != ⊥) : x - ⊥ = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `EReal.top_sub`：top_sub {x : EReal} (hx : x != ⊤) : ⊤ - x = ⊤
-/
lemma sub_nonneg {x y : EReal} (h_top : x ≠ ⊤ ∨ y ≠ ⊤) (h_bot : x ≠ ⊥ ∨ y ≠ ⊥) :
    0 ≤ x - y ↔ y ≤ x := by
  cases x <;> cases y <;> simp_all [← EReal.coe_sub]
/-
**EReal.sub_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_nonpos {x y : EReal} : x - y <= 0 ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EReal.bot_sub`：bot_sub (x : EReal) : ⊥ - x = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.sub_top`：sub_top (x : EReal) : x - ⊤ = ⊥
· 使用引理 `EReal.sub_bot`：sub_bot {x : EReal} (h : x != ⊥) : x - ⊥ = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用引理 `EReal.top_sub`：top_sub {x : EReal} (hx : x != ⊤) : ⊤ - x = ⊤
-/
lemma sub_nonpos {x y : EReal} : x - y ≤ 0 ↔ x ≤ y := by
  cases x <;> cases y <;> simp [← EReal.coe_sub]
/-
**EReal.sub_pos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_pos {x y : EReal} : 0 < x - y ↔ y < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.bot_sub`：bot_sub (x : EReal) : ⊥ - x = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.sub_top`：sub_top (x : EReal) : x - ⊤ = ⊥
· 使用引理 `EReal.sub_bot`：sub_bot {x : EReal} (h : x != ⊥) : x - ⊥ = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用引理 `EReal.top_sub`：top_sub {x : EReal} (hx : x != ⊤) : ⊤ - x = ⊤
-/
lemma sub_pos {x y : EReal} : 0 < x - y ↔ y < x := by
  cases x <;> cases y <;> simp [← EReal.coe_sub]
/-
**EReal.sub_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_neg {x y : EReal} (h_top : x != ⊤ ∨ y != ⊤) (h_bot : x != ⊥ ∨ y != ⊥) 
: x - y < 0 ↔ x < y
参数：h_top : x != ⊤ ∨ y != ⊤；h_bot : x != ⊥ ∨ y != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EReal.bot_sub`：bot_sub (x : EReal) : ⊥ - x = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `EReal.sub_top`：sub_top (x : EReal) : x - ⊤ = ⊥
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用引理 `EReal.sub_bot`：sub_bot {x : EReal} (h : x != ⊥) : x - ⊥ = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `EReal.top_sub`：top_sub {x : EReal} (hx : x != ⊤) : ⊤ - x = ⊤
-/
lemma sub_neg {x y : EReal} (h_top : x ≠ ⊤ ∨ y ≠ ⊤) (h_bot : x ≠ ⊥ ∨ y ≠ ⊥) :
    x - y < 0 ↔ x < y := by
  cases x <;> cases y <;> simp_all [← EReal.coe_sub]
/-
**EReal.sub_le_sub** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：sub_le_sub {x y z t : EReal} (h : x <= y) (h' : t <= z) : x - z <= y - t
参数：h : x <= y；h' : t <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.neg_le_neg_iff`：∀ {a b : EReal}, -a ≤ -b ↔ b ≤ a
-/
theorem sub_le_sub {x y z t : EReal} (h : x ≤ y) (h' : t ≤ z) : x - z ≤ y - t :=
  add_le_add h (neg_le_neg_iff.2 h')
/-
**EReal.sub_lt_sub_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：sub_lt_sub_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z <= t) (hz : z
 != ⊥) (ht : t != ⊤) : x - t < y - z
参数：h : x < y；h' : z <= t；hz : z != ⊥；ht : t != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.add_lt_add_of_lt_of_le`：add_lt_add_of_lt_of_le {x y z t : EReal} (
h : x < y) (h' : z <= t) (hz : z != ⊥) (ht : t != ⊤) : x + z < y + t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.neg_le_neg_iff`：∀ {a b : EReal}, -a ≤ -b ↔ b ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem sub_lt_sub_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x - t < y - z :=
  add_lt_add_of_lt_of_le h (neg_le_neg_iff.2 h') (by simp [ht]) (by simp [hz])
/-
**EReal.coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal** 是 Mathlib 中的一个定理，位于命名空
间 `EReal`。
形式化陈述：coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal (x : Real) : (x : EReal) =
 Real.toNNReal x - Real.toNNReal (-x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_of_nonpos`：toNNReal_of_nonpos {r : Real} : r <= 0 -> Real.
toNNReal r = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
· 使用定理 `EReal.coe_ennreal_zero`：coe_ennreal_zero : ((0 : Real>=0∞) : EReal) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `EReal.coe_nnreal_eq_coe_real`：coe_nnreal_eq_coe_real (x : Real>=0) : ((x
 : Real>=0∞) : EReal) = (x : Real)
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `EReal.coe_neg`：∀ (x : ℝ), ↑(-x) = -↑x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal (x : ℝ) :
    (x : EReal) = Real.toNNReal x - Real.toNNReal (-x) := by
  rcases le_total 0 x with (h | h)
  · lift x to ℝ≥0 using h
    rw [Real.toNNReal_of_nonpos (neg_nonpos.mpr x.coe_nonneg), Real.toNNReal_coe, ENNReal.coe_zero,
      coe_ennreal_zero, sub_zero]
    rfl
  · rw [Real.toNNReal_of_nonpos h, ENNReal.coe_zero, coe_ennreal_zero, coe_nnreal_eq_coe_real,
      Real.coe_toNNReal, zero_sub, coe_neg, neg_neg]
    exact neg_nonneg.2 h
/-
**EReal.toReal_sub** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：toReal_sub {x y : EReal} (hx : x != ⊤) (h'x : x != ⊥) (hy : y != ⊤) (h'y :
 y != ⊥) : toReal (x - y) = toReal x - toReal y
参数：hx : x != ⊤；h'x : x != ⊥；hy : y != ⊤；h'y : y != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
-/
theorem toReal_sub {x y : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toReal (x - y) = toReal x - toReal y := by
  lift x to ℝ using ⟨hx, h'x⟩
  lift y to ℝ using ⟨hy, h'y⟩
  rfl
/-
**EReal.toENNReal_sub** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_sub {x y : EReal} (hy : 0 <= y) : (x - y).toENNReal = x.toENNRea
l - y.toENNReal
参数：hy : 0 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.bot_sub`：bot_sub (x : EReal) : ⊥ - x = ⊥
· 使用引理 `EReal.toENNReal_of_ne_top`：toENNReal_of_ne_top {x : EReal} (hx : x != ⊤)
 : x.toENNReal = ENNReal.ofReal x.toReal
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EReal.sub_top`：sub_top (x : EReal) : x - ⊤ = ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `EReal.toENNReal_of_nonpos`：toENNReal_of_nonpos {x : EReal} (hx : x <= 0)
 : x.toENNReal = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `EReal.sub_nonpos`：sub_nonpos {x y : EReal} : x - y <= 0 ↔ x <= y
· 使用定理 `EReal.coe_le_coe_iff`：∀ {x y : ℝ}, ↑x ≤ ↑y ↔ x ≤ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用引理 `EReal.toENNReal_le_toENNReal`：toENNReal_le_toENNReal {x y : EReal} (h : 
x <= y) : x.toENNReal <= y.toENNReal
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_beq_false`：∀ {α : Type u_1} [inst : BEq α] [ReflBEq α] {a b : α}, 
(a == b) = false → a ≠ b
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `Std.LawfulBEqOrd.equivBEq`：∀ {α : Type u} [inst : BEq α] [inst_1 : Ord α
] [Std.LawfulBEqOrd α] [Std.TransOrd α], EquivBEq α
· 使用定理 `Std.LawfulBCmp.toLawfulBEqCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : 
LT α} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   S
td.LawfulBEqCmp cmp
· 使用定理 `instLawfulBCmpCompare_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], 
Std.LawfulBCmp compare
· 使用定理 `Std.LawfulBCmp.toTransCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : LT α
} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   Std.T
ransCmp cmp
· 使用定理 `EReal.coe_sub`：∀ (x y : ℝ), ↑(x - y) = ↑x - ↑y
（共 38 条，此处仅展示前 30 条）
-/
lemma toENNReal_sub {x y : EReal} (hy : 0 ≤ y) :
    (x - y).toENNReal = x.toENNReal - y.toENNReal := by
  induction x <;> induction y <;> try {· simp_all [zero_tsub, ENNReal.sub_top]}
  rename_i x y
  by_cases hxy : x ≤ y
  · rw [toENNReal_of_nonpos <| sub_nonpos.mpr <| EReal.coe_le_coe_iff.mpr hxy]
    exact (tsub_eq_zero_of_le <| toENNReal_le_toENNReal <| EReal.coe_le_coe_iff.mpr hxy).symm
  · rw [toENNReal_of_ne_top (ne_of_beq_false rfl).symm, ← coe_sub, toReal_coe,
      ofReal_sub x (EReal.coe_nonneg.mp hy)]
    simp
/-
**EReal.add_sub_add_comm** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：add_sub_add_comm {a b c d : EReal} (h1 : c != ⊥ ∨ d != ⊤) (h2 : c != ⊤ ∨ d
 != ⊥) : a + b - (c + d) = (a - c) + (b - d)
参数：h1 : c != ⊥ ∨ d != ⊤；h2 : c != ⊤ ∨ d != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `EReal.neg_add`：neg_add {x y : EReal} (h1 : x != ⊥ ∨ y != ⊤) (h2 : x != ⊤
 ∨ y != ⊥) : -(x + y) = -x - y
-/
lemma add_sub_add_comm {a b c d : EReal} (h1 : c ≠ ⊥ ∨ d ≠ ⊤) (h2 : c ≠ ⊤ ∨ d ≠ ⊥) :
    a + b - (c + d) = (a - c) + (b - d) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, EReal.neg_add h1 h2, sub_eq_add_neg]
  grind
/-
**EReal.add_sub_cancel_right** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：add_sub_cancel_right {a : EReal} {b : Real} : a + b - b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
lemma add_sub_cancel_right {a : EReal} {b : Real} : a + b - b = a := by
  cases a <;> norm_cast
  exact _root_.add_sub_cancel_right _ _
/-
**EReal.add_sub_cancel_left** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：add_sub_cancel_left {a : EReal} {b : Real} : b + a - b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `EReal.add_sub_cancel_right`：add_sub_cancel_right {a : EReal} {b : Real} 
: a + b - b = a
-/
lemma add_sub_cancel_left {a : EReal} {b : Real} : b + a - b = a := by
  rw [add_comm, EReal.add_sub_cancel_right]
/-
**EReal.sub_add_cancel** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_add_cancel {a : EReal} {b : Real} : a - b + b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用引理 `EReal.add_sub_cancel_left`：add_sub_cancel_left {a : EReal} {b : Real} : 
b + a - b = a
-/
lemma sub_add_cancel {a : EReal} {b : Real} : a - b + b = a := by
  rw [add_comm, ← add_sub_assoc, add_sub_cancel_left]
/-
**EReal.sub_add_cancel_right** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_add_cancel_right {a : EReal} {b : Real} : b - (a + b) = -a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b : G), a 
- (b + a) = -b
-/
lemma sub_add_cancel_right {a : EReal} {b : Real} : b - (a + b) = -a := by
  cases a <;> norm_cast
  exact _root_.sub_add_cancel_right _ _
/-
**EReal.sub_add_cancel_left** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_add_cancel_left {a : EReal} {b : Real} : b - (b + a) = -a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `EReal.sub_add_cancel_right`：sub_add_cancel_right {a : EReal} {b : Real} 
: b - (a + b) = -a
-/
lemma sub_add_cancel_left {a : EReal} {b : Real} : b - (b + a) = -a := by
  rw [add_comm, sub_add_cancel_right]
/-
**EReal.le_sub_iff_add_le** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：le_sub_iff_add_le {a b c : EReal} (hb : b != ⊥ ∨ c != ⊥) (ht : b != ⊤ ∨ c 
!= ⊤) : a <= c - b ↔ a + b <= c
参数：hb : b != ⊥ ∨ c != ⊥；ht : b != ⊤ ∨ c != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EReal.sub_bot`：sub_bot {x : EReal} (h : x != ⊥) : x - ⊥ = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `EReal.add_bot`：add_bot (x : EReal) : x + ⊥ = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddLECancellable.add_le_add_iff_right`：∀ {α : Type u_1} [inst : LE α] [i
nst_1 : Add α] [IsAddCommutative α] [AddLeftMono α] {a b c : α},   AddLECancella
ble a → (b + a ≤ c + a ↔ b …
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `EReal.addLECancellable_coe`：∀ (x : ℝ), AddLECancellable ↑x
· 使用引理 `EReal.sub_add_cancel`：sub_add_cancel {a : EReal} {b : Real} : a - b + b 
= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `EReal.sub_top`：sub_top (x : EReal) : x - ⊤ = ⊥
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.add_top_iff_ne_bot`：add_top_iff_ne_bot {x : EReal} : x + ⊤ = ⊤ ↔ x
 != ⊥
-/
lemma le_sub_iff_add_le {a b c : EReal} (hb : b ≠ ⊥ ∨ c ≠ ⊥) (ht : b ≠ ⊤ ∨ c ≠ ⊤) :
    a ≤ c - b ↔ a + b ≤ c := by
  induction b with
  | bot =>
    simp only [ne_eq, not_true_eq_false, false_or] at hb
    simp only [sub_bot hb, le_top, add_bot, bot_le]
  | coe b =>
    rw [← (addLECancellable_coe b).add_le_add_iff_right, sub_add_cancel]
  | top =>
    simp only [ne_eq, not_true_eq_false, false_or, sub_top, le_bot_iff] at ht ⊢
    refine ⟨fun h ↦ h ▸ (bot_add ⊤).symm ▸ bot_le, fun h ↦ ?_⟩
    by_contra ha
    exact (h.trans_lt (Ne.lt_top ht)).ne (add_top_iff_ne_bot.2 ha)
/-
**EReal.sub_le_iff_le_add** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_le_iff_le_add {a b c : EReal} (h₁ : b != ⊥ ∨ c != ⊤) (h₂ : b != ⊤ ∨ c 
!= ⊥) : a - b <= c ↔ a <= c + b
参数：h₁ : b != ⊥ ∨ c != ⊤；h₂ : b != ⊤ ∨ c != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `EReal.le_sub_iff_add_le`：le_sub_iff_add_le {a b c : EReal} (hb : b != ⊥ 
∨ c != ⊥) (ht : b != ⊤ ∨ c != ⊤) : a <= c - b ↔ a + b <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma sub_le_iff_le_add {a b c : EReal} (h₁ : b ≠ ⊥ ∨ c ≠ ⊤) (h₂ : b ≠ ⊤ ∨ c ≠ ⊥) :
    a - b ≤ c ↔ a ≤ c + b := by
  suffices a + (-b) ≤ c ↔ a ≤ c - (-b) by simpa [sub_eq_add_neg]
  refine (le_sub_iff_add_le ?_ ?_).symm <;> simpa
/-
**EReal.lt_sub_iff_add_lt** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b c : EReal}, b ≠ ⊥ ∨ c ≠ ⊤ → b ≠ ⊤ ∨ c ≠ ⊥ → (c < a - b ↔ c + b < a)
参数：c < a - b ↔ c + b < a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用引理 `EReal.sub_le_iff_le_add`：sub_le_iff_le_add {a b c : EReal} (h₁ : b != ⊥ 
∨ c != ⊤) (h₂ : b != ⊤ ∨ c != ⊥) : a - b <= c ↔ a <= c + b
-/
protected theorem lt_sub_iff_add_lt {a b c : EReal} (h₁ : b ≠ ⊥ ∨ c ≠ ⊤) (h₂ : b ≠ ⊤ ∨ c ≠ ⊥) :
    c < a - b ↔ c + b < a :=
  lt_iff_lt_of_le_iff_le (sub_le_iff_le_add h₁ h₂)
/-
**EReal.sub_le_of_le_add** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：sub_le_of_le_add {a b c : EReal} (h : a <= b + c) : a - c <= b
参数：h : a <= b + c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `EReal.add_bot`：add_bot (x : EReal) : x + ⊥ = ⊥
· 使用定理 `EReal.bot_sub`：bot_sub (x : EReal) : ⊥ - x = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `EReal.sub_le_iff_le_add`：sub_le_iff_le_add {a b c : EReal} (h₁ : b != ⊥ 
∨ c != ⊤) (h₂ : b != ⊤ ∨ c != ⊥) : a - b <= c ↔ a <= c + b
· 使用定理 `EReal.coe_ne_bot`：coe_ne_bot (x : Real) : (x : EReal) != ⊥
· 使用定理 `EReal.coe_ne_top`：coe_ne_top (x : Real) : (x : EReal) != ⊤
· 使用定理 `EReal.sub_top`：sub_top (x : EReal) : x - ⊤ = ⊥
-/
theorem sub_le_of_le_add {a b c : EReal} (h : a ≤ b + c) : a - c ≤ b := by
  induction c with
  | bot => rw [add_bot, le_bot_iff] at h; simp only [h, bot_sub, bot_le]
  | coe c => exact (sub_le_iff_le_add (.inl (coe_ne_bot c)) (.inl (coe_ne_top c))).2 h
  | top => simp only [sub_top, bot_le]

/-- See also `EReal.sub_le_of_le_add`. -/
/-
**EReal.sub_le_of_le_add'** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：sub_le_of_le_add' {a b c : EReal} (h : a <= b + c) : a - b <= c
参数：h : a <= b + c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.sub_le_of_le_add`：sub_le_of_le_add {a b c : EReal} (h : a <= b + c
) : a - c <= b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
See also `EReal.sub_le_of_le_add`.
-/
theorem sub_le_of_le_add' {a b c : EReal} (h : a ≤ b + c) : a - b ≤ c :=
  sub_le_of_le_add (add_comm b c ▸ h)
/-
**EReal.add_le_of_le_sub** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：add_le_of_le_sub {a b c : EReal} (h : a <= b - c) : a + c <= b
参数：h : a <= b - c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `EReal.sub_le_of_le_add`：sub_le_of_le_add {a b c : EReal} (h : a <= b + c
) : a - c <= b
-/
lemma add_le_of_le_sub {a b c : EReal} (h : a ≤ b - c) : a + c ≤ b := by
  rw [← neg_neg c]
  exact sub_le_of_le_add h
/-
**EReal.sub_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_lt_iff {a b c : EReal} (h₁ : b != ⊥ ∨ c != ⊥) (h₂ : b != ⊤ ∨ c != ⊤) :
 c - b < a ↔ c < a + b
参数：h₁ : b != ⊥ ∨ c != ⊥；h₂ : b != ⊤ ∨ c != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用引理 `EReal.le_sub_iff_add_le`：le_sub_iff_add_le {a b c : EReal} (hb : b != ⊥ 
∨ c != ⊥) (ht : b != ⊤ ∨ c != ⊤) : a <= c - b ↔ a + b <= c
-/
lemma sub_lt_iff {a b c : EReal} (h₁ : b ≠ ⊥ ∨ c ≠ ⊥) (h₂ : b ≠ ⊤ ∨ c ≠ ⊤) :
    c - b < a ↔ c < a + b :=
  lt_iff_lt_of_le_iff_le (le_sub_iff_add_le h₁ h₂)
/-
**EReal.add_lt_of_lt_sub** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：add_lt_of_lt_sub {a b c : EReal} (h : a < b - c) : a + c < b
参数：h : a < b - c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `EReal.sub_le_of_le_add`：sub_le_of_le_add {a b c : EReal} (h : a <= b + c
) : a - c <= b
-/
lemma add_lt_of_lt_sub {a b c : EReal} (h : a < b - c) : a + c < b := by
  contrapose! h
  exact sub_le_of_le_add h
/-
**EReal.sub_lt_of_lt_add** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_lt_of_lt_add {a b c : EReal} (h : a < b + c) : a - c < b
参数：h : a < b + c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.add_lt_of_lt_sub`：add_lt_of_lt_sub {a b c : EReal} (h : a < b - c)
 : a + c < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma sub_lt_of_lt_add {a b c : EReal} (h : a < b + c) : a - c < b :=
  add_lt_of_lt_sub <| by rwa [sub_eq_add_neg, neg_neg]

/-- See also `EReal.sub_lt_of_lt_add`. -/
/-
**EReal.sub_lt_of_lt_add'** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_lt_of_lt_add' {a b c : EReal} (h : a < b + c) : a - b < c
参数：h : a < b + c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.sub_lt_of_lt_add`：sub_lt_of_lt_add {a b c : EReal} (h : a < b + c)
 : a - c < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
See also `EReal.sub_lt_of_lt_add`.
-/
lemma sub_lt_of_lt_add' {a b c : EReal} (h : a < b + c) : a - b < c :=
  sub_lt_of_lt_add <| by rwa [add_comm]
/-
**EReal.sub_lt_sub_of_le_of_gt** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_lt_sub_of_le_of_gt {x y z t : EReal} (h : x <= y) (h' : z < t) (hx_top
 : x != ⊤) (hy_bot : y != ⊥) : x - t < y - z
参数：h : x <= y；h' : z < t；hx_top : x != ⊤；hy_bot : y != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.sub_lt_of_lt_add'`：sub_lt_of_lt_add' {a b c : EReal} (h : a < b + 
c) : a - b < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_assoc'`：∀ {G : Type u_3} [inst : SubNegMonoid G] (a b c : G), a 
+ (b - c) = a + b - c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `EReal.top_add_of_ne_bot`：top_add_of_ne_bot {x : EReal} (h : x != ⊥) : ⊤ 
+ x = ⊤
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `EReal.sub_pos`：sub_pos {x y : EReal} : 0 < x - y ↔ y < x
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `EReal.add_top_of_ne_bot`：add_top_of_ne_bot {x : EReal} (h : x != ⊥) : x 
+ ⊤ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_toReal`：coe_toReal {x : EReal} (hx : x != ⊤) (h'x : x != ⊥) : 
(x.toReal : EReal) = x
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `EReal.toReal_pos`：toReal_pos {x : EReal} (hx : 0 < x) (h'x : x != ⊤) : 0
 < x.toReal
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `EReal.add_lt_add`：add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t)
 : x + z < y + t
-/
lemma sub_lt_sub_of_le_of_gt {x y z t : EReal} (h : x ≤ y) (h' : z < t)
    (hx_top : x ≠ ⊤) (hy_bot : y ≠ ⊥) :
    x - t < y - z := by
  refine sub_lt_of_lt_add' ?_
  rw [add_sub_assoc', add_comm, add_sub_assoc]
  by_cases hy_top : y = ⊤
  · rw [hy_top, top_add_of_ne_bot]
    · exact hx_top.lt_top
    · exact ne_bot_of_le_ne_bot (by simp) (sub_pos.mpr h').le
  by_cases hxy : x = y
  · rw [hxy]
    lift y to ℝ using ⟨hy_top, hy_bot⟩
    by_cases htz_top : t - z = ⊤
    · simp_all
    rw [← coe_toReal htz_top <| ne_bot_of_le_ne_bot (by simp) (sub_pos.mpr h').le]
    norm_cast
    refine lt_add_of_pos_right y ?_
    exact EReal.toReal_pos (sub_pos.mpr h') htz_top
  · rw [← add_zero x]
    exact add_lt_add (by grind) (sub_pos.mpr h')

/-! ### Addition and order -/

set_option backward.isDefEq.respectTransparency false in
/-
**EReal.le_of_forall_lt_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：le_of_forall_lt_iff_le {x y : EReal} : (forall z : Real, x < z -> y <= z) 
↔ y <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.le_of_forall_lt_iff_le`：le_of_forall_lt_iff_le : (forall z : α, 
x < z -> y <= z) ↔ y <= x
· 使用定理 `WithTop.denselyOrdered`：∀ {α : Type u_1} [inst : LT α] [DenselyOrdered α
] [NoMaxOrder α], DenselyOrdered (WithTop α)
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `WithTop.noMinOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α] [Nonem
pty α], NoMinOrder (WithTop α)
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.forall`：∀ {α : Type u_1} {p : WithTop α → Prop}, (∀ (x : WithTop
 α), p x) ↔ p ⊤ ∧ ∀ (x : α), p ↑x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
### Addition and order
-/
lemma le_of_forall_lt_iff_le {x y : EReal} : (∀ z : ℝ, x < z → y ≤ z) ↔ y ≤ x := by
  refine ⟨fun h ↦ WithBot.le_of_forall_lt_iff_le.1 ?_, fun h _ x_z ↦ h.trans x_z.le⟩
  rw [WithTop.forall]
  aesop

set_option backward.isDefEq.respectTransparency false in
/-
**EReal.ge_of_forall_gt_iff_ge** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：ge_of_forall_gt_iff_ge {x y : EReal} : (forall z : Real, z < y -> z <= x) 
↔ y <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.ge_of_forall_gt_iff_ge`：ge_of_forall_gt_iff_ge : (forall z : α, 
z < x -> z <= y) ↔ x <= y
· 使用定理 `WithTop.denselyOrdered`：∀ {α : Type u_1} [inst : LT α] [DenselyOrdered α
] [NoMaxOrder α], DenselyOrdered (WithTop α)
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `WithTop.noMinOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α] [Nonem
pty α], NoMinOrder (WithTop α)
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.forall`：∀ {α : Type u_1} {p : WithTop α → Prop}, (∀ (x : WithTop
 α), p x) ↔ p ⊤ ∧ ∀ (x : α), p ↑x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma ge_of_forall_gt_iff_ge {x y : EReal} : (∀ z : ℝ, z < y → z ≤ x) ↔ y ≤ x := by
  refine ⟨fun h ↦ WithBot.ge_of_forall_gt_iff_ge.1 ?_, fun h _ x_z ↦ x_z.le.trans h⟩
  rw [WithTop.forall]
  aesop
/-
**EReal.exists_lt_add_left** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_lt_add_left {a b c : EReal} (hc : c < a + b) : ∃ a' < a, c < a' + b := by
  obtain ⟨a', hc', ha'⟩ := exists_between (sub_lt_of_lt_add hc)
  refine ⟨a', ha', (sub_lt_iff (.inl ?_) (.inr hc.ne_top)).1 hc'⟩
  contrapose! hc
  exact hc ▸ (add_bot a).symm ▸ bot_le
/-
**EReal.exists_lt_add_right** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_lt_add_right {a b c : EReal} (hc : c < a + b) : ∃ b' < b, c < a + b' := by
  simp_rw [add_comm a] at hc ⊢; exact exists_lt_add_left hc
/-
**EReal.add_le_of_forall_lt** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：add_le_of_forall_lt {a b c : EReal} (h : forall a' < a, forall b' < b, a' 
+ b' <= c) : a + b <= c
参数：h : forall a' < a, forall b' < b, a' + b' <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_lt_imp_le_of_dense`：∀ {α : Type u_2} [inst : LinearOrder α]
 [DenselyOrdered α] {a₁ a₂ : α}, (∀ a < a₂, a ≤ a₁) → a₂ ≤ a₁
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `_private.Mathlib.Data.EReal.Operations.0.EReal.exists_lt_add_left`：∀ {a 
b c : EReal}, c < a + b → ∃ a' < a, c < a' + b
· 使用定理 `_private.Mathlib.Data.EReal.Operations.0.EReal.exists_lt_add_right`：∀ {a
 b c : EReal}, c < a + b → ∃ b' < b, c < a + b'
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma add_le_of_forall_lt {a b c : EReal} (h : ∀ a' < a, ∀ b' < b, a' + b' ≤ c) : a + b ≤ c := by
  refine le_of_forall_lt_imp_le_of_dense fun d hd ↦ ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_add_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_add_right hd
  exact hd.le.trans (h _ ha' _ hb')
/-
**EReal.le_add_of_forall_gt** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：le_add_of_forall_gt {a b c : EReal} (h₁ : a != ⊥ ∨ b != ⊤) (h₂ : a != ⊤ ∨ 
b != ⊥) (h : forall a' > a, forall b' > b, c <= a' + b') : c <= a + b
参数：h₁ : a != ⊥ ∨ b != ⊤；h₂ : a != ⊤ ∨ b != ⊥；h : forall a' > a, forall b' > b, c
 <= a' + b'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.neg_le_neg_iff`：∀ {a b : EReal}, -a ≤ -b ↔ b ≤ a
· 使用引理 `EReal.neg_add`：neg_add {x y : EReal} (h1 : x != ⊥ ∨ y != ⊤) (h2 : x != ⊤
 ∨ y != ⊥) : -(x + y) = -x - y
· 使用引理 `EReal.add_le_of_forall_lt`：add_le_of_forall_lt {a b c : EReal} (h : fora
ll a' < a, forall b' < b, a' + b' <= c) : a + b <= c
· 使用定理 `EReal.le_neg_of_le_neg`：∀ {a b : EReal}, a ≤ -b → b ≤ -a
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `EReal.lt_neg_of_lt_neg`：∀ {a b : EReal}, a < -b → b < -a
-/
lemma le_add_of_forall_gt {a b c : EReal} (h₁ : a ≠ ⊥ ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ b ≠ ⊥)
    (h : ∀ a' > a, ∀ b' > b, c ≤ a' + b') : c ≤ a + b := by
  rw [← neg_le_neg_iff, neg_add h₁ h₂]
  refine add_le_of_forall_lt fun a' ha' b' hb' ↦ EReal.le_neg_of_le_neg ?_
  rw [neg_add (.inr hb'.ne_top) (.inl ha'.ne_top)]
  exact h _ (EReal.lt_neg_of_lt_neg ha') _ (EReal.lt_neg_of_lt_neg hb')
/-
**EReal._root_.ENNReal.toEReal_sub** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ENNReal.toEReal_sub {x y : ℝ≥0∞} (hy_top : y ≠ ∞) (h_le : y ≤ x) :
    (x - y).toEReal = x.toEReal - y.toEReal := by
  lift y to ℝ≥0 using hy_top
  cases x with
  | top => simp [coe_nnreal_eq_coe_real]
  | coe x =>
    simp only [coe_nnreal_eq_coe_real, ← ENNReal.coe_sub, NNReal.coe_sub (mod_cast h_le), coe_sub]

/-! ### Multiplication -/

/-
**EReal.top_mul_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：⊤ * ⊤ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Multiplication
-/
@[simp] lemma top_mul_top : (⊤ : EReal) * ⊤ = ⊤ := rfl
/-
**EReal.top_mul_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：⊤ * ⊥ = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Multiplication
-/
@[simp] lemma top_mul_bot : (⊤ : EReal) * ⊥ = ⊥ := rfl
/-
**EReal.bot_mul_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：⊥ * ⊤ = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Multiplication
-/
@[simp] lemma bot_mul_top : (⊥ : EReal) * ⊤ = ⊥ := rfl
/-
**EReal.bot_mul_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：⊥ * ⊥ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Multiplication
-/
@[simp] lemma bot_mul_bot : (⊥ : EReal) * ⊥ = ⊤ := rfl
/-
**EReal.coe_mul_top_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：coe_mul_top_of_pos {x : Real} (h : 0 < x) : (x : EReal) * ⊤ = ⊤
参数：h : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t

--- 原说明 ---
### Multiplication
-/
lemma coe_mul_top_of_pos {x : ℝ} (h : 0 < x) : (x : EReal) * ⊤ = ⊤ :=
  if_pos h
/-
**EReal.coe_mul_top_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：coe_mul_top_of_neg {x : Real} (h : x < 0) : (x : EReal) * ⊤ = ⊥
参数：h : x < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma coe_mul_top_of_neg {x : ℝ} (h : x < 0) : (x : EReal) * ⊤ = ⊥ :=
  (if_neg h.not_gt).trans (if_neg h.ne)
/-
**EReal.top_mul_coe_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：top_mul_coe_of_pos {x : Real} (h : 0 < x) : (⊤ : EReal) * x = ⊤
参数：h : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma top_mul_coe_of_pos {x : ℝ} (h : 0 < x) : (⊤ : EReal) * x = ⊤ :=
  if_pos h
/-
**EReal.top_mul_coe_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：top_mul_coe_of_neg {x : Real} (h : x < 0) : (⊤ : EReal) * x = ⊥
参数：h : x < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma top_mul_coe_of_neg {x : ℝ} (h : x < 0) : (⊤ : EReal) * x = ⊥ :=
  (if_neg h.not_gt).trans (if_neg h.ne)
/-
**EReal.mul_top_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x : EReal}, 0 < x → x * ⊤ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
· 使用引理 `EReal.coe_mul_top_of_pos`：coe_mul_top_of_pos {x : Real} (h : 0 < x) : (x
 : EReal) * ⊤ = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.coe_pos`：∀ {x : ℝ}, 0 < ↑x ↔ 0 < x
-/
lemma mul_top_of_pos : ∀ {x : EReal}, 0 < x → x * ⊤ = ⊤
  | ⊥, h => absurd h not_lt_bot
  | (x : ℝ), h => coe_mul_top_of_pos (EReal.coe_pos.1 h)
  | ⊤, _ => rfl
/-
**EReal.mul_top_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x : EReal}, x < 0 → x * ⊤ = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.coe_mul_top_of_neg`：coe_mul_top_of_neg {x : Real} (h : x < 0) : (x
 : EReal) * ⊤ = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.coe_neg'`：∀ {x : ℝ}, ↑x < 0 ↔ x < 0
· 使用定理 `not_top_lt`：not_top_lt : ¬⊤ < a
-/
lemma mul_top_of_neg : ∀ {x : EReal}, x < 0 → x * ⊤ = ⊥
  | ⊥, _ => rfl
  | (x : ℝ), h => coe_mul_top_of_neg (EReal.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt
/-
**EReal.top_mul_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤
参数：h : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用定理 `EReal.mul_top_of_pos`：∀ {x : EReal}, 0 < x → x * ⊤ = ⊤
-/
lemma top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤ := by
  rw [EReal.mul_comm]
  exact mul_top_of_pos h
/-
**EReal.top_mul_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：top_mul_of_neg {x : EReal} (h : x < 0) : ⊤ * x = ⊥
参数：h : x < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用定理 `EReal.mul_top_of_neg`：∀ {x : EReal}, x < 0 → x * ⊤ = ⊥
-/
lemma top_mul_of_neg {x : EReal} (h : x < 0) : ⊤ * x = ⊥ := by
  rw [EReal.mul_comm]
  exact mul_top_of_neg h
/-
**EReal.top_mul_coe_ennreal** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：top_mul_coe_ennreal {x : Real>=0∞} (hx : x != 0) : ⊤ * (x : EReal) = ⊤
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.top_mul_of_pos`：top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.coe_ennreal_pos`：coe_ennreal_pos {x : Real>=0∞} : (0 : EReal) < x 
↔ 0 < x
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma top_mul_coe_ennreal {x : ℝ≥0∞} (hx : x ≠ 0) : ⊤ * (x : EReal) = ⊤ :=
  top_mul_of_pos <| coe_ennreal_pos.mpr <| pos_iff_ne_zero.mpr hx
/-
**EReal.coe_ennreal_mul_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_mul_top {x : Real>=0∞} (hx : x != 0) : (x : EReal) * ⊤ = ⊤
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用引理 `EReal.top_mul_coe_ennreal`：top_mul_coe_ennreal {x : Real>=0∞} (hx : x !=
 0) : ⊤ * (x : EReal) = ⊤
-/
lemma coe_ennreal_mul_top {x : ℝ≥0∞} (hx : x ≠ 0) : (x : EReal) * ⊤ = ⊤ := by
  rw [EReal.mul_comm, top_mul_coe_ennreal hx]
/-
**EReal.coe_mul_bot_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：coe_mul_bot_of_pos {x : Real} (h : 0 < x) : (x : EReal) * ⊥ = ⊥
参数：h : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma coe_mul_bot_of_pos {x : ℝ} (h : 0 < x) : (x : EReal) * ⊥ = ⊥ :=
  if_pos h
/-
**EReal.coe_mul_bot_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：coe_mul_bot_of_neg {x : Real} (h : x < 0) : (x : EReal) * ⊥ = ⊤
参数：h : x < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma coe_mul_bot_of_neg {x : ℝ} (h : x < 0) : (x : EReal) * ⊥ = ⊤ :=
  (if_neg h.not_gt).trans (if_neg h.ne)
/-
**EReal.bot_mul_coe_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：bot_mul_coe_of_pos {x : Real} (h : 0 < x) : (⊥ : EReal) * x = ⊥
参数：h : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma bot_mul_coe_of_pos {x : ℝ} (h : 0 < x) : (⊥ : EReal) * x = ⊥ :=
  if_pos h
/-
**EReal.bot_mul_coe_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：bot_mul_coe_of_neg {x : Real} (h : x < 0) : (⊥ : EReal) * x = ⊤
参数：h : x < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma bot_mul_coe_of_neg {x : ℝ} (h : x < 0) : (⊥ : EReal) * x = ⊤ :=
  (if_neg h.not_gt).trans (if_neg h.ne)
/-
**EReal.mul_bot_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x : EReal}, 0 < x → x * ⊥ = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
· 使用引理 `EReal.coe_mul_bot_of_pos`：coe_mul_bot_of_pos {x : Real} (h : 0 < x) : (x
 : EReal) * ⊥ = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.coe_pos`：∀ {x : ℝ}, 0 < ↑x ↔ 0 < x
-/
lemma mul_bot_of_pos : ∀ {x : EReal}, 0 < x → x * ⊥ = ⊥
  | ⊥, h => absurd h not_lt_bot
  | (x : ℝ), h => coe_mul_bot_of_pos (EReal.coe_pos.1 h)
  | ⊤, _ => rfl
/-
**EReal.mul_bot_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x : EReal}, x < 0 → x * ⊥ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.coe_mul_bot_of_neg`：coe_mul_bot_of_neg {x : Real} (h : x < 0) : (x
 : EReal) * ⊥ = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.coe_neg'`：∀ {x : ℝ}, ↑x < 0 ↔ x < 0
· 使用定理 `not_top_lt`：not_top_lt : ¬⊤ < a
-/
lemma mul_bot_of_neg : ∀ {x : EReal}, x < 0 → x * ⊥ = ⊤
  | ⊥, _ => rfl
  | (x : ℝ), h => coe_mul_bot_of_neg (EReal.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt
/-
**EReal.bot_mul_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：bot_mul_of_pos {x : EReal} (h : 0 < x) : ⊥ * x = ⊥
参数：h : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用定理 `EReal.mul_bot_of_pos`：∀ {x : EReal}, 0 < x → x * ⊥ = ⊥
-/
lemma bot_mul_of_pos {x : EReal} (h : 0 < x) : ⊥ * x = ⊥ := by
  rw [EReal.mul_comm]
  exact mul_bot_of_pos h
/-
**EReal.bot_mul_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：bot_mul_of_neg {x : EReal} (h : x < 0) : ⊥ * x = ⊤
参数：h : x < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用定理 `EReal.mul_bot_of_neg`：∀ {x : EReal}, x < 0 → x * ⊥ = ⊤
-/
lemma bot_mul_of_neg {x : EReal} (h : x < 0) : ⊥ * x = ⊤ := by
  rw [EReal.mul_comm]
  exact mul_bot_of_neg h
/-
**EReal.toReal_mul** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toReal_mul {x y : EReal} : toReal (x * y) = toReal x * toReal y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.induction₂_symm`：induction₂_symm {P : EReal -> EReal -> Prop} (sym
m : forall {x y}, P x y -> P y x) (top_top : P ⊤ ⊤) (top_pos : forall x : Real, 
0 < x -> P …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `EReal.top_mul_coe_of_pos`：top_mul_coe_of_pos {x : Real} (h : 0 < x) : (⊤
 : EReal) * x = ⊤
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `EReal.top_mul_coe_of_neg`：top_mul_coe_of_neg {x : Real} (h : x < 0) : (⊤
 : EReal) * x = ⊥
· 使用引理 `EReal.coe_mul_bot_of_pos`：coe_mul_bot_of_pos {x : Real} (h : 0 < x) : (x
 : EReal) * ⊥ = ⊥
· 使用引理 `EReal.coe_mul_bot_of_neg`：coe_mul_bot_of_neg {x : Real} (h : x < 0) : (x
 : EReal) * ⊥ = ⊤
-/
lemma toReal_mul {x y : EReal} : toReal (x * y) = toReal x * toReal y := by
  induction x, y using induction₂_symm with
  | top_zero | zero_bot | top_top | top_bot | bot_bot => simp
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => norm_cast
  | top_pos _ h => simp [top_mul_coe_of_pos h]
  | top_neg _ h => simp [top_mul_coe_of_neg h]
  | pos_bot _ h => simp [coe_mul_bot_of_pos h]
  | neg_bot _ h => simp [coe_mul_bot_of_neg h]
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoZeroDivisors EReal where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    contrapose! h
    cases a <;> cases b <;> try {· simp_all [← EReal.coe_mul]}
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [EReal.bot_mul_of_neg, EReal.bot_mul_of_pos, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [EReal.mul_bot_of_pos, EReal.mul_bot_of_neg, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [EReal.mul_top_of_neg, EReal.mul_top_of_pos, h]
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [EReal.top_mul_of_pos, EReal.top_mul_of_neg, h]
/-
**EReal.mul_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_pos_iff {a b : EReal} : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.induction₂_symm`：induction₂_symm {P : EReal -> EReal -> Prop} (sym
m : forall {x y}, P x y -> P y x) (top_top : P ⊤ ⊤) (top_pos : forall x : Real, 
0 < x -> P …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `EReal.top_mul_coe_of_pos`：top_mul_coe_of_pos {x : Real} (h : 0 < x) : (⊤
 : EReal) * x = ⊤
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用引理 `EReal.top_mul_coe_of_neg`：top_mul_coe_of_neg {x : Real} (h : x < 0) : (⊤
 : EReal) * x = ⊥
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用引理 `EReal.coe_mul_bot_of_pos`：coe_mul_bot_of_pos {x : Real} (h : 0 < x) : (x
 : EReal) * ⊥ = ⊥
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `EReal.coe_mul_bot_of_neg`：coe_mul_bot_of_neg {x : Real} (h : x < 0) : (x
 : EReal) * ⊥ = ⊤
（共 31 条，此处仅展示前 30 条）
-/
lemma mul_pos_iff {a b : EReal} : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  induction a, b using EReal.induction₂_symm with
  | symm h => simp [EReal.mul_comm, h, and_comm]
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx, EReal.top_mul_coe_of_neg hx, le_of_lt]
  | top_bot => simp
  | pos_bot _ hx => simp [hx, EReal.coe_mul_bot_of_pos hx, le_of_lt]
  | coe_coe x y => simp [← coe_mul, _root_.mul_pos_iff]
  | zero_bot => simp
  | neg_bot _ hx => simp [hx, EReal.coe_mul_bot_of_neg hx]
  | bot_bot => simp
/-
**EReal.mul_nonneg_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_nonneg_iff {a b : EReal} : 0 <= a * b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <
= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_eq_mul`：zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0
· 使用定理 `EReal.instNoZeroDivisors`：NoZeroDivisors EReal
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mul_nonneg_iff {a b : EReal} : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  simp_rw [le_iff_lt_or_eq, mul_pos_iff, zero_eq_mul (a := a)]
  rcases lt_trichotomy a 0 with (h | h | h) <;> rcases lt_trichotomy b 0 with (h' | h' | h')
    <;> simp only [h, h', true_or, true_and, or_true, and_true] <;> tauto
/-
**EReal.mul_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `EReal.mul_nonneg_iff`：mul_nonneg_iff {a b : EReal} : 0 <= a * b ↔ 0 <= a
 ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
-/
protected lemma mul_nonneg {a b : EReal} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  mul_nonneg_iff.mpr <| .inl ⟨ha, hb⟩

/-- The product of two positive extended real numbers is positive. -/
/-
**EReal.mul_pos** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, 0 < a → 0 < b → 0 < a * b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `EReal.mul_pos_iff`：mul_pos_iff {a b : EReal} : 0 < a * b ↔ 0 < a ∧ 0 < b
 ∨ a < 0 ∧ b < 0

--- 原说明 ---
The product of two positive extended real numbers is positive.
-/
protected lemma mul_pos {a b : EReal} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  mul_pos_iff.mpr (Or.inl ⟨ha, hb⟩)

/-- Induct on two ereals by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that `P x y` implies `P (-x) y` for all
`x`, `y`. -/
@[elab_as_elim]
/-
**EReal.induction** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induct on two ereals by performing case splits on the sign of one whenever the o
ther is
infinite. This version eliminates some cases by assuming that `P x y` implies `P
 (-x) y` for all
`x`, `y`.
-/
lemma induction₂_neg_left {P : EReal → EReal → Prop} (neg_left : ∀ {x y}, P x y → P (-x) y)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : ℝ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (zero_top : P 0 ⊤) (zero_bot : P 0 ⊥)
    (pos_top : ∀ x : ℝ, 0 < x → P x ⊤) (pos_bot : ∀ x : ℝ, 0 < x → P x ⊥)
    (coe_coe : ∀ x y : ℝ, P x y) : ∀ x y, P x y :=
  have : ∀ y, (∀ x : ℝ, 0 < x → P x y) → ∀ x : ℝ, x < 0 → P x y := fun _ h x hx =>
    neg_neg (x : EReal) ▸ neg_left <| h _ (neg_pos_of_neg hx)
  @induction₂ P top_top top_pos top_zero top_neg top_bot pos_top pos_bot zero_top
    coe_coe zero_bot (this _ pos_top) (this _ pos_bot) (neg_left top_top)
    (fun x hx => neg_left <| top_pos x hx) (neg_left top_zero)
    (fun x hx => neg_left <| top_neg x hx) (neg_left top_bot)

/-- Induct on two ereals by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that `P` is symmetric and `P x y` implies
`P (-x) y` for all `x`, `y`. -/
@[elab_as_elim]
/-
**EReal.induction** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induct on two ereals by performing case splits on the sign of one whenever the o
ther is
infinite. This version eliminates some cases by assuming that `P` is symmetric a
nd `P x y` implies
`P (-x) y` for all `x`, `y`.
-/
lemma induction₂_symm_neg {P : EReal → EReal → Prop}
    (symm : ∀ {x y}, P x y → P y x)
    (neg_left : ∀ {x y}, P x y → P (-x) y) (top_top : P ⊤ ⊤)
    (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x) (top_zero : P ⊤ 0) (coe_coe : ∀ x y : ℝ, P x y) :
    ∀ x y, P x y :=
  have neg_right : ∀ {x y}, P x y → P x (-y) := fun h => symm <| neg_left <| symm h
  have : ∀ x, (∀ y : ℝ, 0 < y → P x y) → ∀ y : ℝ, y < 0 → P x y := fun _ h y hy =>
    neg_neg (y : EReal) ▸ neg_right (h _ (neg_pos_of_neg hy))
  @induction₂_neg_left P neg_left top_top top_pos top_zero (this _ top_pos) (neg_right top_top)
    (symm top_zero) (symm <| neg_left top_zero) (fun x hx => symm <| top_pos x hx)
    (fun x hx => symm <| neg_left <| top_pos x hx) coe_coe
/-
**EReal.neg_mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x y : EReal), -x * y = -(x * y)
参数：x y : EReal；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.induction₂_neg_left`：induction₂_neg_left {P : EReal -> EReal -> Pr
op} (neg_left : forall {x y}, P x y -> P (-x) y) (top_top : P ⊤ ⊤) (top_pos : fo
rall x : Real, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `EReal.top_mul_coe_of_pos`：top_mul_coe_of_pos {x : Real} (h : 0 < x) : (⊤
 : EReal) * x = ⊤
· 使用定理 `EReal.neg_top`：neg_top : -(⊤ : EReal) = ⊥
· 使用引理 `EReal.bot_mul_coe_of_pos`：bot_mul_coe_of_pos {x : Real} (h : 0 < x) : (⊥
 : EReal) * x = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `EReal.top_mul_coe_of_neg`：top_mul_coe_of_neg {x : Real} (h : x < 0) : (⊤
 : EReal) * x = ⊥
· 使用引理 `EReal.bot_mul_coe_of_neg`：bot_mul_coe_of_neg {x : Real} (h : x < 0) : (⊥
 : EReal) * x = ⊤
· 使用定理 `EReal.neg_bot`：neg_bot : -(⊥ : EReal) = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `EReal.coe_mul_top_of_pos`：coe_mul_top_of_pos {x : Real} (h : 0 < x) : (x
 : EReal) * ⊤ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_neg`：∀ (x : ℝ), ↑(-x) = -↑x
· 使用引理 `EReal.coe_mul_top_of_neg`：coe_mul_top_of_neg {x : Real} (h : x < 0) : (x
 : EReal) * ⊤ = ⊥
· 使用定理 `neg_neg_of_pos`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Partial
Order α] [IsOrderedAddMonoid α] {a : α}, 0 < a → -a < 0
· 使用引理 `EReal.coe_mul_bot_of_pos`：coe_mul_bot_of_pos {x : Real} (h : 0 < x) : (x
 : EReal) * ⊥ = ⊥
· 使用引理 `EReal.coe_mul_bot_of_neg`：coe_mul_bot_of_neg {x : Real} (h : x < 0) : (x
 : EReal) * ⊥ = ⊤
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
protected lemma neg_mul (x y : EReal) : -x * y = -(x * y) := by
  induction x, y using induction₂_neg_left with
  | top_zero | zero_top | zero_bot => simp only [zero_mul, mul_zero, neg_zero]
  | top_top | top_bot => rfl
  | neg_left h => rw [h, neg_neg, neg_neg]
  | coe_coe => norm_cast; exact neg_mul _ _
  | top_pos _ h => rw [top_mul_coe_of_pos h, neg_top, bot_mul_coe_of_pos h]
  | pos_top _ h => rw [coe_mul_top_of_pos h, neg_top, ← coe_neg,
    coe_mul_top_of_neg (neg_neg_of_pos h)]
  | top_neg _ h => rw [top_mul_coe_of_neg h, neg_top, bot_mul_coe_of_neg h, neg_bot]
  | pos_bot _ h => rw [coe_mul_bot_of_pos h, neg_bot, ← coe_neg,
    coe_mul_bot_of_neg (neg_neg_of_pos h)]
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasDistribNeg EReal where
  neg_mul := EReal.neg_mul
  mul_neg := fun x y => by
    rw [x.mul_comm, x.mul_comm]
    exact y.neg_mul x
/-
**EReal.mul_neg_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_neg_iff {a b : EReal} : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `EReal.lt_neg_comm`：lt_neg_comm {a b : EReal} : a < -b ↔ b < -a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用引理 `EReal.mul_pos_iff`：mul_pos_iff {a b : EReal} : 0 < a * b ↔ 0 < a ∧ 0 < b
 ∨ a < 0 ∧ b < 0
· 使用定理 `EReal.neg_lt_comm`：neg_lt_comm {a b : EReal} : -a < b ↔ -b < a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mul_neg_iff {a b : EReal} : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  nth_rw 1 [← neg_zero]
  rw [lt_neg_comm, ← mul_neg a, mul_pos_iff, neg_lt_comm, lt_neg_comm, neg_zero]
/-
**EReal.mul_nonpos_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_nonpos_iff {a b : EReal} : a * b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <
= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `EReal.le_neg`：∀ {a b : EReal}, a ≤ -b ↔ b ≤ -a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用引理 `EReal.mul_nonneg_iff`：mul_nonneg_iff {a b : EReal} : 0 <= a * b ↔ 0 <= a
 ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
· 使用定理 `EReal.neg_le`：∀ {a b : EReal}, -a ≤ b ↔ -b ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mul_nonpos_iff {a b : EReal} : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  nth_rw 1 [← neg_zero]
  rw [EReal.le_neg, ← mul_neg, mul_nonneg_iff, EReal.neg_le, EReal.le_neg, neg_zero]
/-
**EReal.mul_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_eq_top (a b : EReal) : a * b = ⊤ ↔ (a = ⊥ ∧ b < 0) ∨ (a < 0 ∧ b = ⊥) ∨
 (a = ⊤ ∧ 0 < b) ∨ (0 < a ∧ b = ⊤)
参数：a b : EReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.induction₂_symm`：induction₂_symm {P : EReal -> EReal -> Prop} (sym
m : forall {x y}, P x y -> P y x) (top_top : P ⊤ ⊤) (top_pos : forall x : Real, 
0 < x -> P …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `EReal.top_mul_coe_of_pos`：top_mul_coe_of_pos {x : Real} (h : 0 < x) : (⊤
 : EReal) * x = ⊤
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `EReal.top_mul_coe_of_neg`：top_mul_coe_of_neg {x : Real} (h : x < 0) : (⊤
 : EReal) * x = ⊥
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `EReal.coe_mul_bot_of_pos`：coe_mul_bot_of_pos {x : Real} (h : 0 < x) : (x
 : EReal) * ⊥ = ⊥
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `EReal.coe_ne_top`：coe_ne_top (x : Real) : (x : EReal) != ⊤
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `EReal.coe_mul_bot_of_neg`：coe_mul_bot_of_neg {x : Real} (h : x < 0) : (x
 : EReal) * ⊥ = ⊤
-/
lemma mul_eq_top (a b : EReal) :
    a * b = ⊤ ↔ (a = ⊥ ∧ b < 0) ∨ (a < 0 ∧ b = ⊥) ∨ (a = ⊤ ∧ 0 < b) ∨ (0 < a ∧ b = ⊤) := by
  induction a, b using EReal.induction₂_symm with
  | symm h => grind [EReal.mul_comm]
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx.le, EReal.top_mul_coe_of_neg hx]
  | top_bot => simp
  | pos_bot _ hx => simp [hx.le, EReal.coe_mul_bot_of_pos hx]
  | coe_coe x y =>
    simpa only [EReal.coe_ne_bot, EReal.coe_neg', false_and, and_false, EReal.coe_ne_top,
      EReal.coe_pos, or_self, iff_false, EReal.coe_mul] using! EReal.coe_ne_top _
  | zero_bot => simp
  | neg_bot _ hx => simp [hx, EReal.coe_mul_bot_of_neg hx]
  | bot_bot => simp
/-
**EReal.mul_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_ne_top (a b : EReal) : a * b != ⊤ ↔ (a != ⊥ ∨ 0 <= b) ∧ (0 <= a ∨ b !=
 ⊥) ∧ (a != ⊤ ∨ b <= 0) ∧ (a <= 0 ∨ b != ⊤)
参数：a b : EReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `EReal.mul_eq_top`：mul_eq_top (a b : EReal) : a * b = ⊤ ↔ (a = ⊥ ∧ b < 0)
 ∨ (a < 0 ∧ b = ⊥) ∨ (a = ⊤ ∧ 0 < b) ∨ (0 < a ∧ b = ⊤)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mul_ne_top (a b : EReal) :
    a * b ≠ ⊤ ↔ (a ≠ ⊥ ∨ 0 ≤ b) ∧ (0 ≤ a ∨ b ≠ ⊥) ∧ (a ≠ ⊤ ∨ b ≤ 0) ∧ (a ≤ 0 ∨ b ≠ ⊤) := by
  rw [ne_eq, mul_eq_top]
  -- push the negation while keeping the disjunctions, that is converting `¬(p ∧ q)` into `¬p ∨ ¬q`
  -- rather than `p → ¬q`, since we already have disjunctions in the rhs
  push +distrib Not
  rfl
/-
**EReal.mul_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_eq_bot (a b : EReal) : a * b = ⊥ ↔ (a = ⊥ ∧ 0 < b) ∨ (0 < a ∧ b = ⊥) ∨
 (a = ⊤ ∧ b < 0) ∨ (a < 0 ∧ b = ⊤)
参数：a b : EReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.neg_eq_top_iff`：neg_eq_top_iff {x : EReal} : -x = ⊤ ↔ x = ⊥
· 使用定理 `EReal.neg_mul`：∀ (x y : EReal), -x * y = -(x * y)
· 使用引理 `EReal.mul_eq_top`：mul_eq_top (a b : EReal) : a * b = ⊤ ↔ (a = ⊥ ∧ b < 0)
 ∨ (a < 0 ∧ b = ⊥) ∨ (a = ⊤ ∧ 0 < b) ∨ (0 < a ∧ b = ⊤)
· 使用定理 `EReal.neg_eq_bot_iff`：neg_eq_bot_iff {x : EReal} : -x = ⊥ ↔ x = ⊤
· 使用定理 `EReal.neg_lt_comm`：neg_lt_comm {a b : EReal} : -a < b ↔ -b < a
· 使用定理 `EReal.lt_neg_comm`：lt_neg_comm {a b : EReal} : a < -b ↔ b < -a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
lemma mul_eq_bot (a b : EReal) :
    a * b = ⊥ ↔ (a = ⊥ ∧ 0 < b) ∨ (0 < a ∧ b = ⊥) ∨ (a = ⊤ ∧ b < 0) ∨ (a < 0 ∧ b = ⊤) := by
  rw [← neg_eq_top_iff, ← EReal.neg_mul, mul_eq_top, neg_eq_bot_iff, neg_eq_top_iff,
    neg_lt_comm, lt_neg_comm, neg_zero]
  tauto
/-
**EReal.mul_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_ne_bot (a b : EReal) : a * b != ⊥ ↔ (a != ⊥ ∨ b <= 0) ∧ (a <= 0 ∨ b !=
 ⊥) ∧ (a != ⊤ ∨ 0 <= b) ∧ (0 <= a ∨ b != ⊤)
参数：a b : EReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `EReal.mul_eq_bot`：mul_eq_bot (a b : EReal) : a * b = ⊥ ↔ (a = ⊥ ∧ 0 < b)
 ∨ (0 < a ∧ b = ⊥) ∨ (a = ⊤ ∧ b < 0) ∨ (a < 0 ∧ b = ⊤)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mul_ne_bot (a b : EReal) :
    a * b ≠ ⊥ ↔ (a ≠ ⊥ ∨ b ≤ 0) ∧ (a ≤ 0 ∨ b ≠ ⊥) ∧ (a ≠ ⊤ ∨ 0 ≤ b) ∧ (0 ≤ a ∨ b ≠ ⊤) := by
  rw [ne_eq, mul_eq_bot]
  push +distrib Not
  rfl

/-- `EReal.toENNReal` is multiplicative. For the version with the nonnegativity
hypothesis on the second variable, see `EReal.toENNReal_mul'`. -/
/-
**EReal.toENNReal_mul** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_mul {x y : EReal} (hx : 0 <= x) : (x * y).toENNReal = x.toENNRea
l * y.toENNReal
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EReal.toENNReal_of_nonpos`：toENNReal_of_nonpos {x : EReal} (hx : x <= 0)
 : x.toENNReal = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `EReal.toENNReal_of_ne_top`：toENNReal_of_ne_top {x : EReal} (hx : x != ⊤)
 : x.toENNReal = ENNReal.ofReal x.toReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `EReal.mul_top_of_pos`：∀ {x : EReal}, 0 < x → x * ⊤ = ⊤
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用引理 `EReal.top_mul_of_neg`：top_mul_of_neg {x : EReal} (h : x < 0) : ⊤ * x = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.coe_neg'`：∀ {x : ℝ}, ↑x < 0 ↔ x < 0
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用引理 `EReal.top_mul_of_pos`：top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤
· 使用定理 `EReal.coe_pos`：∀ {x : ℝ}, 0 < ↑x ↔ 0 < x
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
`EReal.toENNReal` is multiplicative. For the version with the nonnegativity
hypothesis on the second variable, see `EReal.toENNReal_mul'`.
-/
lemma toENNReal_mul {x y : EReal} (hx : 0 ≤ x) :
    (x * y).toENNReal = x.toENNReal * y.toENNReal := by
  induction x <;> induction y
    <;> try {· simp_all [mul_nonpos_iff, ofReal_mul, ← coe_mul]}
  · rcases eq_or_lt_of_le hx with (hx | hx)
    · simp [← hx]
    · simp_all [mul_top_of_pos hx]
  · rename_i a
    rcases lt_trichotomy a 0 with (ha | ha | ha)
    · simp_all [le_of_lt, top_mul_of_neg (EReal.coe_neg'.mpr ha)]
    · simp [ha]
    · simp_all [top_mul_of_pos (EReal.coe_pos.mpr ha)]

/-- `EReal.toENNReal` is multiplicative. For the version with the nonnegativity
hypothesis on the first variable, see `EReal.toENNReal_mul`. -/
/-
**EReal.toENNReal_mul'** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_mul' {x y : EReal} (hy : 0 <= y) : (x * y).toENNReal = x.toENNRe
al * y.toENNReal
参数：hy : 0 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用引理 `EReal.toENNReal_mul`：toENNReal_mul {x y : EReal} (hx : 0 <= x) : (x * y)
.toENNReal = x.toENNReal * y.toENNReal
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
`EReal.toENNReal` is multiplicative. For the version with the nonnegativity
hypothesis on the first variable, see `EReal.toENNReal_mul`.
-/
lemma toENNReal_mul' {x y : EReal} (hy : 0 ≤ y) :
    (x * y).toENNReal = x.toENNReal * y.toENNReal := by
  rw [EReal.mul_comm, toENNReal_mul hy, mul_comm]
/-
**EReal.right_distrib_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：right_distrib_of_nonneg {a b c : EReal} (ha : 0 <= a) (hb : 0 <= b) : (a +
 b) * c = a * c + b * c
参数：ha : 0 <= a；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `EReal.instCanLiftENNRealToERealLeOfNat`：CanLift EReal ENNReal ENNReal.to
EReal fun x => 0 ≤ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `EReal.coe_ennreal_add`：coe_ennreal_add (x y : ENNReal) : ((x + y : Real>
=0∞) : EReal) = x + y
· 使用引理 `EReal.neg_add`：neg_add {x y : EReal} (h1 : x != ⊥ ∨ y != ⊤) (h2 : x != ⊤
 ∨ y != ⊥) : -(x + y) = -x - y
· 使用定理 `EReal.coe_ennreal_ne_bot`：coe_ennreal_ne_bot (x : Real>=0∞) : (x : EReal
) != ⊥
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
lemma right_distrib_of_nonneg {a b c : EReal} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * c = a * c + b * c := by
  lift a to ℝ≥0∞ using ha
  lift b to ℝ≥0∞ using hb
  cases c using recENNReal with
  | coe c => exact_mod_cast add_mul a b c
  | neg_coe c hc =>
    simp only [mul_neg, ← coe_ennreal_add, ← coe_ennreal_mul, add_mul]
    rw [coe_ennreal_add, EReal.neg_add (.inl (coe_ennreal_ne_bot _)) (.inr (coe_ennreal_ne_bot _)),
      sub_eq_add_neg]
/-
**EReal.left_distrib_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：left_distrib_of_nonneg {a b c : EReal} (ha : 0 <= a) (hb : 0 <= b) : c * (
a + b) = c * a + c * b
参数：ha : 0 <= a；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用引理 `EReal.right_distrib_of_nonneg`：right_distrib_of_nonneg {a b c : EReal} (
ha : 0 <= a) (hb : 0 <= b) : (a + b) * c = a * c + b * c
-/
lemma left_distrib_of_nonneg {a b c : EReal} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    c * (a + b) = c * a + c * b := by
  nth_rewrite 1 [EReal.mul_comm]; nth_rewrite 2 [EReal.mul_comm]; nth_rewrite 3 [EReal.mul_comm]
  exact right_distrib_of_nonneg ha hb
/-
**EReal.mul_sub_of_nonneg_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_sub_of_nonneg_of_nonpos {a b c : EReal} (hb : 0 <= b) (hc : c <= 0) : 
a * (b - c) = a * b - a * c
参数：hb : 0 <= b；hc : c <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `EReal.left_distrib_of_nonneg`：left_distrib_of_nonneg {a b c : EReal} (ha
 : 0 <= a) (hb : 0 <= b) : c * (a + b) = c * a + c * b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_sub_of_nonneg_of_nonpos {a b c : EReal} (hb : 0 ≤ b) (hc : c ≤ 0) :
    a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg, left_distrib_of_nonneg hb (by simpa)]
  simp [← neg_mul, sub_eq_add_neg]
/-
**EReal.left_distrib_of_nonneg_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：left_distrib_of_nonneg_of_ne_top {x : EReal} (hx_nonneg : 0 <= x) (hx_ne_t
op : x != ⊤) (y z : EReal) : x * (y + z) = x * y + x * z
参数：hx_nonneg : 0 <= x；hx_ne_top : x != ⊤；y z : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `EReal.add_bot`：add_bot (x : EReal) : x + ⊥ = ⊥
· 使用定理 `EReal.mul_bot_of_pos`：∀ {x : EReal}, 0 < x → x * ⊥ = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥
· 使用定理 `EReal.mul_top_of_pos`：∀ {x : EReal}, 0 < x → x * ⊤ = ⊤
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `EReal.add_top_of_ne_bot`：add_top_of_ne_bot {x : EReal} (h : x != ⊥) : x 
+ ⊤ = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `EReal.top_add_of_ne_bot`：top_add_of_ne_bot {x : EReal} (h : x != ⊥) : ⊤ 
+ x = ⊤
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
-/
lemma left_distrib_of_nonneg_of_ne_top {x : EReal} (hx_nonneg : 0 ≤ x)
    (hx_ne_top : x ≠ ⊤) (y z : EReal) :
    x * (y + z) = x * y + x * z := by
  cases hx_nonneg.eq_or_lt' with
  | inl hx0 => simp [hx0]
  | inr hx0 =>
  lift x to ℝ using ⟨hx_ne_top, hx0.ne_bot⟩
  cases y <;> cases z <;>
    simp [mul_bot_of_pos hx0, mul_top_of_pos hx0, ← coe_mul, ← coe_add, mul_add]
/-
**EReal.right_distrib_of_nonneg_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：right_distrib_of_nonneg_of_ne_top {x : EReal} (hx_nonneg : 0 <= x) (hx_ne_
top : x != ⊤) (y z : EReal) : (y + z) * x = y * x + z * x
参数：hx_nonneg : 0 <= x；hx_ne_top : x != ⊤；y z : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用引理 `EReal.left_distrib_of_nonneg_of_ne_top`：left_distrib_of_nonneg_of_ne_top
 {x : EReal} (hx_nonneg : 0 <= x) (hx_ne_top : x != ⊤) (y z : EReal) : x * (y + 
z) = x * y + x * z
-/
lemma right_distrib_of_nonneg_of_ne_top {x : EReal} (hx_nonneg : 0 ≤ x)
    (hx_ne_top : x ≠ ⊤) (y z : EReal) :
    (y + z) * x = y * x + z * x := by
  simpa only [EReal.mul_comm] using left_distrib_of_nonneg_of_ne_top hx_nonneg hx_ne_top y z
/-
**EReal.mul_sub_of_nonneg_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_sub_of_nonneg_of_ne_top {a b c : EReal} (ha : 0 <= a) (ha' : a != ⊤) :
 a * (b - c) = a * b - a * c
参数：ha : 0 <= a；ha' : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `EReal.left_distrib_of_nonneg_of_ne_top`：left_distrib_of_nonneg_of_ne_top
 {x : EReal} (hx_nonneg : 0 <= x) (hx_ne_top : x != ⊤) (y z : EReal) : x * (y + 
z) = x * y + x * z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_sub_of_nonneg_of_ne_top {a b c : EReal} (ha : 0 ≤ a) (ha' : a ≠ ⊤) :
    a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg, left_distrib_of_nonneg_of_ne_top ha ha']
  simp [← neg_mul, sub_eq_add_neg]
/-
**EReal.sub_mul_of_nonneg_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sub_mul_of_nonneg_of_ne_top {a b c : EReal} (ha : 0 <= a) (ha' : a != ⊤) :
 (b - c) * a = b * a - c * a
参数：ha : 0 <= a；ha' : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `EReal.right_distrib_of_nonneg_of_ne_top`：right_distrib_of_nonneg_of_ne_t
op {x : EReal} (hx_nonneg : 0 <= x) (hx_ne_top : x != ⊤) (y z : EReal) : (y + z)
 * x = y * x + z * x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sub_mul_of_nonneg_of_ne_top {a b c : EReal} (ha : 0 ≤ a) (ha' : a ≠ ⊤) :
    (b - c) * a = b * a - c * a := by
  rw [sub_eq_add_neg, right_distrib_of_nonneg_of_ne_top ha ha']
  simp [← neg_mul, sub_eq_add_neg]

@[simp]
/-
**EReal.nsmul_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：nsmul_eq_mul (n : Nat) (x : EReal) : n • x = n * x
参数：n : Nat；x : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `EReal.right_distrib_of_nonneg`：right_distrib_of_nonneg {a b c : EReal} (
ha : 0 <= a) (hb : 0 <= b) : (a + b) * c = a * c + b * c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
-/
lemma nsmul_eq_mul (n : ℕ) (x : EReal) : n • x = n * x := by
  induction n with
  | zero => rw [zero_smul, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [succ_nsmul, ih, Nat.cast_succ]
    convert! (EReal.right_distrib_of_nonneg _ _).symm <;> simp

end EReal

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: sum of two `EReal`s. -/
@[positivity (_ + _ : EReal)]
meta def evalERealAdd : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(EReal), ~q($a + $b) =>
    assertInstancesCommute
    match ← core zα pα a with
    | .positive pa =>
      match (← core zα pα b).toNonneg with
      | some pb => pure (.positive q(EReal.add_pos_of_pos_of_nonneg $pa $pb))
      | _ => pure .none
    | .nonnegative pa =>
      match ← core zα pα b with
      | .positive pb => pure (.positive q(Right.add_pos_of_nonneg_of_pos $pa $pb))
      | .nonnegative pb => pure (.nonnegative q(add_nonneg $pa $pb))
      | _ => pure .none
    | _ => pure .none
  | _, _, _ => throwError "not a sum of 2 `EReal`s"

/-- Extension for the `positivity` tactic: product of two `EReal`s. -/
@[positivity (_ * _ : EReal)]
meta def evalERealMul : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(EReal), ~q($a * $b) =>
    assertInstancesCommute
    match ← core zα pα a with
    | .positive pa =>
      match ← core zα pα b with
      | .positive pb => pure <| .positive q(EReal.mul_pos $pa $pb)
      | .nonnegative pb => pure <| .nonnegative q(EReal.mul_nonneg (le_of_lt $pa) $pb)
      | .nonzero pb => pure <| .nonzero q(mul_ne_zero (ne_of_gt $pa) $pb)
      | _ => pure .none
    | .nonnegative pa =>
      match (← core zα pα b).toNonneg with
      | some pb => pure (.nonnegative q(EReal.mul_nonneg $pa $pb))
      | none => pure .none
    | .nonzero pa =>
      match (← core zα pα b).toNonzero with
      | some pb => pure (.nonzero q(mul_ne_zero $pa $pb))
      | none => pure .none
    | _ => pure .none
  | _, _, _ => throwError "not a product of 2 `EReal`s"

end Mathlib.Meta.Positivity

