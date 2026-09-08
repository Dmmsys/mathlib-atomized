/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Order.Nonneg.Basic
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Nonnegative rationals

This file defines the nonnegative rationals as a subtype of `Rat` and provides its basic algebraic
order structure.

Note that `NNRat` is not declared as a `Semifield` here. See `Mathlib/Algebra/Field/Rat.lean` for
that instance.

We also define an instance `CanLift ℚ ℚ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℚ` and `hx : 0 ≤ x` in the proof context with `x : ℚ≥0` while replacing all occurrences
of `x` with `↑x`. This tactic also works for a function `f : α → ℚ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

`ℚ≥0` is notation for `NNRat` in scope `NNRat`.

## Huge warning

Whenever you state a lemma about the coercion `ℚ≥0 → ℚ`, check that Lean inserts `NNRat.cast`, not
`Subtype.val`. Else your lemma will never apply.
-/

@[expose] public section

assert_not_exists CompleteLattice IsOrderedMonoid

library_note «specialised high priority simp lemma» /--
It sometimes happens that a `@[simp]` lemma declared early in the library can be proved by `simp`
using later, more general simp lemmas. In that case, the following reasons might be arguments for
the early lemma to be tagged `@[simp high]` (rather than `@[simp, nolint simpNF]` or
un-`@[simp]`ed):
1. There is a significant portion of the library which needs the early lemma to be available via
  `simp` and which doesn't have access to the more general lemmas.
2. The more general lemmas have more complicated typeclass assumptions, causing rewrites with them
  to be slower.
-/

open Function

/-
**Rat.instPosMulMono** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Rat.instPosMulMono : PosMulMono Rat where mul_le_mul_of_nonneg_left r hr p
 q hpq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Rat.mul_nonneg`：∀ {a b : ℚ}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
-/
instance Rat.instPosMulMono : PosMulMono ℚ where
  mul_le_mul_of_nonneg_left r hr p q hpq := by
    simpa [mul_sub, sub_nonneg] using Rat.mul_nonneg hr (sub_nonneg.2 hpq)

deriving instance CommSemiring for NNRat

deriving instance AddCancelCommMonoid for NNRat

deriving instance LinearOrder for NNRat

deriving instance Sub for NNRat

deriving instance Inhabited for NNRat

namespace NNRat

variable {p q : ℚ≥0}

/-
**NNRat.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
形式化陈述：instNontrivial : Nontrivial Rat>=0 where exists_pair_ne
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
instance instNontrivial : Nontrivial ℚ≥0 where exists_pair_ne := ⟨1, 0, by decide⟩
/-
**NNRat.instOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
形式化陈述：instOrderBot : OrderBot Rat>=0 where bot
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderBot : OrderBot ℚ≥0 where
  bot := 0
  bot_le q := q.2
/-
**NNRat.val_eq_cast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ≥0), ↑q = ↑q
参数：q : ℚ≥0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma val_eq_cast (q : ℚ≥0) : q.1 = q := rfl
/-
**NNRat.instCharZero** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
形式化陈述：instCharZero : CharZero Rat>=0 where cast_injective a b hab
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance instCharZero : CharZero ℚ≥0 where
  cast_injective a b hab := by simpa using! congr_arg num hab
/-
**NNRat.canLift** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
形式化陈述：canLift : CanLift Rat Rat>=0 (↑) fun q => 0 <= q where prf q hq
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance canLift : CanLift ℚ ℚ≥0 (↑) fun q ↦ 0 ≤ q where
  prf q hq := ⟨⟨q, hq⟩, rfl⟩

@[ext]
/-
**NNRat.ext** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：ext : (p : Rat) = (q : Rat) -> p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem ext : (p : ℚ) = (q : ℚ) → p = q :=
  Subtype.ext
/-
**NNRat.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：Function.Injective NNRat.cast
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
protected theorem coe_injective : Injective ((↑) : ℚ≥0 → ℚ) :=
  Subtype.coe_injective

-- See note [specialised high priority simp lemma]
@[simp high, norm_cast]
/-
**NNRat.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_inj : (p : Rat) = q ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
-/
theorem coe_inj : (p : ℚ) = q ↔ p = q :=
  Subtype.coe_inj
/-
**NNRat.ne_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：ne_iff {x y : Rat>=0} : (x : Rat) != (y : Rat) ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `NNRat.coe_inj`：coe_inj : (p : Rat) = q ↔ p = q
-/
theorem ne_iff {x y : ℚ≥0} : (x : ℚ) ≠ (y : ℚ) ↔ x ≠ y :=
  NNRat.coe_inj.not

-- TODO: We have to write `NNRat.cast` explicitly, else the statement picks up `Subtype.val` instead
/-
**NNRat.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ) (hq : 0 ≤ q), ↑⟨q, hq⟩ = q
参数：q : ℚ；hq : 0 ≤ q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mk (q : ℚ) (hq) : NNRat.cast ⟨q, hq⟩ = q := rfl
/-
**NNRat.** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «forall» {p : ℚ≥0 → Prop} : (∀ q, p q) ↔ ∀ q hq, p ⟨q, hq⟩ := Subtype.forall
/-
**NNRat.** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «exists» {p : ℚ≥0 → Prop} : (∃ q, p q) ↔ ∃ q hq, p ⟨q, hq⟩ := Subtype.exists

/-- Reinterpret a rational number `q` as a non-negative rational number. Returns `0` if `q ≤ 0`. -/
/-
**NNRat._root_.Rat.toNNRat** 是 Mathlib 中的一个定义，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a rational number `q` as a non-negative rational number. Returns `0`
 if `q ≤ 0`.
-/
def _root_.Rat.toNNRat (q : ℚ) : ℚ≥0 :=
  ⟨max q 0, le_max_right _ _⟩
/-
**NNRat._root_.Rat.coe_toNNRat** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Rat.coe_toNNRat (q : ℚ) (hq : 0 ≤ q) : (q.toNNRat : ℚ) = q :=
  max_eq_left hq
/-
**NNRat._root_.Rat.le_coe_toNNRat** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Rat.le_coe_toNNRat (q : ℚ) : q ≤ q.toNNRat :=
  le_max_left _ _

open Rat (toNNRat)

@[simp]
/-
**NNRat.coe_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_nonneg (q : Rat>=0) : (0 : Rat) <= q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_nonneg (q : ℚ≥0) : (0 : ℚ) ≤ q :=
  q.2
/-
**NNRat.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_zero : ((0 : ℚ≥0) : ℚ) = 0 := rfl
/-
**NNRat.num_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：NNRat.num 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma num_zero : num 0 = 0 := rfl
/-
**NNRat.den_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：NNRat.den 0 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma den_zero : den 0 = 1 := rfl
/-
**NNRat.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_one : ((1 : ℚ≥0) : ℚ) = 1 := rfl
/-
**NNRat.num_one** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：NNRat.num 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma num_one : num 1 = 1 := rfl
/-
**NNRat.den_one** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：NNRat.den 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma den_one : den 1 = 1 := rfl

@[simp, norm_cast]
/-
**NNRat.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_add (p q : Rat>=0) : ((p + q : Rat>=0) : Rat) = p + q
参数：p q : Rat>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (p q : ℚ≥0) : ((p + q : ℚ≥0) : ℚ) = p + q :=
  rfl

@[simp, norm_cast]
/-
**NNRat.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_mul (p q : Rat>=0) : ((p * q : Rat>=0) : Rat) = p * q
参数：p q : Rat>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (p q : ℚ≥0) : ((p * q : ℚ≥0) : ℚ) = p * q :=
  rfl
/-
**NNRat.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ≥0) (n : ℕ), ↑(q ^ n) = ↑q ^ n
参数：q : ℚ≥0；n : ℕ；q ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_pow (q : ℚ≥0) (n : ℕ) : (↑(q ^ n) : ℚ) = (q : ℚ) ^ n :=
  rfl
/-
**NNRat.num_pow** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ≥0) (n : ℕ), (q ^ n).num = q.num ^ n
参数：q : ℚ≥0；n : ℕ；q ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natAbs_pow`：∀ (n : ℤ) (k : ℕ), (n ^ k).natAbs = n.natAbs ^ k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma num_pow (q : ℚ≥0) (n : ℕ) : (q ^ n).num = q.num ^ n := by simp [num, Int.natAbs_pow]
/-
**NNRat.den_pow** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ≥0) (n : ℕ), (q ^ n).den = q.den ^ n
参数：q : ℚ≥0；n : ℕ；q ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma den_pow (q : ℚ≥0) (n : ℕ) : (q ^ n).den = q.den ^ n := rfl

@[simp, norm_cast]
/-
**NNRat.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_sub (h : q <= p) : ((p - q : Rat>=0) : Rat) = p - q
参数：h : q <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_sub_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE α] [Add
LeftMono α] {a b c : α}, a ≤ b - c ↔ c ≤ b - a
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem coe_sub (h : q ≤ p) : ((p - q : ℚ≥0) : ℚ) = p - q :=
  max_eq_left <| le_sub_comm.2 <| by rwa [sub_zero]

-- See note [specialised high priority simp lemma]
@[simp high]
/-
**NNRat.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_eq_zero : (q : Rat) = 0 ↔ q = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_zero : (q : ℚ) = 0 ↔ q = 0 := by norm_cast
/-
**NNRat.coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_ne_zero : (q : Rat) != 0 ↔ q != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `NNRat.coe_eq_zero`：coe_eq_zero : (q : Rat) = 0 ↔ q = 0
-/
theorem coe_ne_zero : (q : ℚ) ≠ 0 ↔ q ≠ 0 :=
  coe_eq_zero.not

@[simp]
/-
**NNRat.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：mk_zero : (⟨0, le_rfl⟩ : Rat>=0) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem mk_zero : (⟨0, le_rfl⟩ : ℚ≥0) = 0 := rfl

@[norm_cast]
/-
**NNRat.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_le_coe : (p : Rat) <= q ↔ p <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_le_coe : (p : ℚ) ≤ q ↔ p ≤ q :=
  Iff.rfl

@[norm_cast]
/-
**NNRat.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_lt_coe : (p : Rat) < q ↔ p < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_lt_coe : (p : ℚ) < q ↔ p < q :=
  Iff.rfl

@[norm_cast]
/-
**NNRat.coe_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_pos : (0 : Rat) < q ↔ 0 < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_pos : (0 : ℚ) < q ↔ 0 < q :=
  Iff.rfl
/-
**NNRat.coe_mono** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_mono : Monotone ((↑) : Rat>=0 -> Rat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNRat.coe_le_coe`：coe_le_coe : (p : Rat) <= q ↔ p <= q
-/
theorem coe_mono : Monotone ((↑) : ℚ≥0 → ℚ) :=
  fun _ _ ↦ coe_le_coe.2
/-
**NNRat.toNNRat_mono** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：toNNRat_mono : Monotone toNNRat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem toNNRat_mono : Monotone toNNRat :=
  fun _ _ h ↦ max_le_max h le_rfl

@[simp]
/-
**NNRat.toNNRat_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：toNNRat_coe (q : Rat>=0) : toNNRat q = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem toNNRat_coe (q : ℚ≥0) : toNNRat q = q :=
  ext <| max_eq_left q.2

@[simp]
/-
**NNRat.toNNRat_coe_nat** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：toNNRat_coe_nat (n : Nat) : toNNRat n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.coe_toNNRat`：∀ (q : ℚ), 0 ≤ q → ↑q.toNNRat = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
-/
theorem toNNRat_coe_nat (n : ℕ) : toNNRat n = n :=
  ext <| by simp only [Nat.cast_nonneg', Rat.coe_toNNRat]; rfl

/-- `toNNRat` and `(↑) : ℚ≥0 → ℚ` form a Galois insertion. -/
/-
**NNRat.gi** 是 Mathlib 中的一个定义，位于命名空间 `NNRat`。
形式化陈述：GaloisInsertion Rat.toNNRat NNRat.cast
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.coe_mono`：coe_mono : Monotone ((↑) : Rat>=0 -> Rat)
· 使用定理 `NNRat.toNNRat_mono`：toNNRat_mono : Monotone toNNRat
· 使用定理 `Rat.le_coe_toNNRat`：∀ (q : ℚ), q ≤ ↑q.toNNRat
· 使用定理 `NNRat.toNNRat_coe`：toNNRat_coe (q : Rat>=0) : toNNRat q = q

--- 原说明 ---
`toNNRat` and `(↑) : ℚ≥0 → ℚ` form a Galois insertion.
-/
protected def gi : GaloisInsertion toNNRat (↑) :=
  GaloisInsertion.monotoneIntro coe_mono toNNRat_mono Rat.le_coe_toNNRat toNNRat_coe

/-- Coercion `ℚ≥0 → ℚ` as a `RingHom`. -/
/-
**NNRat.coeHom** 是 Mathlib 中的一个定义，位于命名空间 `NNRat`。
形式化陈述：coeHom : Rat>=0 ->+* Rat where toFun
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.coe_one`：↑1 = 1
· 使用定理 `NNRat.coe_mul`：coe_mul (p q : Rat>=0) : ((p * q : Rat>=0) : Rat) = p * q
· 使用定理 `NNRat.coe_zero`：↑0 = 0
· 使用定理 `NNRat.coe_add`：coe_add (p q : Rat>=0) : ((p + q : Rat>=0) : Rat) = p + q

--- 原说明 ---
Coercion `ℚ≥0 → ℚ` as a `RingHom`.
-/
def coeHom : ℚ≥0 →+* ℚ where
  toFun := (↑)
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero
  map_add' := coe_add
/-
**NNRat.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (n : ℕ), ↑↑n = ↑n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_natCast (n : ℕ) : (↑(↑n : ℚ≥0) : ℚ) = n := rfl

@[simp]
/-
**NNRat.mk_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：mk_natCast (n : Nat) : @Eq Rat>=0 (⟨(n : Rat), Nat.cast_nonneg' n⟩ : Rat>=
0) n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
-/
theorem mk_natCast (n : ℕ) : @Eq ℚ≥0 (⟨(n : ℚ), Nat.cast_nonneg' n⟩ : ℚ≥0) n :=
  rfl

@[simp]
/-
**NNRat.coe_coeHom** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_coeHom : ⇑coeHom = ((↑) : Rat>=0 -> Rat)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coeHom : ⇑coeHom = ((↑) : ℚ≥0 → ℚ) :=
  rfl

@[norm_cast]
/-
**NNRat.nsmul_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：nsmul_coe (q : Rat>=0) (n : Nat) : ↑(n • q) = n • (q : Rat)
参数：q : Rat>=0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
-/
theorem nsmul_coe (q : ℚ≥0) (n : ℕ) : ↑(n • q) = n • (q : ℚ) :=
  coeHom.toAddMonoidHom.map_nsmul _ _
/-
**NNRat.bddAbove_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：bddAbove_coe {s : Set Rat>=0} : BddAbove ((↑) '' s : Set Rat) ↔ BddAbove s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem bddAbove_coe {s : Set ℚ≥0} : BddAbove ((↑) '' s : Set ℚ) ↔ BddAbove s :=
  ⟨fun ⟨b, hb⟩ ↦
    ⟨toNNRat b, fun ⟨y, _⟩ hys ↦
      show y ≤ max b 0 from (hb <| Set.mem_image_of_mem _ hys).trans <| le_max_left _ _⟩,
    fun ⟨b, hb⟩ ↦ ⟨b, fun _ ⟨_, hx, Eq⟩ ↦ Eq ▸ hb hx⟩⟩
/-
**NNRat.bddBelow_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：bddBelow_coe (s : Set Rat>=0) : BddBelow (((↑) : Rat>=0 -> Rat) '' s)
参数：s : Set Rat>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem bddBelow_coe (s : Set ℚ≥0) : BddBelow (((↑) : ℚ≥0 → ℚ) '' s) :=
  ⟨0, fun _ ⟨q, _, h⟩ ↦ h ▸ q.2⟩

@[norm_cast]
/-
**NNRat.coe_max** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_max (x y : Rat>=0) : ((max x y : Rat>=0) : Rat) = max (x : Rat) (y : R
at)
参数：x y : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `NNRat.coe_mono`：coe_mono : Monotone ((↑) : Rat>=0 -> Rat)
-/
theorem coe_max (x y : ℚ≥0) : ((max x y : ℚ≥0) : ℚ) = max (x : ℚ) (y : ℚ) :=
  coe_mono.map_max

@[norm_cast]
/-
**NNRat.coe_min** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：coe_min (x y : Rat>=0) : ((min x y : Rat>=0) : Rat) = min (x : Rat) (y : R
at)
参数：x y : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `NNRat.coe_mono`：coe_mono : Monotone ((↑) : Rat>=0 -> Rat)
-/
theorem coe_min (x y : ℚ≥0) : ((min x y : ℚ≥0) : ℚ) = min (x : ℚ) (y : ℚ) :=
  coe_mono.map_min
/-
**NNRat.sub_def** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：sub_def (p q : Rat>=0) : p - q = toNNRat (p - q)
参数：p q : Rat>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_def (p q : ℚ≥0) : p - q = toNNRat (p - q) :=
  rfl

@[simp]
/-
**NNRat.abs_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：abs_coe (q : Rat>=0) : |(q : Rat)| = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem abs_coe (q : ℚ≥0) : |(q : ℚ)| = q :=
  abs_of_nonneg q.2

-- See note [specialised high priority simp lemma]
@[simp high]
/-
**NNRat.nonpos_iff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：nonpos_iff_eq_zero (q : Rat>=0) : q <= 0 ↔ q = 0
参数：q : Rat>=0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonpos_iff_eq_zero (q : ℚ≥0) : q ≤ 0 ↔ q = 0 :=
  ⟨fun h => le_antisymm h q.2, fun h => h.symm ▸ q.2⟩

end NNRat

open NNRat

namespace Rat

variable {p q : ℚ}

@[simp]
/-
**Rat.toNNRat_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：toNNRat_zero : toNNRat 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNNRat_zero : toNNRat 0 = 0 := rfl

@[simp]
/-
**Rat.toNNRat_one** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：toNNRat_one : toNNRat 1 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNNRat_one : toNNRat 1 = 1 := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Rat.toNNRat_pos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：toNNRat_pos : 0 < toNNRat q ↔ 0 < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toNNRat_pos : 0 < toNNRat q ↔ 0 < q := by simp [toNNRat, ← coe_lt_coe]

@[simp]
/-
**Rat.toNNRat_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：toNNRat_eq_zero : toNNRat q = 0 ↔ q <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Rat.toNNRat_pos`：toNNRat_pos : 0 < toNNRat q ↔ 0 < q
-/
theorem toNNRat_eq_zero : toNNRat q = 0 ↔ q ≤ 0 := by
  simpa [-toNNRat_pos] using (@toNNRat_pos q).not

alias ⟨_, toNNRat_of_nonpos⟩ := toNNRat_eq_zero

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Rat.toNNRat_le_toNNRat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：toNNRat_le_toNNRat_iff (hp : 0 <= p) : toNNRat q <= toNNRat p ↔ q <= p
参数：hp : 0 <= p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toNNRat_le_toNNRat_iff (hp : 0 ≤ p) : toNNRat q ≤ toNNRat p ↔ q ≤ p := by
  simp [← coe_le_coe, toNNRat, hp]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Rat.toNNRat_lt_toNNRat_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：toNNRat_lt_toNNRat_iff' : toNNRat q < toNNRat p ↔ q < p ∧ 0 < p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toNNRat_lt_toNNRat_iff' : toNNRat q < toNNRat p ↔ q < p ∧ 0 < p := by
  simp [← coe_lt_coe, toNNRat]
/-
**Rat.toNNRat_lt_toNNRat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：toNNRat_lt_toNNRat_iff (h : 0 < p) : toNNRat q < toNNRat p ↔ q < p
参数：h : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Rat.toNNRat_lt_toNNRat_iff'`：toNNRat_lt_toNNRat_iff' : toNNRat q < toNNR
at p ↔ q < p ∧ 0 < p
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
-/
theorem toNNRat_lt_toNNRat_iff (h : 0 < p) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans (and_iff_left h)
/-
**Rat.toNNRat_lt_toNNRat_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：toNNRat_lt_toNNRat_iff_of_nonneg (hq : 0 <= q) : toNNRat q < toNNRat p ↔ q
 < p
参数：hq : 0 <= q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Rat.toNNRat_lt_toNNRat_iff'`：toNNRat_lt_toNNRat_iff' : toNNRat q < toNNR
at p ↔ q < p ∧ 0 < p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem toNNRat_lt_toNNRat_iff_of_nonneg (hq : 0 ≤ q) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans ⟨And.left, fun h ↦ ⟨h, hq.trans_lt h⟩⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Rat.toNNRat_add** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：toNNRat_add (hq : 0 <= q) (hp : 0 <= p) : toNNRat (q + p) = toNNRat q + to
NNRat p
参数：hq : 0 <= q；hp : 0 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toNNRat_add (hq : 0 ≤ q) (hp : 0 ≤ p) : toNNRat (q + p) = toNNRat q + toNNRat p :=
  NNRat.ext <| by simp [toNNRat, hq, hp, add_nonneg]
/-
**Rat.toNNRat_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：toNNRat_add_le : toNNRat (q + p) <= toNNRat q + toNNRat p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNRat.coe_le_coe`：coe_le_coe : (p : Rat) <= q ↔ p <= q
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `NNRat.coe_nonneg`：coe_nonneg (q : Rat>=0) : (0 : Rat) <= q
-/
theorem toNNRat_add_le : toNNRat (q + p) ≤ toNNRat q + toNNRat p :=
  coe_le_coe.1 <| max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) <| coe_nonneg _
/-
**Rat.toNNRat_le_iff_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：toNNRat_le_iff_le_coe {p : Rat>=0} : toNNRat q <= p ↔ q <= ↑p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem toNNRat_le_iff_le_coe {p : ℚ≥0} : toNNRat q ≤ p ↔ q ≤ ↑p :=
  NNRat.gi.gc q p
/-
**Rat.le_toNNRat_iff_coe_le** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：le_toNNRat_iff_coe_le {q : Rat>=0} (hp : 0 <= p) : q <= toNNRat p ↔ ↑q <= 
p
参数：hp : 0 <= p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.coe_le_coe`：coe_le_coe : (p : Rat) <= q ↔ p <= q
· 使用定理 `Rat.coe_toNNRat`：∀ (q : ℚ), 0 ≤ q → ↑q.toNNRat = q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_toNNRat_iff_coe_le {q : ℚ≥0} (hp : 0 ≤ p) : q ≤ toNNRat p ↔ ↑q ≤ p := by
  rw [← coe_le_coe, Rat.coe_toNNRat p hp]
/-
**Rat.le_toNNRat_iff_coe_le'** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：le_toNNRat_iff_coe_le' {q : Rat>=0} (hq : 0 < q) : q <= toNNRat p ↔ ↑q <= 
p
参数：hq : 0 < q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Rat.le_toNNRat_iff_coe_le`：le_toNNRat_iff_coe_le {q : Rat>=0} (hp : 0 <=
 p) : q <= toNNRat p ↔ ↑q <= p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.toNNRat_eq_zero`：toNNRat_eq_zero : toNNRat q = 0 ↔ q <= 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `NNRat.coe_nonneg`：coe_nonneg (q : Rat>=0) : (0 : Rat) <= q
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_toNNRat_iff_coe_le' {q : ℚ≥0} (hq : 0 < q) : q ≤ toNNRat p ↔ ↑q ≤ p :=
  (le_or_gt 0 p).elim le_toNNRat_iff_coe_le fun hp ↦ by
    simp only [(hp.trans_le q.coe_nonneg).not_ge, toNNRat_eq_zero.2 hp.le, hq.not_ge]
/-
**Rat.toNNRat_lt_iff_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：toNNRat_lt_iff_lt_coe {p : Rat>=0} (hq : 0 <= q) : toNNRat q < p ↔ q < ↑p
参数：hq : 0 <= q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.coe_lt_coe`：coe_lt_coe : (p : Rat) < q ↔ p < q
· 使用定理 `Rat.coe_toNNRat`：∀ (q : ℚ), 0 ≤ q → ↑q.toNNRat = q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toNNRat_lt_iff_lt_coe {p : ℚ≥0} (hq : 0 ≤ q) : toNNRat q < p ↔ q < ↑p := by
  rw [← coe_lt_coe, Rat.coe_toNNRat q hq]
/-
**Rat.lt_toNNRat_iff_coe_lt** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：lt_toNNRat_iff_coe_lt {q : Rat>=0} : q < toNNRat p ↔ ↑q < p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.lt_iff_lt`：lt_iff_lt (gc : GaloisConnection l u) {a : α
} {b : β} : b < l a ↔ u b < a
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem lt_toNNRat_iff_coe_lt {q : ℚ≥0} : q < toNNRat p ↔ ↑q < p :=
  NNRat.gi.gc.lt_iff_lt

set_option backward.isDefEq.respectTransparency false in
/-
**Rat.toNNRat_mul** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：toNNRat_mul (hp : 0 <= p) : toNNRat (p * q) = toNNRat p * toNNRat q
参数：hp : 0 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.toNNRat_eq_zero`：toNNRat_eq_zero : toNNRat q = 0 ↔ q <= 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem toNNRat_mul (hp : 0 ≤ p) : toNNRat (p * q) = toNNRat p * toNNRat q := by
  rcases le_total 0 q with hq | hq
  · ext; simp [toNNRat, hp, hq, mul_nonneg]
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [toNNRat_eq_zero.2 hq, toNNRat_eq_zero.2 hpq, mul_zero]

end Rat

/-- The absolute value on `ℚ` as a map to `ℚ≥0`. -/
@[pp_nodot]
/-
**Rat.nnabs** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Rat.nnabs (x : Rat) : Rat>=0
参数：x : Rat。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The absolute value on `ℚ` as a map to `ℚ≥0`.
-/
def Rat.nnabs (x : ℚ) : ℚ≥0 :=
  ⟨abs x, abs_nonneg x⟩

@[norm_cast, simp]
/-
**Rat.coe_nnabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Rat.coe_nnabs (x : Rat) : (Rat.nnabs x : Rat) = abs x
参数：x : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Rat.coe_nnabs (x : ℚ) : (Rat.nnabs x : ℚ) = abs x := rfl

/-! ### Numerator and denominator -/


namespace NNRat

variable {p q : ℚ≥0}

/-
**NNRat.num_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ≥0), (↑q).num = ↑q.num
参数：q : ℚ≥0；↑q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = |n|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[norm_cast] lemma num_coe (q : ℚ≥0) : (q : ℚ).num = q.num := by
  simp only [num, Int.natCast_natAbs, Rat.num_nonneg, coe_nonneg, abs_of_nonneg]
/-
**NNRat.natAbs_num_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：natAbs_num_coe : (q : Rat).num.natAbs = q.num
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natAbs_num_coe : (q : ℚ).num.natAbs = q.num := rfl
/-
**NNRat.den_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {q : ℚ≥0}, (↑q).den = q.den
参数：↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma den_coe : (q : ℚ).den = q.den := rfl
/-
**NNRat.num_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {q : ℚ≥0}, q.num ≠ 0 ↔ q ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma num_ne_zero : q.num ≠ 0 ↔ q ≠ 0 := by simp [num]
/-
**NNRat.num_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {q : ℚ≥0}, 0 < q.num ↔ 0 < q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `NNRat.nonpos_iff_eq_zero`：nonpos_iff_eq_zero (q : Rat>=0) : q <= 0 ↔ q =
 0
-/
@[simp] lemma num_pos : 0 < q.num ↔ 0 < q := by
  simpa [num, -nonpos_iff_eq_zero] using nonpos_iff_eq_zero _ |>.not.symm
/-
**NNRat.den_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ≥0), 0 < q.den
参数：q : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.den_pos`：∀ (self : ℚ), 0 < self.den
-/
@[simp] lemma den_pos (q : ℚ≥0) : 0 < q.den := Rat.den_pos _
/-
**NNRat.den_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ≥0), q.den ≠ 0
参数：q : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.den_ne_zero`：∀ (q : ℚ), q.den ≠ 0
-/
@[simp] lemma den_ne_zero (q : ℚ≥0) : q.den ≠ 0 := Rat.den_ne_zero _
/-
**NNRat.coprime_num_den** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：coprime_num_den (q : Rat>=0) : q.num.Coprime q.den
参数：q : Rat>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
-/
lemma coprime_num_den (q : ℚ≥0) : q.num.Coprime q.den := by simpa [num, den] using Rat.reduced _

-- TODO: Rename `Rat.coe_nat_num`, `Rat.intCast_den`, `Rat.ofNat_num`, `Rat.ofNat_den`
/-
**NNRat.num_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (n : ℕ), (↑n).num = n
参数：n : ℕ；↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma num_natCast (n : ℕ) : num n = n := rfl
/-
**NNRat.den_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (n : ℕ), (↑n).den = 1
参数：n : ℕ；↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma den_natCast (n : ℕ) : den n = 1 := rfl
/-
**NNRat.num_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).num = OfNat.ofNat n
参数：n : ℕ；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma num_ofNat (n : ℕ) [n.AtLeastTwo] : num ofNat(n) = OfNat.ofNat n :=
  rfl
/-
**NNRat.den_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).den = 1
参数：n : ℕ；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma den_ofNat (n : ℕ) [n.AtLeastTwo] : den ofNat(n) = 1 := rfl
/-
**NNRat.ext_num_den** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：ext_num_den (hn : p.num = q.num) (hd : p.den = q.den) : p = q
参数：hn : p.num = q.num；hd : p.den = q.den。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `Rat.ext`：∀ {p q : ℚ}, p.num = q.num → p.den = q.den → p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
-/
theorem ext_num_den (hn : p.num = q.num) (hd : p.den = q.den) : p = q := by
  refine ext <| Rat.ext ?_ hd
  simpa [num_coe]
/-
**NNRat.ext_num_den_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：ext_num_den_iff : p = q ↔ p.num = q.num ∧ p.den = q.den
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext_num_den`：ext_num_den (hn : p.num = q.num) (hd : p.den = q.den)
 : p = q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ext_num_den_iff : p = q ↔ p.num = q.num ∧ p.den = q.den :=
  ⟨by rintro rfl; exact ⟨rfl, rfl⟩, fun h ↦ ext_num_den h.1 h.2⟩

/-- Form the quotient `n / d` where `n d : ℕ`.

See also `Rat.divInt` and `mkRat`. -/
/-
**NNRat.divNat** 是 Mathlib 中的一个定义，位于命名空间 `NNRat`。
形式化陈述：divNat (n d : Nat) : Rat>=0
参数：n d : Nat。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Form the quotient `n / d` where `n d : ℕ`.

See also `Rat.divInt` and `mkRat`.
-/
def divNat (n d : ℕ) : ℚ≥0 :=
  ⟨.divInt n d, Rat.divInt_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg d)⟩

variable {n₁ n₂ d₁ d₂ : ℕ}
/-
**NNRat.coe_divNat** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (n d : ℕ), ↑(NNRat.divNat n d) = Rat.divInt ↑n ↑d
参数：n d : ℕ；NNRat.divNat n d。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_divNat (n d : ℕ) : (divNat n d : ℚ) = .divInt n d := rfl
/-
**NNRat.mk_divInt** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：mk_divInt (n d : Nat) : ⟨.divInt n d, Rat.divInt_nonneg (Int.natCast_nonne
g n) (Int.natCast_nonneg d)⟩ = divNat n d
参数：n d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.divInt_nonneg`：∀ {a b : ℤ}, 0 ≤ a → 0 ≤ b → 0 ≤ Rat.divInt a b
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
-/
lemma mk_divInt (n d : ℕ) :
    ⟨.divInt n d, Rat.divInt_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg d)⟩ =
      divNat n d := rfl
/-
**NNRat.divNat_inj** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：divNat_inj (h₁ : d₁ != 0) (h₂ : d₂ != 0) : divNat n₁ d₁ = divNat n₂ d₂ ↔ n
₁ * d₂ = n₂ * d₁
参数：h₁ : d₁ != 0；h₂ : d₂ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.coe_inj`：coe_inj : (p : Rat) = q ↔ p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.divInt_ofNat`：∀ (num : ℤ) (den : ℕ), Rat.divInt num ↑den = mkRat num
 den
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma divNat_inj (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) : divNat n₁ d₁ = divNat n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  rw [← coe_inj]; simp [Rat.mkRat_eq_iff, h₁, h₂]; norm_cast

set_option backward.isDefEq.respectTransparency false in
/-
**NNRat.divNat_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (n : ℕ), NNRat.divNat n 0 = 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.divInt_zero`：∀ (n : ℤ), Rat.divInt n 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma divNat_zero (n : ℕ) : divNat n 0 = 0 := by simp [divNat]
/-
**NNRat.num_divNat_den** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ≥0), NNRat.divNat q.num q.den = q
参数：q : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.mkRat_num_den'`：∀ (a : ℚ), mkRat a.num a.den = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.divInt_ofNat`：∀ (num : ℤ) (den : ℕ), Rat.divInt num ↑den = mkRat num
 den
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma num_divNat_den (q : ℚ≥0) : divNat q.num q.den = q :=
  ext <| by rw [← (q : ℚ).mkRat_num_den']; simp [num_coe, den_coe]
/-
**NNRat.natCast_eq_divNat** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：natCast_eq_divNat (n : Nat) : (n : Rat>=0) = divNat n 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.num_divNat_den`：∀ (q : ℚ≥0), NNRat.divNat q.num q.den = q
-/
lemma natCast_eq_divNat (n : ℕ) : (n : ℚ≥0) = divNat n 1 := (num_divNat_den _).symm
/-
**NNRat.divNat_mul_divNat** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：divNat_mul_divNat (n₁ n₂ : Nat) {d₁ d₂} : divNat n₁ d₁ * divNat n₂ d₂ = di
vNat (n₁ * n₂) (d₁ * d₂)
参数：n₁ n₂ : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Rat.divInt_mul_divInt`：∀ (n₁ n₂ : ℤ) {d₁ d₂ : ℤ}, Rat.divInt n₁ d₁ * Rat
.divInt n₂ d₂ = Rat.divInt (n₁ * n₂) (d₁ * d₂)
-/
lemma divNat_mul_divNat (n₁ n₂ : ℕ) {d₁ d₂} :
    divNat n₁ d₁ * divNat n₂ d₂ = divNat (n₁ * n₂) (d₁ * d₂) := by
  ext; push_cast; exact Rat.divInt_mul_divInt _ _
/-
**NNRat.divNat_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：divNat_mul_left {a : Nat} (ha : a != 0) (n d : Nat) : divNat (a * n) (a * 
d) = divNat n d
参数：ha : a != 0；n d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Rat.divInt_mul_left`：∀ {n d a : ℤ}, a ≠ 0 → Rat.divInt (a * n) (a * d) =
 Rat.divInt n d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
lemma divNat_mul_left {a : ℕ} (ha : a ≠ 0) (n d : ℕ) : divNat (a * n) (a * d) = divNat n d := by
  ext; push_cast; exact Rat.divInt_mul_left (mod_cast ha)
/-
**NNRat.divNat_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：divNat_mul_right {a : Nat} (ha : a != 0) (n d : Nat) : divNat (n * a) (d *
 a) = divNat n d
参数：ha : a != 0；n d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Rat.divInt_mul_right`：∀ {n d a : ℤ}, a ≠ 0 → Rat.divInt (n * a) (d * a) 
= Rat.divInt n d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
lemma divNat_mul_right {a : ℕ} (ha : a ≠ 0) (n d : ℕ) : divNat (n * a) (d * a) = divNat n d := by
  ext; push_cast; exact Rat.divInt_mul_right (mod_cast ha)
/-
**NNRat.mul_den_eq_num** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ≥0), q * ↑q.den = ↑q.num
参数：q : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `NNRat.den_coe`：∀ {q : ℚ≥0}, (↑q).den = q.den
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
· 使用定理 `Rat.mul_den_eq_num`：∀ (q : ℚ), q * ↑q.den = ↑q.num
-/
@[simp] lemma mul_den_eq_num (q : ℚ≥0) : q * q.den = q.num := by
  ext
  push_cast
  rw [← Int.cast_natCast, ← den_coe, ← Int.cast_natCast q.num, ← num_coe]
  exact Rat.mul_den_eq_num _
/-
**NNRat.den_mul_eq_num** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ≥0), ↑q.den * q = ↑q.num
参数：q : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `NNRat.mul_den_eq_num`：∀ (q : ℚ≥0), q * ↑q.den = ↑q.num
-/
@[simp] lemma den_mul_eq_num (q : ℚ≥0) : q.den * q = q.num := by rw [mul_comm, mul_den_eq_num]

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with nonnegative rational
numbers of the form `n / d` with `d ≠ 0` and `n`, `d` coprime. -/
@[elab_as_elim]
/-
**NNRat.numDenCasesOn.** 是 Mathlib 中的一个定义，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with nonnegativ
e rational
numbers of the form `n / d` with `d ≠ 0` and `n`, `d` coprime.
-/
def numDenCasesOn.{u} {C : ℚ≥0 → Sort u} (q) (H : ∀ n d, d ≠ 0 → n.Coprime d → C (divNat n d)) :
    C q := by rw [← q.num_divNat_den]; exact H _ _ q.den_ne_zero q.coprime_num_den
/-
**NNRat.add_def** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：add_def (q r : Rat>=0) : q + r = divNat (q.num * r.den + r.num * q.den) (q
.den * r.den)
参数：q r : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.add_def'`：∀ (a b : ℚ), a + b = mkRat (a.num * ↑b.den + b.num * ↑a.de
n) (a.den * b.den)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_def (q r : ℚ≥0) : q + r = divNat (q.num * r.den + r.num * q.den) (q.den * r.den) := by
  ext; simp [Rat.add_def', Rat.mkRat_eq_divInt, num_coe, den_coe]
/-
**NNRat.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：mul_def (q r : Rat>=0) : q * r = divNat (q.num * r.num) (q.den * r.den)
参数：q r : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.mul_eq_mkRat`：mul_eq_mkRat (q r : Rat) : q * r = mkRat (q.num * r.nu
m) (q.den * r.den)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_def (q r : ℚ≥0) : q * r = divNat (q.num * r.num) (q.den * r.den) := by
  ext; simp [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt, num_coe, den_coe]
/-
**NNRat.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：lt_def {p q : Rat>=0} : p < q ↔ p.num * q.den < q.num * p.den
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.coe_lt_coe`：coe_lt_coe : (p : Rat) < q ↔ p < q
· 使用定理 `Rat.lt_iff`：∀ (a b : ℚ), a < b ↔ a.num * ↑b.den < b.num * ↑a.den
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_def {p q : ℚ≥0} : p < q ↔ p.num * q.den < q.num * p.den := by
  rw [← NNRat.coe_lt_coe, Rat.lt_iff]; norm_cast
/-
**NNRat.le_def** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：le_def {p q : Rat>=0} : p <= q ↔ p.num * q.den <= q.num * p.den
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.coe_le_coe`：coe_le_coe : (p : Rat) <= q ↔ p <= q
· 使用定理 `Rat.le_iff`：∀ (a b : ℚ), a ≤ b ↔ a.num * ↑b.den ≤ b.num * ↑a.den
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def {p q : ℚ≥0} : p ≤ q ↔ p.num * q.den ≤ q.num * p.den := by
  rw [← NNRat.coe_le_coe, Rat.le_iff]; norm_cast

end NNRat

namespace Mathlib.Tactic.Qify

/-
**Mathlib.Tactic.Qify.nnratCast_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Qif
y`。
形式化陈述：∀ (a b : ℚ≥0), a = b ↔ ↑a = ↑b
参数：a b : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `NNRat.coe_inj`：coe_inj : (p : Rat) = q ↔ p = q
-/
@[qify_simps] lemma nnratCast_eq (a b : ℚ≥0) : a = b ↔ (a : ℚ) = (b : ℚ) := NNRat.coe_inj.symm
/-
**Mathlib.Tactic.Qify.nnratCast_le** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Qif
y`。
形式化陈述：∀ (a b : ℚ≥0), a ≤ b ↔ ↑a ≤ ↑b
参数：a b : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `NNRat.coe_le_coe`：coe_le_coe : (p : Rat) <= q ↔ p <= q
-/
@[qify_simps] lemma nnratCast_le (a b : ℚ≥0) : a ≤ b ↔ (a : ℚ) ≤ (b : ℚ) := NNRat.coe_le_coe.symm
/-
**Mathlib.Tactic.Qify.nnratCast_lt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Qif
y`。
形式化陈述：∀ (a b : ℚ≥0), a < b ↔ ↑a < ↑b
参数：a b : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `NNRat.coe_lt_coe`：coe_lt_coe : (p : Rat) < q ↔ p < q
-/
@[qify_simps] lemma nnratCast_lt (a b : ℚ≥0) : a < b ↔ (a : ℚ) < (b : ℚ) := NNRat.coe_lt_coe.symm
/-
**Mathlib.Tactic.Qify.nnratCast_ne** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Qif
y`。
形式化陈述：∀ (a b : ℚ≥0), a ≠ b ↔ ↑a ≠ ↑b
参数：a b : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `NNRat.ne_iff`：ne_iff {x y : Rat>=0} : (x : Rat) != (y : Rat) ↔ x != y
-/
@[qify_simps] lemma nnratCast_ne (a b : ℚ≥0) : a ≠ b ↔ (a : ℚ) ≠ (b : ℚ) := NNRat.ne_iff.symm

end Mathlib.Tactic.Qify

