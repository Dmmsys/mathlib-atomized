/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# The rational numbers possess a linear order

This file constructs the order on `ℚ` and proves various facts relating the order to
ring structure on `ℚ`. This only uses unbundled type classes, e.g. `CovariantClass`,
relating the order structure and algebra structure on `ℚ`.
For the bundled `LinearOrderedCommRing` instance on `ℚ`, see `Algebra.Order.Ring.Rat`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Field Finset Set.Icc GaloisConnection

namespace Rat

variable {a b c p q : ℚ}

/-
**Rat.mkRat_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {a : ℤ}, 0 ≤ a → ∀ (b : ℕ), 0 ≤ mkRat a b
参数：b : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.divInt_ofNat`：∀ (num : ℤ) (den : ℕ), Rat.divInt num ↑den = mkRat num
 den
· 使用定理 `Rat.divInt_nonneg`：∀ {a b : ℤ}, 0 ≤ a → 0 ≤ b → 0 ≤ Rat.divInt a b
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
-/
@[simp] lemma mkRat_nonneg {a : ℤ} (ha : 0 ≤ a) (b : ℕ) : 0 ≤ mkRat a b := by
  simpa using divInt_nonneg ha (Int.natCast_nonneg _)
/-
**Rat.ofScientific_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：ofScientific_nonneg (m : Nat) (s : Bool) (e : Nat) : 0 <= Rat.ofScientific
 m s e
参数：m : Nat；s : Bool；e : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.ofScientific.eq_1`：∀ (m : ℕ) (s : Bool) (e : ℕ), Rat.ofScientific m 
s e = if s = true then Rat.normalize (↑m) (10 ^ e) ⋯ else ↑(m * 10 ^ e)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Rat.num_nonneg`：∀ {q : ℚ}, 0 ≤ q.num ↔ 0 ≤ q
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ofScientific_nonneg (m : ℕ) (s : Bool) (e : ℕ) : 0 ≤ Rat.ofScientific m s e := by
  rw [Rat.ofScientific]
  cases s
  · rw [if_neg (by decide)]
    exact num_nonneg.mp <| Int.natCast_nonneg _
  · grind [normalize_eq_mkRat, Rat.mkRat_nonneg]
/-
**Rat._root_.NNRatCast.toOfScientific** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.NNRatCast.toOfScientific {K} [NNRatCast K] : OfScientific K where
  ofScientific (m : ℕ) (b : Bool) (d : ℕ) :=
    NNRat.cast ⟨Rat.ofScientific m b d, ofScientific_nonneg m b d⟩
/-
**Rat._root_.NNRatCast.toOfScientific_def** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NNRatCast.toOfScientific_def {K} [NNRatCast K] (m : ℕ) (b : Bool) (d : ℕ) :
    (OfScientific.ofScientific m b d : K) =
      NNRat.cast ⟨(OfScientific.ofScientific m b d : ℚ), ofScientific_nonneg m b d⟩ :=
  rfl

/-- Casting a scientific literal via `ℚ≥0` is the same as casting directly. -/
@[simp, norm_cast]
/-
**Rat._root_.NNRat.cast_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Casting a scientific literal via `ℚ≥0` is the same as casting directly.
-/
theorem _root_.NNRat.cast_ofScientific {K} [NNRatCast K] (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℚ≥0) = (OfScientific.ofScientific m s e : K) :=
  rfl
/-
**Rat.divInt_le_divInt** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {a b c d : ℤ}, 0 < b → 0 < d → (Rat.divInt a b ≤ Rat.divInt c d ↔ a * d 
≤ c * b)
参数：Rat.divInt a b ≤ Rat.divInt c d ↔ a * d ≤ c * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.le_iff_sub_nonneg`：∀ (a b : ℚ), a ≤ b ↔ 0 ≤ b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.sub_nonneg`：∀ {a b : ℤ}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Rat.neg_divInt`：∀ (n d : ℤ), -Rat.divInt n d = Rat.divInt (-n) d
· 使用定理 `Rat.divInt_add_divInt`：∀ (n₁ n₂ : ℤ) {d₁ d₂ : ℤ},   d₁ ≠ 0 → d₂ ≠ 0 → Ra
t.divInt n₁ d₁ + Rat.divInt n₂ d₂ = Rat.divInt (n₁ * d₂ + n₂ * d₁) (d₁ * d₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Int.mul_pos`：∀ {a b : ℤ}, 0 < a → 0 < b → 0 < a * b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma divInt_le_divInt {a b c d : ℤ} (b0 : 0 < b) (d0 : 0 < d) :
    a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_sub_nonneg, ← Int.sub_nonneg]
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, Int.mul_pos d0 b0]
/-
**Rat.lt_iff_le_not_ge** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (a b : ℚ), a < b ↔ a ≤ b ∧ ¬b ≤ a
参数：a b : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.LawfulOrderLT.lt_iff`：∀ {α : Type u} {inst : LT α} {inst_1 : LE α} [
self : Std.LawfulOrderLT α] (a b : α), a < b ↔ a ≤ b ∧ ¬b ≤ a
· 使用定理 `Lean.Grind.instLawfulOrderLTRat`：Std.LawfulOrderLT ℚ
-/
protected lemma lt_iff_le_not_ge (a b : ℚ) : a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  Std.LawfulOrderLT.lt_iff a b
/-
**Rat.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：linearOrder : LinearOrder Rat where le_refl _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.le_refl`：∀ {a : ℚ}, a ≤ a
· 使用定理 `Rat.le_trans`：∀ {a b c : ℚ}, a ≤ b → b ≤ c → a ≤ c
· 使用定理 `Rat.lt_iff_le_not_ge`：∀ (a b : ℚ), a < b ↔ a ≤ b ∧ ¬b ≤ a
· 使用定理 `Rat.le_antisymm`：∀ {a b : ℚ}, a ≤ b → b ≤ a → a = b
· 使用定理 `Rat.le_total`：∀ {a b : ℚ}, a ≤ b ∨ b ≤ a
-/
instance linearOrder : LinearOrder ℚ where
  le_refl _ := Rat.le_refl
  le_trans _ _ _ := Rat.le_trans
  le_antisymm _ _ := Rat.le_antisymm
  le_total _ _ := Rat.le_total
  toDecidableEq := inferInstance
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  lt_iff_le_not_ge := Rat.lt_iff_le_not_ge
/-
**Rat.mkRat_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mkRat_nonneg_iff (a : Int) {b : Nat} (hb : b != 0) : 0 <= mkRat a b ↔ 0 <=
 a
参数：a : Int；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.divInt_nonneg_iff_of_pos_right`：∀ {a b : ℤ}, 0 < b → (0 ≤ Rat.divInt
 a b ↔ 0 ≤ a)
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
theorem mkRat_nonneg_iff (a : ℤ) {b : ℕ} (hb : b ≠ 0) : 0 ≤ mkRat a b ↔ 0 ≤ a :=
  divInt_nonneg_iff_of_pos_right (show 0 < (b : ℤ) by simpa using Nat.pos_of_ne_zero hb)
/-
**Rat.mkRat_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mkRat_pos_iff (a : Int) {b : Nat} (hb : b != 0) : 0 < mkRat a b ↔ 0 < a
参数：a : Int；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkRat_pos_iff (a : ℤ) {b : ℕ} (hb : b ≠ 0) : 0 < mkRat a b ↔ 0 < a := by
  grind [mkRat_nonneg_iff, Rat.mkRat_eq_zero]
/-
**Rat.mkRat_pos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mkRat_pos {a : Int} (ha : 0 < a) {b : Nat} (hb : b != 0) : 0 < mkRat a b
参数：ha : 0 < a；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.mkRat_pos_iff`：mkRat_pos_iff (a : Int) {b : Nat} (hb : b != 0) : 0 <
 mkRat a b ↔ 0 < a
-/
theorem mkRat_pos {a : ℤ} (ha : 0 < a) {b : ℕ} (hb : b ≠ 0) : 0 < mkRat a b :=
  (mkRat_pos_iff a hb).mpr ha
/-
**Rat.mkRat_nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mkRat_nonpos_iff (a : Int) {b : Nat} (hb : b != 0) : mkRat a b <= 0 ↔ a <=
 0
参数：a : Int；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkRat_nonpos_iff (a : ℤ) {b : ℕ} (hb : b ≠ 0) : mkRat a b ≤ 0 ↔ a ≤ 0 := by
  grind [mkRat_pos_iff]
/-
**Rat.mkRat_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mkRat_nonpos {a : Int} (ha : a <= 0) (b : Nat) : mkRat a b <= 0
参数：ha : a <= 0；b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mkRat_zero`：∀ (n : ℤ), mkRat n 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.mkRat_nonpos_iff`：mkRat_nonpos_iff (a : Int) {b : Nat} (hb : b != 0)
 : mkRat a b <= 0 ↔ a <= 0
-/
theorem mkRat_nonpos {a : ℤ} (ha : a ≤ 0) (b : ℕ) : mkRat a b ≤ 0 := by
  obtain rfl | hb := eq_or_ne b 0
  · simp
  · exact (mkRat_nonpos_iff a hb).mpr ha
/-
**Rat.mkRat_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mkRat_neg_iff (a : Int) {b : Nat} (hb : b != 0) : mkRat a b < 0 ↔ a < 0
参数：a : Int；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkRat_neg_iff (a : ℤ) {b : ℕ} (hb : b ≠ 0) : mkRat a b < 0 ↔ a < 0 := by
  grind [mkRat_nonneg_iff]
/-
**Rat.mkRat_neg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mkRat_neg {a : Int} (ha : a < 0) {b : Nat} (hb : b != 0) : mkRat a b < 0
参数：ha : a < 0；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.mkRat_neg_iff`：mkRat_neg_iff (a : Int) {b : Nat} (hb : b != 0) : mkR
at a b < 0 ↔ a < 0
-/
theorem mkRat_neg {a : ℤ} (ha : a < 0) {b : ℕ} (hb : b ≠ 0) : mkRat a b < 0 :=
  (mkRat_neg_iff a hb).mpr ha

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

/-
**Rat.instDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instDistribLattice : DistribLattice Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instan
ces non-computably.
-/
instance instDistribLattice : DistribLattice ℚ := inferInstance
/-
**Rat.instLattice** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instLattice : Lattice Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLattice : Lattice ℚ := inferInstance
/-
**Rat.instSemilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instSemilatticeInf : SemilatticeInf Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeInf : SemilatticeInf ℚ := inferInstance
/-
**Rat.instSemilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instSemilatticeSup : SemilatticeSup Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeSup : SemilatticeSup ℚ := inferInstance
/-
**Rat.instInf** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instInf : Min Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInf : Min ℚ := inferInstance
/-
**Rat.instSup** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instSup : Max Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSup : Max ℚ := inferInstance
/-
**Rat.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instPartialOrder : PartialOrder Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrder : PartialOrder ℚ := inferInstance
/-
**Rat.instPreorder** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instPreorder : Preorder Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPreorder : Preorder ℚ := inferInstance

/-! ### Miscellaneous lemmas -/

/-
**Rat.** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Miscellaneous lemmas
-/
instance : AddLeftMono ℚ where
  elim := fun _ _ _ h => Rat.add_le_add_left.2 h
/-
**Rat.num_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {a : ℚ}, a.num ≤ 0 ↔ a ≤ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `Bool.decide_or`：∀ (p q : Prop) [dpq : Decidable (p ∨ q)] [dp : Decidable
 p] [dq : Decidable q], decide (p ∨ q) = (decide p || decide q)
· 使用定理 `Bool.and_eq_true`：∀ (a b : Bool), ((a && b) = true) = (a = true ∧ b = tr
ue)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `Bool.or_eq_true`：∀ (a b : Bool), ((a || b) = true) = (a = true ∨ b = tru
e)
· 使用定理 `Bool.if_false_left`：∀ (p : Prop) [h : Decidable p] (f : Bool), (if p the
n false else f) = (!decide p && f)
· 使用定理 `Bool.decide_and`：∀ (p q : Prop) [dpq : Decidable (p ∧ q)] [dp : Decidabl
e p] [dq : Decidable q], decide (p ∧ q) = (decide p && decide q)
· 使用定理 `Bool.not_and`：∀ (x y : Bool), (!(x && y)) = (!x || !y)
· 使用定理 `Bool.not_or`：∀ (x y : Bool), (!(x || y)) = (!x && !y)
· 使用定理 `Bool.if_true_left`：∀ (p : Prop) [h : Decidable p] (f : Bool), (if p then
 true else f) = (decide p || f)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Bool.ite_eq_false_distrib`：∀ (p : Prop) [h : Decidable p] (t f : Bool), 
((if p then t else f) = false) = if p then t = false else f = false
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma num_nonpos {a : ℚ} : a.num ≤ 0 ↔ a ≤ 0 := by
  simp +instances [Int.le_iff_lt_or_eq, instLE, Rat.blt]
/-
**Rat.num_pos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {a : ℚ}, 0 < a.num ↔ 0 < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Rat.num_nonpos`：∀ {a : ℚ}, a.num ≤ 0 ↔ a ≤ 0
-/
@[simp] lemma num_pos {a : ℚ} : 0 < a.num ↔ 0 < a := lt_iff_lt_of_le_iff_le num_nonpos
/-
**Rat.num_neg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {a : ℚ}, a.num < 0 ↔ a < 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Rat.num_nonneg`：∀ {q : ℚ}, 0 ≤ q.num ↔ 0 ≤ q
-/
@[simp] lemma num_neg {a : ℚ} : a.num < 0 ↔ a < 0 := lt_iff_lt_of_le_iff_le num_nonneg
/-
**Rat.div_lt_div_iff_mul_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {a b c d : ℤ}, 0 < b → 0 < d → (↑a / ↑b < ↑c / ↑d ↔ a * d < c * b)
参数：↑a / ↑b < ↑c / ↑d ↔ a * d < c * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Rat.div_def'`：div_def' (q r : Rat) : q / r = (q.num * r.den) /. (q.den *
 r.num)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Rat.divInt_le_divInt`：∀ {a b c d : ℤ}, 0 < b → 0 < d → (Rat.divInt a b ≤
 Rat.divInt c d ↔ a * d ≤ c * b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[deprecated "use `div_lt_div_iff₀`" (since := "2026-03-20")] theorem div_lt_div_iff_mul_lt_mul
    {a b c d : ℤ} (b_pos : 0 < b) (d_pos : 0 < d) :
    (a : ℚ) / b < c / d ↔ a * d < c * b := by
  simp only [lt_iff_le_not_ge]
  apply and_congr
  · simp [div_def', Rat.divInt_le_divInt b_pos d_pos]
  · simp [div_def', Rat.divInt_le_divInt d_pos b_pos]
/-
**Rat.num_le_denom_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：num_le_denom_iff {q : Rat} : q.num <= q.den ↔ q <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem num_le_denom_iff {q : ℚ} : q.num ≤ q.den ↔ q ≤ 1 := by simp [Rat.le_iff]
/-
**Rat.num_lt_denom_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：num_lt_denom_iff {q : Rat} : q.num < q.den ↔ q < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem num_lt_denom_iff {q : ℚ} : q.num < q.den ↔ q < 1 := by simp [Rat.lt_iff]

@[deprecated (since := "2026-02-24")] alias lt_one_iff_num_lt_denom := Rat.num_lt_denom_iff
/-
**Rat.abs_def** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：abs_def (q : Rat) : |q| = q.num.natAbs /. q.den
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem abs_def (q : ℚ) : |q| = q.num.natAbs /. q.den := by
  grind [abs_of_nonpos, neg_def, Rat.num_nonneg, abs_of_nonneg, num_divInt_den]
/-
**Rat.abs_def'** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：abs_def' (q : Rat) : |q| = ⟨|q.num|, q.den, q.den_ne_zero, q.num.abs_eq_na
tAbs ▸ q.reduced⟩
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.ext`：∀ {p q : ℚ}, p.num = q.num → p.den = q.den → p = q
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Rat.den_ne_zero`：∀ (q : ℚ), q.den ≠ 0
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.abs_def`：abs_def (q : Rat) : |q| = q.num.natAbs /. q.den
· 使用定理 `Rat.mk_eq_divInt`：∀ {num : ℤ} {den : ℕ} {nz : den ≠ 0} {c : num.natAbs.C
oprime den},   { num := num, den := den, den_nz := nz, reduced := c } = Rat.divI
nt num…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem abs_def' (q : ℚ) :
    |q| = ⟨|q.num|, q.den, q.den_ne_zero, q.num.abs_eq_natAbs ▸ q.reduced⟩ := by
  refine ext ?_ ?_ <;>
    simp [Int.abs_eq_natAbs, abs_def,
      ← Rat.mk_eq_divInt (num := q.num.natAbs) (nz := q.den_ne_zero) (c := q.reduced)]

@[simp]
/-
**Rat.num_abs_eq_abs_num** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：num_abs_eq_abs_num (q : Rat) : |q|.num = |q.num|
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Rat.den_ne_zero`：∀ (q : ℚ), q.den ≠ 0
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.abs_def'`：abs_def' (q : Rat) : |q| = ⟨|q.num|, q.den, q.den_ne_zero,
 q.num.abs_eq_natAbs ▸ q.reduced⟩
-/
theorem num_abs_eq_abs_num (q : ℚ) : |q|.num = |q.num| := by
  rw [abs_def']

@[simp]
/-
**Rat.den_abs_eq_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：den_abs_eq_den (q : Rat) : |q|.den = q.den
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Rat.den_ne_zero`：∀ (q : ℚ), q.den ≠ 0
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.abs_def'`：abs_def' (q : Rat) : |q| = ⟨|q.num|, q.den, q.den_ne_zero,
 q.num.abs_eq_natAbs ▸ q.reduced⟩
-/
theorem den_abs_eq_den (q : ℚ) : |q|.den = q.den := by
  rw [abs_def']

end Rat

