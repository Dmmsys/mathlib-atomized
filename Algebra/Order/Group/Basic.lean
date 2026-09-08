/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Lemmas about the interaction of power operations with order
-/

public section

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton

open Function Int

variable {α : Type*}

section OrderedCommGroup
variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {m n : ℤ} {a b : α}

@[to_additive zsmul_left_strictMono]
/-
**zpow_right_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_right_strictMono (ha : 1 < a) : StrictMono fun n : Int => a ^ n
参数：ha : 1 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_int_of_lt_succ`：strictMono_int_of_lt_succ {f : Int -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `lt_mul_of_one_lt_right'`：lt_mul_of_one_lt_right' [MulLeftStrictMono α] (
a : α) {b : α} (h : 1 < b) : a < a * b
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma zpow_right_strictMono (ha : 1 < a) : StrictMono fun n : ℤ ↦ a ^ n := by
  refine strictMono_int_of_lt_succ fun n ↦ ?_
  rw [zpow_add_one]
  exact lt_mul_of_one_lt_right' (a ^ n) ha

@[to_additive zsmul_left_strictAnti]
/-
**zpow_right_strictAnti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_right_strictAnti (ha : a < 1) : StrictAnti fun n : Int => a ^ n
参数：ha : a < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictAnti_int_of_succ_lt`：strictAnti_int_of_succ_lt {f : Int -> α} (hf 
: forall n, f (n + 1) < f n) : StrictAnti f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `mul_lt_of_lt_one_right'`：mul_lt_of_lt_one_right' [MulLeftStrictMono α] (
a : α) {b : α} (h : b < 1) : a * b < a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma zpow_right_strictAnti (ha : a < 1) : StrictAnti fun n : ℤ ↦ a ^ n := by
  refine strictAnti_int_of_succ_lt fun n ↦ ?_
  rw [zpow_add_one]
  exact mul_lt_of_lt_one_right' (a ^ n) ha

@[to_additive zsmul_left_inj]
/-
**zpow_right_inj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_right_inj (ha : 1 < a) {m n : Int} : a ^ m = a ^ n ↔ m = n
参数：ha : 1 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `zpow_right_strictMono`：zpow_right_strictMono (ha : 1 < a) : StrictMono f
un n : Int => a ^ n
-/
lemma zpow_right_inj (ha : 1 < a) {m n : ℤ} : a ^ m = a ^ n ↔ m = n :=
  (zpow_right_strictMono ha).injective.eq_iff

@[to_additive zsmul_left_mono]
/-
**zpow_right_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_right_mono (ha : 1 <= a) : Monotone fun n : Int => a ^ n
参数：ha : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_int_of_le_succ`：monotone_int_of_le_succ {f : Int -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma zpow_right_mono (ha : 1 ≤ a) : Monotone fun n : ℤ ↦ a ^ n := by
  refine monotone_int_of_le_succ fun n ↦ ?_
  rw [zpow_add_one]
  exact le_mul_of_one_le_right' ha

@[to_additive (attr := gcongr) zsmul_le_zsmul_left]
/-
**zpow_le_zpow_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_le_zpow_right (ha : 1 <= a) (h : m <= n) : a ^ m <= a ^ n
参数：ha : 1 <= a；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zpow_right_mono`：zpow_right_mono (ha : 1 <= a) : Monotone fun n : Int =>
 a ^ n
-/
lemma zpow_le_zpow_right (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n := zpow_right_mono ha h

@[to_additive (attr := gcongr) zsmul_lt_zsmul_left]
/-
**zpow_lt_zpow_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_lt_zpow_right (ha : 1 < a) (h : m < n) : a ^ m < a ^ n
参数：ha : 1 < a；h : m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zpow_right_strictMono`：zpow_right_strictMono (ha : 1 < a) : StrictMono f
un n : Int => a ^ n
-/
lemma zpow_lt_zpow_right (ha : 1 < a) (h : m < n) : a ^ m < a ^ n := zpow_right_strictMono ha h

@[to_additive zsmul_le_zsmul_iff_left]
/-
**zpow_le_zpow_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_le_zpow_iff_right (ha : 1 < a) : a ^ m <= a ^ n ↔ m <= n
参数：ha : 1 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `zpow_right_strictMono`：zpow_right_strictMono (ha : 1 < a) : StrictMono f
un n : Int => a ^ n
-/
lemma zpow_le_zpow_iff_right (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (zpow_right_strictMono ha).le_iff_le

@[to_additive zsmul_lt_zsmul_iff_left]
/-
**zpow_lt_zpow_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_lt_zpow_iff_right (ha : 1 < a) : a ^ m < a ^ n ↔ m < n
参数：ha : 1 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `zpow_right_strictMono`：zpow_right_strictMono (ha : 1 < a) : StrictMono f
un n : Int => a ^ n
-/
lemma zpow_lt_zpow_iff_right (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_right_strictMono ha).lt_iff_lt

variable (α)

@[to_additive zsmul_strictMono_right]
/-
**zpow_left_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_left_strictMono (hn : 0 < n) : StrictMono ((· ^ n) : α -> α)
参数：hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_lt_div'`：one_lt_div' : 1 < a / b ↔ b < a
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `Group.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N] [Cov
ariantClass N N (fun x1 x2 => x1 * x2) r],   ContravariantClass N N (fun x1 x2 =
> x…
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用引理 `div_zpow`：div_zpow (a b : α) (n : Int) : (a / b) ^ n = a ^ n / b ^ n
· 使用引理 `one_lt_zpow`：one_lt_zpow {x : G} (hx : 1 < x) {n : Int} (hn : 0 < n) : 1
 < x ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma zpow_left_strictMono (hn : 0 < n) : StrictMono ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_lt_div', ← div_zpow]; exact one_lt_zpow (one_lt_div'.2 hab) hn

@[to_additive zsmul_mono_right]
/-
**zpow_left_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_left_mono (hn : 0 <= n) : Monotone ((· ^ n) : α -> α)
参数：hn : 0 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_le_div'`：one_le_div' : 1 <= a / b ↔ b <= a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用引理 `div_zpow`：div_zpow (a b : α) (n : Int) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `one_le_zpow`：one_le_zpow {x : G} (H : 1 <= x) {n : Int} (hn : 0 <= n) : 
1 <= x ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma zpow_left_mono (hn : 0 ≤ n) : Monotone ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_le_div', ← div_zpow]; exact one_le_zpow (one_le_div'.2 hab) hn

variable {α}

@[to_additive (attr := gcongr) zsmul_le_zsmul_right]
/-
**zpow_le_zpow_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_le_zpow_left (hn : 0 <= n) (h : a <= b) : a ^ n <= b ^ n
参数：hn : 0 <= n；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zpow_left_mono`：zpow_left_mono (hn : 0 <= n) : Monotone ((· ^ n) : α -> 
α)
-/
lemma zpow_le_zpow_left (hn : 0 ≤ n) (h : a ≤ b) : a ^ n ≤ b ^ n := zpow_left_mono α hn h

@[to_additive (attr := gcongr) zsmul_lt_zsmul_right]
/-
**zpow_lt_zpow_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_lt_zpow_left (hn : 0 < n) (h : a < b) : a ^ n < b ^ n
参数：hn : 0 < n；h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zpow_left_strictMono`：zpow_left_strictMono (hn : 0 < n) : StrictMono ((·
 ^ n) : α -> α)
-/
lemma zpow_lt_zpow_left (hn : 0 < n) (h : a < b) : a ^ n < b ^ n := zpow_left_strictMono α hn h

end OrderedCommGroup

section LinearOrderedCommGroup

variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] {n : ℤ} {a b : α}

@[to_additive zsmul_le_zsmul_iff_right]
/-
**zpow_le_zpow_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_le_zpow_iff_left (hn : 0 < n) : a ^ n <= b ^ n ↔ a <= b
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `zpow_left_strictMono`：zpow_left_strictMono (hn : 0 < n) : StrictMono ((·
 ^ n) : α -> α)
-/
lemma zpow_le_zpow_iff_left (hn : 0 < n) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (zpow_left_strictMono α hn).le_iff_le

@[to_additive zsmul_lt_zsmul_iff_right]
/-
**zpow_lt_zpow_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_lt_zpow_iff_left (hn : 0 < n) : a ^ n < b ^ n ↔ a < b
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `zpow_left_strictMono`：zpow_left_strictMono (hn : 0 < n) : StrictMono ((·
 ^ n) : α -> α)
-/
lemma zpow_lt_zpow_iff_left (hn : 0 < n) : a ^ n < b ^ n ↔ a < b :=
  (zpow_left_strictMono α hn).lt_iff_lt

variable (α) in
/-- A nontrivial densely linear ordered commutative group can't be a cyclic group. -/
@[to_additive
  /-- A nontrivial densely linear ordered additive commutative group can't be a cyclic group. -/]
/-
**not_isCyclic_of_denselyOrdered** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isCyclic_of_denselyOrdered [DenselyOrdered α] [Nontrivial α] : ¬IsCycl
ic α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_zpow_surjective`：exists_zpow_surjective (G : Type*) [Pow G Int] [
IsCyclic G] : exists g : G, Function.Surjective (g ^ · : Int -> G)
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_lt_zpow_iff_right`：zpow_lt_zpow_iff_right (ha : 1 < a) : a ^ m < a 
^ n ↔ m < n
· 使用定理 `one_lt_inv'`：∀ {α : Type u} [inst : Group α] [inst_1 : LT α] [MulLeftStr
ictMono α] {a : α}, 1 < a⁻¹ ↔ a < 1
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `inv_zpow'`：inv_zpow' (a : α) (n : Int) : a⁻¹ ^ n = a ^ (-n)
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem not_isCyclic_of_denselyOrdered [DenselyOrdered α] [Nontrivial α] : ¬IsCyclic α := by
  intro h
  rcases exists_zpow_surjective α with ⟨a, ha⟩
  rcases lt_trichotomy a 1 with hlt | rfl | hlt
  · rcases exists_between hlt with ⟨b, hab, hb⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by lia
    rw [← one_lt_inv'] at hlt
    simp_rw [← zpow_lt_zpow_iff_right hlt]
    simp_all
  · rcases exists_ne (1 : α) with ⟨b, hb⟩
    simpa [hb.symm] using ha b
  · rcases exists_between hlt with ⟨b, hb, hba⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by lia
    simp_rw [← zpow_lt_zpow_iff_right hlt]
    simp_all

end LinearOrderedCommGroup

