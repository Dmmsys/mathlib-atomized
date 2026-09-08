/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Lemmas about densely linearly ordered groups.
-/

public section

variable {α : Type*}

section DenselyOrdered

variable [Group α] [LinearOrder α]
variable [MulLeftMono α]
variable [DenselyOrdered α] {a b : α}

@[to_additive]
/-
**le_of_forall_lt_one_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_forall_lt_one_mul_le (h : forall ε < 1, a * ε <= b) : a <= b
参数：h : forall ε < 1, a * ε <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_one_lt_le_mul`：le_of_forall_one_lt_le_mul (h : forall ε : α
, 1 < ε -> a <= b * ε) : a <= b
· 使用定理 `Group.existsMulOfLE`：∀ (α : Type u) [inst : Group α] [inst_1 : LE α], Ex
istsMulOfLE α
-/
theorem le_of_forall_lt_one_mul_le (h : ∀ ε < 1, a * ε ≤ b) : a ≤ b :=
  le_of_forall_one_lt_le_mul (α := αᵒᵈ) h

@[to_additive]
/-
**le_of_forall_one_lt_div_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_forall_one_lt_div_le (h : forall ε : α, 1 < ε -> a / ε <= b) : a <= 
b
参数：h : forall ε : α, 1 < ε -> a / ε <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_lt_one_mul_le`：le_of_forall_lt_one_mul_le (h : forall ε < 1
, a * ε <= b) : a <= b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.one_lt_inv_iff`：Left.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
-/
theorem le_of_forall_one_lt_div_le (h : ∀ ε : α, 1 < ε → a / ε ≤ b) : a ≤ b :=
  le_of_forall_lt_one_mul_le fun ε ε1 => by
    simpa only [div_eq_mul_inv, inv_inv] using h ε⁻¹ (Left.one_lt_inv_iff.2 ε1)

@[to_additive]
/-
**le_iff_forall_lt_one_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_forall_lt_one_mul_le : a <= b ↔ forall ε < 1, a * ε <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iff_forall_one_lt_le_mul`：le_iff_forall_one_lt_le_mul [MulLeftStrictM
ono α] : a <= b ↔ forall ε, 1 < ε -> a <= b * ε
· 使用定理 `Group.existsMulOfLE`：∀ (α : Type u) [inst : Group α] [inst_1 : LE α], Ex
istsMulOfLE α
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
-/
theorem le_iff_forall_lt_one_mul_le : a ≤ b ↔ ∀ ε < 1, a * ε ≤ b :=
  le_iff_forall_one_lt_le_mul (α := αᵒᵈ)

end DenselyOrdered

section DenselyOrdered

@[to_additive]
/-
**exists_lt_mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_lt_mul_left [Group α] [LT α] [DenselyOrdered α]
    [MulRightStrictMono α] {a b c : α} (hc : c < a * b) :
    ∃ a' < a, c < a' * b := by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul.1 hc'⟩

@[to_additive]
/-
**exists_lt_mul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_lt_mul_right [CommGroup α] [LT α] [DenselyOrdered α]
    [MulLeftStrictMono α] {a b c : α} (hc : c < a * b) :
    ∃ b' < b, c < a * b' := by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul'.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul'.1 hc'⟩

@[to_additive]
/-
**exists_mul_left_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_mul_left_lt [Group α] [LT α] [DenselyOrdered α]
    [MulRightStrictMono α] {a b c : α} (hc : a * b < c) :
    ∃ a' > a, a' * b < c := by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt.1 hc'⟩

@[to_additive]
/-
**exists_mul_right_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_mul_right_lt [CommGroup α] [LT α] [DenselyOrdered α]
    [MulLeftStrictMono α] {a b c : α} (hc : a * b < c) :
    ∃ b' > b, a * b' < c := by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt'.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt'.1 hc'⟩

@[to_additive]
/-
**le_mul_of_forall_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_mul_of_forall_lt [CommGroup α] [LinearOrder α] [MulLeftMono α] [Densely
Ordered α] {a b c : α} (h : forall a' > a, forall b' > b, c <= a' * b') : c <= a
 * b
参数：h : forall a' > a, forall b' > b, c <= a' * b'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_gt_imp_ge_of_dense`：le_of_forall_gt_imp_ge_of_dense (h : fo
rall a, a₂ < a -> a₁ <= a) : a₁ <= a₂
· 使用定理 `_private.Mathlib.Algebra.Order.Group.DenselyOrdered.0.exists_mul_left_lt
`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LT α] [DenselyOrdered α] [MulRight
StrictMono α] {a b c : α},   a * b < c → ∃ a' > a, a' * b < c
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `_private.Mathlib.Algebra.Order.Group.DenselyOrdered.0.exists_mul_right_l
t`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : LT α] [DenselyOrdered α] [Mul
LeftStrictMono α] {a b c : α},   a * b < c → ∃ b' > b, a * b' <…
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma le_mul_of_forall_lt [CommGroup α] [LinearOrder α] [MulLeftMono α]
    [DenselyOrdered α] {a b c : α} (h : ∀ a' > a, ∀ b' > b, c ≤ a' * b') :
    c ≤ a * b := by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd ↦ ?_
  obtain ⟨a', ha', hd⟩ := exists_mul_left_lt hd
  obtain ⟨b', hb', hd⟩ := exists_mul_right_lt hd
  exact (h a' ha' b' hb').trans hd.le

@[to_additive]
/-
**mul_le_of_forall_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_le_of_forall_lt [CommGroup α] [LinearOrder α] [MulLeftMono α] [Densely
Ordered α] {a b c : α} (h : forall a' < a, forall b' < b, a' * b' <= c) : a * b 
<= c
参数：h : forall a' < a, forall b' < b, a' * b' <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_lt_imp_le_of_dense`：∀ {α : Type u_2} [inst : LinearOrder α]
 [DenselyOrdered α] {a₁ a₂ : α}, (∀ a < a₂, a ≤ a₁) → a₂ ≤ a₁
· 使用定理 `_private.Mathlib.Algebra.Order.Group.DenselyOrdered.0.exists_lt_mul_left
`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LT α] [DenselyOrdered α] [MulRight
StrictMono α] {a b c : α},   c < a * b → ∃ a' < a, c < a' * b
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `_private.Mathlib.Algebra.Order.Group.DenselyOrdered.0.exists_lt_mul_righ
t`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : LT α] [DenselyOrdered α] [Mul
LeftStrictMono α] {a b c : α},   c < a * b → ∃ b' < b, c < a * …
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma mul_le_of_forall_lt [CommGroup α] [LinearOrder α] [MulLeftMono α]
    [DenselyOrdered α] {a b c : α} (h : ∀ a' < a, ∀ b' < b, a' * b' ≤ c) :
    a * b ≤ c := by
  refine le_of_forall_lt_imp_le_of_dense fun d hd ↦ ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_mul_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_mul_right hd
  exact hd.le.trans (h a' ha' b' hb')

end DenselyOrdered

variable {M : Type*} [LinearOrder M] [DenselyOrdered M] {x : M}

section Monoid
variable [CommMonoid M] [ExistsMulOfLE M] [IsOrderedCancelMonoid M]

@[to_additive]
/-
**exists_pow_two_le_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_pow_two_le_of_one_lt (hx : 1 < x) : ∃ y : M, 1 < y ∧ y ^ 2 ≤ x := by
  obtain ⟨y, hy, hyx⟩ := exists_between hx
  obtain hyx | hxy := le_total (y ^ 2) x
  · exact ⟨y, hy, hyx⟩
  obtain ⟨z, hz, rfl⟩ := exists_one_lt_mul_of_lt' hyx
  exact ⟨z, hz, by simpa [pow_succ] using hxy⟩

@[to_additive]
/-
**exists_pow_lt_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pow_lt_of_one_lt (hx : 1 < x) : forall n : Nat, exists y : M, 1 < y
 ∧ y ^ n < x | 0 => ⟨x, by simpa⟩ | 1 => by simpa using exists_between hx | n + 
2 => by obtain ⟨y, hy, hyx⟩
参数：hx : 1 < x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_pow_lt_of_one_lt (hx : 1 < x) : ∀ n : ℕ, ∃ y : M, 1 < y ∧ y ^ n < x
  | 0 => ⟨x, by simpa⟩
  | 1 => by simpa using exists_between hx
  | n + 2 => by
    obtain ⟨y, hy, hyx⟩ := exists_pow_lt_of_one_lt hx (n + 1)
    obtain ⟨z, hz, hzy⟩ := exists_pow_two_le_of_one_lt hy
    refine ⟨z, hz, hyx.trans_le' ?_⟩
    calc z ^ (n + 2)
      _ ≤ z ^ (2 * (n + 1)) := pow_right_monotone hz.le (by lia)
      _ = (z ^ 2) ^ (n + 1) := by rw [pow_mul]
      _ ≤ y ^ (n + 1) := pow_le_pow_left' hzy (n + 1)

end Monoid

section Group
variable [CommGroup M] [IsOrderedCancelMonoid M]

@[to_additive]
/-
**exists_lt_pow_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lt_pow_of_lt_one (hx : x < 1) (n : Nat) : exists y : M, y < 1 ∧ x <
 y ^ n
参数：hx : x < 1；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pow_lt_of_one_lt`：exists_pow_lt_of_one_lt (hx : 1 < x) : forall n
 : Nat, exists y : M, 1 < y ∧ y ^ n < x | 0 => ⟨x, by simpa⟩ | 1 => by simpa usi
ng exists_bet…
· 使用定理 `Group.existsMulOfLE`：∀ (α : Type u) [inst : Group α] [inst_1 : LE α], Ex
istsMulOfLE α
· 使用定理 `one_lt_inv_of_inv`：∀ {α : Type u} [inst : Group α] [inst_1 : LT α] [MulL
eftStrictMono α] {a : α}, a < 1 → 1 < a⁻¹
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `inv_lt_one_of_one_lt`：inv_lt_one_of_one_lt : 1 < a -> a⁻¹ < 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
theorem exists_lt_pow_of_lt_one (hx : x < 1) (n : ℕ) : ∃ y : M, y < 1 ∧ x < y ^ n := by
  obtain ⟨y, hy, hy'⟩ := exists_pow_lt_of_one_lt (one_lt_inv_of_inv hx) n
  use y⁻¹, inv_lt_one_of_one_lt hy
  simpa [lt_inv'] using hy'

end Group

