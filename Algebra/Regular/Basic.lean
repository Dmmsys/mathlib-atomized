/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Regular.Defs

/-!
# Regular elements

By definition, a regular element in a commutative ring is a non-zero divisor.
Lemma `IsRegular.of_ne_zero` implies that every non-zero element of an integral domain is regular.
Since it assumes that the ring is a cancellative `MonoidWithZero` it applies also,
for instance, to `ℕ`.

The lemmas in Section `MulZeroClass` show that the `0` element is (left/right-)regular if and
only if the `MulZeroClass` is trivial.  This is useful when figuring out stopping conditions for
regular sequences: if `0` is ever an element of a regular sequence, then we can extend the sequence
by adding one further `0`.

The final goal is to develop part of the API to prove, eventually, results about non-zero-divisors.
-/

public section

variable {R : Type*}

section Mul

variable [Mul R]

/-
**IsLeftRegular.right_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `IsLeftRegular`。
形式化陈述：∀ {R : Type u_1} [inst : Mul R] {a : R}, (∀ (b : R), Commute a b) → IsLeft
Regular a → IsRightRegular a
参数：∀ (b : R), Commute a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
-/
@[to_additive] theorem IsLeftRegular.right_of_commute {a : R}
    (ca : ∀ b, Commute a b) (h : IsLeftRegular a) : IsRightRegular a :=
  fun x y xy => h <| (ca x).trans <| xy.trans <| (ca y).symm
/-
**IsRightRegular.left_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `IsRightRegular`。
形式化陈述：∀ {R : Type u_1} [inst : Mul R] {a : R}, (∀ (b : R), Commute a b) → IsRigh
tRegular a → IsLeftRegular a
参数：∀ (b : R), Commute a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Commute.symm_iff`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b
 ↔ Commute b a
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
-/
@[to_additive] theorem IsRightRegular.left_of_commute {a : R}
    (ca : ∀ b, Commute a b) (h : IsRightRegular a) : IsLeftRegular a := by
  simp only [@Commute.symm_iff R _ a] at ca
  exact fun x y xy => h <| (ca x).trans <| xy.trans <| (ca y).symm
/-
**Commute.isRightRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u_1} [inst : Mul R] {a : R}, (∀ (b : R), Commute a b) → (IsRig
htRegular a ↔ IsLeftRegular a)
参数：∀ (b : R), Commute a b；IsRightRegular a ↔ IsLeftRegular a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRightRegular.left_of_commute`：∀ {R : Type u_1} [inst : Mul R] {a : R},
 (∀ (b : R), Commute a b) → IsRightRegular a → IsLeftRegular a
· 使用定理 `IsLeftRegular.right_of_commute`：∀ {R : Type u_1} [inst : Mul R] {a : R},
 (∀ (b : R), Commute a b) → IsLeftRegular a → IsRightRegular a
-/
@[to_additive] theorem Commute.isRightRegular_iff {a : R} (ca : ∀ b, Commute a b) :
    IsRightRegular a ↔ IsLeftRegular a :=
  ⟨IsRightRegular.left_of_commute ca, IsLeftRegular.right_of_commute ca⟩

@[to_additive]
/-
**Commute.isRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.isRegular_iff {a : R} (ca : forall b, Commute a b) : IsRegular a ↔
 IsLeftRegular a
参数：ca : forall b, Commute a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `IsLeftRegular.right_of_commute`：∀ {R : Type u_1} [inst : Mul R] {a : R},
 (∀ (b : R), Commute a b) → IsLeftRegular a → IsRightRegular a
-/
theorem Commute.isRegular_iff {a : R} (ca : ∀ b, Commute a b) : IsRegular a ↔ IsLeftRegular a :=
  ⟨fun h => h.left, fun h => ⟨h, h.right_of_commute ca⟩⟩

end Mul

section Semigroup

variable [Semigroup R] {a b : R}

/-- In a semigroup, the product of left-regular elements is left-regular. -/
@[to_additive
/-- In an additive semigroup, the sum of add-left-regular elements is add-left.regular. -/]
/-
**IsLeftRegular.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLeftRegular b) : IsLeft
Regular (a * b)
参数：lra : IsLeftRegular a；lrb : IsLeftRegular b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `comp_mul_left`：comp_mul_left (x y : α) : (x * ·) ∘ (y * ·) = (x * y * ·)
-/
theorem IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLeftRegular b) : IsLeftRegular (a * b) :=
  show Function.Injective (((a * b) * ·)) from comp_mul_left a b ▸ lra.comp lrb

/-- In a semigroup, the product of right-regular elements is right-regular. -/
@[to_additive
/-- In an additive semigroup, the sum of add-right-regular elements is add-right-regular. -/]
/-
**IsRightRegular.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRightRegular.mul (rra : IsRightRegular a) (rrb : IsRightRegular b) : IsR
ightRegular (a * b)
参数：rra : IsRightRegular a；rrb : IsRightRegular b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `comp_mul_right`：comp_mul_right (x y : α) : (· * x) ∘ (· * y) = (· * (y *
 x))
-/
theorem IsRightRegular.mul (rra : IsRightRegular a) (rrb : IsRightRegular b) :
    IsRightRegular (a * b) :=
  show Function.Injective (· * (a * b)) from comp_mul_right b a ▸ rrb.comp rra

/-- In a semigroup, the product of regular elements is regular. -/
@[to_additive /-- In an additive semigroup, the sum of add-regular elements is add-regular. -/]
/-
**IsRegular.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRegular.mul (rra : IsRegular a) (rrb : IsRegular b) : IsRegular (a * b)
参数：rra : IsRegular a；rrb : IsRegular b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.mul`：IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLe
ftRegular b) : IsLeftRegular (a * b)
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `IsRightRegular.mul`：IsRightRegular.mul (rra : IsRightRegular a) (rrb : I
sRightRegular b) : IsRightRegular (a * b)
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c

--- 原说明 ---
In a semigroup, the product of regular elements is regular.
-/
theorem IsRegular.mul (rra : IsRegular a) (rrb : IsRegular b) :
    IsRegular (a * b) :=
  ⟨rra.left.mul rrb.left, rra.right.mul rrb.right⟩

/-- If an element `b` becomes left-regular after multiplying it on the left by a left-regular
element, then `b` is left-regular. -/
@[to_additive /-- If an element `b` becomes add-left-regular after adding to it on the left
an add-left-regular element, then `b` is add-left-regular. -/]
/-
**IsLeftRegular.of_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) : IsLeftRegular b
参数：ab : IsLeftRegular (a * b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `comp_mul_left`：comp_mul_left (x y : α) : (x * ·) ∘ (y * ·) = (x * y * ·)
-/
theorem IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) : IsLeftRegular b :=
  Function.Injective.of_comp (f := (a * ·)) (by rwa [comp_mul_left a b])

/-- An element is left-regular if and only if multiplying it on the left by a left-regular element
is left-regular. -/
@[to_additive (attr := simp) /-- An element is add-left-regular if and only if adding to it on the
left an add-left-regular element is add-left-regular. -/]
/-
**mul_isLeftRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_isLeftRegular_iff (b : R) (ha : IsLeftRegular a) : IsLeftRegular (a * 
b) ↔ IsLeftRegular b
参数：b : R；ha : IsLeftRegular a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.of_mul`：IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) 
: IsLeftRegular b
· 使用定理 `IsLeftRegular.mul`：IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLe
ftRegular b) : IsLeftRegular (a * b)
-/
theorem mul_isLeftRegular_iff (b : R) (ha : IsLeftRegular a) :
    IsLeftRegular (a * b) ↔ IsLeftRegular b :=
  ⟨fun ab => IsLeftRegular.of_mul ab, fun ab => IsLeftRegular.mul ha ab⟩

/-- If an element `b` becomes right-regular after multiplying it on the right by a right-regular
element, then `b` is right-regular. -/
@[to_additive /-- If an element `b` becomes add-right-regular after adding to it on the right
an add-right-regular element, then `b` is add-right-regular. -/]
/-
**IsRightRegular.of_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRightRegular.of_mul (ab : IsRightRegular (b * a)) : IsRightRegular b
参数：ab : IsRightRegular (b * a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem IsRightRegular.of_mul (ab : IsRightRegular (b * a)) : IsRightRegular b := by
  refine fun x y xy => ab (?_ : x * (b * a) = y * (b * a))
  rw [← mul_assoc, ← mul_assoc]
  exact congr_arg (· * a) xy

/-- An element is right-regular if and only if multiplying it on the right with a right-regular
element is right-regular. -/
@[to_additive (attr := simp)
/-- An element is add-right-regular if and only if adding it on the right to
an add-right-regular element is add-right-regular. -/]
/-
**mul_isRightRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_isRightRegular_iff (b : R) (ha : IsRightRegular a) : IsRightRegular (b
 * a) ↔ IsRightRegular b
参数：b : R；ha : IsRightRegular a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRightRegular.of_mul`：IsRightRegular.of_mul (ab : IsRightRegular (b * a
)) : IsRightRegular b
· 使用定理 `IsRightRegular.mul`：IsRightRegular.mul (rra : IsRightRegular a) (rrb : I
sRightRegular b) : IsRightRegular (a * b)
-/
theorem mul_isRightRegular_iff (b : R) (ha : IsRightRegular a) :
    IsRightRegular (b * a) ↔ IsRightRegular b :=
  ⟨fun ab => IsRightRegular.of_mul ab, fun ab => IsRightRegular.mul ab ha⟩

/-- Two elements `a` and `b` are regular if and only if both products `a * b` and `b * a`
are regular. -/
@[to_additive /-- Two elements `a` and `b` are add-regular if and only if both sums `a + b` and
`b + a` are add-regular. -/]
/-
**isRegular_mul_and_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRegular_mul_and_mul_iff : IsRegular (a * b) ∧ IsRegular (b * a) ↔ IsRegu
lar a ∧ IsRegular b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.of_mul`：IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) 
: IsLeftRegular b
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `IsRightRegular.of_mul`：IsRightRegular.of_mul (ab : IsRightRegular (b * a
)) : IsRightRegular b
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
· 使用定理 `IsRegular.mul`：IsRegular.mul (rra : IsRegular a) (rrb : IsRegular b) : I
sRegular (a * b)
-/
theorem isRegular_mul_and_mul_iff :
    IsRegular (a * b) ∧ IsRegular (b * a) ↔ IsRegular a ∧ IsRegular b := by
  refine ⟨?_, ?_⟩
  · rintro ⟨ab, ba⟩
    exact
      ⟨⟨IsLeftRegular.of_mul ba.left, IsRightRegular.of_mul ab.right⟩,
        ⟨IsLeftRegular.of_mul ab.left, IsRightRegular.of_mul ba.right⟩⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha.mul hb, hb.mul ha⟩

/-- The "most used" implication of `mul_and_mul_iff`, with split hypotheses, instead of `∧`. -/
@[to_additive /-- The "most used" implication of `add_and_add_iff`, with split
hypotheses, instead of `∧`. -/]
/-
**IsRegular.and_of_mul_of_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRegular.and_of_mul_of_mul (ab : IsRegular (a * b)) (ba : IsRegular (b * 
a)) : IsRegular a ∧ IsRegular b
参数：ab : IsRegular (a * b)；ba : IsRegular (b * a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isRegular_mul_and_mul_iff`：isRegular_mul_and_mul_iff : IsRegular (a * b)
 ∧ IsRegular (b * a) ↔ IsRegular a ∧ IsRegular b
-/
theorem IsRegular.and_of_mul_of_mul (ab : IsRegular (a * b)) (ba : IsRegular (b * a)) :
    IsRegular a ∧ IsRegular b :=
  isRegular_mul_and_mul_iff.mp ⟨ab, ba⟩

end Semigroup


section MulOneClass

variable [MulOneClass R]

/-- If multiplying by `1` on either side is the identity, `1` is regular. -/
@[to_additive /-- If adding `0` on either side is the identity, `0` is regular. -/]
/-
**isRegular_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRegular_one : IsRegular (1 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
If multiplying by `1` on either side is the identity, `1` is regular.
-/
theorem isRegular_one : IsRegular (1 : R) :=
  ⟨fun a b ab => (one_mul a).symm.trans (Eq.trans ab (one_mul b)), fun a b ab =>
    (mul_one a).symm.trans (Eq.trans ab (mul_one b))⟩

end MulOneClass

section CommSemigroup

variable [CommSemigroup R] {a b : R}

/-- A product is regular if and only if the factors are. -/
@[to_additive /-- A sum is add-regular if and only if the summands are. -/]
/-
**isRegular_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRegular_mul_iff : IsRegular (a * b) ↔ IsRegular a ∧ IsRegular b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isRegular_mul_and_mul_iff`：isRegular_mul_and_mul_iff : IsRegular (a * b)
 ∧ IsRegular (b * a) ↔ IsRegular a ∧ IsRegular b

--- 原说明 ---
A product is regular if and only if the factors are.
-/
theorem isRegular_mul_iff : IsRegular (a * b) ↔ IsRegular a ∧ IsRegular b := by
  refine Iff.trans ?_ isRegular_mul_and_mul_iff
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

/-- If a product is regular, so is its left factor. -/
@[to_additive /-- If a sum is add-regular, so is its left summand. -/]
/-
**IsRegular.of_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRegular.of_mul_left (h : IsRegular (a * b)) : IsRegular a
参数：h : IsRegular (a * b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isRegular_mul_iff`：isRegular_mul_iff : IsRegular (a * b) ↔ IsRegular a ∧
 IsRegular b

--- 原说明 ---
If a product is regular, so is its left factor.
-/
theorem IsRegular.of_mul_left (h : IsRegular (a * b)) : IsRegular a :=
  (isRegular_mul_iff.mp h).1

/-- If a product is regular, so is its right factor. -/
@[to_additive /-- If a sum is add-regular, so is its right summand. -/]
/-
**IsRegular.of_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRegular.of_mul_right (h : IsRegular (a * b)) : IsRegular b
参数：h : IsRegular (a * b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isRegular_mul_iff`：isRegular_mul_iff : IsRegular (a * b) ↔ IsRegular a ∧
 IsRegular b

--- 原说明 ---
If a product is regular, so is its right factor.
-/
theorem IsRegular.of_mul_right (h : IsRegular (a * b)) : IsRegular b :=
  (isRegular_mul_iff.mp h).2

end CommSemigroup

section Monoid

variable [Monoid R] {a b : R} {n : ℕ}

/-- An element admitting a left inverse is left-regular. -/
@[to_additive /-- An element admitting a left additive opposite is add-left-regular. -/]
/-
**isLeftRegular_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeftRegular_of_mul_eq_one (h : b * a = 1) : IsLeftRegular a
参数：h : b * a = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.of_mul`：IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) 
: IsLeftRegular b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `isRegular_one`：isRegular_one : IsRegular (1 : R)

--- 原说明 ---
An element admitting a left inverse is left-regular.
-/
theorem isLeftRegular_of_mul_eq_one (h : b * a = 1) : IsLeftRegular a :=
  IsLeftRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.left)

/-- An element admitting a right inverse is right-regular. -/
@[to_additive /-- An element admitting a right additive opposite is add-right-regular. -/]
/-
**isRightRegular_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRightRegular_of_mul_eq_one (h : a * b = 1) : IsRightRegular a
参数：h : a * b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRightRegular.of_mul`：IsRightRegular.of_mul (ab : IsRightRegular (b * a
)) : IsRightRegular b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
· 使用定理 `isRegular_one`：isRegular_one : IsRegular (1 : R)

--- 原说明 ---
An element admitting a right inverse is right-regular.
-/
theorem isRightRegular_of_mul_eq_one (h : a * b = 1) : IsRightRegular a :=
  IsRightRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.right)

/-- If `R` is a monoid, an element in `Rˣ` is regular. -/
@[to_additive /-- If `R` is an additive monoid, an element in `add_units R` is add-regular. -/]
/-
**Units.isRegular** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.isRegular (a : Rˣ) : IsRegular (a : R)
参数：a : Rˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLeftRegular_of_mul_eq_one`：isLeftRegular_of_mul_eq_one (h : b * a = 1)
 : IsLeftRegular a
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `isRightRegular_of_mul_eq_one`：isRightRegular_of_mul_eq_one (h : a * b = 
1) : IsRightRegular a
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1

--- 原说明 ---
If `R` is a monoid, an element in `Rˣ` is regular.
-/
theorem Units.isRegular (a : Rˣ) : IsRegular (a : R) :=
  ⟨isLeftRegular_of_mul_eq_one a.inv_mul, isRightRegular_of_mul_eq_one a.mul_inv⟩

/-- A unit in a monoid is regular. -/
@[to_additive /-- An additive unit in an additive monoid is add-regular. -/]
/-
**IsUnit.isRegular** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.isRegular (ua : IsUnit a) : IsRegular a
参数：ua : IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isRegular`：Units.isRegular (a : Rˣ) : IsRegular (a : R)

--- 原说明 ---
A unit in a monoid is regular.
-/
theorem IsUnit.isRegular (ua : IsUnit a) : IsRegular a := by
  rcases ua with ⟨a, rfl⟩
  exact Units.isRegular a

/-- Any power of a left-regular element is left-regular. -/
@[to_additive]
/-
**IsLeftRegular.pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLeftRegular.pow (n : Nat) (rla : IsLeftRegular a) : IsLeftRegular (a ^ n
)
参数：n : Nat；rla : IsLeftRegular a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.Injective.iterate`：∀ {α : Type u} {f : α → α}, Function.Injecti
ve f → ∀ (n : ℕ), Function.Injective f^[n]

--- 原说明 ---
Any power of a left-regular element is left-regular.
-/
lemma IsLeftRegular.pow (n : ℕ) (rla : IsLeftRegular a) : IsLeftRegular (a ^ n) := by
  simp only [IsLeftRegular, ← mul_left_iterate, rla.iterate n]

/-- Any power of a right-regular element is right-regular. -/
@[to_additive]
/-
**IsRightRegular.pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRightRegular.pow (n : Nat) (rra : IsRightRegular a) : IsRightRegular (a 
^ n)
参数：n : Nat；rra : IsRightRegular a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsRightRegular.eq_1`：∀ {R : Type u_1} [inst : Mul R] (c : R), IsRightReg
ular c = Function.Injective fun x => x * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (
fun x => x * a)^[n] = fun x => x * a ^ n
· 使用定理 `Function.Injective.iterate`：∀ {α : Type u} {f : α → α}, Function.Injecti
ve f → ∀ (n : ℕ), Function.Injective f^[n]

--- 原说明 ---
Any power of a right-regular element is right-regular.
-/
lemma IsRightRegular.pow (n : ℕ) (rra : IsRightRegular a) : IsRightRegular (a ^ n) := by
  rw [IsRightRegular, ← mul_right_iterate]
  exact rra.iterate n

/-- Any power of a regular element is regular. -/
/-
**IsRegular.pow** 是 Mathlib 中的一个定理，位于命名空间 `IsRegular`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] {a : R} (n : ℕ), IsRegular a → IsRegula
r (a ^ n)
参数：n : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLeftRegular.pow`：IsLeftRegular.pow (n : Nat) (rla : IsLeftRegular a) :
 IsLeftRegular (a ^ n)
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用引理 `IsRightRegular.pow`：IsRightRegular.pow (n : Nat) (rra : IsRightRegular a
) : IsRightRegular (a ^ n)
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c

--- 原说明 ---
Any power of a regular element is regular.
-/
@[to_additive] lemma IsRegular.pow (n : ℕ) (ra : IsRegular a) : IsRegular (a ^ n) :=
  ⟨IsLeftRegular.pow n ra.left, IsRightRegular.pow n ra.right⟩

/-- An element `a` is left-regular if and only if a positive power of `a` is left-regular. -/
@[to_additive]
/-
**IsLeftRegular.pow_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLeftRegular.pow_iff (n0 : 0 < n) : IsLeftRegular (a ^ n) ↔ IsLeftRegular
 a where mp
参数：n0 : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `IsLeftRegular.of_mul`：IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) 
: IsLeftRegular b
· 使用引理 `IsLeftRegular.pow`：IsLeftRegular.pow (n : Nat) (rla : IsLeftRegular a) :
 IsLeftRegular (a ^ n)

--- 原说明 ---
An element `a` is left-regular if and only if a positive power of `a` is left-re
gular.
-/
lemma IsLeftRegular.pow_iff (n0 : 0 < n) : IsLeftRegular (a ^ n) ↔ IsLeftRegular a where
  mp := by rw [← Nat.succ_pred_eq_of_pos n0, pow_succ]; exact .of_mul
  mpr := .pow n

/-- An element `a` is right-regular if and only if a positive power of `a` is right-regular. -/
@[to_additive]
/-
**IsRightRegular.pow_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRightRegular.pow_iff (n0 : 0 < n) : IsRightRegular (a ^ n) ↔ IsRightRegu
lar a where mp
参数：n0 : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `IsRightRegular.of_mul`：IsRightRegular.of_mul (ab : IsRightRegular (b * a
)) : IsRightRegular b
· 使用引理 `IsRightRegular.pow`：IsRightRegular.pow (n : Nat) (rra : IsRightRegular a
) : IsRightRegular (a ^ n)

--- 原说明 ---
An element `a` is right-regular if and only if a positive power of `a` is right-
regular.
-/
lemma IsRightRegular.pow_iff (n0 : 0 < n) : IsRightRegular (a ^ n) ↔ IsRightRegular a where
  mp := by rw [← Nat.succ_pred_eq_of_pos n0, pow_succ']; exact .of_mul
  mpr := .pow n

/-- An element `a` is regular if and only if a positive power of `a` is regular. -/
/-
**IsRegular.pow_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRegular`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] {a : R} {n : ℕ}, 0 < n → (IsRegular (a 
^ n) ↔ IsRegular a)
参数：IsRegular (a ^ n) ↔ IsRegular a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsLeftRegular.pow_iff`：IsLeftRegular.pow_iff (n0 : 0 < n) : IsLeftRegula
r (a ^ n) ↔ IsLeftRegular a where mp
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用引理 `IsRightRegular.pow_iff`：IsRightRegular.pow_iff (n0 : 0 < n) : IsRightReg
ular (a ^ n) ↔ IsRightRegular a where mp
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
· 使用引理 `IsLeftRegular.pow`：IsLeftRegular.pow (n : Nat) (rla : IsLeftRegular a) :
 IsLeftRegular (a ^ n)
· 使用引理 `IsRightRegular.pow`：IsRightRegular.pow (n : Nat) (rra : IsRightRegular a
) : IsRightRegular (a ^ n)

--- 原说明 ---
An element `a` is regular if and only if a positive power of `a` is regular.
-/
@[to_additive] lemma IsRegular.pow_iff {n : ℕ} (n0 : 0 < n) : IsRegular (a ^ n) ↔ IsRegular a where
  mp h := ⟨(IsLeftRegular.pow_iff n0).mp h.left, (IsRightRegular.pow_iff n0).mp h.right⟩
  mpr h := ⟨.pow n h.left, .pow n h.right⟩
/-
**IsLeftRegular.mul_left_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLeftRegular`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] {a b : R}, IsLeftRegular a → (a * b = a
 ↔ b = 1)
参数：a * b = a ↔ b = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
@[to_additive (attr := simp)] lemma IsLeftRegular.mul_left_eq_self_iff (ha : IsLeftRegular a) :
    a * b = a ↔ b = 1 :=
  ⟨fun h ↦ by rwa [← ha.eq_iff, mul_one], fun h ↦ by rw [h, mul_one]⟩
/-
**IsRightRegular.mul_right_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRightRegular
`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] {a b : R}, IsRightRegular a → (b * a = 
a ↔ b = 1)
参数：b * a = a ↔ b = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
@[to_additive (attr := simp)] lemma IsRightRegular.mul_right_eq_self_iff (ha : IsRightRegular a) :
    b * a = a ↔ b = 1 :=
  ⟨fun h ↦ by rwa [← ha.eq_iff, one_mul], fun h ↦ by rw [h, one_mul]⟩

namespace IsDedekindFiniteMonoid

/-
**IsDedekindFiniteMonoid.iff_isLeftRegular_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名
空间 `IsDedekindFiniteMonoid`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R], IsDedekindFiniteMonoid R ↔ ∀ (x y : R)
, x * y = 1 → IsLeftRegular x
参数：x y : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLeftRegular_of_mul_eq_one`：isLeftRegular_of_mul_eq_one (h : b * a = 1)
 : IsLeftRegular a
· 使用定理 `IsDedekindFiniteMonoid.mul_eq_one_symm`：∀ {M : Type u_2} {inst : MulOne 
M} [self : IsDedekindFiniteMonoid M] {a b : M}, a * b = 1 → b * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma iff_isLeftRegular_of_mul_eq_one :
    IsDedekindFiniteMonoid R ↔ ∀ x y : R, x * y = 1 → IsLeftRegular x where
  mp _ x y eq := isLeftRegular_of_mul_eq_one (mul_eq_one_symm eq)
  mpr h := ⟨fun eq ↦ h _ _ eq <| by simp [← mul_assoc, eq]⟩
/-
**IsDedekindFiniteMonoid.iff_isRightRegular_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命
名空间 `IsDedekindFiniteMonoid`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R], IsDedekindFiniteMonoid R ↔ ∀ (x y : R)
, x * y = 1 → IsRightRegular y
参数：x y : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isRightRegular_of_mul_eq_one`：isRightRegular_of_mul_eq_one (h : a * b = 
1) : IsRightRegular a
· 使用定理 `IsDedekindFiniteMonoid.mul_eq_one_symm`：∀ {M : Type u_2} {inst : MulOne 
M} [self : IsDedekindFiniteMonoid M] {a b : M}, a * b = 1 → b * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma iff_isRightRegular_of_mul_eq_one :
    IsDedekindFiniteMonoid R ↔ ∀ x y : R, x * y = 1 → IsRightRegular y where
  mp _ x y eq := isRightRegular_of_mul_eq_one (mul_eq_one_symm eq)
  mpr h := ⟨fun eq ↦ h _ _ eq <| by simp [mul_assoc, eq]⟩

end IsDedekindFiniteMonoid

end Monoid

