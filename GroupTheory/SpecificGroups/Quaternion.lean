/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Quaternion Groups

We define the (generalised) quaternion groups `QuaternionGroup n` of order `4n`, also known as
dicyclic groups, with elements `a i` and `xa i` for `i : ZMod n`. The (generalised) quaternion
groups can be defined by the presentation
$\langle a, x | a^{2n} = 1, x^2 = a^n, x^{-1}ax=a^{-1}\rangle$. We write `a i` for
$a^i$ and `xa i` for $x * a^i$. For `n=2` the quaternion group `QuaternionGroup 2` is isomorphic to
the unit integral quaternions `(Quaternion ℤ)ˣ`.

## Main definition

`QuaternionGroup n`: The (generalised) quaternion group of order `4n`.

## Implementation notes

This file is heavily based on `DihedralGroup` by Shing Tak Lam.

In mathematics, the name "quaternion group" is reserved for the cases `n ≥ 2`. Since it would be
inconvenient to carry around this condition we define `QuaternionGroup` also for `n = 0` and
`n = 1`. `QuaternionGroup 0` is isomorphic to the infinite dihedral group, while
`QuaternionGroup 1` is isomorphic to a cyclic group of order `4`.

## References

* https://en.wikipedia.org/wiki/Dicyclic_group
* https://en.wikipedia.org/wiki/Quaternion_group

## TODO

Show that `QuaternionGroup 2 ≃* (Quaternion ℤ)ˣ`.

-/

@[expose] public section


/-- The (generalised) quaternion group `QuaternionGroup n` of order `4n`. It can be defined by the
presentation $\langle a, x | a^{2n} = 1, x^2 = a^n, x^{-1}ax=a^{-1}\rangle$. We write `a i` for
$a^i$ and `xa i` for $x * a^i$.
-/
/-
**QuaternionGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：ℕ → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (generalised) quaternion group `QuaternionGroup n` of order `4n`. It can be 
defined by the
presentation $\langle a, x | a^{2n} = 1, x^2 = a^n, x^{-1}ax=a^{-1}\rangle$. We 
write `a i` for
$a^i$ and `xa i` for $x * a^i$.
-/
inductive QuaternionGroup (n : ℕ) : Type
  | a : ZMod (2 * n) → QuaternionGroup n
  | xa : ZMod (2 * n) → QuaternionGroup n
  deriving DecidableEq

namespace QuaternionGroup

variable {n : ℕ}

set_option backward.privateInPublic true in
/-- Multiplication of the quaternion group.
-/
/-
**QuaternionGroup.mul** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of the quaternion group.
-/
private def mul : QuaternionGroup n → QuaternionGroup n → QuaternionGroup n
  | a i, a j => a (i + j)
  | a i, xa j => xa (j - i)
  | xa i, a j => xa (i + j)
  | xa i, xa j => a (n + j - i)

set_option backward.privateInPublic true in
/-- The identity `1` is given by `aⁱ`.
-/
/-
**QuaternionGroup.one** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity `1` is given by `aⁱ`.
-/
private def one : QuaternionGroup n :=
  a 0

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**QuaternionGroup.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (QuaternionGroup n) :=
  ⟨one⟩

set_option backward.privateInPublic true in
/-- The inverse of an element of the quaternion group.
-/
/-
**QuaternionGroup.inv** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of an element of the quaternion group.
-/
private def inv : QuaternionGroup n → QuaternionGroup n
  | a i => a (-i)
  | xa i => xa (n + i)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The group structure on `QuaternionGroup n`.
-/
/-
**QuaternionGroup.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group structure on `QuaternionGroup n`.
-/
instance : Group (QuaternionGroup n) where
  mul := mul
  mul_assoc := by
    unfold instHMul
    rintro (i | i) (j | j) (k | k) <;> simp only [mul] <;> ring_nf
    have : (2 * n : ZMod (2 * n)) = 0 := by norm_cast; simp
    grind
  one := one
  one_mul := by
    rintro (i | i)
    · exact congr_arg a (zero_add i)
    · exact congr_arg xa (sub_zero i)
  mul_one := by
    rintro (i | i)
    · exact congr_arg a (add_zero i)
    · exact congr_arg xa (add_zero i)
  inv := inv
  inv_mul_cancel := by
    rintro (i | i)
    · exact congr_arg a (neg_add_cancel i)
    · exact congr_arg a (sub_self (n + i))

@[simp]
/-
**QuaternionGroup.a_mul_a** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：a_mul_a (i j : ZMod (2 * n)) : a i * a j = a (i + j)
参数：i j : ZMod (2 * n)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a_mul_a (i j : ZMod (2 * n)) : a i * a j = a (i + j) :=
  rfl

@[simp]
/-
**QuaternionGroup.a_mul_xa** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：a_mul_xa (i j : ZMod (2 * n)) : a i * xa j = xa (j - i)
参数：i j : ZMod (2 * n)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a_mul_xa (i j : ZMod (2 * n)) : a i * xa j = xa (j - i) :=
  rfl

@[simp]
/-
**QuaternionGroup.xa_mul_a** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：xa_mul_a (i j : ZMod (2 * n)) : xa i * a j = xa (i + j)
参数：i j : ZMod (2 * n)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xa_mul_a (i j : ZMod (2 * n)) : xa i * a j = xa (i + j) :=
  rfl

@[simp]
/-
**QuaternionGroup.xa_mul_xa** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：xa_mul_xa (i j : ZMod (2 * n)) : xa i * xa j = a ((n : ZMod (2 * n)) + j -
 i)
参数：i j : ZMod (2 * n)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xa_mul_xa (i j : ZMod (2 * n)) : xa i * xa j = a ((n : ZMod (2 * n)) + j - i) :=
  rfl

@[simp]
/-
**QuaternionGroup.a_zero** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：a_zero : a 0 = (1 : QuaternionGroup n)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a_zero : a 0 = (1 : QuaternionGroup n) := by
  rfl
/-
**QuaternionGroup.one_def** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：one_def : (1 : QuaternionGroup n) = a 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : QuaternionGroup n) = a 0 :=
  rfl

set_option backward.privateInPublic true in
/-
**QuaternionGroup.fintypeHelper** 是 Mathlib 中的一个定义，位于命名空间 `QuaternionGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def fintypeHelper : ZMod (2 * n) ⊕ ZMod (2 * n) ≃ QuaternionGroup n where
  invFun i :=
    match i with
    | a j => Sum.inl j
    | xa j => Sum.inr j
  toFun i :=
    match i with
    | Sum.inl j => a j
    | Sum.inr j => xa j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

/-- The special case that more or less by definition `QuaternionGroup 0` is isomorphic to the
infinite dihedral group. -/
/-
**QuaternionGroup.quaternionGroupZeroEquivDihedralGroupZero** 是 Mathlib 中的一个定义，位
于命名空间 `QuaternionGroup`。
形式化陈述：quaternionGroupZeroEquivDihedralGroupZero : QuaternionGroup 0 ≃* DihedralG
roup 0 where toFun | a j => DihedralGroup.r j | xa j => DihedralGroup.sr j invFu
n | DihedralGroup.r j => a j | DihedralGroup.sr j => xa j left_inv
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The special case that more or less by definition `QuaternionGroup 0` is isomorph
ic to the
infinite dihedral group.
-/
def quaternionGroupZeroEquivDihedralGroupZero : QuaternionGroup 0 ≃* DihedralGroup 0 where
  toFun
    | a j => DihedralGroup.r j
    | xa j => DihedralGroup.sr j
  invFun
    | DihedralGroup.r j => a j
    | DihedralGroup.sr j => xa j
  left_inv := by rintro (k | k) <;> rfl
  right_inv := by rintro (k | k) <;> rfl
  map_mul' := by rintro (k | k) (l | l) <;> simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `0 < n`, then `QuaternionGroup n` is a finite group.
-/
/-
**QuaternionGroup.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `0 < n`, then `QuaternionGroup n` is a finite group.
-/
instance [NeZero n] : Fintype (QuaternionGroup n) :=
  Fintype.ofEquiv _ fintypeHelper
/-
**QuaternionGroup.** 是 Mathlib 中的一个实例，位于命名空间 `QuaternionGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial (QuaternionGroup n) :=
  ⟨⟨a 0, xa 0, by simp [-a_zero]⟩⟩

/-- If `0 < n`, then `QuaternionGroup n` has `4n` elements.
-/
/-
**QuaternionGroup.card** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：card [NeZero n] : Fintype.card (QuaternionGroup n) = 4 * n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHMul`：∀ {n m : ℕ} [hn : NeZero n] [hm : NeZero m], NeZero (
n * m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
· 使用定理 `Fintype.card_sum`：Fintype.card_sum [Fintype α] [Fintype β] : Fintype.car
d (α oplus β) = Fintype.card α + Fintype.card β
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0

--- 原说明 ---
If `0 < n`, then `QuaternionGroup n` has `4n` elements.
-/
theorem card [NeZero n] : Fintype.card (QuaternionGroup n) = 4 * n := by
  rw [← Fintype.card_eq.mpr ⟨fintypeHelper⟩, Fintype.card_sum, ZMod.card, two_mul]
  ring

@[simp]
/-
**QuaternionGroup.a_one_pow** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：a_one_pow (k : Nat) : (a 1 : QuaternionGroup n) ^ k = a k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `QuaternionGroup.a_mul_a`：a_mul_a (i j : ZMod (2 * n)) : a i * a j = a (i
 + j)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem a_one_pow (k : ℕ) : (a 1 : QuaternionGroup n) ^ k = a k := by
  induction k with
  | zero => rw [Nat.cast_zero]; rfl
  | succ k IH =>
    rw [pow_succ, IH, a_mul_a]
    congr 1
    norm_cast
/-
**QuaternionGroup.a_one_pow_n** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：a_one_pow_n : (a 1 : QuaternionGroup n) ^ (2 * n) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuaternionGroup.a_one_pow`：a_one_pow (k : Nat) : (a 1 : QuaternionGroup 
n) ^ k = a k
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `QuaternionGroup.a_zero`：a_zero : a 0 = (1 : QuaternionGroup n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem a_one_pow_n : (a 1 : QuaternionGroup n) ^ (2 * n) = 1 := by
  simp

@[simp]
/-
**QuaternionGroup.xa_sq** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：xa_sq (i : ZMod (2 * n)) : xa i ^ 2 = a n
参数：i : ZMod (2 * n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem xa_sq (i : ZMod (2 * n)) : xa i ^ 2 = a n := by simp [sq]

@[simp]
/-
**QuaternionGroup.xa_pow_four** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：xa_pow_four (i : ZMod (2 * n)) : xa i ^ 4 = 1
参数：i : ZMod (2 * n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `QuaternionGroup.a_zero`：a_zero : a 0 = (1 : QuaternionGroup n)
-/
theorem xa_pow_four (i : ZMod (2 * n)) : xa i ^ 4 = 1 := by
  calc xa i ^ 4
      = a (n + n) := by simp [pow_succ, add_sub_assoc, sub_sub_cancel]
    _ = a ↑(2 * n) := by simp [Nat.cast_add, two_mul]
    _ = 1 := by simp

/-- If `0 < n`, then `xa i` has order 4.
-/
@[simp]
/-
**QuaternionGroup.orderOf_xa** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：orderOf_xa [NeZero n] (i : ZMod (2 * n)) : orderOf (xa i) = 4
参数：i : ZMod (2 * n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `orderOf_eq_prime_pow`：orderOf_eq_prime_pow (hnot : ¬x ^ p ^ n = 1) (hfin
 : x ^ p ^ (n + 1) = 1) : orderOf x = p ^ (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `QuaternionGroup.xa_sq`：xa_sq (i : ZMod (2 * n)) : xa i ^ 2 = a n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
· 使用定理 `Nat.mod_mul_left_div_self`：∀ (m n k : ℕ), m % (k * n) / n = m / n % k
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ZMod.val_zero`：∀ {n : ℕ}, ZMod.val 0 = 0
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `QuaternionGroup.xa_pow_four`：xa_pow_four (i : ZMod (2 * n)) : xa i ^ 4 =
 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `0 < n`, then `xa i` has order 4.
-/
theorem orderOf_xa [NeZero n] (i : ZMod (2 * n)) : orderOf (xa i) = 4 := by
  change _ = 2 ^ 2
  have : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  apply orderOf_eq_prime_pow
  · intro h
    simp only [pow_one, xa_sq] at h
    injection h with h'
    apply_fun ZMod.val at h'
    apply_fun (· / n) at h'
    simp only [ZMod.val_natCast, ZMod.val_zero, Nat.zero_div, Nat.mod_mul_left_div_self,
      Nat.div_self (NeZero.pos n), reduceCtorEq] at h'
  · simp

/-- In the special case `n = 1`, `Quaternion 1` is a cyclic group (of order `4`). -/
/-
**QuaternionGroup.quaternionGroup_one_isCyclic** 是 Mathlib 中的一个定理，位于命名空间 `Quater
nionGroup`。
形式化陈述：quaternionGroup_one_isCyclic : IsCyclic (QuaternionGroup 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_of_orderOf_eq_card`：isCyclic_of_orderOf_eq_card [Finite α] (x :
 α) (hx : orderOf x = Nat.card α) : IsCyclic α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `QuaternionGroup.card`：card [NeZero n] : Fintype.card (QuaternionGroup n)
 = 4 * n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `QuaternionGroup.orderOf_xa`：orderOf_xa [NeZero n] (i : ZMod (2 * n)) : o
rderOf (xa i) = 4

--- 原说明 ---
In the special case `n = 1`, `Quaternion 1` is a cyclic group (of order `4`).
-/
theorem quaternionGroup_one_isCyclic : IsCyclic (QuaternionGroup 1) := by
  apply isCyclic_of_orderOf_eq_card
  · rw [Nat.card_eq_fintype_card, card, mul_one]
    exact orderOf_xa 0

/-- If `0 < n`, then `a 1` has order `2 * n`.
-/
@[simp]
/-
**QuaternionGroup.orderOf_a_one** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：orderOf_a_one : orderOf (a 1 : QuaternionGroup n) = 2 * n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `QuaternionGroup.one_def`：one_def : (1 : QuaternionGroup n) = a 0
· 使用定理 `QuaternionGroup.a_one_pow`：a_one_pow (k : Nat) : (a 1 : QuaternionGroup 
n) ^ k = a k
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `QuaternionGroup.a.inj`：∀ {n : ℕ} {a a_1 : ZMod (2 * n)}, QuaternionGroup
.a a = QuaternionGroup.a a_1 → a = a_1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instNeZeroNatHMul`：∀ {n m : ℕ} [hn : NeZero n] [hm : NeZero m], NeZero (
n * m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `QuaternionGroup.a_one_pow_n`：a_one_pow_n : (a 1 : QuaternionGroup n) ^ (
2 * n) = 1
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
· 使用定理 `ZMod.val_eq_zero`：∀ {n : ℕ} (a : ZMod n), a.val = 0 ↔ a = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `orderOf_pos`：orderOf_pos (x : G) : 0 < orderOf x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `0 < n`, then `a 1` has order `2 * n`.
-/
theorem orderOf_a_one : orderOf (a 1 : QuaternionGroup n) = 2 * n := by
  rcases eq_zero_or_neZero n with rfl | hn
  · simp_rw [mul_zero, orderOf_eq_zero_iff']
    intro n h
    rw [one_def, a_one_pow]
    apply mt a.inj
    have : CharZero (ZMod (2 * 0)) := ZMod.charZero
    simpa using h.ne'
  apply (Nat.le_of_dvd
    (NeZero.pos _) (orderOf_dvd_of_pow_eq_one (@a_one_pow_n n))).lt_or_eq.resolve_left
  intro h
  have h1 : (a 1 : QuaternionGroup n) ^ orderOf (a 1) = 1 := pow_orderOf_eq_one _
  rw [a_one_pow] at h1
  injection h1 with h2
  rw [← ZMod.val_eq_zero, ZMod.val_natCast, Nat.mod_eq_of_lt h] at h2
  exact absurd h2.symm (orderOf_pos _).ne

/-- If `0 < n`, then `a i` has order `(2 * n) / gcd (2 * n) i`.
-/
/-
**QuaternionGroup.orderOf_a** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：orderOf_a [NeZero n] (i : ZMod (2 * n)) : orderOf (a i) = 2 * n / Nat.gcd 
(2 * n) i.val
参数：i : ZMod (2 * n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `instNeZeroNatHMul`：∀ {n m : ℕ} [hn : NeZero n] [hm : NeZero m], NeZero (
n * m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `QuaternionGroup.a_one_pow`：a_one_pow (k : Nat) : (a 1 : QuaternionGroup 
n) ^ k = a k
· 使用定理 `orderOf_pow`：orderOf_pow (x : G) : orderOf (x ^ n) = orderOf x / Nat.gcd
 (orderOf x) n
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `QuaternionGroup.orderOf_a_one`：orderOf_a_one : orderOf (a 1 : Quaternion
Group n) = 2 * n

--- 原说明 ---
If `0 < n`, then `a i` has order `(2 * n) / gcd (2 * n) i`.
-/
theorem orderOf_a [NeZero n] (i : ZMod (2 * n)) :
    orderOf (a i) = 2 * n / Nat.gcd (2 * n) i.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  rw [← a_one_pow, orderOf_pow, orderOf_a_one]
/-
**QuaternionGroup.exponent** 是 Mathlib 中的一个定理，位于命名空间 `QuaternionGroup`。
形式化陈述：exponent : Monoid.exponent (QuaternionGroup n) = 2 * lcm n 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `lcm_mul_left`：lcm_mul_left [StrongNormalizedGCDMonoid α] (a b c : α) : l
cm (a * b) (a * c) = normalize a * lcm b c
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `GCDMonoid.lcm_zero_left`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} 
[self : GCDMonoid α] (a : α), lcm 0 a = 0
· 使用定理 `Monoid.exponent_eq_zero_of_order_zero`：exponent_eq_zero_of_order_zero {g
 : G} (hg : orderOf g = 0) : exponent G = 0
· 使用定理 `QuaternionGroup.orderOf_a_one`：orderOf_a_one : orderOf (a 1 : Quaternion
Group n) = 2 * n
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `Monoid.exponent_dvd_of_forall_pow_eq_one`：∀ {G : Type u} [inst : Monoid 
G] {n : ℕ}, (∀ (g : G), g ^ n = 1) → Monoid.exponent G ∣ n
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `QuaternionGroup.orderOf_a`：orderOf_a [NeZero n] (i : ZMod (2 * n)) : ord
erOf (a i) = 2 * n / Nat.gcd (2 * n) i.val
· 使用定理 `Nat.dvd_trans`：∀ {a b c : ℕ}, a ∣ b → b ∣ c → a ∣ c
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `dvd_lcm_left`：dvd_lcm_left [GCDMonoid α] (a b : α) : a ∣ lcm a b
· 使用定理 `QuaternionGroup.orderOf_xa`：orderOf_xa [NeZero n] (i : ZMod (2 * n)) : o
rderOf (xa i) = 4
· 使用定理 `dvd_lcm_right`：dvd_lcm_right [GCDMonoid α] (a b : α) : b ∣ lcm a b
· 使用定理 `lcm_dvd`：lcm_dvd [GCDMonoid α] {a b c : α} (hab : a ∣ b) (hcb : c ∣ b) :
 lcm a c ∣ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Monoid.order_dvd_exponent`：order_dvd_exponent (g : G) : orderOf g ∣ expo
nent G
-/
theorem exponent : Monoid.exponent (QuaternionGroup n) = 2 * lcm n 2 := by
  rw [← normalize_eq 2, ← lcm_mul_left, normalize_eq]
  simp only [Nat.reduceMul]
  rcases eq_zero_or_neZero n with rfl | hn
  · simp only [lcm_zero_left, mul_zero]
    exact Monoid.exponent_eq_zero_of_order_zero orderOf_a_one
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro (m | m)
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_a]
      refine Nat.dvd_trans ⟨gcd (2 * n) m.val, ?_⟩ (dvd_lcm_left (2 * n) 4)
      exact (Nat.div_mul_cancel (Nat.gcd_dvd_left (2 * n) m.val)).symm
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_xa]
      exact dvd_lcm_right (2 * n) 4
  · apply lcm_dvd
    · convert! Monoid.order_dvd_exponent (a 1)
      exact orderOf_a_one.symm
    · convert! Monoid.order_dvd_exponent (xa (0 : ZMod (2 * n)))
      exact (orderOf_xa 0).symm

end QuaternionGroup

