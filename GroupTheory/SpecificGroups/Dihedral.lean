/-
Copyright (c) 2020 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.GroupAction.CardCommute
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Dihedral Groups

We define the dihedral groups `DihedralGroup n`, with elements `r i` and `sr i` for `i : ZMod n`.

For `n ≠ 0`, `DihedralGroup n` represents the symmetry group of the regular `n`-gon. `r i`
represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the
`n`-gon. `DihedralGroup 0` corresponds to the infinite dihedral group.
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

/-- For `n ≠ 0`, `DihedralGroup n` represents the symmetry group of the regular `n`-gon.
`r i` represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of
the `n`-gon. `DihedralGroup 0` corresponds to the infinite dihedral group.
-/
/-
**DihedralGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：ℕ → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `n ≠ 0`, `DihedralGroup n` represents the symmetry group of the regular `n`-
gon.
`r i` represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents 
the reflections of
the `n`-gon. `DihedralGroup 0` corresponds to the infinite dihedral group.
-/
inductive DihedralGroup (n : ℕ) : Type
  | r : ZMod n → DihedralGroup n
  | sr : ZMod n → DihedralGroup n
  deriving DecidableEq

namespace DihedralGroup

variable {n : ℕ}

set_option backward.privateInPublic true in
/-- Multiplication of the dihedral group.
-/
/-
**DihedralGroup.mul** 是 Mathlib 中的一个定义，位于命名空间 `DihedralGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of the dihedral group.
-/
private def mul : DihedralGroup n → DihedralGroup n → DihedralGroup n
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)

set_option backward.privateInPublic true in
/-- The identity `1` is the rotation by `0`.
-/
/-
**DihedralGroup.one** 是 Mathlib 中的一个定义，位于命名空间 `DihedralGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity `1` is the rotation by `0`.
-/
private def one : DihedralGroup n :=
  r 0

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**DihedralGroup.** 是 Mathlib 中的一个实例，位于命名空间 `DihedralGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (DihedralGroup n) :=
  ⟨one⟩

set_option backward.privateInPublic true in
/-- The inverse of an element of the dihedral group.
-/
/-
**DihedralGroup.inv** 是 Mathlib 中的一个定义，位于命名空间 `DihedralGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of an element of the dihedral group.
-/
private def inv : DihedralGroup n → DihedralGroup n
  | r i => r (-i)
  | sr i => sr i

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The group structure on `DihedralGroup n`.
-/
/-
**DihedralGroup.** 是 Mathlib 中的一个实例，位于命名空间 `DihedralGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group structure on `DihedralGroup n`.
-/
instance : Group (DihedralGroup n) where
  mul := mul
  mul_assoc := by rintro (a | a) (b | b) (c | c) <;> simp only [(· * ·), mul] <;> ring_nf
  one := one
  one_mul := by
    rintro (a | a)
    · exact congr_arg r (zero_add a)
    · exact congr_arg sr (sub_zero a)
  mul_one := by
    rintro (a | a)
    · exact congr_arg r (add_zero a)
    · exact congr_arg sr (add_zero a)
  inv := inv
  inv_mul_cancel := by
    rintro (a | a)
    · exact congr_arg r (neg_add_cancel a)
    · exact congr_arg r (sub_self a)

@[simp]
/-
**DihedralGroup.r_mul_r** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：r_mul_r (i j : ZMod n) : r i * r j = r (i + j)
参数：i j : ZMod n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem r_mul_r (i j : ZMod n) : r i * r j = r (i + j) :=
  rfl

@[simp]
/-
**DihedralGroup.r_mul_sr** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：r_mul_sr (i j : ZMod n) : r i * sr j = sr (j - i)
参数：i j : ZMod n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem r_mul_sr (i j : ZMod n) : r i * sr j = sr (j - i) :=
  rfl

@[simp]
/-
**DihedralGroup.sr_mul_r** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：sr_mul_r (i j : ZMod n) : sr i * r j = sr (i + j)
参数：i j : ZMod n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sr_mul_r (i j : ZMod n) : sr i * r j = sr (i + j) :=
  rfl

@[simp]
/-
**DihedralGroup.sr_mul_sr** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：sr_mul_sr (i j : ZMod n) : sr i * sr j = r (j - i)
参数：i j : ZMod n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sr_mul_sr (i j : ZMod n) : sr i * sr j = r (j - i) :=
  rfl

@[simp]
/-
**DihedralGroup.inv_r** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：inv_r (i : ZMod n) : (r i)⁻¹ = r (-i)
参数：i : ZMod n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_r (i : ZMod n) : (r i)⁻¹ = r (-i) :=
  rfl

@[simp]
/-
**DihedralGroup.inv_sr** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：inv_sr (i : ZMod n) : (sr i)⁻¹ = sr i
参数：i : ZMod n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_sr (i : ZMod n) : (sr i)⁻¹ = sr i :=
  rfl

@[simp]
/-
**DihedralGroup.r_zero** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：r_zero : r 0 = (1 : DihedralGroup n)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem r_zero : r 0 = (1 : DihedralGroup n) :=
  rfl
/-
**DihedralGroup.one_def** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：one_def : (1 : DihedralGroup n) = r 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : DihedralGroup n) = r 0 :=
  rfl

@[simp]
/-
**DihedralGroup.r_pow** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：r_pow (i : ZMod n) (k : Nat) : (r i) ^ k = r (i * k : ZMod n)
参数：i : ZMod n；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `DihedralGroup.r_mul_r`：r_mul_r (i j : ZMod n) : r i * r j = r (i + j)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `DihedralGroup.r.injEq`：∀ {n : ℕ} (a a_1 : ZMod n), (DihedralGroup.r a = 
DihedralGroup.r a_1) = (a = a_1)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem r_pow (i : ZMod n) (k : ℕ) : (r i) ^ k = r (i * k : ZMod n) := by
  induction k with
  | zero => simp only [pow_zero, Nat.cast_zero, mul_zero, r_zero]
  | succ k IH =>
    rw [pow_add, pow_one, IH, r_mul_r, Nat.cast_add, Nat.cast_one, r.injEq, mul_add, mul_one]

@[simp]
/-
**DihedralGroup.r_zpow** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：r_zpow (i : ZMod n) (k : Int) : (r i) ^ k = r (i * k : ZMod n)
参数：i : ZMod n；k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `DihedralGroup.r_pow`：r_pow (i : ZMod n) (k : Nat) : (r i) ^ k = r (i * k
 : ZMod n)
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_mul_eq_mul_neg`：neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
-/
theorem r_zpow (i : ZMod n) (k : ℤ) : (r i) ^ k = r (i * k : ZMod n) := by
  cases k <;> simp [r_pow, neg_mul_eq_mul_neg]

/-- The equivalence between the dihedral group and the sum of `ZMod`s. -/
@[simps]
/-
**DihedralGroup.equivSum** 是 Mathlib 中的一个定义，位于命名空间 `DihedralGroup`。
形式化陈述：equivSum : DihedralGroup n ≃ (ZMod n) oplus (ZMod n) where toFun | r j => 
.inl j | sr j => .inr j invFun | .inl j => r j | .inr j => sr j left_inv
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the dihedral group and the sum of `ZMod`s.
-/
def equivSum : DihedralGroup n ≃ (ZMod n) ⊕ (ZMod n) where
  toFun
    | r j => .inl j
    | sr j => .inr j
  invFun
    | .inl j => r j
    | .inr j => sr j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

/-- If `0 < n`, then `DihedralGroup n` is a finite group.
-/
/-
**DihedralGroup.** 是 Mathlib 中的一个实例，位于命名空间 `DihedralGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `0 < n`, then `DihedralGroup n` is a finite group.
-/
instance [NeZero n] : Fintype (DihedralGroup n) :=
  Fintype.ofEquiv _ equivSum.symm
/-
**DihedralGroup.** 是 Mathlib 中的一个实例，位于命名空间 `DihedralGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Infinite (DihedralGroup 0) :=
  equivSum.symm.infinite_iff.mp inferInstance
/-
**DihedralGroup.** 是 Mathlib 中的一个实例，位于命名空间 `DihedralGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial (DihedralGroup n) :=
  ⟨⟨r 0, sr 0, by by_contra h; injection h⟩⟩

/-- If `0 < n`, then `DihedralGroup n` has `2n` elements.
-/
/-
**DihedralGroup.card** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Fintype.card_sum`：Fintype.card_sum [Fintype α] [Fintype β] : Fintype.car
d (α oplus β) = Fintype.card α + Fintype.card β
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n

--- 原说明 ---
If `0 < n`, then `DihedralGroup n` has `2n` elements.
-/
theorem card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n := by
  rw [← Fintype.card_eq.mpr ⟨equivSum.symm⟩, Fintype.card_sum, ZMod.card, two_mul]
/-
**DihedralGroup.nat_card** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：nat_card : Nat.card (DihedralGroup n) = 2 * n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `DihedralGroup.instInfiniteOfNatNat`：Infinite (DihedralGroup 0)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `DihedralGroup.card`：card [NeZero n] : Fintype.card (DihedralGroup n) = 2
 * n
-/
theorem nat_card : Nat.card (DihedralGroup n) = 2 * n := by
  cases n
  · rw [Nat.card_eq_zero_of_infinite]
  · rw [Nat.card_eq_fintype_card, card]
/-
**DihedralGroup.r_one_pow** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：r_one_pow (k : Nat) : (r 1 : DihedralGroup n) ^ k = r k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DihedralGroup.r_pow`：r_pow (i : ZMod n) (k : Nat) : (r i) ^ k = r (i * k
 : ZMod n)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem r_one_pow (k : ℕ) : (r 1 : DihedralGroup n) ^ k = r k := by
  simp only [r_pow, one_mul]
/-
**DihedralGroup.r_one_zpow** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：r_one_zpow (k : Int) : (r 1 : DihedralGroup n) ^ k = r k
参数：k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DihedralGroup.r_zpow`：r_zpow (i : ZMod n) (k : Int) : (r i) ^ k = r (i *
 k : ZMod n)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem r_one_zpow (k : ℤ) : (r 1 : DihedralGroup n) ^ k = r k := by
  simp only [r_zpow, one_mul]
/-
**DihedralGroup.r_one_pow_n** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：r_one_pow_n : r (1 : ZMod n) ^ n = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DihedralGroup.r_pow`：r_pow (i : ZMod n) (k : Nat) : (r i) ^ k = r (i * k
 : ZMod n)
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem r_one_pow_n : r (1 : ZMod n) ^ n = 1 := by
  simp
/-
**DihedralGroup.sr_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：sr_mul_self (i : ZMod n) : sr i * sr i = 1
参数：i : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sr_mul_self (i : ZMod n) : sr i * sr i = 1 := by
  simp

/-- `sr i` has order 2.
-/
@[simp]
/-
**DihedralGroup.orderOf_sr** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：orderOf_sr (i : ZMod n) : orderOf (sr i) = 2
参数：i : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `orderOf_eq_prime`：orderOf_eq_prime (hg : x ^ p = 1) (hg1 : x != 1) : ord
erOf x = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `DihedralGroup.sr_mul_self`：sr_mul_self (i : ZMod n) : sr i * sr i = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
`sr i` has order 2.
-/
theorem orderOf_sr (i : ZMod n) : orderOf (sr i) = 2 := by
  apply orderOf_eq_prime
  · rw [sq, sr_mul_self]
  · simp [← r_zero]

/-- `r 1` has order `n`.
-/
@[simp]
/-
**DihedralGroup.orderOf_r_one** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：orderOf_r_one : orderOf (r 1 : DihedralGroup n) = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_eq_zero_iff'`：orderOf_eq_zero_iff' : orderOf x = 0 ↔ forall n : 
Nat, 0 < n -> x ^ n != 1
· 使用定理 `DihedralGroup.r_one_pow`：r_one_pow (k : Nat) : (r 1 : DihedralGroup n) ^
 k = r k
· 使用定理 `DihedralGroup.one_def`：one_def : (1 : DihedralGroup n) = r 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `DihedralGroup.r.inj`：∀ {n : ℕ} {a a_1 : ZMod n}, DihedralGroup.r a = Dih
edralGroup.r a_1 → a = a_1
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
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `DihedralGroup.r_one_pow_n`：r_one_pow_n : r (1 : ZMod n) ^ n = 1
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
· 使用定理 `ZMod.val_eq_zero`：∀ {n : ℕ} (a : ZMod n), a.val = 0 ↔ a = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `orderOf_pos`：orderOf_pos (x : G) : 0 < orderOf x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
`r 1` has order `n`.
-/
theorem orderOf_r_one : orderOf (r 1 : DihedralGroup n) = n := by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · rw [orderOf_eq_zero_iff']
    intro n hn
    rw [r_one_pow, one_def]
    apply mt r.inj
    simpa using hn.ne'
  · apply (Nat.le_of_dvd (NeZero.pos n) <|
      orderOf_dvd_of_pow_eq_one <| @r_one_pow_n n).lt_or_eq.resolve_left
    intro h
    have h1 : (r 1 : DihedralGroup n) ^ orderOf (r 1) = 1 := pow_orderOf_eq_one _
    rw [r_one_pow] at h1
    injection h1 with h2
    rw [← ZMod.val_eq_zero, ZMod.val_natCast, Nat.mod_eq_of_lt h] at h2
    exact absurd h2.symm (orderOf_pos _).ne

/-- If `0 < n`, then `r i` has order `n / gcd n i`.
-/
/-
**DihedralGroup.orderOf_r** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：orderOf_r [NeZero n] (i : ZMod n) : orderOf (r i) = n / Nat.gcd n i.val
参数：i : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `DihedralGroup.r_one_pow`：r_one_pow (k : Nat) : (r 1 : DihedralGroup n) ^
 k = r k
· 使用定理 `orderOf_pow`：orderOf_pow (x : G) : orderOf (x ^ n) = orderOf x / Nat.gcd
 (orderOf x) n
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `DihedralGroup.orderOf_r_one`：orderOf_r_one : orderOf (r 1 : DihedralGrou
p n) = n

--- 原说明 ---
If `0 < n`, then `r i` has order `n / gcd n i`.
-/
theorem orderOf_r [NeZero n] (i : ZMod n) : orderOf (r i) = n / Nat.gcd n i.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  rw [← r_one_pow, orderOf_pow, orderOf_r_one]
/-
**DihedralGroup.exponent** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：exponent : Monoid.exponent (DihedralGroup n) = lcm n 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `Monoid.exponent_eq_zero_of_order_zero`：exponent_eq_zero_of_order_zero {g
 : G} (hg : orderOf g = 0) : exponent G = 0
· 使用定理 `DihedralGroup.orderOf_r_one`：orderOf_r_one : orderOf (r 1 : DihedralGrou
p n) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `Monoid.exponent_dvd_of_forall_pow_eq_one`：∀ {G : Type u} [inst : Monoid 
G] {n : ℕ}, (∀ (g : G), g ^ n = 1) → Monoid.exponent G ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `DihedralGroup.orderOf_r`：orderOf_r [NeZero n] (i : ZMod n) : orderOf (r 
i) = n / Nat.gcd n i.val
· 使用定理 `Nat.dvd_trans`：∀ {a b c : ℕ}, a ∣ b → b ∣ c → a ∣ c
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `dvd_lcm_left`：dvd_lcm_left [GCDMonoid α] (a b : α) : a ∣ lcm a b
· 使用定理 `DihedralGroup.orderOf_sr`：orderOf_sr (i : ZMod n) : orderOf (sr i) = 2
· 使用定理 `dvd_lcm_right`：dvd_lcm_right [GCDMonoid α] (a b : α) : b ∣ lcm a b
· 使用定理 `lcm_dvd`：lcm_dvd [GCDMonoid α] {a b c : α} (hab : a ∣ b) (hcb : c ∣ b) :
 lcm a c ∣ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Monoid.order_dvd_exponent`：order_dvd_exponent (g : G) : orderOf g ∣ expo
nent G
-/
theorem exponent : Monoid.exponent (DihedralGroup n) = lcm n 2 := by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · exact Monoid.exponent_eq_zero_of_order_zero orderOf_r_one
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro (m | m)
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_r]
      refine Nat.dvd_trans ⟨gcd n m.val, ?_⟩ (dvd_lcm_left n 2)
      exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n m.val)).symm
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_sr]
      exact dvd_lcm_right n 2
  · apply lcm_dvd
    · convert! Monoid.order_dvd_exponent (r (1 : ZMod n))
      exact orderOf_r_one.symm
    · convert! Monoid.order_dvd_exponent (sr (0 : ZMod n))
      exact (orderOf_sr 0).symm
/-
**DihedralGroup.not_commutative** 是 Mathlib 中的一个引理，位于命名空间 `DihedralGroup`。
形式化陈述：not_commutative : forall {n : Nat}, n != 1 -> n != 2 -> ¬IsMulCommutative 
(DihedralGroup n) | 0, _, _, h' => by simpa using h'.is_comm.comm (r 1) (sr 0) |
 n + 3, _, _, h' => by have
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `DihedralGroup.sr.injEq`：∀ {n : ℕ} (a a_1 : ZMod n), (DihedralGroup.sr a 
= DihedralGroup.sr a_1) = (a = a_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `Nat.Simproc.add_le_gt`：∀ (a : ℕ) {b c : ℕ}, b > c → (a + b ≤ c) = False
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.zero_lt_two`：0 < 2
· 使用定理 `Nat.dvd_of_mod_eq_zero`：∀ {m n : ℕ}, n % m = 0 → m ∣ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ZMod.val_two_eq_two_mod`：val_two_eq_two_mod (n : Nat) : (2 : ZMod n).val
 = 2 % n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.val_eq_zero`：∀ {n : ℕ} (a : ZMod n), a.val = 0 ↔ a = 0
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `neg_eq_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
-a = b ↔ a + b = 0
· 使用定理 `DihedralGroup.sr_mul_r`：sr_mul_r (i j : ZMod n) : sr i * r j = sr (i + j
)
· 使用定理 `DihedralGroup.r_mul_sr`：r_mul_sr (i j : ZMod n) : r i * sr j = sr (j - i
)
-/
lemma not_commutative : ∀ {n : ℕ}, n ≠ 1 → n ≠ 2 → ¬IsMulCommutative (DihedralGroup n)
  | 0, _, _, h' => by simpa using h'.is_comm.comm (r 1) (sr 0)
  | n + 3, _, _, h' => by
    have := h'.is_comm.comm (r 1) (sr 0)
    rw [r_mul_sr, zero_sub, sr_mul_r, zero_add, sr.injEq, neg_eq_iff_add_eq_zero,
      one_add_one_eq_two, ← ZMod.val_eq_zero, ZMod.val_two_eq_two_mod] at this
    simpa using Nat.le_of_dvd Nat.zero_lt_two <| Nat.dvd_of_mod_eq_zero this
/-
**DihedralGroup.commutative_iff** 是 Mathlib 中的一个引理，位于命名空间 `DihedralGroup`。
形式化陈述：commutative_iff : IsMulCommutative (DihedralGroup n) ↔ n = 1 ∨ n = 2 where
 mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `DihedralGroup.not_commutative`：not_commutative : forall {n : Nat}, n != 
1 -> n != 2 -> ¬IsMulCommutative (DihedralGroup n) | 0, _, _, h' => by simpa usi
ng h'.is_comm.comm …
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma commutative_iff : IsMulCommutative (DihedralGroup n) ↔ n = 1 ∨ n = 2 where
  mp := by contrapose!; rintro ⟨h1, h2⟩; exact not_commutative h1 h2
  mpr := by rintro (rfl | rfl) <;> exact ⟨⟨by decide⟩⟩
/-
**DihedralGroup.not_isCyclic** 是 Mathlib 中的一个引理，位于命名空间 `DihedralGroup`。
形式化陈述：not_isCyclic (h1 : n != 1) : ¬ IsCyclic (DihedralGroup n)
参数：h1 : n != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DihedralGroup.exponent`：exponent : Monoid.exponent (DihedralGroup n) = l
cm n 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lcm_same`：lcm_same [NormalizedGCDMonoid α] (a : α) : lcm a a = normalize
 a
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `DihedralGroup.card`：card [NeZero n] : Fintype.card (DihedralGroup n) = 2
 * n
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `IsCyclic.exponent_eq_card`：IsCyclic.exponent_eq_card [Group α] [IsCyclic
 α] : exponent α = Nat.card α
· 使用引理 `DihedralGroup.not_commutative`：not_commutative : forall {n : Nat}, n != 
1 -> n != 2 -> ¬IsMulCommutative (DihedralGroup n) | 0, _, _, h' => by simpa usi
ng h'.is_comm.comm …
-/
lemma not_isCyclic (h1 : n ≠ 1) : ¬ IsCyclic (DihedralGroup n) := fun h => by
  by_cases h2 : n = 2
  · simpa [exponent, card, h2] using h.exponent_eq_card
  · exact not_commutative h1 h2 h.isMulCommutative
/-
**DihedralGroup.isCyclic_iff** 是 Mathlib 中的一个引理，位于命名空间 `DihedralGroup`。
形式化陈述：isCyclic_iff : IsCyclic (DihedralGroup n) ↔ n = 1 where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用引理 `DihedralGroup.not_isCyclic`：not_isCyclic (h1 : n != 1) : ¬ IsCyclic (Dih
edralGroup n)
· 使用定理 `isCyclic_of_prime_card`：isCyclic_of_prime_card {p : Nat} [hp : Fact p.Pr
ime] (h : Nat.card α = p) : IsCyclic α
· 使用定理 `DihedralGroup.nat_card`：nat_card : Nat.card (DihedralGroup n) = 2 * n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isCyclic_iff : IsCyclic (DihedralGroup n) ↔ n = 1 where
  mp := not_imp_not.mp not_isCyclic
  mpr h := h ▸ isCyclic_of_prime_card (p := 2) nat_card
/-
**DihedralGroup.** 是 Mathlib 中的一个实例，位于命名空间 `DihedralGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsKleinFour (DihedralGroup 2) where
  card_four := DihedralGroup.nat_card
  exponent_two := DihedralGroup.exponent

set_option backward.isDefEq.respectTransparency false in
/-- If n is odd, then the Dihedral group of order $2n$ has $n(n+3)$ pairs (represented as
$n + n + n + n*n$) of commuting elements. -/
@[simps]
/-
**DihedralGroup.oddCommuteEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DihedralGroup`。
形式化陈述：oddCommuteEquiv (hn : Odd n) : { p : DihedralGroup n × DihedralGroup n // 
Commute p.1 p.2 } ≃ ZMod n oplus ZMod n oplus ZMod n oplus ZMod n × ZMod n
参数：hn : Odd n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.add_self_eq_zero_iff_eq_zero`：add_self_eq_zero_iff_eq_zero {n : Nat
} (hn : Odd n) {a : ZMod n} : a + a = 0 ↔ a = 0

--- 原说明 ---
If n is odd, then the Dihedral group of order $2n$ has $n(n+3)$ pairs (represent
ed as
$n + n + n + n*n$) of commuting elements.
-/
def oddCommuteEquiv (hn : Odd n) : { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } ≃
    ZMod n ⊕ ZMod n ⊕ ZMod n ⊕ ZMod n × ZMod n :=
  let u := ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr hn.not_two_dvd_nat)
  have hu : ∀ a : ZMod n, a + a = 0 ↔ a = 0 := fun _ => ZMod.add_self_eq_zero_iff_eq_zero hn
  { toFun := fun
      | ⟨⟨sr i, r _⟩, _⟩ => Sum.inl i
      | ⟨⟨r _, sr j⟩, _⟩ => Sum.inr (Sum.inl j)
      | ⟨⟨sr i, sr j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inl (i + j)))
      | ⟨⟨r i, r j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inr ⟨i, j⟩))
    invFun := fun
      | .inl i => ⟨⟨sr i, r 0⟩, congrArg sr ((add_zero i).trans (sub_zero i).symm)⟩
      | .inr (.inl j) => ⟨⟨r 0, sr j⟩, congrArg sr ((sub_zero j).trans (add_zero j).symm)⟩
      | .inr (.inr (.inl k)) => ⟨⟨sr (u⁻¹ * k), sr (u⁻¹ * k)⟩, rfl⟩
      | .inr (.inr (.inr ⟨i, j⟩)) => ⟨⟨r i, r j⟩, congrArg r (add_comm i j)⟩
    left_inv := fun
      | ⟨⟨r _, r _⟩, _⟩ => rfl
      | ⟨⟨r i, sr j⟩, h⟩ => by
        simpa [-r_zero, sub_eq_add_neg, neg_eq_iff_add_eq_zero, hu, eq_comm (a := i) (b := 0)]
          using h.eq
      | ⟨⟨sr i, r j⟩, h⟩ => by
        simpa [-r_zero, sub_eq_add_neg, eq_neg_iff_add_eq_zero, hu, eq_comm (a := j) (b := 0)]
          using h.eq
      | ⟨⟨sr i, sr j⟩, h⟩ => by
        replace h := r.inj h
        rw [← neg_sub, neg_eq_iff_add_eq_zero, hu, sub_eq_zero] at h
        rw [Subtype.ext_iff, Prod.ext_iff, sr.injEq, sr.injEq, h, and_self, ← two_mul]
        exact u.inv_mul_cancel_left j
    right_inv := fun
      | .inl _ => rfl
      | .inr (.inl _) => rfl
      | .inr (.inr (.inl k)) =>
        congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl) <| two_mul (u⁻¹ * k) ▸ u.mul_inv_cancel_left k
      | .inr (.inr (.inr ⟨_, _⟩)) => rfl }

/-- If n is odd, then the Dihedral group of order $2n$ has $n(n+3)$ pairs of commuting elements. -/
/-
**DihedralGroup.card_commute_odd** 是 Mathlib 中的一个引理，位于命名空间 `DihedralGroup`。
形式化陈述：card_commute_odd (hn : Odd n) : Nat.card { p : DihedralGroup n × DihedralG
roup n // Commute p.1 p.2 } = n * (n + 3)
参数：hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Odd.pos`：Odd.pos [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
 [Nontrivial R] {a : R} : Odd a -> 0 < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_sum`：card_sum [Finite α] [Finite β] : Nat.card (α oplus β) = Na
t.card α + Nat.card β
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.card_zmod`：card_zmod (n : Nat) : Nat.card (ZMod n) = n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If n is odd, then the Dihedral group of order $2n$ has $n(n+3)$ pairs of commuti
ng elements.
-/
lemma card_commute_odd (hn : Odd n) :
    Nat.card { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } = n * (n + 3) := by
  have hn' : NeZero n := ⟨hn.pos.ne'⟩
  simp_rw [Nat.card_congr (oddCommuteEquiv hn), Nat.card_sum, Nat.card_prod, Nat.card_zmod]
  ring
/-
**DihedralGroup.card_conjClasses_odd** 是 Mathlib 中的一个引理，位于命名空间 `DihedralGroup`。
形式化陈述：card_conjClasses_odd (hn : Odd n) : Nat.card (ConjClasses (DihedralGroup n
)) = (n + 3) / 2
参数：hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_div_mul_left`：∀ {m : ℕ} (n k : ℕ), 0 < m → m * n / (m * k) = n /
 k
· 使用引理 `Odd.pos`：Odd.pos [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
 [Nontrivial R] {a : R} : Odd a -> 0 < a
· 使用引理 `DihedralGroup.card_commute_odd`：card_commute_odd (hn : Odd n) : Nat.card
 { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } = n * (n + 3)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `card_comm_eq_card_conjClasses_mul_card`：card_comm_eq_card_conjClasses_mu
l_card (G : Type*) [Group G] : Nat.card { p : G × G // Commute p.1 p.2 } = Nat.c
ard (ConjClasses G) * Nat.ca…
· 使用定理 `DihedralGroup.nat_card`：nat_card : Nat.card (DihedralGroup n) = 2 * n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mul_div_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma card_conjClasses_odd (hn : Odd n) :
    Nat.card (ConjClasses (DihedralGroup n)) = (n + 3) / 2 := by
  rw [← Nat.mul_div_mul_left _ 2 hn.pos, ← card_commute_odd hn, mul_comm,
    card_comm_eq_card_conjClasses_mul_card, nat_card, Nat.mul_div_left _ (mul_pos two_pos hn.pos)]
/-
**DihedralGroup.center_eq_bot_of_odd_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `DihedralG
roup`。
形式化陈述：center_eq_bot_of_odd_ne_one (hodd : Odd n) (hne1 : n != 1) : Subgroup.cent
er (DihedralGroup n) = ⊥
参数：hodd : Odd n；hne1 : n != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `DihedralGroup.sr.inj`：∀ {n : ℕ} {a a_1 : ZMod n}, DihedralGroup.sr a = D
ihedralGroup.sr a_1 → a = a_1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `ZMod.add_self_eq_zero_iff_eq_zero`：add_self_eq_zero_iff_eq_zero {n : Nat
} (hn : Odd n) {a : ZMod n} : a + a = 0 ↔ a = 0
-/
theorem center_eq_bot_of_odd_ne_one (hodd : Odd n) (hne1 : n ≠ 1) :
    Subgroup.center (DihedralGroup n) = ⊥ := by
  simp only [Subgroup.eq_bot_iff_forall, Subgroup.mem_center_iff]
  rintro (i | i) h
  · have heq := sr.inj (h (sr i))
    simp_all
  · have heq := sr.inj (h (r 1))
    have : Fact (1 < n) := ⟨by grind⟩
    simp [sub_eq_iff_eq_add, add_assoc, ZMod.add_self_eq_zero_iff_eq_zero hodd] at heq

end DihedralGroup

