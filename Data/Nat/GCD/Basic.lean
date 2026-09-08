/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Algebra.Group.Nat.Units
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.GroupWithZero.Nat

/-!
# Properties of `Nat.gcd`, `Nat.lcm`, and `Nat.Coprime`

Definitions are provided in batteries.

Generalizations of these are provided in a later file as `GCDMonoid.gcd` and
`GCDMonoid.lcm`.

Note that the global `IsCoprime` is not a straightforward generalization of `Nat.Coprime`, see
`Nat.isCoprime_iff_coprime` for the connection between the two.

Most of this file could be moved to batteries as well.
-/

public section

assert_not_exists IsOrderedMonoid

namespace Nat
variable {a a₁ a₂ b b₁ b₂ c : ℕ}

/-! ### `gcd` -/

/-
**Nat.gcd_greatest** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：gcd_greatest {a b d : Nat} (hda : d ∣ a) (hdb : d ∣ b) (hd : forall e : Na
t, e ∣ a -> e ∣ b -> e ∣ d) : d = a.gcd b
参数：hda : d ∣ a；hdb : d ∣ b；hd : forall e : Nat, e ∣ a -> e ∣ b -> e ∣ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `Nat.dvd_gcd`：∀ {k m n : ℕ}, k ∣ m → k ∣ n → k ∣ m.gcd n

--- 原说明 ---
### `gcd`
-/
theorem gcd_greatest {a b d : ℕ} (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : ℕ, e ∣ a → e ∣ b → e ∣ d) :
    d = a.gcd b :=
  (dvd_antisymm (hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)) (dvd_gcd hda hdb)).symm
/-
**Nat.gcd_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：gcd_right_comm (a b c : Nat) : gcd (gcd a b) c = gcd (gcd a c) b
参数：a b c : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.gcd_assoc`：∀ (m n k : ℕ), (m.gcd n).gcd k = m.gcd (n.gcd k)
· 使用定理 `Nat.gcd_comm`：∀ (m n : ℕ), m.gcd n = n.gcd m
-/
theorem gcd_right_comm (a b c : ℕ) : gcd (gcd a b) c = gcd (gcd a c) b := by
  rw [gcd_assoc, gcd_assoc, gcd_comm b c]

/-! Lemmas where one argument consists of addition of a multiple of the other -/

@[simp]
/-
**Nat.pow_sub_one_mod_pow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_sub_one_mod_pow_sub_one (a b c : Nat) : (a ^ c - 1) % (a ^ b - 1) = a 
^ (c % b) - 1
参数：a b c : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zero_pow_eq`：zero_pow_eq (n : Nat) : (0 : M₀) ^ n = if n = 0 then 1 else
 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.eq_or_lt_of_le`：∀ {n m : ℕ}, n ≤ m → n = m ∨ n < m
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Nat.sub_lt_sub_iff_right`：∀ {a b c : ℕ}, c ≤ a → (a - c < b - c ↔ a < b)
· 使用定理 `Nat.one_le_pow`：∀ (n m : ℕ), 0 < m → 1 ≤ m ^ n
· 使用定理 `Nat.pow_lt_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n < a ^ m ↔ n < m)
· 使用定理 `Nat.add_sub_assoc`：∀ {m k : ℕ}, k ≤ m → ∀ (n : ℕ), n + m - k = n + (m - 
k)
· 使用定理 `Nat.mul_add_one`：∀ (n m : ℕ), n * (m + 1) = n * m + n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.add_mod_right`：∀ (x z : ℕ), (x + z) % z = x % z
· 使用定理 `Nat.add_mod`：∀ (a b n : ℕ), (a + b) % n = (a % n + b % n) % n
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
Lemmas where one argument consists of addition of a multiple of the other
-/
theorem pow_sub_one_mod_pow_sub_one (a b c : ℕ) : (a ^ c - 1) % (a ^ b - 1) = a ^ (c % b) - 1 := by
  rcases eq_zero_or_pos a with rfl | ha0
  · simp [zero_pow_eq]; split_ifs <;> simp
  rcases Nat.eq_or_lt_of_le ha0 with rfl | ha1
  · simp
  rcases eq_zero_or_pos b with rfl | hb0
  · simp
  rcases lt_or_ge c b with h | h
  · rw [mod_eq_of_lt, mod_eq_of_lt h]
    rwa [Nat.sub_lt_sub_iff_right (one_le_pow c a ha0), Nat.pow_lt_pow_iff_right ha1]
  · suffices a ^ (c - b + b) - 1 = a ^ (c - b) * (a ^ b - 1) + (a ^ (c - b) - 1) by
      rw [← Nat.sub_add_cancel h, add_mod_right, this, add_mod, mul_mod, mod_self,
        mul_zero, zero_mod, zero_add, mod_mod, pow_sub_one_mod_pow_sub_one]
    rw [← Nat.add_sub_assoc (one_le_pow (c - b) a ha0), ← mul_add_one, pow_add,
      Nat.sub_add_cancel (one_le_pow b a ha0)]

@[simp]
/-
**Nat.pow_sub_one_gcd_pow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_sub_one_gcd_pow_sub_one (a b c : Nat) : gcd (a ^ b - 1) (a ^ c - 1) = 
a ^ gcd b c - 1
参数：a b c : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pow_sub_one_gcd_pow_sub_one._unary`：∀ (a : ℕ) (_x : (_ : ℕ) ×' ℕ), (
a ^ _x.1 - 1).gcd (a ^ _x.2 - 1) = a ^ _x.1.gcd _x.2 - 1
-/
theorem pow_sub_one_gcd_pow_sub_one (a b c : ℕ) :
    gcd (a ^ b - 1) (a ^ c - 1) = a ^ gcd b c - 1 := by
  rcases eq_zero_or_pos b with rfl | hb
  · simp
  replace hb : c % b < b := mod_lt c hb
  rw [gcd_rec, pow_sub_one_mod_pow_sub_one, pow_sub_one_gcd_pow_sub_one, ← gcd_rec]

/-! ### `lcm` and divisibility -/

/-
**Nat.dvd_lcm_of_dvd_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_lcm_of_dvd_left (h : a ∣ b) (c : Nat) : a ∣ lcm b c
参数：h : a ∣ b；c : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.dvd_lcm_left`：∀ (m n : ℕ), m ∣ m.lcm n

--- 原说明 ---
### `lcm` and divisibility
-/
theorem dvd_lcm_of_dvd_left (h : a ∣ b) (c : ℕ) : a ∣ lcm b c :=
  h.trans (dvd_lcm_left b c)

alias Dvd.dvd.nat_lcm_right := dvd_lcm_of_dvd_left
/-
**Nat.dvd_of_lcm_right_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_of_lcm_right_dvd {a b c : Nat} (h : lcm a b ∣ c) : a ∣ c
参数：h : lcm a b ∣ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.dvd_lcm_left`：∀ (m n : ℕ), m ∣ m.lcm n
-/
theorem dvd_of_lcm_right_dvd {a b c : ℕ} (h : lcm a b ∣ c) : a ∣ c :=
  (dvd_lcm_left a b).trans h
/-
**Nat.dvd_lcm_of_dvd_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_lcm_of_dvd_right {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ lcm c b
参数：h : a ∣ b；c : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.dvd_lcm_right`：∀ (m n : ℕ), n ∣ m.lcm n
-/
theorem dvd_lcm_of_dvd_right {a b : ℕ} (h : a ∣ b) (c : ℕ) : a ∣ lcm c b :=
  h.trans (dvd_lcm_right c b)

alias Dvd.dvd.nat_lcm_left := dvd_lcm_of_dvd_right
/-
**Nat.dvd_of_lcm_left_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_of_lcm_left_dvd {a b c : Nat} (h : lcm a b ∣ c) : b ∣ c
参数：h : lcm a b ∣ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.dvd_lcm_right`：∀ (m n : ℕ), n ∣ m.lcm n
-/
theorem dvd_of_lcm_left_dvd {a b c : ℕ} (h : lcm a b ∣ c) : b ∣ c :=
  (dvd_lcm_right a b).trans h

/-!
### `Coprime`

See also `Nat.coprime_of_dvd` and `Nat.coprime_of_dvd'` to prove `Nat.Coprime m n`.
-/

/-
**Nat.Coprime.lcm_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Coprime`。
形式化陈述：∀ {m n : ℕ}, m.Coprime n → m.lcm n = m * n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.Coprime.gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n → m.gcd n = 1
· 使用定理 `Nat.gcd_mul_lcm`：∀ (m n : ℕ), m.gcd n * m.lcm n = m * n

--- 原说明 ---
### `Coprime`

See also `Nat.coprime_of_dvd` and `Nat.coprime_of_dvd'` to prove `Nat.Coprime m 
n`.
-/
theorem Coprime.lcm_eq_mul {m n : ℕ} (h : Coprime m n) : lcm m n = m * n := by
  rw [← one_mul (lcm m n), ← h.gcd_eq_one, gcd_mul_lcm]
/-
**Nat.Coprime.stdSymm** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Coprime`。
形式化陈述：Std.Symm Nat.Coprime
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
-/
instance Coprime.stdSymm : Std.Symm Coprime where
  symm _ _ := Coprime.symm

@[deprecated (since := "2026-06-10")] alias Coprime.symmetric := Coprime.stdSymm
/-
**Nat.Coprime.dvd_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Coprime`。
形式化陈述：∀ {m n k : ℕ}, k.Coprime n → (k ∣ m * n ↔ k ∣ m)
参数：k ∣ m * n ↔ k ∣ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_right`：∀ {k n m : ℕ}, k.Coprime n → k ∣ m * n
 → k ∣ m
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
-/
theorem Coprime.dvd_mul_right {m n k : ℕ} (H : Coprime k n) : k ∣ m * n ↔ k ∣ m :=
  ⟨H.dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h n⟩
/-
**Nat.Coprime.dvd_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Coprime`。
形式化陈述：∀ {m n k : ℕ}, k.Coprime m → (k ∣ m * n ↔ k ∣ n)
参数：k ∣ m * n ↔ k ∣ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_left`：∀ {k m n : ℕ}, k.Coprime m → k ∣ m * n 
→ k ∣ n
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
-/
theorem Coprime.dvd_mul_left {m n k : ℕ} (H : Coprime k m) : k ∣ m * n ↔ k ∣ n :=
  ⟨H.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h m⟩

@[simp]
/-
**Nat.coprime_add_self_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_add_self_right {m n : Nat} : Coprime m (n + m) ↔ Coprime m n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_add_self_right`：∀ (m n : ℕ), m.gcd (n + m) = m.gcd n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_add_self_right {m n : ℕ} : Coprime m (n + m) ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_add_self_right]

@[simp]
/-
**Nat.coprime_self_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_self_add_right {m n : Nat} : Coprime m (m + n) ↔ Coprime m n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.coprime_add_self_right`：coprime_add_self_right {m n : Nat} : Coprime
 m (n + m) ↔ Coprime m n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_self_add_right {m n : ℕ} : Coprime m (m + n) ↔ Coprime m n := by
  rw [add_comm, coprime_add_self_right]

@[simp]
/-
**Nat.coprime_add_self_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_add_self_left {m n : Nat} : Coprime (m + n) n ↔ Coprime m n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_add_self_left`：∀ (m n : ℕ), (n + m).gcd m = n.gcd m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_add_self_left {m n : ℕ} : Coprime (m + n) n ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_add_self_left]

@[simp]
/-
**Nat.coprime_self_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_self_add_left {m n : Nat} : Coprime (m + n) m ↔ Coprime n m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_self_add_left`：∀ (m n : ℕ), (m + n).gcd m = n.gcd m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_self_add_left {m n : ℕ} : Coprime (m + n) m ↔ Coprime n m := by
  rw [Coprime, Coprime, gcd_self_add_left]

@[simp]
/-
**Nat.coprime_add_mul_right_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_add_mul_right_right (m n k : Nat) : Coprime m (n + k * m) ↔ Coprim
e m n
参数：m n k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_add_mul_right_right`：∀ (m n k : ℕ), m.gcd (n + k * m) = m.gcd n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_add_mul_right_right (m n k : ℕ) : Coprime m (n + k * m) ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_add_mul_right_right]

@[simp]
/-
**Nat.coprime_add_mul_left_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_add_mul_left_right (m n k : Nat) : Coprime m (n + m * k) ↔ Coprime
 m n
参数：m n k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_add_mul_left_right`：∀ (m n k : ℕ), m.gcd (n + m * k) = m.gcd n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_add_mul_left_right (m n k : ℕ) : Coprime m (n + m * k) ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_add_mul_left_right]

@[simp]
/-
**Nat.coprime_mul_right_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_mul_right_add_right (m n k : Nat) : Coprime m (k * m + n) ↔ Coprim
e m n
参数：m n k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_mul_right_add_right`：∀ (m n k : ℕ), m.gcd (k * m + n) = m.gcd n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_mul_right_add_right (m n k : ℕ) : Coprime m (k * m + n) ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_mul_right_add_right]

@[simp]
/-
**Nat.coprime_mul_left_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_mul_left_add_right (m n k : Nat) : Coprime m (m * k + n) ↔ Coprime
 m n
参数：m n k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_mul_left_add_right`：∀ (m n k : ℕ), m.gcd (m * k + n) = m.gcd n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_mul_left_add_right (m n k : ℕ) : Coprime m (m * k + n) ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_mul_left_add_right]

@[simp]
/-
**Nat.coprime_add_mul_right_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_add_mul_right_left (m n k : Nat) : Coprime (m + k * n) n ↔ Coprime
 m n
参数：m n k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_add_mul_right_left`：∀ (m n k : ℕ), (n + k * m).gcd m = n.gcd m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_add_mul_right_left (m n k : ℕ) : Coprime (m + k * n) n ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_add_mul_right_left]

@[simp]
/-
**Nat.coprime_add_mul_left_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_add_mul_left_left (m n k : Nat) : Coprime (m + n * k) n ↔ Coprime 
m n
参数：m n k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_add_mul_left_left`：∀ (m n k : ℕ), (n + m * k).gcd m = n.gcd m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_add_mul_left_left (m n k : ℕ) : Coprime (m + n * k) n ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_add_mul_left_left]

@[simp]
/-
**Nat.coprime_mul_right_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_mul_right_add_left (m n k : Nat) : Coprime (k * n + m) n ↔ Coprime
 m n
参数：m n k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_mul_right_add_left`：∀ (m n k : ℕ), (k * m + n).gcd m = n.gcd m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_mul_right_add_left (m n k : ℕ) : Coprime (k * n + m) n ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_mul_right_add_left]

@[simp]
/-
**Nat.coprime_mul_left_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_mul_left_add_left (m n k : Nat) : Coprime (n * k + m) n ↔ Coprime 
m n
参数：m n k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_mul_left_add_left`：∀ (m n k : ℕ), (m * k + n).gcd m = n.gcd m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_mul_left_add_left (m n k : ℕ) : Coprime (n * k + m) n ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_mul_left_add_left]
/-
**Nat.add_coprime_iff_left** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：add_coprime_iff_left (h : c ∣ b) : Coprime (a + b) c ↔ Coprime a c
参数：h : c ∣ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma add_coprime_iff_left (h : c ∣ b) : Coprime (a + b) c ↔ Coprime a c := by
  obtain ⟨n, rfl⟩ := h; simp
/-
**Nat.add_coprime_iff_right** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：add_coprime_iff_right (h : c ∣ a) : Coprime (a + b) c ↔ Coprime b c
参数：h : c ∣ a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma add_coprime_iff_right (h : c ∣ a) : Coprime (a + b) c ↔ Coprime b c := by
  obtain ⟨n, rfl⟩ := h; simp
/-
**Nat.coprime_add_iff_left** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：coprime_add_iff_left (h : a ∣ c) : Coprime a (b + c) ↔ Coprime a b
参数：h : a ∣ c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma coprime_add_iff_left (h : a ∣ c) : Coprime a (b + c) ↔ Coprime a b := by
  obtain ⟨n, rfl⟩ := h; simp
/-
**Nat.coprime_add_iff_right** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：coprime_add_iff_right (h : a ∣ b) : Coprime a (b + c) ↔ Coprime a c
参数：h : a ∣ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma coprime_add_iff_right (h : a ∣ b) : Coprime a (b + c) ↔ Coprime a c := by
  obtain ⟨n, rfl⟩ := h; simp

-- TODO: Replace `Nat.Coprime.coprime_dvd_left`
/-
**Nat.Coprime.of_dvd_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Coprime`。
形式化陈述：∀ {a₁ a₂ b : ℕ}, a₁ ∣ a₂ → a₂.Coprime b → a₁.Coprime b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.coprime_dvd_left`：∀ {m k n : ℕ}, m ∣ k → k.Coprime n → m.Cop
rime n
-/
lemma Coprime.of_dvd_left (ha : a₁ ∣ a₂) (h : Coprime a₂ b) : Coprime a₁ b := h.coprime_dvd_left ha

-- TODO: Replace `Nat.Coprime.coprime_dvd_right`
/-
**Nat.Coprime.of_dvd_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Coprime`。
形式化陈述：∀ {a b₁ b₂ : ℕ}, b₁ ∣ b₂ → a.Coprime b₂ → a.Coprime b₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.coprime_dvd_right`：∀ {n m k : ℕ}, n ∣ m → k.Coprime m → k.Co
prime n
-/
lemma Coprime.of_dvd_right (hb : b₁ ∣ b₂) (h : Coprime a b₂) : Coprime a b₁ :=
  h.coprime_dvd_right hb
/-
**Nat.Coprime.of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Coprime`。
形式化陈述：∀ {a₁ a₂ b₁ b₂ : ℕ}, a₁ ∣ a₂ → b₁ ∣ b₂ → a₂.Coprime b₂ → a₁.Coprime b₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.of_dvd_right`：∀ {a b₁ b₂ : ℕ}, b₁ ∣ b₂ → a.Coprime b₂ → a.Co
prime b₁
· 使用定理 `Nat.Coprime.of_dvd_left`：∀ {a₁ a₂ b : ℕ}, a₁ ∣ a₂ → a₂.Coprime b → a₁.Co
prime b
-/
lemma Coprime.of_dvd (ha : a₁ ∣ a₂) (hb : b₁ ∣ b₂) (h : Coprime a₂ b₂) : Coprime a₁ b₁ :=
  (h.of_dvd_left ha).of_dvd_right hb

@[simp]
/-
**Nat.coprime_sub_self_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_sub_self_left {m n : Nat} (h : m <= n) : Coprime (n - m) m ↔ Copri
me n m
参数：h : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_sub_self_left`：∀ {m n : ℕ}, m ≤ n → (n - m).gcd m = n.gcd m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_sub_self_left {m n : ℕ} (h : m ≤ n) : Coprime (n - m) m ↔ Coprime n m := by
  rw [Coprime, Coprime, gcd_sub_self_left h]

@[simp]
/-
**Nat.coprime_sub_self_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_sub_self_right {m n : Nat} (h : m <= n) : Coprime m (n - m) ↔ Copr
ime m n
参数：h : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_sub_self_right`：∀ {m n : ℕ}, m ≤ n → m.gcd (n - m) = m.gcd n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_sub_self_right {m n : ℕ} (h : m ≤ n) : Coprime m (n - m) ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_sub_self_right h]

@[simp]
/-
**Nat.coprime_self_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_self_sub_left {m n : Nat} (h : m <= n) : Coprime (n - m) n ↔ Copri
me m n
参数：h : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_self_sub_left`：∀ {m n : ℕ}, n ≤ m → (m - n).gcd m = n.gcd m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_self_sub_left {m n : ℕ} (h : m ≤ n) : Coprime (n - m) n ↔ Coprime m n := by
  rw [Coprime, Coprime, gcd_self_sub_left h]

@[simp]
/-
**Nat.coprime_self_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_self_sub_right {m n : Nat} (h : m <= n) : Coprime n (n - m) ↔ Copr
ime n m
参数：h : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
· 使用定理 `Nat.gcd_self_sub_right`：∀ {m n : ℕ}, n ≤ m → m.gcd (m - n) = m.gcd n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_self_sub_right {m n : ℕ} (h : m ≤ n) : Coprime n (n - m) ↔ Coprime n m := by
  rw [Coprime, Coprime, gcd_self_sub_right h]

@[simp]
/-
**Nat.coprime_pow_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_pow_left_iff {n : Nat} (hn : 0 < n) (a b : Nat) : Nat.Coprime (a ^
 n) b ↔ Nat.Coprime a b
参数：hn : 0 < n；a b : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `Nat.ne_of_gt`：∀ {a b : ℕ}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_succ`：∀ (n m : ℕ), n ^ m.succ = n ^ m * n
· 使用定理 `Nat.coprime_mul_iff_left`：∀ {m n k : ℕ}, (m * n).Coprime k ↔ m.Coprime k
 ∧ n.Coprime k
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.Coprime.pow_left`：∀ {m k : ℕ} (n : ℕ), m.Coprime k → (m ^ n).Coprime
 k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coprime_pow_left_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    Nat.Coprime (a ^ n) b ↔ Nat.Coprime a b := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [Nat.pow_succ, Nat.coprime_mul_iff_left]
  exact ⟨And.right, fun hab => ⟨hab.pow_left _, hab⟩⟩

@[simp]
/-
**Nat.coprime_pow_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_pow_right_iff {n : Nat} (hn : 0 < n) (a b : Nat) : Nat.Coprime a (
b ^ n) ↔ Nat.Coprime a b
参数：hn : 0 < n；a b : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.coprime_comm`：∀ {n m : ℕ}, n.Coprime m ↔ m.Coprime n
· 使用定理 `Nat.coprime_pow_left_iff`：coprime_pow_left_iff {n : Nat} (hn : 0 < n) (a
 b : Nat) : Nat.Coprime (a ^ n) b ↔ Nat.Coprime a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coprime_pow_right_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    Nat.Coprime a (b ^ n) ↔ Nat.Coprime a b := by
  rw [Nat.coprime_comm, coprime_pow_left_iff hn, Nat.coprime_comm]
/-
**Nat.not_coprime_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_coprime_zero_zero : ¬Coprime 0 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_coprime_zero_zero : ¬Coprime 0 0 := by simp
/-
**Nat.coprime_one_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_one_left_iff (n : Nat) : Coprime 1 n ↔ True
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.gcd_one_left`：∀ (n : ℕ), Nat.gcd 1 n = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coprime_one_left_iff (n : ℕ) : Coprime 1 n ↔ True := by simp [Coprime]
/-
**Nat.coprime_one_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_one_right_iff (n : Nat) : Coprime n 1 ↔ True
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.gcd_one_right`：∀ (n : ℕ), n.gcd 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coprime_one_right_iff (n : ℕ) : Coprime n 1 ↔ True := by simp [Coprime]
/-
**Nat.gcd_mul_of_coprime_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：gcd_mul_of_coprime_of_dvd {a b c : Nat} (hac : Coprime a c) (b_dvd_c : b ∣
 c) : gcd (a * b) c = b
参数：hac : Coprime a c；b_dvd_c : b ∣ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq_mul_left_of_dvd`：exists_eq_mul_left_of_dvd (h : a ∣ b) : exist
s c, b = c * a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.gcd_mul_right`：∀ (m n k : ℕ), (m * n).gcd (k * n) = m.gcd k * n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Coprime.coprime_mul_right_right`：∀ {m n k : ℕ}, m.Coprime (n * k) → 
m.Coprime n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem gcd_mul_of_coprime_of_dvd {a b c : ℕ} (hac : Coprime a c) (b_dvd_c : b ∣ c) :
    gcd (a * b) c = b := by
  rcases exists_eq_mul_left_of_dvd b_dvd_c with ⟨d, rfl⟩
  rw [gcd_mul_right]
  convert! one_mul b
  exact Coprime.coprime_mul_right_right hac
/-
**Nat.Coprime.eq_of_mul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Coprime`。
形式化陈述：∀ {m n : ℕ}, m.Coprime n → m * n = 0 → m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.coprime_zero_left`：∀ (n : ℕ), Nat.Coprime 0 n ↔ n = 1
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Nat.mul_eq_zero`：∀ {m n : ℕ}, n * m = 0 ↔ n = 0 ∨ m = 0
-/
theorem Coprime.eq_of_mul_eq_zero {m n : ℕ} (h : m.Coprime n) (hmn : m * n = 0) :
    m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 :=
  (Nat.mul_eq_zero.mp hmn).imp (fun hm => ⟨hm, n.coprime_zero_left.mp <| hm ▸ h⟩) fun hn =>
    let eq := hn ▸ h.symm
    ⟨m.coprime_zero_left.mp <| eq, hn⟩
/-
**Nat.coprime_iff_isRelPrime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_iff_isRelPrime {m n : Nat} : m.Coprime n ↔ IsRelPrime m n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem coprime_iff_isRelPrime {m n : ℕ} : m.Coprime n ↔ IsRelPrime m n := by
  simp_rw [coprime_iff_gcd_eq_one, IsRelPrime, ← and_imp, ← dvd_gcd_iff, isUnit_iff_dvd_one]
  exact ⟨fun h _ ↦ (h ▸ ·), (dvd_one.mp <| · dvd_rfl)⟩

/-- If `k:ℕ` divides coprime `a` and `b` then `k = 1` -/
/-
**Nat.eq_one_of_dvd_coprimes** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_one_of_dvd_coprimes {a b k : Nat} (h_ab_coprime : Coprime a b) (hka : k
 ∣ a) (hkb : k ∣ b) : k = 1
参数：h_ab_coprime : Coprime a b；hka : k ∣ a；hkb : k ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `Nat.coprime_iff_isRelPrime`：coprime_iff_isRelPrime {m n : Nat} : m.Copri
me n ↔ IsRelPrime m n

--- 原说明 ---
If `k:ℕ` divides coprime `a` and `b` then `k = 1`
-/
theorem eq_one_of_dvd_coprimes {a b k : ℕ} (h_ab_coprime : Coprime a b) (hka : k ∣ a)
    (hkb : k ∣ b) : k = 1 :=
  dvd_one.mp (isUnit_iff_dvd_one.mp <| coprime_iff_isRelPrime.mp h_ab_coprime hka hkb)
/-
**Nat.Coprime.mul_add_mul_ne_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Coprime`。
形式化陈述：∀ {m n a b : ℕ}, m.Coprime n → a ≠ 0 → b ≠ 0 → a * m + b * n ≠ m * n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_right`：∀ {k n m : ℕ}, k.Coprime n → k ∣ m * n
 → k ∣ m
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.dvd_add_iff_left`：∀ {k m n : ℕ}, k ∣ n → (k ∣ m ↔ k ∣ m + n)
· 使用定理 `Nat.dvd_mul_left`：∀ (a b : ℕ), a ∣ b * a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Nat.dvd_add_iff_right`：∀ {k m n : ℕ}, k ∣ m → (k ∣ n ↔ k ∣ m + n)
· 使用定理 `Nat.dvd_mul_right`：∀ (a b : ℕ), a ∣ a * b
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_zero_of_mul_eq_self_left`：eq_zero_of_mul_eq_self_left [IsRightCancelM
ulZero M₀] (h₁ : b != 1) (h₂ : b * a = a) : a = 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.add_le_add`：∀ {a b c d : ℕ}, a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.add_mul`：∀ (n m k : ℕ), (n + m) * k = n * k + m * k
-/
theorem Coprime.mul_add_mul_ne_mul {m n a b : ℕ} (cop : Coprime m n) (ha : a ≠ 0) (hb : b ≠ 0) :
    a * m + b * n ≠ m * n := by
  intro h
  obtain ⟨x, rfl⟩ : n ∣ a :=
    cop.symm.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_left (Nat.dvd_mul_left n b)).mpr
        ((congr_arg _ h).mpr (Nat.dvd_mul_left n m)))
  obtain ⟨y, rfl⟩ : m ∣ b :=
    cop.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_right (Nat.dvd_mul_left m (n * x))).mpr
        ((congr_arg _ h).mpr (Nat.dvd_mul_right m n)))
  rw [mul_comm, mul_ne_zero_iff, ← one_le_iff_ne_zero] at ha hb
  refine mul_ne_zero hb.2 ha.2 (eq_zero_of_mul_eq_self_left (ne_of_gt (add_le_add ha.1 hb.1)) ?_)
  rw [← mul_assoc, ← h, Nat.add_mul, Nat.add_mul, mul_comm _ n, ← mul_assoc, mul_comm y]

variable {x n m k : ℕ}
/-
**Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：gcd_mul_gcd_eq_iff_dvd_mul_of_coprime (hcop : Coprime n m) : gcd x n * gcd
 x m = x ↔ x ∣ n * m
参数：hcop : Coprime n m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_dvd_mul`：∀ {a b c d : ℕ}, a ∣ b → c ∣ d → a * c ∣ b * d
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.Coprime.mul_dvd_of_dvd_of_dvd`：∀ {m n a : ℕ}, m.Coprime n → m ∣ a → 
n ∣ a → m * n ∣ a
· 使用定理 `Nat.Coprime.gcd_both`：∀ {m n : ℕ} (k l : ℕ), m.Coprime n → (k.gcd m).Cop
rime (l.gcd n)
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.dvd_gcd_mul_gcd_iff_dvd_mul`：∀ {k n m : ℕ}, k ∣ k.gcd n * k.gcd m ↔ 
k ∣ n * m
-/
theorem gcd_mul_gcd_eq_iff_dvd_mul_of_coprime (hcop : Coprime n m) :
    gcd x n * gcd x m = x ↔ x ∣ n * m := by
  refine ⟨fun h ↦ ?_, (dvd_antisymm ?_ <| dvd_gcd_mul_gcd_iff_dvd_mul.mpr ·)⟩
  refine h ▸ Nat.mul_dvd_mul ?_ ?_ <;> exact x.gcd_dvd_right _
  refine (hcop.gcd_both x x).mul_dvd_of_dvd_of_dvd ?_ ?_ <;> exact x.gcd_dvd_left _
/-
**Nat.div_mul_div** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：div_mul_div (hkm : m ∣ k) (hkn : n ∣ m) : (k / m) * (m / n) = k / n
参数：hkm : m ∣ k；hkn : n ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_eq_of_eq_mul_left`：∀ {n m k : ℕ}, 0 < n → m = k * n → m / n = k
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
-/
lemma div_mul_div (hkm : m ∣ k) (hkn : n ∣ m) : (k / m) * (m / n) = k / n := by
  rcases n.eq_zero_or_pos with hn | hn
  · simp [hn]
  refine (Nat.div_eq_of_eq_mul_left hn ?_).symm
  rw [mul_assoc, Nat.div_mul_cancel hkn, Nat.div_mul_cancel hkm]
/-
**Nat.div_dvd_div_left** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：div_dvd_div_left (hkm : m ∣ k) (hkn : n ∣ m) : k / m ∣ k / n
参数：hkm : m ∣ k；hkn : n ∣ m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.div_mul_div`：div_mul_div (hkm : m ∣ k) (hkn : n ∣ m) : (k / m) * (m 
/ n) = k / n
-/
lemma div_dvd_div_left (hkm : m ∣ k) (hkn : n ∣ m) : k / m ∣ k / n :=
  ⟨_, (div_mul_div hkm hkn).symm⟩
/-
**Nat.div_lcm_eq_div_gcd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：div_lcm_eq_div_gcd (hkm : m ∣ k) (hkn : n ∣ k) : (k / m).lcm (k / n) = k /
 (m.gcd n)
参数：hkm : m ∣ k；hkn : n ∣ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lcm_eq_iff`：∀ {n m l : ℕ}, n.lcm m = l ↔ n ∣ l ∧ m ∣ l ∧ ∀ (c : ℕ), 
n ∣ c → m ∣ c → l ∣ c
· 使用引理 `Nat.div_dvd_div_left`：div_dvd_div_left (hkm : m ∣ k) (hkn : n ∣ m) : k /
 m ∣ k / n
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.gcd_zero_left`：∀ (y : ℕ), Nat.gcd 0 y = y
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `Nat.gcd_zero_right`：∀ (n : ℕ), n.gcd 0 = n
· 使用定理 `Nat.div_dvd_iff_dvd_mul`：∀ {a b c : ℕ}, b ∣ a → 0 < b → (a / b ∣ c ↔ a ∣
 b * c)
· 使用定理 `Nat.dvd_trans`：∀ {a b c : ℕ}, a ∣ b → b ∣ c → a ∣ c
· 使用定理 `Nat.gcd_pos_of_pos_left`：∀ {m : ℕ} (n : ℕ), 0 < m → 0 < m.gcd n
· 使用定理 `Nat.gcd_mul_right`：∀ (m n k : ℕ), (m * n).gcd (k * n) = m.gcd k * n
· 使用定理 `Nat.dvd_gcd`：∀ {k m n : ℕ}, k ∣ m → k ∣ n → k ∣ m.gcd n
-/
lemma div_lcm_eq_div_gcd (hkm : m ∣ k) (hkn : n ∣ k) : (k / m).lcm (k / n) = k / (m.gcd n) := by
  rw [Nat.lcm_eq_iff]
  refine ⟨div_dvd_div_left hkm (Nat.gcd_dvd_left m n),
        div_dvd_div_left hkn (Nat.gcd_dvd_right m n), fun c hmc hnc ↦ ?_⟩
  rcases m.eq_zero_or_pos with hm | hm
  · simp_all
  rcases n.eq_zero_or_pos with hn | hn
  · simp_all
  rw [Nat.div_dvd_iff_dvd_mul hkm hm] at hmc
  rw [Nat.div_dvd_iff_dvd_mul hkn hn] at hnc
  simpa [Nat.div_dvd_iff_dvd_mul (Nat.dvd_trans (Nat.gcd_dvd_left m n) hkm)
    (gcd_pos_of_pos_left n hm), Nat.gcd_mul_right m c n] using (Nat.dvd_gcd hmc hnc)

end Nat

