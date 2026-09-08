/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Characteristic of semirings
-/

@[expose] public section

assert_not_exists Algebra LinearMap orderOf

open Finset

variable {R S : Type*}

namespace Commute

variable [Semiring R] {p : ℕ} (hp : p.Prime) {x y : R}
include hp

/-
**Commute.add_pow_prime_pow_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p : ℕ},   Nat.Prime p →     ∀ {x y :
 R},       Commute x y →         ∀ (n : ℕ),           (x + y) ^ p ^ n =         
    x ^ p ^ n + y ^ p ^ n + ↑p * ∑ k ∈ Finset.Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n 
- k) * ↑((p ^ n).choose k / p)
参数：n : ℕ；x + y；p ^ n；p ^ n - k；(p ^ n).choose k / p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.add_pow`：add_pow (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑ m
 in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用引理 `Finset.Ico_add_one_right_eq_Icc`：Ico_add_one_right_eq_Icc (a b : α) : Ic
o a (b + 1) = Icc a b
· 使用定理 `Finset.right_notMem_Ico`：right_notMem_Ico : b ∉ Ico a b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.Icc_eq_cons_Ico`：Icc_eq_cons_Ico (h : a <= b) : Icc a b = (Ico a 
b).cons b right_notMem_Ico
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Finset.left_notMem_Ioo`：left_notMem_Ioo : a ∉ Ioo a b
· 使用定理 `Finset.Ico_eq_cons_Ioo`：Ico_eq_cons_Ioo (h : a < b) : Ico a b = (Ioo a b
).cons a left_notMem_Ioo
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Finset.cons.congr_simp`：∀ {α : Type u_1} (a a_1 : α) (e_a : a = a_1) (s 
s_1 : Finset α) (e_s : s = s_1) (h : a ∉ s),   Finset.cons a s h = Finset.cons a
_1 s_1 ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
（共 39 条，此处仅展示前 30 条）
-/
protected lemma add_pow_prime_pow_eq' (h : Commute x y) (n : ℕ) :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * ∑ k ∈ Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * ↑((p ^ n).choose k / p) := calc
  _ = ∑ k ∈ Icc 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * (p ^ n).choose k := by
    rw [h.add_pow, ← Nat.Ico_zero_eq_range, Ico_add_one_right_eq_Icc]
  _ = x ^ p ^ n + y ^ p ^ n + ∑ k ∈ Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * (p ^ n).choose k := by
    simp_rw [Icc_eq_cons_Ico zero_le, Ico_eq_cons_Ioo (pow_pos hp.pos _)]
    simp [-cons_eq_insert, add_assoc]
  _ = _ := by
    simp_rw [mul_sum]
    congr! 2 with k hk
    obtain ⟨hk₀, hk⟩ := mem_Ioo.1 hk
    -- The maths is over now. We just commute things to their place.
    rw [Nat.cast_comm, mul_assoc (_ * _)]
    norm_cast
    rw [Nat.div_mul_cancel (hp.dvd_choose_pow _ _)] <;> lia
/-
**Commute.add_pow_prime_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p : ℕ},   Nat.Prime p →     ∀ {x y :
 R},       Commute x y →         ∀ (n : ℕ),           (x + y) ^ p ^ n =         
    x ^ p ^ n + y ^ p ^ n +               ↑p * x * y * ∑ k ∈ Finset.Ioo 0 (p ^ n
), x ^ (k - 1) * y ^ (p ^ n - k - 1) * ↑((p ^ n).choose k / p)
参数：n : ℕ；x + y；p ^ n；k - 1；p ^ n - k - 1；(p ^ n).choose k / p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.add_pow_prime_pow_eq'`：∀ {R : Type u_1} [inst : Semiring R] {p :
 ℕ},   Nat.Prime p →     ∀ {x y : R},       Commute x y →         ∀ (n : ℕ),    
       (x + y) ^ p …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioo`：mem_Ioo : x in Ioo a b ↔ a < x ∧ x < b
· 使用引理 `mul_pow_sub_one`：mul_pow_sub_one (hn : n != 0) (a : M) : a * a ^ (n - 1)
 = a ^ n
· 使用定理 `Commute.mul_mul_mul_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S
}, Commute b c → ∀ (a d : S), a * b * (c * d) = a * c * (b * d)
· 使用定理 `Commute.pow_left`：pow_left (h : Commute a b) (n : Nat) : Commute (a ^ n)
 b
-/
protected lemma add_pow_prime_pow_eq (h : Commute x y) (n : ℕ) :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * x * y *
          ∑ k ∈ Ioo 0 (p ^ n), x ^ (k - 1) * y ^ (p ^ n - k - 1) * ↑((p ^ n).choose k / p) := by
  rw [h.add_pow_prime_pow_eq' hp, mul_assoc _ x, mul_assoc, mul_sum _ _ (_ * _)]
  congr! 3 with k hk
  obtain ⟨hk₀, hk⟩ := mem_Ioo.1 hk
  rw [← mul_pow_sub_one (by lia), ← mul_pow_sub_one (n := p ^ n - k) (by lia)]
  rw [(h.pow_left _).mul_mul_mul_comm, mul_assoc (x * y)]
/-
**Commute.add_pow_prime_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p : ℕ},   Nat.Prime p →     ∀ {x y :
 R},       Commute x y → (x + y) ^ p = x ^ p + y ^ p + ↑p * ∑ k ∈ Finset.Ioo 0 p
, x ^ k * y ^ (p - k) * ↑(p.choose k / p)
参数：x + y；p - k；p.choose k / p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Commute.add_pow_prime_pow_eq'`：∀ {R : Type u_1} [inst : Semiring R] {p :
 ℕ},   Nat.Prime p →     ∀ {x y : R},       Commute x y →         ∀ (n : ℕ),    
       (x + y) ^ p …
-/
protected lemma add_pow_prime_eq' (h : Commute x y) :
    (x + y) ^ p = x ^ p + y ^ p + p * ∑ k ∈ Ioo 0 p, x ^ k * y ^ (p - k) * ↑(p.choose k / p) := by
  simpa using h.add_pow_prime_pow_eq' hp 1
/-
**Commute.add_pow_prime_eq** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p : ℕ},   Nat.Prime p →     ∀ {x y :
 R},       Commute x y →         (x + y) ^ p =           x ^ p + y ^ p + ↑p * x 
* y * ∑ k ∈ Finset.Ioo 0 p, x ^ (k - 1) * y ^ (p - k - 1) * ↑(p.choose k / p)
参数：x + y；k - 1；p - k - 1；p.choose k / p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Commute.add_pow_prime_pow_eq`：∀ {R : Type u_1} [inst : Semiring R] {p : 
ℕ},   Nat.Prime p →     ∀ {x y : R},       Commute x y →         ∀ (n : ℕ),     
      (x + y) ^ p …
-/
protected lemma add_pow_prime_eq (h : Commute x y) :
    (x + y) ^ p =
      x ^ p + y ^ p + p * x * y *
        ∑ k ∈ Ioo 0 p, x ^ (k - 1) * y ^ (p - k - 1) * ↑(p.choose k / p) := by
  simpa using h.add_pow_prime_pow_eq hp 1
/-
**Commute.exists_add_pow_prime_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p : ℕ},   Nat.Prime p → ∀ {x y : R},
 Commute x y → ∀ (n : ℕ), ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + ↑p * x 
* y * r
参数：n : ℕ；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.add_pow_prime_pow_eq`：∀ {R : Type u_1} [inst : Semiring R] {p : 
ℕ},   Nat.Prime p →     ∀ {x y : R},       Commute x y →         ∀ (n : ℕ),     
      (x + y) ^ p …
-/
protected theorem exists_add_pow_prime_pow_eq (h : Commute x y) (n : ℕ) :
    ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * x * y * r :=
  ⟨_, h.add_pow_prime_pow_eq hp n⟩
/-
**Commute.exists_add_pow_prime_eq** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p : ℕ},   Nat.Prime p → ∀ {x y : R},
 Commute x y → ∃ r, (x + y) ^ p = x ^ p + y ^ p + ↑p * x * y * r
参数：x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.add_pow_prime_eq`：∀ {R : Type u_1} [inst : Semiring R] {p : ℕ}, 
  Nat.Prime p →     ∀ {x y : R},       Commute x y →         (x + y) ^ p =      
     x ^ p + y…
-/
protected theorem exists_add_pow_prime_eq (h : Commute x y) :
    ∃ r, (x + y) ^ p = x ^ p + y ^ p + p * x * y * r :=
  ⟨_, h.add_pow_prime_eq hp⟩

end Commute

section CommSemiring

variable [CommSemiring R] {p : ℕ} (hp : p.Prime) (x y : R) (n : ℕ)
include hp

/-
**add_pow_prime_pow_eq'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_prime_pow_eq' : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * ∑ k 
in Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * ↑((p ^ n).choose k / p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.add_pow_prime_pow_eq'`：∀ {R : Type u_1} [inst : Semiring R] {p :
 ℕ},   Nat.Prime p →     ∀ {x y : R},       Commute x y →         ∀ (n : ℕ),    
       (x + y) ^ p …
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma add_pow_prime_pow_eq' :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * ∑ k ∈ Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * ↑((p ^ n).choose k / p) :=
  (Commute.all x y).add_pow_prime_pow_eq' hp n
/-
**add_pow_prime_pow_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_prime_pow_eq : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * x * y
 * ∑ k in Ioo 0 (p ^ n), x ^ (k - 1) * y ^ (p ^ n - k - 1) * ↑((p ^ n).choose k 
/ p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.add_pow_prime_pow_eq`：∀ {R : Type u_1} [inst : Semiring R] {p : 
ℕ},   Nat.Prime p →     ∀ {x y : R},       Commute x y →         ∀ (n : ℕ),     
      (x + y) ^ p …
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma add_pow_prime_pow_eq :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * x * y *
          ∑ k ∈ Ioo 0 (p ^ n), x ^ (k - 1) * y ^ (p ^ n - k - 1) * ↑((p ^ n).choose k / p) :=
  (Commute.all x y).add_pow_prime_pow_eq hp n
/-
**add_pow_prime_eq'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_prime_eq' : (x + y) ^ p = x ^ p + y ^ p + p * ∑ k in Ioo 0 p, x ^ 
k * y ^ (p - k) * ↑(p.choose k / p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.add_pow_prime_eq'`：∀ {R : Type u_1} [inst : Semiring R] {p : ℕ},
   Nat.Prime p →     ∀ {x y : R},       Commute x y → (x + y) ^ p = x ^ p + y ^ 
p + ↑p * ∑ k ∈ …
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma add_pow_prime_eq' :
    (x + y) ^ p = x ^ p + y ^ p + p * ∑ k ∈ Ioo 0 p, x ^ k * y ^ (p - k) * ↑(p.choose k / p) :=
  (Commute.all x y).add_pow_prime_eq' hp
/-
**add_pow_prime_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_pow_prime_eq : (x + y) ^ p = x ^ p + y ^ p + p * x * y * ∑ k in Ioo 0 
p, x ^ (k - 1) * y ^ (p - k - 1) * ↑(p.choose k / p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.add_pow_prime_eq`：∀ {R : Type u_1} [inst : Semiring R] {p : ℕ}, 
  Nat.Prime p →     ∀ {x y : R},       Commute x y →         (x + y) ^ p =      
     x ^ p + y…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem add_pow_prime_eq :
    (x + y) ^ p =
      x ^ p + y ^ p + p * x * y *
        ∑ k ∈ Ioo 0 p, x ^ (k - 1) * y ^ (p - k - 1) * ↑(p.choose k / p) :=
  (Commute.all x y).add_pow_prime_eq hp
/-
**exists_add_pow_prime_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_add_pow_prime_pow_eq : exists r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ 
p ^ n + p * x * y * r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.exists_add_pow_prime_pow_eq`：∀ {R : Type u_1} [inst : Semiring R
] {p : ℕ},   Nat.Prime p → ∀ {x y : R}, Commute x y → ∀ (n : ℕ), ∃ r, (x + y) ^ 
p ^ n = x ^ p ^ n + y ^ p…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem exists_add_pow_prime_pow_eq :
    ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * x * y * r :=
  (Commute.all x y).exists_add_pow_prime_pow_eq hp n
/-
**exists_add_pow_prime_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_add_pow_prime_eq : exists r, (x + y) ^ p = x ^ p + y ^ p + p * x * 
y * r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.exists_add_pow_prime_eq`：∀ {R : Type u_1} [inst : Semiring R] {p
 : ℕ},   Nat.Prime p → ∀ {x y : R}, Commute x y → ∃ r, (x + y) ^ p = x ^ p + y ^
 p + ↑p * x * y * r
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem exists_add_pow_prime_eq : ∃ r, (x + y) ^ p = x ^ p + y ^ p + p * x * y * r :=
  (Commute.all x y).exists_add_pow_prime_eq hp

end CommSemiring

section Semiring
variable [Semiring R] {x y : R} (p n : ℕ)

section ExpChar
variable [hR : ExpChar R p]

/-
**add_pow_expChar_of_commute** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_expChar_of_commute (h : Commute x y) : (x + y) ^ p = x ^ p + y ^ p
参数：h : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.exists_add_pow_prime_eq`：∀ {R : Type u_1} [inst : Semiring R] {p
 : ℕ},   Nat.Prime p → ∀ {x y : R}, Commute x y → ∃ r, (x + y) ^ p = x ^ p + y ^
 p + ↑p * x * y * r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma add_pow_expChar_of_commute (h : Commute x y) : (x + y) ^ p = x ^ p + y ^ p := by
  obtain _ | hprime := hR
  · simp only [pow_one]
  · let ⟨r, hr⟩ := h.exists_add_pow_prime_eq hprime
    simp [hr]
/-
**add_pow_expChar_pow_of_commute** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_expChar_pow_of_commute (h : Commute x y) : (x + y) ^ p ^ n = x ^ p
 ^ n + y ^ p ^ n
参数：h : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.exists_add_pow_prime_pow_eq`：∀ {R : Type u_1} [inst : Semiring R
] {p : ℕ},   Nat.Prime p → ∀ {x y : R}, Commute x y → ∀ (n : ℕ), ∃ r, (x + y) ^ 
p ^ n = x ^ p ^ n + y ^ p…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma add_pow_expChar_pow_of_commute (h : Commute x y) :
    (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := by
  obtain _ | hprime := hR
  · simp only [one_pow, pow_one]
  · let ⟨r, hr⟩ := h.exists_add_pow_prime_pow_eq hprime n
    simp [hr]
/-
**add_pow_eq_mul_pow_add_pow_div_expChar_of_commute** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：add_pow_eq_mul_pow_add_pow_div_expChar_of_commute (h : Commute x y) : (x +
 y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p)
参数：h : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `add_pow_expChar_of_commute`：add_pow_expChar_of_commute (h : Commute x y)
 : (x + y) ^ p = x ^ p + y ^ p
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
-/
lemma add_pow_eq_mul_pow_add_pow_div_expChar_of_commute (h : Commute x y) :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) := by
  rw [← add_pow_expChar_of_commute _ h, ← pow_mul, ← pow_add, Nat.mod_add_div]

end ExpChar

section CharP
variable [hp : Fact p.Prime] [CharP R p]

/-
**add_pow_char_of_commute** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_char_of_commute (h : Commute x y) : (x + y) ^ p = x ^ p + y ^ p
参数：h : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `add_pow_expChar_of_commute`：add_pow_expChar_of_commute (h : Commute x y)
 : (x + y) ^ p = x ^ p + y ^ p
-/
lemma add_pow_char_of_commute (h : Commute x y) : (x + y) ^ p = x ^ p + y ^ p :=
  add_pow_expChar_of_commute _ h
/-
**add_pow_char_pow_of_commute** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_char_pow_of_commute (h : Commute x y) : (x + y) ^ p ^ n = x ^ p ^ 
n + y ^ p ^ n
参数：h : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `add_pow_expChar_pow_of_commute`：add_pow_expChar_pow_of_commute (h : Comm
ute x y) : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n
-/
lemma add_pow_char_pow_of_commute (h : Commute x y) : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n :=
  add_pow_expChar_pow_of_commute _ _ h
/-
**add_pow_eq_mul_pow_add_pow_div_char_of_commute** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_eq_mul_pow_add_pow_div_char_of_commute (h : Commute x y) : (x + y)
 ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p)
参数：h : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `add_pow_eq_mul_pow_add_pow_div_expChar_of_commute`：add_pow_eq_mul_pow_ad
d_pow_div_expChar_of_commute (h : Commute x y) : (x + y) ^ n = (x + y) ^ (n % p)
 * (x ^ p + y ^ p) ^ (n / p)
-/
lemma add_pow_eq_mul_pow_add_pow_div_char_of_commute (h : Commute x y) :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) :=
  add_pow_eq_mul_pow_add_pow_div_expChar_of_commute _ _ h

end CharP
end Semiring

section CommSemiring
variable [CommSemiring R] (x y : R) (p n : ℕ)

section ExpChar
variable [hR : ExpChar R p]

/-
**add_pow_expChar** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_expChar : (x + y) ^ p = x ^ p + y ^ p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `add_pow_expChar_of_commute`：add_pow_expChar_of_commute (h : Commute x y)
 : (x + y) ^ p = x ^ p + y ^ p
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma add_pow_expChar : (x + y) ^ p = x ^ p + y ^ p := add_pow_expChar_of_commute _ <| .all ..
/-
**add_pow_expChar_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_expChar_pow : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `add_pow_expChar_pow_of_commute`：add_pow_expChar_pow_of_commute (h : Comm
ute x y) : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma add_pow_expChar_pow : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n :=
  add_pow_expChar_pow_of_commute _ _ <| .all ..
/-
**add_pow_eq_mul_pow_add_pow_div_expChar** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_eq_mul_pow_add_pow_div_expChar : (x + y) ^ n = (x + y) ^ (n % p) *
 (x ^ p + y ^ p) ^ (n / p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `add_pow_eq_mul_pow_add_pow_div_expChar_of_commute`：add_pow_eq_mul_pow_ad
d_pow_div_expChar_of_commute (h : Commute x y) : (x + y) ^ n = (x + y) ^ (n % p)
 * (x ^ p + y ^ p) ^ (n / p)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma add_pow_eq_mul_pow_add_pow_div_expChar :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) :=
  add_pow_eq_mul_pow_add_pow_div_expChar_of_commute _ _ <| .all ..

end ExpChar

section CharP
variable [hp : Fact p.Prime] [CharP R p]

/-
**add_pow_char** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_char : (x + y) ^ p = x ^ p + y ^ p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `add_pow_expChar`：add_pow_expChar : (x + y) ^ p = x ^ p + y ^ p
-/
lemma add_pow_char : (x + y) ^ p = x ^ p + y ^ p := add_pow_expChar ..
/-
**add_pow_char_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_char_pow : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `add_pow_expChar_pow`：add_pow_expChar_pow : (x + y) ^ p ^ n = x ^ p ^ n +
 y ^ p ^ n
-/
lemma add_pow_char_pow : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := add_pow_expChar_pow ..
/-
**add_pow_eq_mul_pow_add_pow_div_char** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_pow_eq_mul_pow_add_pow_div_char : (x + y) ^ n = (x + y) ^ (n % p) * (x
 ^ p + y ^ p) ^ (n / p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `add_pow_eq_mul_pow_add_pow_div_expChar`：add_pow_eq_mul_pow_add_pow_div_e
xpChar : (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p)
-/
lemma add_pow_eq_mul_pow_add_pow_div_char :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) :=
  add_pow_eq_mul_pow_add_pow_div_expChar ..

end CharP
end CommSemiring

section Ring
variable [Ring R] {x y : R} (p n : ℕ)

section ExpChar
variable [hR : ExpChar R p]
include hR

/-
**sub_pow_expChar_of_commute** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_pow_expChar_of_commute (h : Commute x y) : (x - y) ^ p = x ^ p - y ^ p
参数：h : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `add_pow_expChar_of_commute`：add_pow_expChar_of_commute (h : Commute x y)
 : (x + y) ^ p = x ^ p + y ^ p
· 使用定理 `Commute.sub_left`：sub_left : Commute a c -> Commute b c -> Commute (a - 
b) c
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sub_pow_expChar_of_commute (h : Commute x y) : (x - y) ^ p = x ^ p - y ^ p := by
  simp [eq_sub_iff_add_eq, ← add_pow_expChar_of_commute _ (h.sub_left rfl)]
/-
**sub_pow_expChar_pow_of_commute** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_pow_expChar_pow_of_commute (h : Commute x y) : (x - y) ^ p ^ n = x ^ p
 ^ n - y ^ p ^ n
参数：h : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `add_pow_expChar_pow_of_commute`：add_pow_expChar_pow_of_commute (h : Comm
ute x y) : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n
· 使用定理 `Commute.sub_left`：sub_left : Commute a c -> Commute b c -> Commute (a - 
b) c
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sub_pow_expChar_pow_of_commute (h : Commute x y) :
    (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := by
  simp [eq_sub_iff_add_eq, ← add_pow_expChar_pow_of_commute _ _ (h.sub_left rfl)]
/-
**sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute (h : Commute x y) : (x -
 y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p)
参数：h : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sub_pow_expChar_of_commute`：sub_pow_expChar_of_commute (h : Commute x y)
 : (x - y) ^ p = x ^ p - y ^ p
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
-/
lemma sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute (h : Commute x y) :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) := by
  rw [← sub_pow_expChar_of_commute _ h, ← pow_mul, ← pow_add, Nat.mod_add_div]

variable (R)
/-
**neg_one_pow_expChar** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_pow_expChar : (-1 : R) ^ p = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `add_pow_expChar_of_commute`：add_pow_expChar_of_commute (h : Commute x y)
 : (x + y) ^ p = x ^ p + y ^ p
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `expChar_ne_zero`：expChar_ne_zero (p : Nat) [hR : ExpChar R p] : p != 0
-/
lemma neg_one_pow_expChar : (-1 : R) ^ p = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 2 [← one_pow p]
  rw [← add_pow_expChar_of_commute _ (Commute.one_right _), neg_add_cancel,
    zero_pow (expChar_ne_zero R p)]
/-
**neg_one_pow_expChar_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_pow_expChar_pow : (-1 : R) ^ p ^ n = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `add_pow_expChar_pow_of_commute`：add_pow_expChar_pow_of_commute (h : Comm
ute x y) : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用引理 `expChar_ne_zero`：expChar_ne_zero (p : Nat) [hR : ExpChar R p] : p != 0
-/
lemma neg_one_pow_expChar_pow : (-1 : R) ^ p ^ n = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 2 [← one_pow (p ^ n)]
  rw [← add_pow_expChar_pow_of_commute _ _ (Commute.one_right _), neg_add_cancel,
    zero_pow (pow_ne_zero _ <| expChar_ne_zero R p)]

end ExpChar

section CharP
variable [hp : Fact p.Prime] [CharP R p]

/-
**sub_pow_char_of_commute** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_pow_char_of_commute (h : Commute x y) : (x - y) ^ p = x ^ p - y ^ p
参数：h : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sub_pow_expChar_of_commute`：sub_pow_expChar_of_commute (h : Commute x y)
 : (x - y) ^ p = x ^ p - y ^ p
-/
lemma sub_pow_char_of_commute (h : Commute x y) : (x - y) ^ p = x ^ p - y ^ p :=
  sub_pow_expChar_of_commute _ h
/-
**sub_pow_char_pow_of_commute** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_pow_char_pow_of_commute (h : Commute x y) : (x - y) ^ p ^ n = x ^ p ^ 
n - y ^ p ^ n
参数：h : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sub_pow_expChar_pow_of_commute`：sub_pow_expChar_pow_of_commute (h : Comm
ute x y) : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n
-/
lemma sub_pow_char_pow_of_commute (h : Commute x y) : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n :=
  sub_pow_expChar_pow_of_commute _ _ h

variable (R)
/-
**neg_one_pow_char** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_pow_char : (-1 : R) ^ p = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `neg_one_pow_expChar`：neg_one_pow_expChar : (-1 : R) ^ p = -1
-/
lemma neg_one_pow_char : (-1 : R) ^ p = -1 := neg_one_pow_expChar ..
/-
**neg_one_pow_char_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_pow_char_pow : (-1 : R) ^ p ^ n = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `neg_one_pow_expChar_pow`：neg_one_pow_expChar_pow : (-1 : R) ^ p ^ n = -1
-/
lemma neg_one_pow_char_pow : (-1 : R) ^ p ^ n = -1 := neg_one_pow_expChar_pow ..
/-
**sub_pow_eq_mul_pow_sub_pow_div_char_of_commute** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_pow_eq_mul_pow_sub_pow_div_char_of_commute (h : Commute x y) : (x - y)
 ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p)
参数：h : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute`：sub_pow_eq_mul_pow_su
b_pow_div_expChar_of_commute (h : Commute x y) : (x - y) ^ n = (x - y) ^ (n % p)
 * (x ^ p - y ^ p) ^ (n / p)
-/
lemma sub_pow_eq_mul_pow_sub_pow_div_char_of_commute (h : Commute x y) :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) :=
  sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute _ _ h

end CharP
end Ring

section CommRing
variable [CommRing R] (x y : R) (n : ℕ) {p : ℕ}

section ExpChar
variable [hR : ExpChar R p]

/-
**sub_pow_expChar** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_pow_expChar : (x - y) ^ p = x ^ p - y ^ p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sub_pow_expChar_of_commute`：sub_pow_expChar_of_commute (h : Commute x y)
 : (x - y) ^ p = x ^ p - y ^ p
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma sub_pow_expChar : (x - y) ^ p = x ^ p - y ^ p := sub_pow_expChar_of_commute _ <| .all ..
/-
**sub_pow_expChar_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_pow_expChar_pow : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sub_pow_expChar_pow_of_commute`：sub_pow_expChar_pow_of_commute (h : Comm
ute x y) : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma sub_pow_expChar_pow : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n :=
  sub_pow_expChar_pow_of_commute _ _ <| .all ..
/-
**sub_pow_eq_mul_pow_sub_pow_div_expChar** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_pow_eq_mul_pow_sub_pow_div_expChar : (x - y) ^ n = (x - y) ^ (n % p) *
 (x ^ p - y ^ p) ^ (n / p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute`：sub_pow_eq_mul_pow_su
b_pow_div_expChar_of_commute (h : Commute x y) : (x - y) ^ n = (x - y) ^ (n % p)
 * (x ^ p - y ^ p) ^ (n / p)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma sub_pow_eq_mul_pow_sub_pow_div_expChar :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) :=
  sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute _ _ <| .all ..

end ExpChar

section CharP
variable [hp : Fact p.Prime] [CharP R p]

/-
**sub_pow_char** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_pow_char : (x - y) ^ p = x ^ p - y ^ p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sub_pow_expChar`：sub_pow_expChar : (x - y) ^ p = x ^ p - y ^ p
-/
lemma sub_pow_char : (x - y) ^ p = x ^ p - y ^ p := sub_pow_expChar ..
/-
**sub_pow_char_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_pow_char_pow : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sub_pow_expChar_pow`：sub_pow_expChar_pow : (x - y) ^ p ^ n = x ^ p ^ n -
 y ^ p ^ n
-/
lemma sub_pow_char_pow : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := sub_pow_expChar_pow ..
/-
**sub_pow_eq_mul_pow_sub_pow_div_char** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_pow_eq_mul_pow_sub_pow_div_char : (x - y) ^ n = (x - y) ^ (n % p) * (x
 ^ p - y ^ p) ^ (n / p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sub_pow_eq_mul_pow_sub_pow_div_expChar`：sub_pow_eq_mul_pow_sub_pow_div_e
xpChar : (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p)
-/
lemma sub_pow_eq_mul_pow_sub_pow_div_char :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) :=
  sub_pow_eq_mul_pow_sub_pow_div_expChar ..

end CharP

/-
**Nat.Prime.dvd_add_pow_sub_pow_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.Prime.dvd_add_pow_sub_pow_of_dvd (hpri : p.Prime) {r : R} (h₁ : r ∣ x 
^ p) (h₂ : r ∣ p * x) : r ∣ (x + y) ^ p - y ^ p
参数：hpri : p.Prime；h₁ : r ∣ x ^ p；h₂ : r ∣ p * x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_pow_prime_eq`：add_pow_prime_eq : (x + y) ^ p = x ^ p + y ^ p + p * x
 * y * ∑ k in Ioo 0 p, x ^ (k - 1) * y ^ (p - k - 1) * ↑(p.choose k / p)
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
lemma Nat.Prime.dvd_add_pow_sub_pow_of_dvd (hpri : p.Prime) {r : R} (h₁ : r ∣ x ^ p)
    (h₂ : r ∣ p * x) : r ∣ (x + y) ^ p - y ^ p := by
  rw [add_pow_prime_eq hpri, add_right_comm, add_assoc, add_sub_assoc, add_sub_cancel_right]
  exact dvd_add h₁ (h₂.trans <| (dvd_mul_right ..).trans <| dvd_mul_right ..)

end CommRing


namespace CharP

section

variable (R) [NonAssocRing R]

/-- The characteristic of a finite ring cannot be zero. -/
/-
**CharP.char_ne_zero_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `CharP`。
形式化陈述：char_ne_zero_of_finite (p : Nat) [CharP R p] [Finite R] : p != 0
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.charP_to_charZero`：charP_to_charZero [CharP R 0] : CharZero R
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `not_injective_infinite_finite`：not_injective_infinite_finite {α β} [Infi
nite α] [Finite β] (f : α -> β) : ¬Injective f
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The characteristic of a finite ring cannot be zero.
-/
theorem char_ne_zero_of_finite (p : ℕ) [CharP R p] [Finite R] : p ≠ 0 := by
  rintro rfl
  have : CharZero R := charP_to_charZero R
  exact absurd Nat.cast_injective (not_injective_infinite_finite ((↑) : ℕ → R))
/-
**CharP.ringChar_ne_zero_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `CharP`。
形式化陈述：ringChar_ne_zero_of_finite [Finite R] : ringChar R != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.char_ne_zero_of_finite`：char_ne_zero_of_finite (p : Nat) [CharP R 
p] [Finite R] : p != 0
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
-/
theorem ringChar_ne_zero_of_finite [Finite R] : ringChar R ≠ 0 :=
  char_ne_zero_of_finite R (ringChar R)

end

section Ring

variable (R) [Ring R] [NoZeroDivisors R] [Nontrivial R] [Finite R]

/-
**CharP.char_is_prime** 是 Mathlib 中的一个定理，位于命名空间 `CharP`。
形式化陈述：char_is_prime (p : Nat) [CharP R p] : p.Prime
参数：p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用定理 `CharP.char_ne_zero_of_finite`：char_ne_zero_of_finite (p : Nat) [CharP R 
p] [Finite R] : p != 0
-/
theorem char_is_prime (p : ℕ) [CharP R p] : p.Prime :=
  Or.resolve_right (char_is_prime_or_zero R p) (char_ne_zero_of_finite R p)
/-
**CharP.prime_ringChar** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：prime_ringChar : Nat.Prime (ringChar R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.char_prime_of_ne_zero`：char_prime_of_ne_zero {p : Nat} [CharP R p]
 (hp : p != 0) : p.Prime
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用定理 `CharP.ringChar_ne_zero_of_finite`：ringChar_ne_zero_of_finite [Finite R] 
: ringChar R != 0
-/
lemma prime_ringChar : Nat.Prime (ringChar R) := by
  apply CharP.char_prime_of_ne_zero R
  exact CharP.ringChar_ne_zero_of_finite R

end Ring
end CharP

/-
Preliminary definitions and results for the Frobenius map.
Necessary here for simple results about sums of `p`-powers that are used in files forbidding
to import algebra-related definitions.
-/
section Frobenius

variable (R : Type*) [CommSemiring R]
variable (p n : ℕ) [ExpChar R p]

/-- The Frobenius map `x ↦ x ^ p`. -/
/-
**frobenius** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：frobenius : R ->+* R where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `add_pow_expChar`：add_pow_expChar : (x + y) ^ p = x ^ p + y ^ p

--- 原说明 ---
The Frobenius map `x ↦ x ^ p`.
-/
def frobenius : R →+* R where
  __ := powMonoidHom p
  map_zero' := zero_pow (expChar_pos R p).ne'
  map_add' _ _ := add_pow_expChar ..

/-- The iterated Frobenius map `x ↦ x ^ p ^ n`. -/
/-
**iterateFrobenius** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iterateFrobenius : R ->+* R where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `add_pow_expChar_pow`：add_pow_expChar_pow : (x + y) ^ p ^ n = x ^ p ^ n +
 y ^ p ^ n

--- 原说明 ---
The iterated Frobenius map `x ↦ x ^ p ^ n`.
-/
def iterateFrobenius : R →+* R where
  __ := powMonoidHom (p ^ n)
  map_zero' := zero_pow (expChar_pow_pos R p n).ne'
  map_add' _ _ := add_pow_expChar_pow ..

variable {R}
/-
**list_sum_pow_char** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：list_sum_pow_char (l : List R) : l.sum ^ p = (l.map (· ^ p : R -> R)).sum
参数：l : List R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
lemma list_sum_pow_char (l : List R) : l.sum ^ p = (l.map (· ^ p : R → R)).sum :=
  map_list_sum (frobenius R p) _
/-
**multiset_sum_pow_char** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：multiset_sum_pow_char (s : Multiset R) : s.sum ^ p = (s.map (· ^ p : R -> 
R)).sum
参数：s : Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
lemma multiset_sum_pow_char (s : Multiset R) : s.sum ^ p = (s.map (· ^ p : R → R)).sum :=
  map_multiset_sum (frobenius R p) _
/-
**sum_pow_char** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sum_pow_char {ι : Type*} (s : Finset ι) (f : ι -> R) : (∑ i in s, f i) ^ p
 = ∑ i in s, f i ^ p
参数：s : Finset ι；f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
lemma sum_pow_char {ι : Type*} (s : Finset ι) (f : ι → R) : (∑ i ∈ s, f i) ^ p = ∑ i ∈ s, f i ^ p :=
  map_sum (frobenius R p) _ _
/-
**list_sum_pow_char_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：list_sum_pow_char_pow (l : List R) : l.sum ^ p ^ n = (l.map (· ^ p ^ n : R
 -> R)).sum
参数：l : List R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
lemma list_sum_pow_char_pow (l : List R) : l.sum ^ p ^ n = (l.map (· ^ p ^ n : R → R)).sum :=
  map_list_sum (iterateFrobenius R p n) _
/-
**multiset_sum_pow_char_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：multiset_sum_pow_char_pow (s : Multiset R) : s.sum ^ p ^ n = (s.map (· ^ p
 ^ n : R -> R)).sum
参数：s : Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
lemma multiset_sum_pow_char_pow (s : Multiset R) :
    s.sum ^ p ^ n = (s.map (· ^ p ^ n : R → R)).sum :=
  map_multiset_sum (iterateFrobenius R p n) _
/-
**sum_pow_char_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sum_pow_char_pow {ι : Type*} (s : Finset ι) (f : ι -> R) : (∑ i in s, f i)
 ^ p ^ n = ∑ i in s, f i ^ p ^ n
参数：s : Finset ι；f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
lemma sum_pow_char_pow {ι : Type*} (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ p ^ n = ∑ i ∈ s, f i ^ p ^ n := map_sum (iterateFrobenius R p n) _ _

end Frobenius

