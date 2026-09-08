/-
Copyright (c) 2024 Antoine Chambert-Loir & María-Inés de Frutos—Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos—Fernández, Yu Shao, Beibei Xiong, Weijie Jiang,
Yi Yuan
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Choose.Multinomial

/-! # Bell numbers for multisets

For `n : ℕ`, the `n`th Bell number is the number of partitions of a set of cardinality `n`.
Here, we define a refinement of these numbers, that count, for any `m : Multiset ℕ`,
the number of partitions of a set of cardinality `m.sum` whose parts have cardinalities
given by `m`.

The definition presents it as a natural number.

* `Multiset.bell`: number of partitions of a set whose parts have cardinalities a given multiset

* `Nat.uniformBell m n` : short name for `Multiset.bell (replicate m n)`

* `Multiset.bell_mul_eq` shows that
  `m.bell * (m.map (fun j ↦ j !)).prod * Π j ∈ (m.toFinset.erase 0), (m.count j)! = m.sum !`

* `Nat.uniformBell_mul_eq`  shows that
  `uniformBell m n * n ! ^ m * m ! = (m * n) !`

* `Nat.uniformBell_succ_left` computes `Nat.uniformBell (m + 1) n` from `Nat.uniformBell m n`

* `Nat.bell n`: the `n`th standard Bell number,
  which counts the number of partitions of a set of cardinality `n`

* `Nat.bell_succ n` shows that
  `Nat.bell (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose n k * Nat.bell (n - k)`

## TODO

Prove that it actually counts the number of partitions as indicated.
(When `m` contains `0`, the result requires to admit repetitions of the empty set as a part.)

-/

@[expose] public section

open Multiset Nat

namespace Multiset

/-- Number of partitions of a set of cardinality `m.sum`
whose parts have cardinalities given by `m` -/
/-
**Multiset.bell** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：bell (m : Multiset Nat) : Nat
参数：m : Multiset Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Number of partitions of a set of cardinality `m.sum`
whose parts have cardinalities given by `m`
-/
def bell (m : Multiset ℕ) : ℕ :=
  Nat.multinomial m.toFinset (fun k ↦ k * m.count k) *
    ∏ k ∈ m.toFinset.erase 0, ∏ j ∈ .range (m.count k), (j * k + k - 1).choose (k - 1)

@[simp]
/-
**Multiset.bell_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bell_zero : bell 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bell_zero : bell 0 = 1 := rfl
/-
**Multiset.bell_mul_eq_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bell_mul_eq_lemma {x : ℕ} (hx : x ≠ 0) :
    ∀ c, x ! ^ c * c ! * ∏ j ∈ Finset.range c, (j * x + x - 1).choose (x - 1) = (x * c)!
  | 0 => by simp
  | c + 1 => calc
      x ! ^ (c + 1) * (c + 1)! * ∏ j ∈ Finset.range (c + 1), (j * x + x - 1).choose (x - 1)
        = x ! * (c + 1) * x ! ^ c * c ! *
            ∏ j ∈ Finset.range (c + 1), (j * x + x - 1).choose (x - 1) := by
        rw [factorial_succ, pow_succ]; ring
      _ = (x ! ^ c * c ! * ∏ j ∈ Finset.range c, (j * x + x - 1).choose (x - 1)) *
            (c * x + x - 1).choose (x - 1) * x ! * (c + 1) := by
        rw [Finset.prod_range_succ]; ring
      _ = (c + 1) * (c * x + x - 1).choose (x - 1) * (x * c)! * x ! := by
        rw [bell_mul_eq_lemma hx]; ring
      _ = (x * (c + 1))! := by
        rw [← Nat.choose_mul_add hx, mul_comm c x, Nat.add_choose_mul_factorial_mul_factorial]
        ring_nf
/-
**Multiset.bell_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bell_mul_eq (m : Multiset Nat) : m.bell * (m.map (fun j => j !)).prod * ∏ 
j in (m.toFinset.erase 0), (m.count j)! = m.sum !
参数：m : Multiset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_right_inj`：∀ {a b c : ℕ}, a ≠ 0 → (a * b = a * c ↔ b = c)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.multinomial_spec`：multinomial_spec : (∏ i in s, (f i)!) * multinomia
l s f = (∑ i in s, f i)!
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.prod_multiset_map_count`：prod_multiset_map_count [DecidableEq ι] 
(s : Multiset ι) {M : Type*} [CommMonoid M] (f : ι -> M) : (s.map f).prod = ∏ m 
in s.toFinset, f m ^…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.Bell.0.Multiset.bell_mul_eq_l
emma`：∀ {x : ℕ},   x ≠ 0 →     ∀ (c : ℕ), x.factorial ^ c * c.factorial * ∏ j ∈ 
Finset.range c, (j * x + x - 1).choose (x - 1) = (x * c).factorial
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.prod_erase_mul`：prod_erase_mul [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (∏ x in s.erase a, f x) * f a = ∏ x in s, f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `Finset.sum_multiset_count`：∀ {M : Type u_4} [inst : AddCommMonoid M] [in
st_1 : DecidableEq M] (s : Multiset M),   s.sum = ∑ m ∈ s.toFinset, Multiset.cou
nt m s • m
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bell_mul_eq (m : Multiset ℕ) :
    m.bell * (m.map (fun j ↦ j !)).prod * ∏ j ∈ (m.toFinset.erase 0), (m.count j)! = m.sum ! := by
  unfold bell
  rw [← Nat.mul_right_inj (a := ∏ i ∈ m.toFinset, (i * count i m)!) (by positivity)]
  simp only [← mul_assoc, Nat.multinomial_spec]
  rw [mul_assoc, mul_assoc, mul_comm]
  congr
  · rw [mul_comm, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_multiset_map_count]
    suffices this : _ by
      by_cases hm : 0 ∈ m.toFinset
      · rw [← Finset.prod_erase_mul _ _ hm]
        rw [← Finset.prod_erase_mul _ _ hm]
        simp only [factorial_zero, one_pow, mul_one, zero_mul]
        exact this
      · nth_rewrite 1 [← Finset.erase_eq_of_notMem hm]
        nth_rewrite 3 [← Finset.erase_eq_of_notMem hm]
        exact this
    rw [← Finset.prod_mul_distrib]
    congr! 1 with x hx
    rw [← mul_assoc, bell_mul_eq_lemma]
    simp only [Finset.mem_erase, ne_eq, mem_toFinset] at hx
    simp only [ne_eq, hx.1, not_false_eq_true]
  · rw [Finset.sum_multiset_count]
    simp only [smul_eq_mul, mul_comm]
/-
**Multiset.bell_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bell_eq (m : Multiset Nat) : m.bell = m.sum ! / ((m.map fun j => j !).prod
 * ∏ j in m.toFinset.erase 0, (m.count j)!)
参数：m : Multiset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_left_inj`：∀ {a b c : ℕ}, a ≠ 0 → (b * a = c * a ↔ b = c)
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
· 使用定理 `Multiset.bell_mul_eq`：bell_mul_eq (m : Multiset Nat) : m.bell * (m.map (
fun j => j !)).prod * ∏ j in (m.toFinset.erase 0), (m.count j)! = m.sum !
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.dvd_mul_left`：∀ (a b : ℕ), a ∣ b * a
-/
theorem bell_eq (m : Multiset ℕ) :
    m.bell = m.sum ! / ((m.map fun j ↦ j !).prod * ∏ j ∈ m.toFinset.erase 0, (m.count j)!) := by
  rw [← Nat.mul_left_inj, Nat.div_mul_cancel _]
  · rw [← mul_assoc]
    exact bell_mul_eq m
  · rw [← bell_mul_eq, mul_assoc]
    apply Nat.dvd_mul_left
  · rw [← Nat.pos_iff_ne_zero]
    exact Nat.mul_pos (by simp [Nat.factorial_pos]) (by positivity)
/-
**Multiset.bell_cons_mul_count** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bell_cons_mul_count (m : Multiset ℕ) {a : ℕ} (ha : a ≠ 0) :
    (a ::ₘ m).bell * (a ::ₘ m).count a = (m.sum + a).choose a * m.bell := by
  let rest := ∏ j ∈ (m.toFinset.erase 0).erase a, (m.count j)!
  have hrest : rest = ∏ j ∈ ((a ::ₘ m).toFinset.erase 0).erase a, ((a ::ₘ m).count j)! := by
    unfold rest
    congr! 1 with j hj
    · grind [Multiset.toFinset_cons]
    · simp [Finset.mem_erase.mp hj]
  let c := (m.map (· !)).prod * (m.count a)! * rest
  have hm0 : m.bell * c = m.sum ! := by
    have hsplit : (m.count a)! * rest = ∏ j ∈ m.toFinset.erase 0, (m.count j)! := by
      by_cases hmem : a ∈ m.toFinset.erase 0
      · rw [← Finset.mul_prod_erase _ _ hmem]
      · have hcount : m.count a = 0 := by grind [Multiset.count_eq_zero_of_notMem]
        simp [rest, Finset.erase_eq_of_notMem hmem, hcount]
    simpa [c, hsplit, mul_assoc] using Multiset.bell_mul_eq m
  have hm : m.sum ! * a ! = m.bell * a ! * c := by grind
  have hc : 0 < a ! * c := Nat.mul_pos (by positivity) <|
    Nat.mul_pos (by simp [Nat.factorial_pos]) (by positivity)
  apply Nat.eq_of_mul_eq_mul_right hc
  calc
    _ = (m.sum + a)! := by
      have hq := Multiset.bell_mul_eq (a ::ₘ m)
      rw [← Finset.mul_prod_erase _ _ (a := a) (by simp [*]), ← hrest] at hq
      simpa [c, Nat.factorial_succ, add_comm, mul_assoc, mul_left_comm] using hq
    _ = ((m.sum + a).choose a * m.bell) * (a ! * c) := by
      simp [← Nat.add_choose_mul_factorial_mul_factorial, mul_assoc, hm]

end Multiset

namespace Nat

/-- Number of possibilities of dividing a set with `m * n` elements into `m` groups
of `n`-element subsets. -/
/-
**Nat.uniformBell** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：uniformBell (m n : Nat) : Nat
参数：m n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Number of possibilities of dividing a set with `m * n` elements into `m` groups
of `n`-element subsets.
-/
def uniformBell (m n : ℕ) : ℕ := bell (replicate m n)
/-
**Nat.uniformBell_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：uniformBell_eq (m n : Nat) : m.uniformBell n = ∏ p in (Finset.range m), ch
oose (p * n + n - 1) (n - 1)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.toFinset_replicate`：toFinset_replicate (n : Nat) (a : α) : (rep
licate n a).toFinset = if n = 0 then ∅ else {a}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.multinomial_empty`：∀ {α : Type u_1} (f : α → ℕ), Nat.multinomial ∅ f
 = 1
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.multinomial_singleton`：∀ {α : Type u_1} (a : α) (f : α → ℕ), Nat.mul
tinomial {a} f = 1
· 使用定理 `Finset.erase_singleton`：erase_singleton (a : α) : ({a} : Finset α).erase
 a = ∅
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Multiset.count_replicate`：count_replicate (a b : α) (n : Nat) : count a 
(replicate n b) = if b = a then n else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
（共 32 条，此处仅展示前 30 条）
-/
theorem uniformBell_eq (m n : ℕ) : m.uniformBell n =
    ∏ p ∈ (Finset.range m), choose (p * n + n - 1) (n - 1) := by
  unfold uniformBell bell
  rw [toFinset_replicate]
  split_ifs with hm
  · simp [hm]
  · by_cases hn : n = 0
    · simp [hn]
    · rw [show ({n} : Finset ℕ).erase 0 = {n} by simp [Ne.symm hn]]
      simp [count_replicate]
/-
**Nat.uniformBell_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：uniformBell_zero_left (n : Nat) : uniformBell 0 n = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.uniformBell_eq`：uniformBell_eq (m n : Nat) : m.uniformBell n = ∏ p i
n (Finset.range m), choose (p * n + n - 1) (n - 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniformBell_zero_left (n : ℕ) : uniformBell 0 n = 1 := by
  simp [uniformBell_eq]
/-
**Nat.uniformBell_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：uniformBell_zero_right (m : Nat) : uniformBell m 0 = 1
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.uniformBell_eq`：uniformBell_eq (m n : Nat) : m.uniformBell n = ∏ p i
n (Finset.range m), choose (p * n + n - 1) (n - 1)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniformBell_zero_right (m : ℕ) : uniformBell m 0 = 1 := by
  simp [uniformBell_eq]
/-
**Nat.uniformBell_succ_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：uniformBell_succ_left (m n : Nat) : uniformBell (m + 1) n = choose (m * n 
+ n - 1) (n - 1) * uniformBell m n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.uniformBell_eq`：uniformBell_eq (m n : Nat) : m.uniformBell n = ∏ p i
n (Finset.range m), choose (p * n + n - 1) (n - 1)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniformBell_succ_left (m n : ℕ) :
    uniformBell (m + 1) n = choose (m * n + n - 1) (n - 1) * uniformBell m n := by
  simp only [uniformBell_eq, Finset.prod_range_succ, mul_comm]
/-
**Nat.uniformBell_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：uniformBell_one_left (n : Nat) : uniformBell 1 n = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.uniformBell_eq`：uniformBell_eq (m n : Nat) : m.uniformBell n = ∏ p i
n (Finset.range m), choose (p * n + n - 1) (n - 1)
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniformBell_one_left (n : ℕ) : uniformBell 1 n = 1 := by
  simp only [uniformBell_eq, Finset.range_one, Finset.prod_singleton, zero_mul,
    zero_add, choose_self]
/-
**Nat.uniformBell_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：uniformBell_one_right (m : Nat) : uniformBell m 1 = 1
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.uniformBell_eq`：uniformBell_eq (m n : Nat) : m.uniformBell n = ∏ p i
n (Finset.range m), choose (p * n + n - 1) (n - 1)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniformBell_one_right (m : ℕ) : uniformBell m 1 = 1 := by
  simp only [uniformBell_eq, mul_one, add_tsub_cancel_right, le_refl,
    tsub_eq_zero_of_le, choose_zero_right, Finset.prod_const_one]
/-
**Nat.uniformBell_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：uniformBell_mul_eq (m : Nat) {n : Nat} (hn : n != 0) : uniformBell m n * n
 ! ^ m * m ! = (m * n)!
参数：m : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_replicate`：map_replicate (f : α -> β) (k : Nat) (a : α) : (
replicate k a).map f = replicate k (f a)
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Multiset.toFinset_replicate`：toFinset_replicate (n : Nat) (a : α) : (rep
licate n a).toFinset = if n = 0 then ∅ else {a}
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.factorial_zero`：Nat.factorial 0 = 1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Multiset.count_replicate_self`：count_replicate_self (a : α) (n : Nat) : 
count a (replicate n a) = n
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `Multiset.bell_mul_eq`：bell_mul_eq (m : Multiset Nat) : m.bell * (m.map (
fun j => j !)).prod * ∏ j in (m.toFinset.erase 0), (m.count j)! = m.sum !
-/
theorem uniformBell_mul_eq (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    uniformBell m n * n ! ^ m * m ! = (m * n)! := by
  convert! bell_mul_eq (replicate m n)
  · simp only [map_replicate, prod_replicate]
  · simp only [toFinset_replicate]
    split_ifs with hm
    · rw [hm, factorial_zero, eq_comm]
      rw [show (∅ : Finset ℕ).erase 0 = ∅ from rfl, Finset.prod_empty]
    · rw [show ({n} : Finset ℕ).erase 0 = {n} by simp [Ne.symm hn]]
      simp only [Finset.prod_singleton, count_replicate_self]
  · simp
/-
**Nat.uniformBell_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：uniformBell_eq_div (m : Nat) {n : Nat} (hn : n != 0) : uniformBell m n = (
m * n)! / (n ! ^ m * m !)
参数：m : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.div_eq_of_eq_mul_left`：∀ {n m k : ℕ}, 0 < n → m = k * n → m / n = k
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.uniformBell_mul_eq`：uniformBell_mul_eq (m : Nat) {n : Nat} (hn : n !
= 0) : uniformBell m n * n ! ^ m * m ! = (m * n)!
-/
theorem uniformBell_eq_div (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    uniformBell m n = (m * n)! / (n ! ^ m * m !) := by
  rw [eq_comm]
  apply Nat.div_eq_of_eq_mul_left
  · exact Nat.mul_pos (Nat.pow_pos n.factorial_pos) m.factorial_pos
  · rw [← mul_assoc, ← uniformBell_mul_eq _ hn]

/--
The `n`th standard Bell number,
which counts the number of partitions of a set of cardinality `n`.
-/
/-
**Nat.bell** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th standard Bell number,
which counts the number of partitions of a set of cardinality `n`.
-/
protected def bell : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ i ≤ n, choose n i * (n - i).bell
/-
**Nat.bell_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bell_succ (n : Nat) : (n + 1).bell = ∑ i <= n, choose n i * (n - i).bell
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.bell.eq_2`：∀ (n : ℕ), n.succ.bell = ∑ i ≤ n, n.choose i * (n - i).be
ll
-/
theorem bell_succ (n : ℕ) :
    (n + 1).bell = ∑ i ≤ n, choose n i * (n - i).bell := by
  rw [Nat.bell]
/-
**Nat.bell_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bell_succ' (n : Nat) : (n + 1).bell = ∑ ij in Finset.antidiagonal n, choos
e n ij.1 * ij.2.bell
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.bell_succ`：bell_succ (n : Nat) : (n + 1).bell = ∑ i <= n, choose n i
 * (n - i).bell
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.range_succ_eq_Iic`：range_succ_eq_Iic (n : Nat) : range (n + 1) = Iic
 n
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`：∀ {M : Type u_3} [inst : 
AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidi
agonal n, f ij.1 ij.2 = ∑ k ∈ Finse…
-/
theorem bell_succ' (n : ℕ) :
    (n + 1).bell = ∑ ij ∈ Finset.antidiagonal n, choose n ij.1 * ij.2.bell := by
  rw [Nat.bell_succ,
    ← Nat.range_succ_eq_Iic,
    ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y ↦ choose n x * y.bell) n]

@[simp]
/-
**Nat.bell_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bell_zero : Nat.bell 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.bell.eq_1`：Nat.bell 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bell_zero : Nat.bell 0 = 1 := by
  simp [Nat.bell]

@[simp]
/-
**Nat.bell_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bell_one : Nat.bell 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.bell.eq_2`：∀ (n : ℕ), n.succ.bell = ∑ i ≤ n, n.choose i * (n - i).be
ll
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `Nat.bell_zero`：bell_zero : Nat.bell 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bell_one : Nat.bell 1 = 1 := by
  have : Finset.Iic 0 = {0} := Eq.symm (Finset.eq_of_veq rfl)
  simp [Nat.bell, this]

@[simp]
/-
**Nat.bell_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bell_two : Nat.bell 2 = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.bell.eq_2`：∀ (n : ℕ), n.succ.bell = ∑ i ≤ n, n.choose i * (n - i).be
ll
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.choose_succ_self_right`：∀ (n : ℕ), (n + 1).choose n = n + 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Nat.bell_one`：bell_one : Nat.bell 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Nat.bell_zero`：bell_zero : Nat.bell 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bell_two : Nat.bell 2 = 2 := by
  have : Finset.Iic 1 = {0, 1} := Finset.eq_of_veq rfl
  simp [Nat.bell, this]
/-
**Nat.bell_eq_sum_erase** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bell_eq_sum_erase {n : Nat} (p : (n + 1).Partition) : p.parts.bell = ∑ a i
n p.parts.toFinset, n.choose (a - 1) * (p.parts.erase a).bell
参数：p : (n + 1).Partition。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_of_mul_eq_mul_left`：∀ {m k n : ℕ}, 0 < n → n * m = n * k → m = k
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `mul_eq_mul_right_iff`：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀] [IsRigh
tCancelMulZero M₀] {a b c : M₀}, a * c = b * c ↔ a = b ∨ c = 0
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.Partition.parts_sum`：∀ {n : ℕ} (self : n.Partition), self.parts.sum 
= n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_multiset_count`：∀ {M : Type u_4} [inst : AddCommMonoid M] [in
st_1 : DecidableEq M] (s : Multiset M),   s.sum = ∑ m ∈ s.toFinset, Multiset.cou
nt m s • m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_dedup`：mem_dedup {a : α} {s : Multiset α} : a in dedup s ↔ 
a in s
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
-/
theorem bell_eq_sum_erase {n : ℕ} (p : (n + 1).Partition) :
    p.parts.bell = ∑ a ∈ p.parts.toFinset, n.choose (a - 1) * (p.parts.erase a).bell := by
  apply Nat.eq_of_mul_eq_mul_left n.succ_pos
  calc
  _ = (∑ a ∈ p.parts.toFinset, p.parts.count a * a) * p.parts.bell := by
    rw [succ_eq_add_one, mul_eq_mul_right_iff]
    left
    simpa [smul_eq_mul, p.parts_sum] using Finset.sum_multiset_count p.parts
  _ = ∑ a ∈ p.parts.toFinset, a * (p.parts.count a * p.parts.bell) := by grind [Finset.sum_mul]
  _ = ∑ a ∈ p.parts.toFinset, (n + 1) * (n.choose (a - 1) * (p.parts.erase a).bell) := by
    congr! 1 with a ha
    have ha0 : a ≠ 0 := by grind
    have hsum : (p.parts.erase a).sum + a = n + 1 := by
      simpa [p.parts_sum, add_comm] using congrArg Multiset.sum (cons_erase (mem_dedup.mp ha))
    grind [Nat.add_one_mul_choose_eq, cons_erase, bell_cons_mul_count]
  _ = _ := by rw [Finset.mul_sum]
/-
**Nat.sigmaPartitionWithPartEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def sigmaPartitionWithPartEquiv (n : ℕ) :
    (Σ i : Fin n.succ, {p : (n + 1).Partition // (i + 1 : ℕ) ∈ p.parts}) ≃
    Σ p : (n + 1).Partition, {a : ℕ // a ∈ p.parts.toFinset} where
  toFun x := ⟨x.2.1, ⟨(x.1 + 1 : ℕ), by simpa using x.2.2⟩⟩
  invFun x := ⟨⟨x.2.1 - 1, by grind⟩, ⟨x.1, by grind⟩⟩
  left_inv x := by simp
  right_inv x := by grind

/-- `Nat.bell n` is equal to the sum of `Multiset.bell m` over all multisets `m : Multiset ℕ` such
that `m.sum = n`. -/
/-
**Nat.bell_eq_sum_partition** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bell_eq_sum_partition (n : Nat) : n.bell = ∑ p : n.Partition, p.parts.bell
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.bell_zero`：bell_zero : Nat.bell 0 = 1
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.Partition.partition_zero_parts`：∀ (p : Nat.Partition 0), p.parts = 0
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.bell_succ`：bell_succ (n : Nat) : (n + 1).bell = ∑ i <= n, choose n i
 * (n - i).bell
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `Nat.range_succ_eq_Iic`：range_succ_eq_Iic (n : Nat) : range (n + 1) = Iic
 n
· 使用定理 `Finset.sum_range`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f :
 ℕ → M), ∑ i ∈ Finset.range n, f i = ∑ i, f ↑i
· 使用定理 `Fintype.sum_sigma'`：∀ {ι : Type u_9} {α : ι → Type u_7} {M : Type u_8} [
inst : Fintype ι] [inst_1 : (i : ι) → Fintype (α i)]   [inst_2 : AddCommMonoid M
] (f : (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
`Nat.bell n` is equal to the sum of `Multiset.bell m` over all multisets `m : Mu
ltiset ℕ` such
that `m.sum = n`.
-/
theorem bell_eq_sum_partition (n : ℕ) : n.bell = ∑ p : n.Partition, p.parts.bell := by
  refine Nat.strong_induction_on n ?_
  rintro (_ | n) ih
  · simp
  rw [Nat.bell_succ]
  calc
  _ = ∑ i ≤ n, ∑ q : (n - i).Partition, n.choose i * q.parts.bell := by
    congr! with i
    simp [ih (n - i) _, Finset.mul_sum]
  _ = ∑ i ≤ n, ∑ p : {p : (n + 1).Partition // (i + 1 : ℕ) ∈ p.parts},
      choose n i * (p.1.parts.erase (i + 1)).bell := by
    congr! with i hi
    have : i ≤ n := Finset.mem_Iic.mp hi
    have h1 : 1 ≤ (i + 1 : ℕ) := by lia
    have h2 : (i + 1 : ℕ) ≤ n + 1 := by lia
    have hsub : n + 1 - (i + 1 : ℕ) = n - i := by lia
    exact hsub ▸ (Fintype.sum_equiv (Partition.partitionWithPartEquiv h1 h2) _ _ (fun _ ↦ rfl)).symm
  _ = ∑ x : Σ p : (n + 1).Partition, p.parts.toFinset,
      choose n (x.2.1 - 1) * (x.1.parts.erase x.2.1).bell := by
    rw [← Nat.range_succ_eq_Iic, Finset.sum_range, ← Fintype.sum_sigma']
    refine Fintype.sum_equiv (sigmaPartitionWithPartEquiv n) _ _ ?_
    simp [sigmaPartitionWithPartEquiv]
  _ = ∑ p : (n + 1).Partition, ∑ a : p.parts.toFinset, choose n (a - 1) * (p.parts.erase a).bell :=
    Fintype.sum_sigma' fun (p : (n + 1).Partition) (a : p.parts.toFinset) ↦
      choose n (a - 1) * (p.parts.erase a.1).bell
  _ = _ := by
    congr! with p
    rw [bell_eq_sum_erase p]
    exact p.parts.toFinset.sum_coe_sort (fun a ↦ choose n (a - 1) * (p.parts.erase a).bell)

end Nat

