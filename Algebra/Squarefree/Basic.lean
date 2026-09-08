/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Squarefree elements of monoids

An element of a monoid is squarefree when it is not divisible by any squares
except the squares of units.

Results about squarefree natural numbers are proved in `Data.Nat.Squarefree`.

## Main Definitions
- `Squarefree r` indicates that `r` is only divisible by `x * x` if `x` is a unit.

## Main Results
- `multiplicity.squarefree_iff_emultiplicity_le_one`: `x` is `Squarefree` iff for every `y`, either
  `emultiplicity y x ≤ 1` or `IsUnit y`.
- `UniqueFactorizationMonoid.squarefree_iff_nodup_factors`: A nonzero element `x` of a unique
  factorization monoid is squarefree iff `factors x` has no duplicate factors.

## Tags
squarefree, multiplicity

-/

@[expose] public section


variable {R : Type*}

/-- An element of a monoid is squarefree if the only squares that
  divide it are the squares of units. -/
/-
**Squarefree** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Squarefree [Monoid R] (r : R) : Prop
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of a monoid is squarefree if the only squares that
  divide it are the squares of units.
-/
def Squarefree [Monoid R] (r : R) : Prop :=
  ∀ x : R, x * x ∣ r → IsUnit x
/-
**IsRelPrime.of_squarefree_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_squarefree_mul [CommMonoid R] {m n : R} (h : Squarefree (m *
 n)) : IsRelPrime m n
参数：h : Squarefree (m * n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
-/
theorem IsRelPrime.of_squarefree_mul [CommMonoid R] {m n : R} (h : Squarefree (m * n)) :
    IsRelPrime m n := fun c hca hcb ↦ h c (mul_dvd_mul hca hcb)

@[simp]
/-
**IsUnit.squarefree** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.squarefree [CommMonoid R] {x : R} (h : IsUnit x) : Squarefree x
参数：h : IsUnit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_mul_isUnit_left`：isUnit_of_mul_isUnit_left [Monoid M] [IsDedek
indFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
-/
theorem IsUnit.squarefree [CommMonoid R] {x : R} (h : IsUnit x) : Squarefree x := fun _ hdvd =>
  isUnit_of_mul_isUnit_left (isUnit_of_dvd_unit hdvd h)
/-
**squarefree_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：squarefree_one [CommMonoid R] : Squarefree (1 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.squarefree`：IsUnit.squarefree [CommMonoid R] {x : R} (h : IsUnit 
x) : Squarefree x
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
theorem squarefree_one [CommMonoid R] : Squarefree (1 : R) :=
  isUnit_one.squarefree

@[simp]
/-
**not_squarefree_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_squarefree_zero [MonoidWithZero R] [Nontrivial R] : ¬Squarefree (0 : R
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Squarefree.eq_1`：∀ {R : Type u_1} [inst : Monoid R] (r : R), Squarefree 
r = ∀ (x : R), x * x ∣ r → IsUnit x
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_squarefree_zero [MonoidWithZero R] [Nontrivial R] : ¬Squarefree (0 : R) := by
  rw [Squarefree, not_forall]
  exact ⟨0, by simp⟩
/-
**Squarefree.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R] {m : R} (hm : Squaref
ree (m : R)) : m != 0
参数：hm : Squarefree (m : R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_squarefree_zero`：not_squarefree_zero [MonoidWithZero R] [Nontrivial 
R] : ¬Squarefree (0 : R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R] {m : R} (hm : Squarefree (m : R)) :
    m ≠ 0 := by
  rintro rfl
  exact not_squarefree_zero hm

@[simp]
/-
**Irreducible.squarefree** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irreducible.squarefree [CommMonoid R] {x : R} (h : Irreducible x) : Square
free x
参数：h : Irreducible x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `isUnit_of_mul_isUnit_left`：isUnit_of_mul_isUnit_left [Monoid M] [IsDedek
indFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
-/
theorem Irreducible.squarefree [CommMonoid R] {x : R} (h : Irreducible x) : Squarefree x := by
  rintro y ⟨z, hz⟩
  rw [mul_assoc] at hz
  rcases h.isUnit_or_isUnit hz with (hu | hu)
  · exact hu
  · apply isUnit_of_mul_isUnit_left hu

@[simp]
/-
**Prime.squarefree** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.squarefree [CommMonoidWithZero R] [IsCancelMulZero R] {x : R} (h : P
rime x) : Squarefree x
参数：h : Prime x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.squarefree`：Irreducible.squarefree [CommMonoid R] {x : R} (h
 : Irreducible x) : Squarefree x
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
-/
theorem Prime.squarefree [CommMonoidWithZero R] [IsCancelMulZero R] {x : R} (h : Prime x) :
    Squarefree x :=
  h.irreducible.squarefree
/-
**Squarefree.of_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Squarefree.of_mul_left [Monoid R] {m n : R} (hmn : Squarefree (m * n)) : S
quarefree m
参数：hmn : Squarefree (m * n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
-/
theorem Squarefree.of_mul_left [Monoid R] {m n : R} (hmn : Squarefree (m * n)) : Squarefree m :=
  fun p hp => hmn p (dvd_mul_of_dvd_left hp n)
/-
**Squarefree.of_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Squarefree.of_mul_right [CommMonoid R] {m n : R} (hmn : Squarefree (m * n)
) : Squarefree n
参数：hmn : Squarefree (m * n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
-/
theorem Squarefree.of_mul_right [CommMonoid R] {m n : R} (hmn : Squarefree (m * n)) :
    Squarefree n := fun p hp => hmn p (dvd_mul_of_dvd_right hp m)
/-
**Squarefree.squarefree_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Squarefree.squarefree_of_dvd [Monoid R] {x y : R} (hdvd : x ∣ y) (hsq : Sq
uarefree y) : Squarefree x
参数：hdvd : x ∣ y；hsq : Squarefree y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
-/
theorem Squarefree.squarefree_of_dvd [Monoid R] {x y : R} (hdvd : x ∣ y) (hsq : Squarefree y) :
    Squarefree x := fun _ h => hsq _ (h.trans hdvd)
/-
**Associated.squarefree_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Associated.squarefree_iff [Monoid R] {x y : R} (h : Associated x y) : Squa
refree x ↔ Squarefree y
参数：h : Associated x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用定理 `Associated.dvd'`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associate
d a b → b ∣ a
· 使用定理 `Associated.dvd`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associated
 a b → a ∣ b
-/
theorem Associated.squarefree_iff [Monoid R] {x y : R} (h : Associated x y) :
    Squarefree x ↔ Squarefree y :=
  ⟨fun hx ↦ hx.squarefree_of_dvd h.dvd', fun hy ↦ hy.squarefree_of_dvd h.dvd⟩
/-
**Squarefree.eq_zero_or_one_of_pow_of_not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Squarefree.eq_zero_or_one_of_pow_of_not_isUnit [Monoid R] {x : R} {n : Nat
} (h : Squarefree (x ^ n)) (h' : ¬ IsUnit x) : n = 0 ∨ n = 1
参数：h : Squarefree (x ^ n)；h' : ¬ IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `instReflDvd_mathlib`：∀ {α : Type u_1} [inst : Monoid α], Std.Refl fun x1
 x2 => x1 ∣ x2
-/
theorem Squarefree.eq_zero_or_one_of_pow_of_not_isUnit [Monoid R] {x : R} {n : ℕ}
    (h : Squarefree (x ^ n)) (h' : ¬ IsUnit x) :
    n = 0 ∨ n = 1 := by
  contrapose! h'
  replace h' : 2 ≤ n := by lia
  have : x * x ∣ x ^ n := by rw [← sq]; exact pow_dvd_pow x h'
  exact h.squarefree_of_dvd this x (refl _)
/-
**Squarefree.pow_dvd_of_pow_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Squarefree.pow_dvd_of_pow_dvd [Monoid R] {x y : R} {n : Nat} (hx : Squaref
ree y) (h : x ^ n ∣ y) : x ^ n ∣ x
参数：hx : Squarefree y；h : x ^ n ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.dvd`：dvd (hu : IsUnit u) : u ∣ a
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `Squarefree.eq_zero_or_one_of_pow_of_not_isUnit`：Squarefree.eq_zero_or_on
e_of_pow_of_not_isUnit [Monoid R] {x : R} {n : Nat} (h : Squarefree (x ^ n)) (h'
 : ¬ IsUnit x) : n = 0 ∨ n = 1
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem Squarefree.pow_dvd_of_pow_dvd [Monoid R] {x y : R} {n : ℕ}
    (hx : Squarefree y) (h : x ^ n ∣ y) : x ^ n ∣ x := by
  by_cases hu : IsUnit x
  · exact (hu.pow n).dvd
  · rcases (hx.squarefree_of_dvd h).eq_zero_or_one_of_pow_of_not_isUnit hu with rfl | rfl <;> simp

section SquarefreeGcdOfSquarefree

variable {α : Type*} [CommMonoidWithZero α] [GCDMonoid α]

/-
**Squarefree.gcd_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Squarefree.gcd_right (a : α) {b : α} (hb : Squarefree b) : Squarefree (gcd
 a b)
参数：a : α；hb : Squarefree b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用定理 `GCDMonoid.gcd_dvd_right`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} 
[self : GCDMonoid α] (a b : α), gcd a b ∣ b
-/
theorem Squarefree.gcd_right (a : α) {b : α} (hb : Squarefree b) : Squarefree (gcd a b) :=
  hb.squarefree_of_dvd (gcd_dvd_right _ _)
/-
**Squarefree.gcd_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Squarefree.gcd_left {a : α} (b : α) (ha : Squarefree a) : Squarefree (gcd 
a b)
参数：b : α；ha : Squarefree a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用定理 `GCDMonoid.gcd_dvd_left`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [
self : GCDMonoid α] (a b : α), gcd a b ∣ a
-/
theorem Squarefree.gcd_left {a : α} (b : α) (ha : Squarefree a) : Squarefree (gcd a b) :=
  ha.squarefree_of_dvd (gcd_dvd_left _ _)

end SquarefreeGcdOfSquarefree

/-
**squarefree_iff_emultiplicity_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：squarefree_iff_emultiplicity_le_one [CommMonoid R] (r : R) : Squarefree r 
↔ forall x : R, emultiplicity x r <= 1 ∨ IsUnit x
参数：r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `pow_dvd_iff_le_emultiplicity`：pow_dvd_iff_le_emultiplicity {k : Nat} : a
 ^ k ∣ b ↔ k <= emultiplicity a b
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `imp_congr`：∀ {a b c d : Prop}, (a ↔ c) → (b ↔ d) → (a → b ↔ c → d)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Order.add_one_le_iff_of_not_isMax`：add_one_le_iff_of_not_isMax (hx : ¬ I
sMax x) : x + 1 <= y ↔ x < y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem squarefree_iff_emultiplicity_le_one [CommMonoid R] (r : R) :
    Squarefree r ↔ ∀ x : R, emultiplicity x r ≤ 1 ∨ IsUnit x := by
  refine forall_congr' fun a => ?_
  rw [← sq, pow_dvd_iff_le_emultiplicity, or_iff_not_imp_left, not_le, imp_congr _ Iff.rfl]
  norm_cast
  rw [← one_add_one_eq_two]
  exact Order.add_one_le_iff_of_not_isMax (by simp)

section Irreducible

variable [CommMonoidWithZero R] [WfDvdMonoid R]

/-
**squarefree_iff_no_irreducibles** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：squarefree_iff_no_irreducibles {x : R} (hx₀ : x != 0) : Squarefree x ↔ for
all p, Irreducible p -> ¬ (p * p ∣ x)
参数：hx₀ : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `WfDvdMonoid.exists_irreducible_factor`：exists_irreducible_factor {a : α}
 (ha : ¬IsUnit a) (ha0 : a != 0) : exists i, Irreducible i ∧ i ∣ a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
-/
theorem squarefree_iff_no_irreducibles {x : R} (hx₀ : x ≠ 0) :
    Squarefree x ↔ ∀ p, Irreducible p → ¬ (p * p ∣ x) := by
  refine ⟨fun h p hp hp' ↦ hp.not_isUnit (h p hp'), fun h d hd ↦ by_contra fun hdu ↦ ?_⟩
  have hd₀ : d ≠ 0 := ne_zero_of_dvd_ne_zero (ne_zero_of_dvd_ne_zero hx₀ hd) (dvd_mul_left d d)
  obtain ⟨p, irr, dvd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd₀
  exact h p irr ((mul_dvd_mul dvd dvd).trans hd)
/-
**irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree** 是 Mathl
ib 中的一个定理，位于命名空间 ``。
形式化陈述：irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree (r : 
R) : (forall x : R, Irreducible x -> ¬x * x ∣ r) ↔ (r = 0 ∧ forall x : R, ¬Irred
ucible x) ∨ Squarefree r
参数：r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `squarefree_iff_no_irreducibles`：squarefree_iff_no_irreducibles {x : R} (
hx₀ : x != 0) : Squarefree x ↔ forall p, Irreducible p -> ¬ (p * p ∣ x)
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
-/
theorem irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree (r : R) :
    (∀ x : R, Irreducible x → ¬x * x ∣ r) ↔ (r = 0 ∧ ∀ x : R, ¬Irreducible x) ∨ Squarefree r := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases eq_or_ne r 0 with (rfl | hr)
    · exact .inl (by simpa using h)
    · exact .inr ((squarefree_iff_no_irreducibles hr).mpr h)
  · rintro (⟨rfl, h⟩ | h)
    · simpa using h
    intro x hx t
    exact hx.not_isUnit (h x t)
/-
**squarefree_iff_irreducible_sq_not_dvd_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：squarefree_iff_irreducible_sq_not_dvd_of_ne_zero {r : R} (hr : r != 0) : S
quarefree r ↔ forall x : R, Irreducible x -> ¬x * x ∣ r
参数：hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree`：ir
reducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree (r : R) : (fo
rall x : R, Irreducible x -> ¬x * x ∣ r) ↔ (r = 0 ∧ forall…
-/
theorem squarefree_iff_irreducible_sq_not_dvd_of_ne_zero {r : R} (hr : r ≠ 0) :
    Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  simpa [hr] using (irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree r).symm
/-
**squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible {r : R} (hr : 
exists x : R, Irreducible x) : Squarefree r ↔ forall x : R, Irreducible x -> ¬x 
* x ∣ r
参数：hr : exists x : R, Irreducible x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree`：ir
reducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree (r : R) : (fo
rall x : R, Irreducible x -> ¬x * x ∣ r) ↔ (r = 0 ∧ forall…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible {r : R}
    (hr : ∃ x : R, Irreducible x) : Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  rw [irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree, ← not_exists]
  simp only [hr, not_true, false_or, and_false]

end Irreducible

section IsRadical

section
variable [CommMonoidWithZero R] [DecompositionMonoid R]

/-
**Squarefree.isRadical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Squarefree.isRadical {x : R} (hx : Squarefree x) : IsRadical x
参数：hx : Squarefree x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isRadical_iff_pow_one_lt`：isRadical_iff_pow_one_lt [Monoid R] (k : Nat) 
(hk : 1 < k) : IsRadical y ↔ forall x, y ∣ x ^ k -> y ∣ x
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `exists_dvd_and_dvd_of_dvd_mul`：exists_dvd_and_dvd_of_dvd_mul [Decomposit
ionMonoid α] {b c a : α} (H : a ∣ b * c) : exists a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a
₁ * a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `IsRelPrime.mul_dvd`：IsRelPrime.mul_dvd (H : IsRelPrime x y) (H1 : x ∣ z)
 (H2 : y ∣ z) : x * y ∣ z
· 使用定理 `IsRelPrime.of_squarefree_mul`：IsRelPrime.of_squarefree_mul [CommMonoid R
] {m n : R} (h : Squarefree (m * n)) : IsRelPrime m n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Squarefree.isRadical {x : R} (hx : Squarefree x) : IsRadical x :=
  (isRadical_iff_pow_one_lt 2 one_lt_two).2 fun y hy ↦ by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (sq y ▸ hy)
    exact (IsRelPrime.of_squarefree_mul hx).mul_dvd ha hb
/-
**Squarefree.dvd_pow_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Squarefree.dvd_pow_iff_dvd {x y : R} {n : Nat} (hsq : Squarefree x) (h0 : 
n != 0) : x ∣ y ^ n ↔ x ∣ y
参数：hsq : Squarefree x；h0 : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Squarefree.isRadical`：Squarefree.isRadical {x : R} (hx : Squarefree x) :
 IsRadical x
· 使用定理 `Dvd.dvd.pow`：∀ {α : Type u_1} [inst : Monoid α] {a b : α}, a ∣ b → ∀ {n 
: ℕ}, n ≠ 0 → a ∣ b ^ n
-/
theorem Squarefree.dvd_pow_iff_dvd {x y : R} {n : ℕ} (hsq : Squarefree x) (h0 : n ≠ 0) :
    x ∣ y ^ n ↔ x ∣ y := ⟨hsq.isRadical n y, (·.pow h0)⟩

end

variable [CommMonoidWithZero R] [IsCancelMulZero R] {x y p d : R}

/-
**IsRadical.squarefree** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRadical.squarefree (h0 : x != 0) (h : IsRadical x) : Squarefree x
参数：h0 : x != 0；h : IsRadical x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `mul_dvd_mul_iff_right`：mul_dvd_mul_iff_right [CommMonoidWithZero α] [IsC
ancelMulZero α] {a b c : α} (hc : c != 0) : a * c ∣ b * c ↔ a ∣ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsRadical.squarefree (h0 : x ≠ 0) (h : IsRadical x) : Squarefree x := by
  rintro z ⟨w, rfl⟩
  specialize h 2 (z * w) ⟨w, by simp_rw [pow_two, mul_left_comm, ← mul_assoc]⟩
  rwa [← one_mul (z * w), mul_assoc, mul_dvd_mul_iff_right, ← isUnit_iff_dvd_one] at h
  rw [mul_assoc, mul_ne_zero_iff] at h0; exact h0.2

namespace Squarefree

/-
**Squarefree.pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right** 是 Mathlib 中的一个定理，
位于命名空间 `Squarefree`。
形式化陈述：pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right {k : Nat} (hx : Squarefree
 x) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) : p ^ k ∣ y
参数：hx : Squarefree x；hp : Prime p；h : p ^ (k + 1) ∣ x * y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_dvd_mul_iff_left`：mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCan
celMulZero α] {a b c : α} (ha : a != 0) : a * b ∣ a * c ↔ b ∣ c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Prime.pow_dvd_of_dvd_mul_left`：Prime.pow_dvd_of_dvd_mul_left {p a b : M}
 (hp : Prime p) (n : Nat) (h : ¬p ∣ a) (h' : p ^ n ∣ a * b) : p ^ n ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right {k : ℕ}
    (hx : Squarefree x) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) :
    p ^ k ∣ y := by
  by_cases hxp : p ∣ x
  · obtain ⟨x', rfl⟩ := hxp
    have hx' : ¬ p ∣ x' := fun contra ↦ hp.not_isUnit <| hx p (mul_dvd_mul_left p contra)
    replace h : p ^ k ∣ x' * y := by
      rw [pow_succ', mul_assoc] at h
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp h
    exact hp.pow_dvd_of_dvd_mul_left _ hx' h
  · exact (pow_dvd_pow _ k.le_succ).trans (hp.pow_dvd_of_dvd_mul_left _ hxp h)
/-
**Squarefree.pow_dvd_of_squarefree_of_pow_succ_dvd_mul_left** 是 Mathlib 中的一个定理，位
于命名空间 `Squarefree`。
形式化陈述：pow_dvd_of_squarefree_of_pow_succ_dvd_mul_left {k : Nat} (hy : Squarefree 
y) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) : p ^ k ∣ x
参数：hy : Squarefree y；hp : Prime p；h : p ^ (k + 1) ∣ x * y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Squarefree.pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right`：pow_dvd_of_s
quarefree_of_pow_succ_dvd_mul_right {k : Nat} (hx : Squarefree x) (hp : Prime p)
 (h : p ^ (k + 1) ∣ x * y) : p ^ k ∣ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_left {k : ℕ}
    (hy : Squarefree y) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) :
    p ^ k ∣ x := by
  rw [mul_comm] at h
  exact pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hy hp h

variable [DecompositionMonoid R]
/-
**Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `S
quarefree`。
形式化陈述：dvd_of_squarefree_of_mul_dvd_mul_right (hx : Squarefree x) (h : d * d ∣ x 
* y) : d ∣ y
参数：hx : Squarefree x；h : d * d ∣ x * y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `exists_dvd_and_dvd_of_dvd_mul`：exists_dvd_and_dvd_of_dvd_mul [Decomposit
ionMonoid α] {b c a : α} (H : a ∣ b * c) : exists a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a
₁ * a₂
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用定理 `Squarefree.isRadical`：Squarefree.isRadical {x : R} (hx : Squarefree x) :
 IsRadical x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `mul_right_injective₀`：mul_right_injective₀ (ha : a != 0) : Function.Inje
ctive (a * ·)
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem dvd_of_squarefree_of_mul_dvd_mul_right (hx : Squarefree x) (h : d * d ∣ x * y) : d ∣ y := by
  nontriviality R
  obtain ⟨a, b, ha, hb, eq⟩ := exists_dvd_and_dvd_of_dvd_mul h
  replace ha : Squarefree a := hx.squarefree_of_dvd ha
  obtain ⟨c, hc⟩ : a ∣ d := ha.isRadical 2 d ⟨b, by rw [sq, eq]⟩
  rw [hc, mul_assoc, (mul_right_injective₀ ha.ne_zero).eq_iff] at eq
  exact dvd_trans ⟨c, by rw [hc, ← eq, mul_comm]⟩ hb
/-
**Squarefree.dvd_of_squarefree_of_mul_dvd_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Sq
uarefree`。
形式化陈述：dvd_of_squarefree_of_mul_dvd_mul_left (hy : Squarefree y) (h : d * d ∣ x *
 y) : d ∣ x
参数：hy : Squarefree y；h : d * d ∣ x * y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right`：dvd_of_squarefree_of_
mul_dvd_mul_right (hx : Squarefree x) (h : d * d ∣ x * y) : d ∣ y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem dvd_of_squarefree_of_mul_dvd_mul_left (hy : Squarefree y) (h : d * d ∣ x * y) : d ∣ x :=
  dvd_of_squarefree_of_mul_dvd_mul_right hy (mul_comm x y ▸ h)

end Squarefree

variable [DecompositionMonoid R]

/-- `x * y` is square-free iff `x` and `y` have no common factors and are themselves square-free. -/
/-
**squarefree_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：squarefree_mul_iff : Squarefree (x * y) ↔ IsRelPrime x y ∧ Squarefree x ∧ 
Squarefree y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_squarefree_mul`：IsRelPrime.of_squarefree_mul [CommMonoid R
] {m n : R} (h : Squarefree (m * n)) : IsRelPrime m n
· 使用定理 `Squarefree.of_mul_left`：Squarefree.of_mul_left [Monoid R] {m n : R} (hmn
 : Squarefree (m * n)) : Squarefree m
· 使用定理 `Squarefree.of_mul_right`：Squarefree.of_mul_right [CommMonoid R] {m n : R
} (hmn : Squarefree (m * n)) : Squarefree n
· 使用定理 `Squarefree.dvd_of_squarefree_of_mul_dvd_mul_left`：dvd_of_squarefree_of_m
ul_dvd_mul_left (hy : Squarefree y) (h : d * d ∣ x * y) : d ∣ x
· 使用定理 `Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right`：dvd_of_squarefree_of_
mul_dvd_mul_right (hx : Squarefree x) (h : d * d ∣ x * y) : d ∣ y

--- 原说明 ---
`x * y` is square-free iff `x` and `y` have no common factors and are themselves
 square-free.
-/
theorem squarefree_mul_iff : Squarefree (x * y) ↔ IsRelPrime x y ∧ Squarefree x ∧ Squarefree y :=
  ⟨fun h ↦ ⟨IsRelPrime.of_squarefree_mul h, h.of_mul_left, h.of_mul_right⟩,
    fun ⟨hp, sqx, sqy⟩ _ dvd ↦ hp (sqy.dvd_of_squarefree_of_mul_dvd_mul_left dvd)
      (sqx.dvd_of_squarefree_of_mul_dvd_mul_right dvd)⟩

open scoped Function in
/-
**Finset.squarefree_prod_of_pairwise_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.squarefree_prod_of_pairwise_isCoprime {ι : Type*} {s : Finset ι} {f
 : ι -> R} (hs : Set.Pairwise s (IsRelPrime on f)) (hs' : forall i in s, Squaref
ree (f i)) : Squarefree (∏ i in s, f i)
参数：hs : Set.Pairwise s (IsRelPrime on f)；hs' : forall i in s, Squarefree (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `squarefree_mul_iff`：squarefree_mul_iff : Squarefree (x * y) ↔ IsRelPrime
 x y ∧ Squarefree x ∧ Squarefree y
· 使用定理 `IsRelPrime.prod_right`：IsRelPrime.prod_right : (forall i in t, IsRelPrim
e x (s i)) -> IsRelPrime x (∏ i in t, s i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.pairwise_insert`：pairwise_insert : (insert a s).Pairwise r ↔ s.Pairw
ise r ∧ forall b in s, a != b -> r a b ∧ r b a
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Finset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Finset α} {hb : b
 ∉ s} (ha : a in s) : a in cons b s hb
-/
theorem Finset.squarefree_prod_of_pairwise_isCoprime {ι : Type*} {s : Finset ι}
    {f : ι → R} (hs : Set.Pairwise s (IsRelPrime on f)) (hs' : ∀ i ∈ s, Squarefree (f i)) :
    Squarefree (∏ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, squarefree_mul_iff]
    rw [Finset.coe_cons, Set.pairwise_insert] at hs
    refine ⟨.prod_right fun i hi ↦ ?_, hs' a (by simp), ?_⟩
    · exact (hs.right i (by simp [hi]) fun h ↦ ha (h ▸ hi)).left
    · exact ih hs.left fun i hi ↦ hs' i <| Finset.mem_cons_of_mem hi
/-
**isRadical_iff_squarefree_or_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRadical_iff_squarefree_or_zero : IsRadical x ↔ Squarefree x ∨ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `IsRadical.squarefree`：IsRadical.squarefree (h0 : x != 0) (h : IsRadical 
x) : Squarefree x
· 使用定理 `Squarefree.isRadical`：Squarefree.isRadical {x : R} (hx : Squarefree x) :
 IsRadical x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_isRadical_iff`：zero_isRadical_iff [MonoidWithZero R] : IsRadical (0
 : R) ↔ IsReduced R
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isRadical_iff_squarefree_or_zero : IsRadical x ↔ Squarefree x ∨ x = 0 :=
  ⟨fun hx ↦ (em <| x = 0).elim .inr fun h ↦ .inl <| hx.squarefree h,
    Or.rec Squarefree.isRadical <| by
      rintro rfl
      rw [zero_isRadical_iff]
      infer_instance⟩
/-
**isRadical_iff_squarefree_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRadical_iff_squarefree_of_ne_zero (h : x != 0) : IsRadical x ↔ Squarefre
e x
参数：h : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRadical.squarefree`：IsRadical.squarefree (h0 : x != 0) (h : IsRadical 
x) : Squarefree x
· 使用定理 `Squarefree.isRadical`：Squarefree.isRadical {x : R} (hx : Squarefree x) :
 IsRadical x
-/
theorem isRadical_iff_squarefree_of_ne_zero (h : x ≠ 0) : IsRadical x ↔ Squarefree x :=
  ⟨IsRadical.squarefree h, Squarefree.isRadical⟩

end IsRadical

namespace UniqueFactorizationMonoid

variable [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

/-
**UniqueFactorizationMonoid._root_.exists_squarefree_dvd_pow_of_ne_zero** 是 Math
lib 中的一个引理，位于命名空间 `UniqueFactorizationMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.exists_squarefree_dvd_pow_of_ne_zero {x : R} (hx : x ≠ 0) :
    ∃ (y : R) (n : ℕ), Squarefree y ∧ y ∣ x ∧ x ∣ y ^ n := by
  induction x using WfDvdMonoid.induction_on_irreducible with
  | zero => contradiction
  | unit u hu => exact ⟨1, 0, squarefree_one, one_dvd u, hu.dvd⟩
  | mul z p hz hp ih =>
    obtain ⟨y, n, hy, hyx, hy'⟩ := ih hz
    rcases n.eq_zero_or_pos with rfl | hn
    · exact ⟨p, 1, hp.squarefree, dvd_mul_right p z, by simp [isUnit_of_dvd_one (pow_zero y ▸ hy')]⟩
    by_cases hp' : p ∣ y
    · exact ⟨y, n + 1, hy, dvd_mul_of_dvd_right hyx _,
        mul_comm p z ▸ pow_succ y n ▸ mul_dvd_mul hy' hp'⟩
    · suffices Squarefree (p * y) from ⟨p * y, n, this,
        mul_dvd_mul_left p hyx, mul_pow p y n ▸ mul_dvd_mul (dvd_pow_self p hn.ne') hy'⟩
      exact squarefree_mul_iff.mpr ⟨hp.isRelPrime_iff_not_dvd.mpr hp', hp.squarefree, hy⟩
/-
**UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors** 是 Mathlib 中
的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：squarefree_iff_nodup_normalizedFactors [NormalizationMonoid R] {x : R} (x0
 : x != 0) : Squarefree x ↔ Multiset.Nodup (normalizedFactors x)
参数：x0 : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `squarefree_iff_emultiplicity_le_one`：squarefree_iff_emultiplicity_le_one
 [CommMonoid R] (r : R) : Squarefree r ↔ forall x : R, emultiplicity x r <= 1 ∨ 
IsUnit x
· 使用定理 `Multiset.nodup_iff_count_le_one`：nodup_iff_count_le_one [DecidableEq α] 
{s : Multiset α} : Nodup s ↔ forall a, count a s <= 1
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_normalized_factor`：irreducible_
of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Irreduc
ible x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.normalize_normalized_factor`：normalize_normali
zed_factor {a : α} : forall x : α, x in normalizedFactors a -> normalize x = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `emultiplicity_zero_eq_zero_of_ne_zero`：emultiplicity_zero_eq_zero_of_ne_
zero (a : α) (ha : a != 0) : emultiplicity 0 a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `WfDvdMonoid.exists_irreducible_factor`：exists_irreducible_factor {a : α}
 (ha : ¬IsUnit a) (ha0 : a != 0) : exists i, Irreducible i ∧ i ∣ a
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `emultiplicity_le_emultiplicity_of_dvd_left`：emultiplicity_le_emultiplici
ty_of_dvd_left {a b c : α} (hdvd : a ∣ b) : emultiplicity b c <= emultiplicity a
 c
-/
theorem squarefree_iff_nodup_normalizedFactors [NormalizationMonoid R] {x : R}
    (x0 : x ≠ 0) : Squarefree x ↔ Multiset.Nodup (normalizedFactors x) := by
  classical
  rw [squarefree_iff_emultiplicity_le_one, Multiset.nodup_iff_count_le_one]
  have := nontrivial_of_ne x 0 x0
  constructor <;> intro h a
  · by_cases hmem : a ∈ normalizedFactors x
    · have ha := irreducible_of_normalized_factor _ hmem
      rcases h a with (h | h)
      · rw [← normalize_normalized_factor _ hmem]
        rw [emultiplicity_eq_count_normalizedFactors ha x0] at h
        assumption_mod_cast
      · have := ha.1
        contradiction
    · simp [Multiset.count_eq_zero_of_notMem hmem]
  · rw [or_iff_not_imp_right]
    intro hu
    rcases eq_or_ne a 0 with rfl | h0
    · simp [x0]
    rcases WfDvdMonoid.exists_irreducible_factor hu h0 with ⟨b, hib, hdvd⟩
    apply le_trans (emultiplicity_le_emultiplicity_of_dvd_left hdvd)
    rw [emultiplicity_eq_count_normalizedFactors hib x0]
    exact_mod_cast h (normalize b)

end UniqueFactorizationMonoid

namespace Int

@[simp]
/-
**Int.squarefree_natAbs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：squarefree_natAbs {n : Int} : Squarefree n.natAbs ↔ Squarefree n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用引理 `Int.natAbs_surjective`：natAbs_surjective : natAbs.Surjective
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem squarefree_natAbs {n : ℤ} : Squarefree n.natAbs ↔ Squarefree n := by
  simp_rw [Squarefree, natAbs_surjective.forall, ← natAbs_mul, natAbs_dvd_natAbs,
    isUnit_iff_natAbs_eq, Nat.isUnit_iff]

@[simp]
/-
**Int.squarefree_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：squarefree_natCast {n : Nat} : Squarefree (n : Int) ↔ Squarefree n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.squarefree_natAbs`：squarefree_natAbs {n : Int} : Squarefree n.natAbs
 ↔ Squarefree n
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem squarefree_natCast {n : ℕ} : Squarefree (n : ℤ) ↔ Squarefree n := by
  rw [← squarefree_natAbs, natAbs_natCast]

end Int

