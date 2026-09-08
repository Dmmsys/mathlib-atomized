/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Additional lemmas about elements of a ring satisfying `IsCoprime`

and elements of a monoid satisfying `IsRelPrime`

These lemmas are in a separate file to the definition of `IsCoprime` or `IsRelPrime`
as they require more imports.

Notably, this includes lemmas about `Finset.prod` as this requires importing BigOperators, and
lemmas about `Pow` since these are easiest to prove via `Finset.prod`.

-/

public section

universe u v

open scoped Function -- required for scoped `on` notation

section IsCoprime

variable {R : Type u} {I : Type v} [CommSemiring R] {x y z : R} {s : I → R} {t : Finset I}

section

/-
**Int.isCoprime_iff_gcd_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.isCoprime_iff_gcd_eq_one {m n : Int} : IsCoprime m n ↔ Int.gcd m n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.gcd_dvd_iff`：gcd_dvd_iff {a b : Int} {n : Nat} : gcd a b ∣ n ↔ exist
s x y : Int, ↑n = a * x + b * y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `IsCoprime.eq_1`：∀ {R : Type u} [inst : CommSemiring R] (x y : R), IsCopr
ime x y = ∃ a b, a * x + b * y = 1
· 使用定理 `Int.gcd_eq_gcd_ab`：∀ (x y : ℤ), ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem Int.isCoprime_iff_gcd_eq_one {m n : ℤ} : IsCoprime m n ↔ Int.gcd m n = 1 := by
  constructor
  · rintro ⟨a, b, h⟩
    refine Nat.dvd_one.mp (Int.gcd_dvd_iff.mpr ⟨a, b, ?_⟩)
    rwa [mul_comm m, mul_comm n, eq_comm]
  · rw [← Int.ofNat_inj, IsCoprime, Int.gcd_eq_gcd_ab, mul_comm m, mul_comm n, Nat.cast_one]
    intro h
    exact ⟨_, _, h⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableRel (IsCoprime : ℤ → ℤ → Prop) :=
  fun m n => decidable_of_iff (Int.gcd m n = 1) Int.isCoprime_iff_gcd_eq_one.symm

@[simp, norm_cast]
/-
**Nat.isCoprime_iff_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.isCoprime_iff_coprime {m n : Nat} : IsCoprime (m : Int) n ↔ Nat.Coprim
e m n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.isCoprime_iff_gcd_eq_one`：Int.isCoprime_iff_gcd_eq_one {m n : Int} :
 IsCoprime m n ↔ Int.gcd m n = 1
· 使用定理 `Int.gcd_natCast_natCast`：∀ (a b : ℕ), (↑a).gcd ↑b = a.gcd b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Nat.isCoprime_iff_coprime {m n : ℕ} : IsCoprime (m : ℤ) n ↔ Nat.Coprime m n := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]

alias ⟨IsCoprime.natCoprime, Nat.Coprime.isCoprime⟩ := Nat.isCoprime_iff_coprime
/-
**Nat.Coprime.cast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.Coprime.cast {R : Type*} [CommRing R] {a b : Nat} (h : Nat.Coprime a b
) : IsCoprime (a : R) (b : R)
参数：h : Nat.Coprime a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `IsCoprime.intCast`：IsCoprime.intCast {R : Type*} [CommRing R] {a b : Int
} (h : IsCoprime a b) : IsCoprime (a : R) (b : R)
· 使用定理 `Nat.Coprime.isCoprime`：∀ {m n : ℕ}, m.Coprime n → IsCoprime ↑m ↑n
-/
theorem Nat.Coprime.cast {R : Type*} [CommRing R] {a b : ℕ} (h : Nat.Coprime a b) :
    IsCoprime (a : R) (b : R) :=
  mod_cast h.isCoprime.intCast
/-
**Rat.isCoprime_num_den** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Rat.isCoprime_num_den (x : Rat) : IsCoprime x.num x.den
参数：x : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_isCoprime_of_dvd_left`：IsCoprime.of_isCoprime_of_dvd_left (
h : IsCoprime y z) (hdvd : x ∣ y) : IsCoprime x z
· 使用定理 `Nat.Coprime.cast`：Nat.Coprime.cast {R : Type*} [CommRing R] {a b : Nat} 
(h : Nat.Coprime a b) : IsCoprime (a : R) (b : R)
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
· 使用定理 `Int.dvd_natAbs_self`：∀ {a : ℤ}, a ∣ ↑a.natAbs
-/
theorem Rat.isCoprime_num_den (x : ℚ) : IsCoprime x.num x.den :=
  x.reduced.cast.of_isCoprime_of_dvd_left Int.dvd_natAbs_self
/-
**Int.isCoprime_gcdA** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.isCoprime_gcdA {x y : Int} (h : IsCoprime x y) : IsCoprime (x.gcdA y) 
y
参数：h : IsCoprime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.gcd_eq_gcd_ab`：∀ (x y : ℤ), ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y
· 使用定理 `Nat.cast_eq_one`：cast_eq_one {n : Nat} : (n : R) = 1 ↔ n = 1
· 使用定理 `Int.isCoprime_iff_gcd_eq_one`：Int.isCoprime_iff_gcd_eq_one {m n : Int} :
 IsCoprime m n ↔ Int.gcd m n = 1
-/
theorem Int.isCoprime_gcdA {x y : ℤ} (h : IsCoprime x y) : IsCoprime (x.gcdA y) y := by
  use x, x.gcdB y
  rwa [mul_comm _ y, ← Int.gcd_eq_gcd_ab, Nat.cast_eq_one, ← Int.isCoprime_iff_gcd_eq_one]
/-
**Int.isCoprime_gcdB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.isCoprime_gcdB {x y : Int} (h : IsCoprime x y) : IsCoprime (x.gcdB y) 
x
参数：h : IsCoprime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.gcd_eq_gcd_ab`：∀ (x y : ℤ), ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y
· 使用定理 `Nat.cast_eq_one`：cast_eq_one {n : Nat} : (n : R) = 1 ↔ n = 1
· 使用定理 `Int.isCoprime_iff_gcd_eq_one`：Int.isCoprime_iff_gcd_eq_one {m n : Int} :
 IsCoprime m n ↔ Int.gcd m n = 1
-/
theorem Int.isCoprime_gcdB {x y : ℤ} (h : IsCoprime x y) : IsCoprime (x.gcdB y) x := by
  use y, x.gcdA y
  rwa [add_comm, mul_comm, ← Int.gcd_eq_gcd_ab, Nat.cast_eq_one, ← Int.isCoprime_iff_gcd_eq_one]
/-
**ne_zero_or_ne_zero_of_nat_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_zero_or_ne_zero_of_nat_coprime {A : Type u} [CommRing A] [Nontrivial A]
 {a b : Nat} (h : Nat.Coprime a b) : (a : A) != 0 ∨ (b : A) != 0
参数：h : Nat.Coprime a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.ne_zero_or_ne_zero`：IsCoprime.ne_zero_or_ne_zero [Nontrivial R
] (h : IsCoprime x y) : x != 0 ∨ y != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `IsCoprime.map`：IsCoprime.map (H : IsCoprime x y) {S : Type v} [CommSemir
ing S] (f : R ->+* S) : IsCoprime (f x) (f y)
· 使用定理 `Nat.Coprime.isCoprime`：∀ {m n : ℕ}, m.Coprime n → IsCoprime ↑m ↑n
-/
theorem ne_zero_or_ne_zero_of_nat_coprime {A : Type u} [CommRing A] [Nontrivial A] {a b : ℕ}
    (h : Nat.Coprime a b) : (a : A) ≠ 0 ∨ (b : A) ≠ 0 :=
  IsCoprime.ne_zero_or_ne_zero (R := A) <| by
    simpa only [map_natCast] using IsCoprime.map (Nat.Coprime.isCoprime h) (Int.castRingHom A)
/-
**IsCoprime.prod_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.prod_left (h : forall i in t, IsCoprime (s i) x) : IsCoprime (∏ 
i in t, s i) x
参数：h : forall i in t, IsCoprime (s i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `isCoprime_one_left`：isCoprime_one_left : IsCoprime 1 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `IsCoprime.mul_left`：IsCoprime.mul_left (H1 : IsCoprime x z) (H2 : IsCopr
ime y z) : IsCoprime (x * y) z
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.forall_mem_cons`：forall_mem_cons (h : a ∉ s) (p : α -> Prop) : (f
orall x, x in cons a s h -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsCoprime.prod_left (h : ∀ i ∈ t, IsCoprime (s i) x) : IsCoprime (∏ i ∈ t, s i) x := by
  induction t using Finset.cons_induction with
  | empty => apply isCoprime_one_left
  | cons b t hbt ih =>
    rw [Finset.prod_cons]
    rw [Finset.forall_mem_cons] at h
    exact h.1.mul_left (ih h.2)
/-
**IsCoprime.prod_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.prod_right : (forall i in t, IsCoprime x (s i)) -> IsCoprime x (
∏ i in t, s i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsCoprime.prod_left`：IsCoprime.prod_left (h : forall i in t, IsCoprime (
s i) x) : IsCoprime (∏ i in t, s i) x
-/
theorem IsCoprime.prod_right : (∀ i ∈ t, IsCoprime x (s i)) → IsCoprime x (∏ i ∈ t, s i) := by
  simpa only [isCoprime_comm] using IsCoprime.prod_left (R := R)
/-
**IsCoprime.prod_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.prod_left_iff : IsCoprime (∏ i in t, s i) x ↔ forall i in t, IsC
oprime (s i) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `isCoprime_one_left`：isCoprime_one_left : IsCoprime 1 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `IsCoprime.mul_left_iff`：IsCoprime.mul_left_iff : IsCoprime (x * y) z ↔ I
sCoprime x z ∧ IsCoprime y z
· 使用定理 `Finset.forall_mem_insert`：forall_mem_insert (a : α) (s : Finset α) (p : 
α -> Prop) : (forall x, x in insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsCoprime.prod_left_iff : IsCoprime (∏ i ∈ t, s i) x ↔ ∀ i ∈ t, IsCoprime (s i) x := by
  classical
  refine Finset.induction_on t (iff_of_true isCoprime_one_left fun _ ↦ by simp) fun b t hbt ih ↦ ?_
  rw [Finset.prod_insert hbt, IsCoprime.mul_left_iff, ih, Finset.forall_mem_insert]
/-
**IsCoprime.prod_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.prod_right_iff : IsCoprime x (∏ i in t, s i) ↔ forall i in t, Is
Coprime x (s i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsCoprime.prod_left_iff`：IsCoprime.prod_left_iff : IsCoprime (∏ i in t, 
s i) x ↔ forall i in t, IsCoprime (s i) x
-/
theorem IsCoprime.prod_right_iff : IsCoprime x (∏ i ∈ t, s i) ↔ ∀ i ∈ t, IsCoprime x (s i) := by
  simpa only [isCoprime_comm] using IsCoprime.prod_left_iff (R := R)
/-
**IsCoprime.of_prod_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_prod_left (H1 : IsCoprime (∏ i in t, s i) x) (i : I) (hit : i
 in t) : IsCoprime (s i) x
参数：H1 : IsCoprime (∏ i in t, s i) x；i : I；hit : i in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsCoprime.prod_left_iff`：IsCoprime.prod_left_iff : IsCoprime (∏ i in t, 
s i) x ↔ forall i in t, IsCoprime (s i) x
-/
theorem IsCoprime.of_prod_left (H1 : IsCoprime (∏ i ∈ t, s i) x) (i : I) (hit : i ∈ t) :
    IsCoprime (s i) x :=
  IsCoprime.prod_left_iff.1 H1 i hit
/-
**IsCoprime.of_prod_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_prod_right (H1 : IsCoprime x (∏ i in t, s i)) (i : I) (hit : 
i in t) : IsCoprime x (s i)
参数：H1 : IsCoprime x (∏ i in t, s i)；i : I；hit : i in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsCoprime.prod_right_iff`：IsCoprime.prod_right_iff : IsCoprime x (∏ i in
 t, s i) ↔ forall i in t, IsCoprime x (s i)
-/
theorem IsCoprime.of_prod_right (H1 : IsCoprime x (∏ i ∈ t, s i)) (i : I) (hit : i ∈ t) :
    IsCoprime x (s i) :=
  IsCoprime.prod_right_iff.1 H1 i hit
/-
**Finset.prod_dvd_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.prod_dvd_of_coprime (Hs : (t : Set I).Pairwise (IsCoprime on s)) (H
s1 : (forall i in t, s i ∣ z)) : (∏ x in t, s x) ∣ z
参数：Hs : (t : Set I).Pairwise (IsCoprime on s)；Hs1 : (forall i in t, s i ∣ z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `IsCoprime.mul_dvd`：IsCoprime.mul_dvd (H : IsCoprime x y) (H1 : x ∣ z) (H
2 : y ∣ z) : x * y ∣ z
· 使用定理 `IsCoprime.prod_right`：IsCoprime.prod_right : (forall i in t, IsCoprime x
 (s i)) -> IsCoprime x (∏ i in t, s i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
theorem Finset.prod_dvd_of_coprime
    (Hs : (t : Set I).Pairwise (IsCoprime on s)) (Hs1 : (∀ i ∈ t, s i ∣ z)) :
    (∏ x ∈ t, s x) ∣ z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a r har ih =>
    rw [Finset.prod_insert har]
    refine IsCoprime.mul_dvd ?_ ?_ ?_
    · refine IsCoprime.prod_right fun i hir ↦ ?_
      exact Hs (by simp) (by simp [hir]) (ne_of_mem_of_not_mem hir har).symm
    · exact Hs1 a (Finset.mem_insert_self a r)
    · refine ih (Hs.mono ?_) fun i hi ↦ Hs1 i <| Finset.mem_insert_of_mem hi
      simp only [Finset.coe_insert, Set.subset_insert]
/-
**Fintype.prod_dvd_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.prod_dvd_of_coprime [Fintype I] (Hs : Pairwise (IsCoprime on s)) (
Hs1 : forall i, s i ∣ z) : (∏ x, s x) ∣ z
参数：Hs : Pairwise (IsCoprime on s)；Hs1 : forall i, s i ∣ z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_dvd_of_coprime`：Finset.prod_dvd_of_coprime (Hs : (t : Set I)
.Pairwise (IsCoprime on s)) (Hs1 : (forall i in t, s i ∣ z)) : (∏ x in t, s x) ∣
 z
· 使用定理 `Pairwise.set_pairwise`：Pairwise.set_pairwise (hl : Pairwise R l) [Std.Sy
mm R] : { x | x in l }.Pairwise R
-/
theorem Fintype.prod_dvd_of_coprime [Fintype I] (Hs : Pairwise (IsCoprime on s))
    (Hs1 : ∀ i, s i ∣ z) : (∏ x, s x) ∣ z :=
  Finset.prod_dvd_of_coprime (Hs.set_pairwise _) fun i _ ↦ Hs1 i

end

open Finset

/-
**exists_sum_eq_one_iff_pairwise_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_sum_eq_one_iff_pairwise_coprime [DecidableEq I] (h : t.Nonempty) : 
(exists μ : I -> R, (∑ i in t, μ i * ∏ j in t \ {i}, s j) = 1) ↔ Pairwise (IsCop
rime on fun i : t => s i)
参数：h : t.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.pairwise_cons'`：pairwise_cons' {a : α} (ha : a ∉ s) (r : β -> β -
> Prop) (f : α -> β) : Pairwise (r on fun a : s.cons a ha => f a) ↔ Pairwise (r 
on fun a : …
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Finset.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : DecidableEq ι] (a : ι) (x : M) (s : Finset ι),   ∑ a' ∈ s, Pi.
single a x …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
（共 56 条，此处仅展示前 30 条）
-/
theorem exists_sum_eq_one_iff_pairwise_coprime [DecidableEq I] (h : t.Nonempty) :
    (∃ μ : I → R, (∑ i ∈ t, μ i * ∏ j ∈ t \ {i}, s j) = 1) ↔
      Pairwise (IsCoprime on fun i : t ↦ s i) := by
  induction h using Finset.Nonempty.cons_induction with
  | singleton =>
    simp [exists_apply_eq, Pairwise, Function.onFun]
  | cons a t hat h ih =>
    rw [pairwise_cons']
    have mem : ∀ x ∈ t, a ∈ insert a t \ {x} := fun x hx ↦ by
      rw [mem_sdiff, mem_singleton]
      exact ⟨mem_insert_self _ _, fun ha ↦ hat (ha ▸ hx)⟩
    constructor
    · rintro ⟨μ, hμ⟩
      rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert hat] at hμ
      refine ⟨ih.mp ⟨Pi.single h.choose (μ a * s h.choose) + μ * fun _ ↦ s a, ?_⟩, fun b hb ↦ ?_⟩
      · rw [prod_eq_mul_prod_sdiff_singleton_of_mem h.choose_spec, ← mul_assoc, ←
          @if_pos _ _ h.choose_spec R (_ * _) 0, ← sum_pi_single', ← sum_add_distrib] at hμ
        rw [← hμ, sum_congr rfl]
        intro x hx
        convert! add_mul (R := R) _ _ _ using 2
        · by_cases hx : x = h.choose
          · rw [hx, Pi.single_eq_same, Pi.single_eq_same]
          · rw [Pi.single_eq_of_ne hx, Pi.single_eq_of_ne hx, zero_mul]
        · convert! (mul_assoc _ _ _).symm
          rw [prod_eq_prod_sdiff_singleton_mul (mem x hx), mul_comm, sdiff_sdiff_comm,
            sdiff_singleton_eq_erase a, erase_insert hat]
      · have : IsCoprime (s b) (s a) :=
          ⟨μ a * ∏ i ∈ t \ {b}, s i, ∑ i ∈ t, μ i * ∏ j ∈ t \ {i}, s j, ?_⟩
        · exact ⟨this.symm, this⟩
        rw [mul_assoc, ← prod_eq_prod_sdiff_singleton_mul hb, sum_mul, ← hμ, sum_congr rfl]
        intro x hx
        rw [mul_assoc]
        congr
        rw [prod_eq_prod_sdiff_singleton_mul (mem x hx) _]
        congr 2
        rw [sdiff_sdiff_comm, sdiff_singleton_eq_erase a, erase_insert hat]
    · rintro ⟨hs, Hb⟩
      obtain ⟨μ, hμ⟩ := ih.mpr hs
      obtain ⟨u, v, huv⟩ := IsCoprime.prod_left fun b hb ↦ (Hb b hb).right
      use fun i ↦ if i = a then u else v * μ i
      have hμ' : (∑ i ∈ t, v * ((μ i * ∏ j ∈ t \ {i}, s j) * s a)) = v * s a := by
        rw [← mul_sum, ← sum_mul, hμ, one_mul]
      rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert hat]
      simp only [↓reduceIte, ite_mul]
      rw [← huv, ← hμ', sum_congr rfl]
      intro x hx
      rw [mul_assoc, if_neg fun ha : x = a ↦ hat (ha.casesOn hx)]
      rw [mul_assoc]
      congr
      rw [prod_eq_prod_sdiff_singleton_mul (mem x hx) _]
      congr 2
      rw [sdiff_sdiff_comm, sdiff_singleton_eq_erase a, erase_insert hat]
/-
**exists_sum_eq_one_iff_pairwise_coprime'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_sum_eq_one_iff_pairwise_coprime' [Fintype I] [Nonempty I] [Decidabl
eEq I] : (exists μ : I -> R, (∑ i : I, μ i * ∏ j in {i}ᶜ, s j) = 1) ↔ Pairwise (
IsCoprime on s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `exists_sum_eq_one_iff_pairwise_coprime`：exists_sum_eq_one_iff_pairwise_c
oprime [DecidableEq I] (h : t.Nonempty) : (exists μ : I -> R, (∑ i in t, μ i * ∏
 j in t \ {i}, s j) = 1) ↔ P…
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
-/
theorem exists_sum_eq_one_iff_pairwise_coprime' [Fintype I] [Nonempty I] [DecidableEq I] :
    (∃ μ : I → R, (∑ i : I, μ i * ∏ j ∈ {i}ᶜ, s j) = 1) ↔ Pairwise (IsCoprime on s) := by
  convert! exists_sum_eq_one_iff_pairwise_coprime Finset.univ_nonempty (s := s) using 1
  simp only [pairwise_subtype_iff_pairwise_finset', coe_univ, Set.pairwise_univ]
/-
**pairwise_coprime_iff_coprime_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pairwise_coprime_iff_coprime_prod [DecidableEq I] : Pairwise (IsCoprime on
 fun i : t => s i) ↔ forall i in t, IsCoprime (s i) (∏ j in t \ {i}, s j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.pairwise_subtype_iff_pairwise_finset'`：pairwise_subtype_iff_pairw
ise_finset' (r : β -> β -> Prop) (f : α -> β) : Pairwise (r on fun x : s => f x)
 ↔ (s : Set α).Pairwise (r on f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsCoprime.prod_right_iff`：IsCoprime.prod_right_iff : IsCoprime x (∏ i in
 t, s i) ↔ forall i in t, IsCoprime x (s i)
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pairwise_coprime_iff_coprime_prod [DecidableEq I] :
    Pairwise (IsCoprime on fun i : t ↦ s i) ↔ ∀ i ∈ t, IsCoprime (s i) (∏ j ∈ t \ {i}, s j) := by
  rw [Finset.pairwise_subtype_iff_pairwise_finset']
  refine ⟨fun hp i hi ↦ IsCoprime.prod_right_iff.mpr fun j hj ↦ ?_, fun hp ↦ ?_⟩
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    exact (hp hj.1 hi hj.2).symm
  · rintro i hi j hj h
    apply IsCoprime.prod_right_iff.mp (hp i hi)
    exact Finset.mem_sdiff.mpr ⟨hj, fun f ↦ h (Finset.mem_singleton.mp f).symm⟩

variable {m n : ℕ}
/-
**IsCoprime.pow_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.pow_left (H : IsCoprime x y) : IsCoprime (x ^ m) y
参数：H : IsCoprime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `IsCoprime.prod_left`：IsCoprime.prod_left (h : forall i in t, IsCoprime (
s i) x) : IsCoprime (∏ i in t, s i) x
-/
theorem IsCoprime.pow_left (H : IsCoprime x y) : IsCoprime (x ^ m) y := by
  rw [← Finset.card_range m, ← Finset.prod_const]
  exact IsCoprime.prod_left fun _ _ ↦ H
/-
**IsCoprime.pow_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.pow_right (H : IsCoprime x y) : IsCoprime x (y ^ n)
参数：H : IsCoprime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `IsCoprime.prod_right`：IsCoprime.prod_right : (forall i in t, IsCoprime x
 (s i)) -> IsCoprime x (∏ i in t, s i)
-/
theorem IsCoprime.pow_right (H : IsCoprime x y) : IsCoprime x (y ^ n) := by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact IsCoprime.prod_right fun _ _ ↦ H
/-
**IsCoprime.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y ^ n)
参数：H : IsCoprime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.pow_right`：IsCoprime.pow_right (H : IsCoprime x y) : IsCoprime
 x (y ^ n)
· 使用定理 `IsCoprime.pow_left`：IsCoprime.pow_left (H : IsCoprime x y) : IsCoprime (
x ^ m) y
-/
theorem IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y ^ n) :=
  H.pow_left.pow_right
/-
**IsCoprime.pow_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.pow_left_iff (hm : 0 < m) : IsCoprime (x ^ m) y ↔ IsCoprime x y
参数：hm : 0 < m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_prod_left`：IsCoprime.of_prod_left (H1 : IsCoprime (∏ i in t
, s i) x) (i : I) (hit : i in t) : IsCoprime (s i) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `IsCoprime.pow_left`：IsCoprime.pow_left (H : IsCoprime x y) : IsCoprime (
x ^ m) y
-/
theorem IsCoprime.pow_left_iff (hm : 0 < m) : IsCoprime (x ^ m) y ↔ IsCoprime x y := by
  refine ⟨fun h ↦ ?_, IsCoprime.pow_left⟩
  rw [← Finset.card_range m, ← Finset.prod_const] at h
  exact h.of_prod_left 0 (Finset.mem_range.mpr hm)
/-
**IsCoprime.pow_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.pow_right_iff (hm : 0 < m) : IsCoprime x (y ^ m) ↔ IsCoprime x y
参数：hm : 0 < m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用定理 `IsCoprime.pow_left_iff`：IsCoprime.pow_left_iff (hm : 0 < m) : IsCoprime 
(x ^ m) y ↔ IsCoprime x y
-/
theorem IsCoprime.pow_right_iff (hm : 0 < m) : IsCoprime x (y ^ m) ↔ IsCoprime x y :=
  isCoprime_comm.trans <| (IsCoprime.pow_left_iff hm).trans <| isCoprime_comm
/-
**IsCoprime.pow_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.pow_iff (hm : 0 < m) (hn : 0 < n) : IsCoprime (x ^ m) (y ^ n) ↔ 
IsCoprime x y
参数：hm : 0 < m；hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsCoprime.pow_left_iff`：IsCoprime.pow_left_iff (hm : 0 < m) : IsCoprime 
(x ^ m) y ↔ IsCoprime x y
· 使用定理 `IsCoprime.pow_right_iff`：IsCoprime.pow_right_iff (hm : 0 < m) : IsCoprim
e x (y ^ m) ↔ IsCoprime x y
-/
theorem IsCoprime.pow_iff (hm : 0 < m) (hn : 0 < n) : IsCoprime (x ^ m) (y ^ n) ↔ IsCoprime x y :=
  (IsCoprime.pow_left_iff hm).trans <| IsCoprime.pow_right_iff hn

end IsCoprime

section RelPrime

variable {α I} [CommMonoid α] [DecompositionMonoid α] {x y z : α} {s : I → α} {t : Finset I}

/-
**IsRelPrime.prod_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.prod_left : (forall i in t, IsRelPrime (s i) x) -> IsRelPrime (
∏ i in t, s i) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `isRelPrime_one_left`：isRelPrime_one_left : IsRelPrime 1 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `IsRelPrime.mul_left`：IsRelPrime.mul_left (H1 : IsRelPrime x z) (H2 : IsR
elPrime y z) : IsRelPrime (x * y) z
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.forall_mem_insert`：forall_mem_insert (a : α) (s : Finset α) (p : 
α -> Prop) : (forall x, x in insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsRelPrime.prod_left : (∀ i ∈ t, IsRelPrime (s i) x) → IsRelPrime (∏ i ∈ t, s i) x := by
  classical
  refine Finset.induction_on t (fun _ ↦ isRelPrime_one_left) fun b t hbt ih H ↦ ?_
  rw [Finset.prod_insert hbt]
  rw [Finset.forall_mem_insert] at H
  exact H.1.mul_left (ih H.2)
/-
**IsRelPrime.prod_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.prod_right : (forall i in t, IsRelPrime x (s i)) -> IsRelPrime 
x (∏ i in t, s i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsRelPrime.prod_left`：IsRelPrime.prod_left : (forall i in t, IsRelPrime 
(s i) x) -> IsRelPrime (∏ i in t, s i) x
-/
theorem IsRelPrime.prod_right : (∀ i ∈ t, IsRelPrime x (s i)) → IsRelPrime x (∏ i ∈ t, s i) := by
  simpa only [isRelPrime_comm] using IsRelPrime.prod_left (α := α)
/-
**IsRelPrime.prod_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.prod_left_iff : IsRelPrime (∏ i in t, s i) x ↔ forall i in t, I
sRelPrime (s i) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `isRelPrime_one_left`：isRelPrime_one_left : IsRelPrime 1 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `IsRelPrime.mul_left_iff`：IsRelPrime.mul_left_iff : IsRelPrime (x * y) z 
↔ IsRelPrime x z ∧ IsRelPrime y z
· 使用定理 `Finset.forall_mem_insert`：forall_mem_insert (a : α) (s : Finset α) (p : 
α -> Prop) : (forall x, x in insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsRelPrime.prod_left_iff : IsRelPrime (∏ i ∈ t, s i) x ↔ ∀ i ∈ t, IsRelPrime (s i) x := by
  classical
  refine Finset.induction_on t (iff_of_true isRelPrime_one_left fun _ ↦ by simp) fun b t hbt ih ↦ ?_
  rw [Finset.prod_insert hbt, IsRelPrime.mul_left_iff, ih, Finset.forall_mem_insert]
/-
**IsRelPrime.prod_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.prod_right_iff : IsRelPrime x (∏ i in t, s i) ↔ forall i in t, 
IsRelPrime x (s i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsRelPrime.prod_left_iff`：IsRelPrime.prod_left_iff : IsRelPrime (∏ i in 
t, s i) x ↔ forall i in t, IsRelPrime (s i) x
-/
theorem IsRelPrime.prod_right_iff : IsRelPrime x (∏ i ∈ t, s i) ↔ ∀ i ∈ t, IsRelPrime x (s i) := by
  simpa only [isRelPrime_comm] using IsRelPrime.prod_left_iff (α := α)
/-
**IsRelPrime.of_prod_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_prod_left (H1 : IsRelPrime (∏ i in t, s i) x) (i : I) (hit :
 i in t) : IsRelPrime (s i) x
参数：H1 : IsRelPrime (∏ i in t, s i) x；i : I；hit : i in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsRelPrime.prod_left_iff`：IsRelPrime.prod_left_iff : IsRelPrime (∏ i in 
t, s i) x ↔ forall i in t, IsRelPrime (s i) x
-/
theorem IsRelPrime.of_prod_left (H1 : IsRelPrime (∏ i ∈ t, s i) x) (i : I) (hit : i ∈ t) :
    IsRelPrime (s i) x :=
  IsRelPrime.prod_left_iff.1 H1 i hit
/-
**IsRelPrime.of_prod_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_prod_right (H1 : IsRelPrime x (∏ i in t, s i)) (i : I) (hit 
: i in t) : IsRelPrime x (s i)
参数：H1 : IsRelPrime x (∏ i in t, s i)；i : I；hit : i in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsRelPrime.prod_right_iff`：IsRelPrime.prod_right_iff : IsRelPrime x (∏ i
 in t, s i) ↔ forall i in t, IsRelPrime x (s i)
-/
theorem IsRelPrime.of_prod_right (H1 : IsRelPrime x (∏ i ∈ t, s i)) (i : I) (hit : i ∈ t) :
    IsRelPrime x (s i) :=
  IsRelPrime.prod_right_iff.1 H1 i hit
/-
**Finset.prod_dvd_of_isRelPrime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.prod_dvd_of_isRelPrime : (t : Set I).Pairwise (IsRelPrime on s) -> 
(forall i in t, s i ∣ z) -> (∏ x in t, s x) ∣ z
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `IsRelPrime.mul_dvd`：IsRelPrime.mul_dvd (H : IsRelPrime x y) (H1 : x ∣ z)
 (H2 : y ∣ z) : x * y ∣ z
· 使用定理 `IsRelPrime.prod_right`：IsRelPrime.prod_right : (forall i in t, IsRelPrim
e x (s i)) -> IsRelPrime x (∏ i in t, s i)
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
-/
theorem Finset.prod_dvd_of_isRelPrime :
    (t : Set I).Pairwise (IsRelPrime on s) → (∀ i ∈ t, s i ∣ z) → (∏ x ∈ t, s x) ∣ z := by
  classical
  exact Finset.induction_on t (fun _ _ ↦ one_dvd z)
    (by
      intro a r har ih Hs Hs1
      rw [Finset.prod_insert har]
      have aux1 : a ∈ (↑(insert a r) : Set I) := Finset.mem_insert_self a r
      refine
        (IsRelPrime.prod_right fun i hir ↦
              Hs aux1 (Finset.mem_insert_of_mem hir) <| by
                rintro rfl
                exact har hir).mul_dvd
          (Hs1 a aux1) (ih (Hs.mono ?_) fun i hi ↦ Hs1 i <| Finset.mem_insert_of_mem hi)
      simp only [Finset.coe_insert, Set.subset_insert])
/-
**Fintype.prod_dvd_of_isRelPrime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.prod_dvd_of_isRelPrime [Fintype I] (Hs : Pairwise (IsRelPrime on s
)) (Hs1 : forall i, s i ∣ z) : (∏ x, s x) ∣ z
参数：Hs : Pairwise (IsRelPrime on s)；Hs1 : forall i, s i ∣ z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_dvd_of_isRelPrime`：Finset.prod_dvd_of_isRelPrime : (t : Set 
I).Pairwise (IsRelPrime on s) -> (forall i in t, s i ∣ z) -> (∏ x in t, s x) ∣ z
· 使用定理 `Pairwise.set_pairwise`：Pairwise.set_pairwise (hl : Pairwise R l) [Std.Sy
mm R] : { x | x in l }.Pairwise R
-/
theorem Fintype.prod_dvd_of_isRelPrime [Fintype I] (Hs : Pairwise (IsRelPrime on s))
    (Hs1 : ∀ i, s i ∣ z) : (∏ x, s x) ∣ z :=
  Finset.prod_dvd_of_isRelPrime (Hs.set_pairwise _) fun i _ ↦ Hs1 i
/-
**pairwise_isRelPrime_iff_isRelPrime_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pairwise_isRelPrime_iff_isRelPrime_prod [DecidableEq I] : Pairwise (IsRelP
rime on fun i : t => s i) ↔ forall i in t, IsRelPrime (s i) (∏ j in t \ {i}, s j
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsRelPrime.prod_right_iff`：IsRelPrime.prod_right_iff : IsRelPrime x (∏ i
 in t, s i) ↔ forall i in t, IsRelPrime x (s i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem pairwise_isRelPrime_iff_isRelPrime_prod [DecidableEq I] :
    Pairwise (IsRelPrime on fun i : t ↦ s i) ↔ ∀ i ∈ t, IsRelPrime (s i) (∏ j ∈ t \ {i}, s j) := by
  refine ⟨fun hp i hi ↦ IsRelPrime.prod_right_iff.mpr fun j hj ↦ ?_, fun hp ↦ ?_⟩
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    obtain ⟨hj, ji⟩ := hj
    exact @hp ⟨i, hi⟩ ⟨j, hj⟩ fun h ↦ ji (congrArg Subtype.val h).symm
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    apply IsRelPrime.prod_right_iff.mp (hp i hi)
    grind

namespace IsRelPrime

variable {m n : ℕ}

/-
**IsRelPrime.pow_left** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：pow_left (H : IsRelPrime x y) : IsRelPrime (x ^ m) y
参数：H : IsRelPrime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `IsRelPrime.prod_left`：IsRelPrime.prod_left : (forall i in t, IsRelPrime 
(s i) x) -> IsRelPrime (∏ i in t, s i) x
-/
theorem pow_left (H : IsRelPrime x y) : IsRelPrime (x ^ m) y := by
  rw [← Finset.card_range m, ← Finset.prod_const]
  exact IsRelPrime.prod_left fun _ _ ↦ H
/-
**IsRelPrime.pow_right** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：pow_right (H : IsRelPrime x y) : IsRelPrime x (y ^ n)
参数：H : IsRelPrime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `IsRelPrime.prod_right`：IsRelPrime.prod_right : (forall i in t, IsRelPrim
e x (s i)) -> IsRelPrime x (∏ i in t, s i)
-/
theorem pow_right (H : IsRelPrime x y) : IsRelPrime x (y ^ n) := by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact IsRelPrime.prod_right fun _ _ ↦ H
/-
**IsRelPrime.pow** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：pow (H : IsRelPrime x y) : IsRelPrime (x ^ m) (y ^ n)
参数：H : IsRelPrime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.pow_right`：pow_right (H : IsRelPrime x y) : IsRelPrime x (y ^
 n)
· 使用定理 `IsRelPrime.pow_left`：pow_left (H : IsRelPrime x y) : IsRelPrime (x ^ m) 
y
-/
theorem pow (H : IsRelPrime x y) : IsRelPrime (x ^ m) (y ^ n) :=
  H.pow_left.pow_right
/-
**IsRelPrime.pow_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：pow_left_iff (hm : 0 < m) : IsRelPrime (x ^ m) y ↔ IsRelPrime x y
参数：hm : 0 < m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_prod_left`：IsRelPrime.of_prod_left (H1 : IsRelPrime (∏ i i
n t, s i) x) (i : I) (hit : i in t) : IsRelPrime (s i) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `IsRelPrime.pow_left`：pow_left (H : IsRelPrime x y) : IsRelPrime (x ^ m) 
y
-/
theorem pow_left_iff (hm : 0 < m) : IsRelPrime (x ^ m) y ↔ IsRelPrime x y := by
  refine ⟨fun h ↦ ?_, IsRelPrime.pow_left⟩
  rw [← Finset.card_range m, ← Finset.prod_const] at h
  exact h.of_prod_left 0 (Finset.mem_range.mpr hm)
/-
**IsRelPrime.pow_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：pow_right_iff (hm : 0 < m) : IsRelPrime x (y ^ m) ↔ IsRelPrime x y
参数：hm : 0 < m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isRelPrime_comm`：isRelPrime_comm : IsRelPrime x y ↔ IsRelPrime y x
· 使用定理 `IsRelPrime.pow_left_iff`：pow_left_iff (hm : 0 < m) : IsRelPrime (x ^ m) 
y ↔ IsRelPrime x y
-/
theorem pow_right_iff (hm : 0 < m) : IsRelPrime x (y ^ m) ↔ IsRelPrime x y :=
  isRelPrime_comm.trans <| (IsRelPrime.pow_left_iff hm).trans <| isRelPrime_comm
/-
**IsRelPrime.pow_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：pow_iff (hm : 0 < m) (hn : 0 < n) : IsRelPrime (x ^ m) (y ^ n) ↔ IsRelPrim
e x y
参数：hm : 0 < m；hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsRelPrime.pow_left_iff`：pow_left_iff (hm : 0 < m) : IsRelPrime (x ^ m) 
y ↔ IsRelPrime x y
· 使用定理 `IsRelPrime.pow_right_iff`：pow_right_iff (hm : 0 < m) : IsRelPrime x (y ^
 m) ↔ IsRelPrime x y
-/
theorem pow_iff (hm : 0 < m) (hn : 0 < n) :
    IsRelPrime (x ^ m) (y ^ n) ↔ IsRelPrime x y :=
  (IsRelPrime.pow_left_iff hm).trans (IsRelPrime.pow_right_iff hn)

end IsRelPrime

end RelPrime

