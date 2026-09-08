/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Lemmas about `factorizationLCMLeft`

This file contains some lemmas about `factorizationLCMLeft`.
These were split from `Mathlib.Data.Nat.Factorization.Basic` to reduce transitive imports.
-/

public section

open Finset List Finsupp

namespace Nat

variable (a b)

/-
**Nat.factorizationLCMLeft_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (b : ℕ), Nat.factorizationLCMLeft 0 b = 1
参数：b : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.lcm_zero_left`：∀ (m : ℕ), Nat.lcm 0 m = 0
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma factorizationLCMLeft_zero_left : factorizationLCMLeft 0 b = 1 := by
  simp [factorizationLCMLeft]
/-
**Nat.factorizationLCMLeft_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a : ℕ), a.factorizationLCMLeft 0 = 1
参数：a : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.lcm_zero_right`：∀ (m : ℕ), m.lcm 0 = 0
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma factorizationLCMLeft_zero_right : factorizationLCMLeft a 0 = 1 := by
  simp [factorizationLCMLeft]
/-
**Nat.factorizationLCRight_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (b : ℕ), Nat.factorizationLCMRight 0 b = 1
参数：b : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.lcm_zero_left`：∀ (m : ℕ), Nat.lcm 0 m = 0
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma factorizationLCRight_zero_left : factorizationLCMRight 0 b = 1 := by
  simp [factorizationLCMRight]
/-
**Nat.factorizationLCMRight_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a : ℕ), a.factorizationLCMRight 0 = 1
参数：a : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.lcm_zero_right`：∀ (m : ℕ), m.lcm 0 = 0
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `Finsupp.prod_fun_one`：prod_fun_one (f : α ->₀ M) : f.prod (fun _ _ => (1
 : N)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma factorizationLCMRight_zero_right : factorizationLCMRight a 0 = 1 := by
  simp [factorizationLCMRight]
/-
**Nat.factorizationLCMLeft_pos** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factorizationLCMLeft_pos : 0 < factorizationLCMLeft a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorizationLCMLeft.eq_1`：∀ (a b : ℕ),   a.factorizationLCMLeft b =
     (a.lcm b).factorization.prod fun p n => if b.factorization p ≤ a.factorizat
ion p then p ^ n el…
· 使用引理 `Finsupp.prod_ne_zero_iff`：prod_ne_zero_iff : f.prod g != 0 ↔ forall i in
 f.support, g i (f i) != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Nat.factorization_zero_right`：factorization_zero_right (n : Nat) : n.fac
torization 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma factorizationLCMLeft_pos : 0 < factorizationLCMLeft a b := by
  apply Nat.pos_of_ne_zero
  rw [factorizationLCMLeft, Finsupp.prod_ne_zero_iff]
  intro p _ H
  by_cases h : b.factorization p ≤ a.factorization p
  · simp only [h, reduceIte, pow_eq_zero_iff', ne_eq] at H
    simpa [H.1] using H.2
  · simp only [h, reduceIte, one_ne_zero] at H
/-
**Nat.factorizationLCMRight_pos** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factorizationLCMRight_pos : 0 < factorizationLCMRight a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorizationLCMRight.eq_1`：∀ (a b : ℕ),   a.factorizationLCMRight b
 =     (a.lcm b).factorization.prod fun p n => if b.factorization p ≤ a.factoriz
ation p then 1 else …
· 使用引理 `Finsupp.prod_ne_zero_iff`：prod_ne_zero_iff : f.prod g != 0 ↔ forall i in
 f.support, g i (f i) != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Nat.factorization_zero_right`：factorization_zero_right (n : Nat) : n.fac
torization 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma factorizationLCMRight_pos : 0 < factorizationLCMRight a b := by
  apply Nat.pos_of_ne_zero
  rw [factorizationLCMRight, Finsupp.prod_ne_zero_iff]
  intro p _ H
  by_cases h : b.factorization p ≤ a.factorization p
  · simp only [h, reduceIte, reduceCtorEq] at H
  · simp only [h, ↓reduceIte, pow_eq_zero_iff', ne_eq] at H
    simpa [H.1] using H.2
/-
**Nat.coprime_factorizationLCMLeft_factorizationLCMRight** 是 Mathlib 中的一个引理，位于命名
空间 `Nat`。
形式化陈述：coprime_factorizationLCMLeft_factorizationLCMRight : (factorizationLCMLeft
 a b).Coprime (factorizationLCMRight a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorizationLCMLeft.eq_1`：∀ (a b : ℕ),   a.factorizationLCMLeft b =
     (a.lcm b).factorization.prod fun p n => if b.factorization p ≤ a.factorizat
ion p then p ^ n el…
· 使用定理 `Nat.factorizationLCMRight.eq_1`：∀ (a b : ℕ),   a.factorizationLCMRight b
 =     (a.lcm b).factorization.prod fun p n => if b.factorization p ≤ a.factoriz
ation p then 1 else …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.coprime_prod_left_iff`：coprime_prod_left_iff {t : Finset ι} {s : ι -
> Nat} {x : Nat} : Coprime (∏ i in t, s i) x ↔ forall i in t, Coprime (s i) x
· 使用定理 `Nat.coprime_prod_right_iff`：coprime_prod_right_iff {x : Nat} {t : Finset
 ι} {s : ι -> Nat} : Coprime x (∏ i in t, s i) ↔ forall i in t, Coprime x (s i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.coprime_one_right_eq_true`：∀ (n : ℕ), n.Coprime 1 = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.coprime_pow_primes`：coprime_pow_primes {p q : Nat} (n m : Nat) (pp :
 Prime p) (pq : Prime q) (h : p != q) : Coprime (p ^ n) (q ^ m)
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.coprime_one_left_eq_true`：∀ (n : ℕ), Nat.Coprime 1 n = True
-/
lemma coprime_factorizationLCMLeft_factorizationLCMRight :
    (factorizationLCMLeft a b).Coprime (factorizationLCMRight a b) := by
  rw [factorizationLCMLeft, factorizationLCMRight]
  refine coprime_prod_left_iff.mpr fun p hp ↦ coprime_prod_right_iff.mpr fun q hq ↦ ?_
  dsimp only; split_ifs with h h'
  any_goals simp only [coprime_one_right_eq_true, coprime_one_left_eq_true]
  refine coprime_pow_primes _ _ (prime_of_mem_primeFactors hp) (prime_of_mem_primeFactors hq) ?_
  contrapose h'; rwa [← h']

variable {a b}
/-
**Nat.factorizationLCMLeft_mul_factorizationLCMRight** 是 Mathlib 中的一个引理，位于命名空间 `
Nat`。
形式化陈述：factorizationLCMLeft_mul_factorizationLCMRight (ha : a != 0) (hb : b != 0)
 : (factorizationLCMLeft a b) * (factorizationLCMRight a b) = lcm a b
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `Nat.lcm_ne_zero`：∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.lcm n ≠ 0
· 使用定理 `Nat.factorizationLCMLeft.eq_1`：∀ (a b : ℕ),   a.factorizationLCMLeft b =
     (a.lcm b).factorization.prod fun p n => if b.factorization p ≤ a.factorizat
ion p then p ^ n el…
· 使用定理 `Nat.factorizationLCMRight.eq_1`：∀ (a b : ℕ),   a.factorizationLCMRight b
 =     (a.lcm b).factorization.prod fun p n => if b.factorization p ≤ a.factoriz
ation p then 1 else …
· 使用定理 `Finsupp.prod_mul`：prod_mul [Zero M] [CommMonoid N] {f : α ->₀ M} {h₁ h₂ 
: α -> M -> N} : (f.prod fun a b => h₁ a b * h₂ a b) = f.prod h₁ * f.prod h₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma factorizationLCMLeft_mul_factorizationLCMRight (ha : a ≠ 0) (hb : b ≠ 0) :
    (factorizationLCMLeft a b) * (factorizationLCMRight a b) = lcm a b := by
  rw [← prod_factorization_pow_eq_self (lcm_ne_zero ha hb), factorizationLCMLeft,
    factorizationLCMRight, ← prod_mul]
  congr; ext p n; split_ifs <;> simp

variable (a b)
/-
**Nat.factorizationLCMLeft_dvd_left** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factorizationLCMLeft_dvd_left : factorizationLCMLeft a b ∣ a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.lcm_zero_right`：∀ (m : ℕ), m.lcm 0 = 0
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `Finsupp.prod_of_support_subset`：prod_of_support_subset (f : α ->₀ M) {s 
: Finset α} (hs : f.support subseteq s) (g : α -> M -> N) (h : forall i in s, g 
i 0 = 1) : f.prod g …
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Nat.factorization_lcm`：factorization_lcm {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a.lcm b).factorization = a.factorization ⊔ b.factorization
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_sup_iff`：lt_sup_iff : a < b ⊔ c ↔ a < b ∨ a < c
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `Finset.prod_dvd_prod_of_dvd`：prod_dvd_prod_of_dvd (f g : ι -> M) (h : fo
rall i in s, f i ∣ g i) : ∏ i in s, f i ∣ ∏ i in s, g i
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
-/
lemma factorizationLCMLeft_dvd_left : factorizationLCMLeft a b ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [dvd_zero]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [factorizationLCMLeft]
  nth_rewrite 2 [← prod_factorization_pow_eq_self ha]
  rw [prod_of_support_subset (s := (lcm a b).factorization.support)]
  · apply prod_dvd_prod_of_dvd; rintro p -; dsimp only; split_ifs with le
    · rw [factorization_lcm ha hb]; apply pow_dvd_pow; exact sup_le le_rfl le
    · apply one_dvd
  · intro p hp; rw [mem_support_iff] at hp ⊢
    rw [factorization_lcm ha hb]; exact (lt_sup_iff.mpr <| .inl <| Nat.pos_of_ne_zero hp).ne'
  · intros; rw [pow_zero]
/-
**Nat.factorizationLCMRight_dvd_right** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factorizationLCMRight_dvd_right : factorizationLCMRight a b ∣ b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.lcm_zero_left`：∀ (m : ℕ), Nat.lcm 0 m = 0
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `Finsupp.prod_of_support_subset`：prod_of_support_subset (f : α ->₀ M) {s 
: Finset α} (hs : f.support subseteq s) (g : α -> M -> N) (h : forall i in s, g 
i 0 = 1) : f.prod g …
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Nat.factorization_lcm`：factorization_lcm {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a.lcm b).factorization = a.factorization ⊔ b.factorization
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_sup_iff`：lt_sup_iff : a < b ⊔ c ↔ a < b ∨ a < c
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `Finset.prod_dvd_prod_of_dvd`：prod_dvd_prod_of_dvd (f g : ι -> M) (h : fo
rall i in s, f i ∣ g i) : ∏ i in s, f i ∣ ∏ i in s, g i
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 33 条，此处仅展示前 30 条）
-/
lemma factorizationLCMRight_dvd_right : factorizationLCMRight a b ∣ b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [factorizationLCMRight]
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [dvd_zero]
  nth_rewrite 2 [← prod_factorization_pow_eq_self hb]
  rw [prod_of_support_subset (s := (lcm a b).factorization.support)]
  · apply Finset.prod_dvd_prod_of_dvd; rintro p -; dsimp only; split_ifs with le
    · apply one_dvd
    · rw [factorization_lcm ha hb]; apply pow_dvd_pow; exact sup_le (not_le.1 le).le le_rfl
  · intro p hp; rw [mem_support_iff] at hp ⊢
    rw [factorization_lcm ha hb]; exact (lt_sup_iff.mpr <| .inr <| Nat.pos_of_ne_zero hp).ne'
  · intros; rw [pow_zero]


end Nat

