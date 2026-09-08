/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# The Carmichael function

## Main definitions

* `ArithmeticFunction.carmichael`: the Carmichael function `λ`,
  also known as the reduced totient function.

## Main results

* A formula for `λ n` in terms of the prime factorization of `n`, given by the following theorems:
  `carmichael_two_pow_of_le_two`, `carmichael_two_pow_of_ne_two`, `carmichael_pow_of_prime_ne_two`,
  and `carmichael_factorization`.

## Notation

We use the standard notation `λ` to represent the Carmichael function,
which is accessible in the scope `ArithmeticFunction.carmichael`.
Since the notation conflicts with the anonymous function notation, it is impossible to use this
notation in statements, but the pretty-printer will use it when showing the goal state.

## Tags

arithmetic functions, totient
-/

@[expose] public section

open Nat Monoid

variable {R : Type*}

namespace ArithmeticFunction

/-- `λ` is the Carmichael function, also known as the reduced totient function,
defined as the exponent of the unit group of `ZMod n`. -/
/-
**ArithmeticFunction.carmichael** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：carmichael : ArithmeticFunction Nat where toFun | 0 => 0 | n + 1 => Nat.fi
nd ExponentExists.of_finite (G
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`λ` is the Carmichael function, also known as the reduced totient function,
defined as the exponent of the unit group of `ZMod n`.
-/
def carmichael : ArithmeticFunction ℕ where
  toFun
    | 0 => 0
    | n + 1 => Nat.find <| ExponentExists.of_finite (G := (ZMod (n + 1))ˣ)
  map_zero' := rfl

@[deprecated (since := "2026-05-06")] alias Carmichael := carmichael

@[inherit_doc]
scoped[ArithmeticFunction.carmichael] notation "λ" => ArithmeticFunction.carmichael

open scoped carmichael
/-
**ArithmeticFunction.carmichael_eq_exponent** 是 Mathlib 中的一个定理，位于命名空间 `Arithmeti
cFunction`。
形式化陈述：carmichael_eq_exponent {n : Nat} (hn : n != 0) : carmichael n = exponent (
ZMod n)ˣ
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem carmichael_eq_exponent {n : ℕ} (hn : n ≠ 0) : carmichael n = exponent (ZMod n)ˣ := by
  cases n with | zero => contradiction | succ n =>
  change Nat.find _ = _
  grind [exponent, ExponentExists.of_finite]

/-- This takes in an `NeZero n` instance instead of an `n ≠ 0` hypothesis. -/
/-
**ArithmeticFunction.carmichael_eq_exponent'** 是 Mathlib 中的一个定理，位于命名空间 `Arithmet
icFunction`。
形式化陈述：carmichael_eq_exponent' (n : Nat) [NeZero n] : carmichael n = exponent (ZM
od n)ˣ
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.carmichael_eq_exponent`：carmichael_eq_exponent {n : N
at} (hn : n != 0) : carmichael n = exponent (ZMod n)ˣ
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0

--- 原说明 ---
This takes in an `NeZero n` instance instead of an `n ≠ 0` hypothesis.
-/
theorem carmichael_eq_exponent' (n : ℕ) [NeZero n] : carmichael n = exponent (ZMod n)ˣ :=
  carmichael_eq_exponent <| NeZero.ne n

@[simp]
/-
**ArithmeticFunction.pow_carmichael** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunctio
n`。
形式化陈述：pow_carmichael {n : Nat} (a : (ZMod n)ˣ) : a ^ carmichael n = 1
参数：a : (ZMod n)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.carmichael_eq_exponent'`：carmichael_eq_exponent' (n :
 Nat) [NeZero n] : carmichael n = exponent (ZMod n)ˣ
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Monoid.pow_exponent_eq_one`：pow_exponent_eq_one (g : G) : g ^ exponent G
 = 1
-/
theorem pow_carmichael {n : ℕ} (a : (ZMod n)ˣ) : a ^ carmichael n = 1 := by
  cases n
  · rw [map_zero, pow_zero]
  rw [carmichael_eq_exponent']
  exact pow_exponent_eq_one a
/-
**ArithmeticFunction.carmichael_dvd_totient** 是 Mathlib 中的一个定理，位于命名空间 `Arithmeti
cFunction`。
形式化陈述：carmichael_dvd_totient (n : Nat) : carmichael n ∣ n.totient
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ZMod.card_units_eq_totient`：∀ (n : ℕ) [NeZero n] [inst : Fintype (ZMod n
)ˣ], Fintype.card (ZMod n)ˣ = n.totient
· 使用定理 `ArithmeticFunction.carmichael_eq_exponent'`：carmichael_eq_exponent' (n :
 Nat) [NeZero n] : carmichael n = exponent (ZMod n)ˣ
· 使用定理 `Group.exponent_dvd_card`：Group.exponent_dvd_card [Fintype G] : Monoid.ex
ponent G ∣ Fintype.card G
-/
theorem carmichael_dvd_totient (n : ℕ) : carmichael n ∣ n.totient := by
  cases n
  · simp
  rw [← ZMod.card_units_eq_totient, carmichael_eq_exponent']
  exact Group.exponent_dvd_card
/-
**ArithmeticFunction.carmichael_dvd** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunctio
n`。
形式化陈述：carmichael_dvd {a b : Nat} (h : a ∣ b) : carmichael a ∣ carmichael b
参数：h : a ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.carmichael_eq_exponent`：carmichael_eq_exponent {n : N
at} (hn : n != 0) : carmichael n = exponent (ZMod n)ˣ
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `ArithmeticFunction.carmichael_eq_exponent'`：carmichael_eq_exponent' (n :
 Nat) [NeZero n] : carmichael n = exponent (ZMod n)ˣ
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MonoidHom.exponent_dvd`：MonoidHom.exponent_dvd {F M₁ M₂ : Type*} [Monoid
 M₁] [Monoid M₂] [FunLike F M₁ M₂] [MonoidHomClass F M₁ M₂] {f : F} (hf : Functi
on.Surjectiv…
· 使用定理 `ZMod.unitsMap_surjective`：unitsMap_surjective [hm : NeZero m] (h : n ∣ m
) : Function.Surjective (unitsMap h)
-/
theorem carmichael_dvd {a b : ℕ} (h : a ∣ b) : carmichael a ∣ carmichael b := by
  cases b
  · simp
  rw [carmichael_eq_exponent <| ne_zero_of_dvd_ne_zero (by lia) h, carmichael_eq_exponent']
  exact MonoidHom.exponent_dvd <| ZMod.unitsMap_surjective h
/-
**ArithmeticFunction.carmichael_lcm** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunctio
n`。
形式化陈述：carmichael_lcm (a b : Nat) : carmichael (Nat.lcm a b) = Nat.lcm (carmichae
l a) (carmichael b)
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.carmichael_eq_exponent`：carmichael_eq_exponent {n : N
at} (hn : n != 0) : carmichael n = exponent (ZMod n)ˣ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.lcm_ne_zero`：∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.lcm n ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lcm_eq_nat_lcm`：lcm_eq_nat_lcm (m n : Nat) : lcm m n = Nat.lcm m n
· 使用定理 `Monoid.exponent_prod`：Monoid.exponent_prod {M₁ M₂ : Type*} [Monoid M₁] [
Monoid M₂] : exponent (M₁ × M₂) = lcm (exponent M₁) (exponent M₂)
· 使用定理 `Monoid.exponent_eq_of_mulEquiv`：exponent_eq_of_mulEquiv (e : G ≃* H) : M
onoid.exponent G = Monoid.exponent H
· 使用定理 `Monoid.exponent_dvd_of_monoidHom`：exponent_dvd_of_monoidHom (e : G ->* H
) (e_inj : Function.Injective e) : Monoid.exponent G ∣ Monoid.exponent H
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Units.map_injective`：map_injective {f : M ->* N} (hf : Function.Injectiv
e f) : Function.Injective (map f)
· 使用定理 `ZMod.castHom_injective`：castHom_injective : Function.Injective (ZMod.cas
tHom (dvd_refl n) R)
· 使用定理 `ArithmeticFunction.carmichael_dvd`：carmichael_dvd {a b : Nat} (h : a ∣ b
) : carmichael a ∣ carmichael b
· 使用定理 `Nat.dvd_lcm_left`：∀ (m n : ℕ), m ∣ m.lcm n
· 使用定理 `Nat.dvd_lcm_right`：∀ (m n : ℕ), n ∣ m.lcm n
· 使用定理 `Nat.lcm_dvd`：∀ {m n k : ℕ}, m ∣ k → n ∣ k → m.lcm n ∣ k
-/
theorem carmichael_lcm (a b : ℕ) :
    carmichael (Nat.lcm a b) = Nat.lcm (carmichael a) (carmichael b) := by
  by_cases! h₀ : a = 0 ∨ b = 0
  · grind [Nat.lcm_eq_zero_iff, map_zero]
  apply dvd_antisymm
  · rw [carmichael_eq_exponent h₀.left, carmichael_eq_exponent h₀.right,
      carmichael_eq_exponent <| lcm_ne_zero h₀.left h₀.right, ← lcm_eq_nat_lcm <| exponent _,
      ← exponent_prod, ← exponent_eq_of_mulEquiv .prodUnits]
    exact exponent_dvd_of_monoidHom _ <| Units.map_injective <| ZMod.castHom_injective _
  · have ha := carmichael_dvd <| Nat.dvd_lcm_left a b
    have hb := carmichael_dvd <| Nat.dvd_lcm_right a b
    exact Nat.lcm_dvd ha hb
/-
**ArithmeticFunction.carmichael_mul** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunctio
n`。
形式化陈述：carmichael_mul {a b : Nat} (h : Coprime a b) : carmichael (a * b) = Nat.lc
m (carmichael a) (carmichael b)
参数：h : Coprime a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.carmichael_lcm`：carmichael_lcm (a b : Nat) : carmicha
el (Nat.lcm a b) = Nat.lcm (carmichael a) (carmichael b)
· 使用定理 `Nat.Coprime.lcm_eq_mul`：∀ {m n : ℕ}, m.Coprime n → m.lcm n = m * n
-/
theorem carmichael_mul {a b : ℕ} (h : Coprime a b) :
    carmichael (a * b) = Nat.lcm (carmichael a) (carmichael b) :=
  h.lcm_eq_mul ▸ carmichael_lcm ..
/-
**ArithmeticFunction.carmichael_finset_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Arithmetic
Function`。
形式化陈述：carmichael_finset_lcm {α : Type*} (s : Finset α) (f : α -> Nat) : carmicha
el (s.lcm f) = s.lcm (carmichael ∘ f)
参数：s : Finset α；f : α -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ArithmeticFunction.carmichael_eq_exponent'`：carmichael_eq_exponent' (n :
 Nat) [NeZero n] : carmichael n = exponent (ZMod n)ˣ
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Monoid.exp_eq_one_of_subsingleton`：exp_eq_one_of_subsingleton [hs : Subs
ingleton G] : exponent G = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.lcm_insert`：lcm_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).lcm f = GCDMonoid.lcm (f b) (s.lcm f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.carmichael_lcm`：carmichael_lcm (a b : Nat) : carmicha
el (Nat.lcm a b) = Nat.lcm (carmichael a) (carmichael b)
-/
theorem carmichael_finset_lcm {α : Type*} (s : Finset α) (f : α → ℕ) :
    carmichael (s.lcm f) = s.lcm (carmichael ∘ f) := by
  classical
  refine s.induction ?_ fun a s ha ih ↦ ?_
  · exact carmichael_eq_exponent' 1 |>.trans exp_eq_one_of_subsingleton
  rw [Finset.lcm_insert, Finset.lcm_insert, ← ih]
  exact carmichael_lcm ..
/-
**ArithmeticFunction.carmichael_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Arithmetic
Function`。
形式化陈述：carmichael_finsetProd {α : Type*} {s : Finset α} {f : α -> Nat} (h : Set.P
airwise s <| Coprime.onFun f) : carmichael (s.prod f) = s.lcm (carmichael ∘ f)
参数：h : Set.Pairwise s <| Coprime.onFun f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.carmichael_finset_lcm`：carmichael_finset_lcm {α : Typ
e*} (s : Finset α) (f : α -> Nat) : carmichael (s.lcm f) = s.lcm (carmichael ∘ f
)
· 使用定理 `Finset.lcm_eq_prod`：lcm_eq_prod {s : Finset ι} {f : ι -> Nat} (h : Set.P
airwise s <| Nat.Coprime.onFun f) : s.lcm f = s.prod f
-/
theorem carmichael_finsetProd {α : Type*} {s : Finset α} {f : α → ℕ}
    (h : Set.Pairwise s <| Coprime.onFun f) : carmichael (s.prod f) = s.lcm (carmichael ∘ f) :=
  s.lcm_eq_prod h ▸ carmichael_finset_lcm ..

@[deprecated (since := "2026-04-08")] alias carmichael_finset_prod := carmichael_finsetProd
/-
**ArithmeticFunction.carmichael_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction`。
形式化陈述：carmichael_factorization (n : Nat) [NeZero n] : carmichael n = n.primeFact
ors.lcm fun p => carmichael (p ^ n.factorization p)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `ArithmeticFunction.carmichael_finsetProd`：carmichael_finsetProd {α : Typ
e*} {s : Finset α} {f : α -> Nat} (h : Set.Pairwise s <| Coprime.onFun f) : carm
ichael (s.prod f) = s.lcm (car…
· 使用定理 `Pairwise.set_of_subtype`：∀ {α : Type u_1} (s : Set α) (r : α → α → Prop)
, (Pairwise fun x y => r ↑x ↑y) → s.Pairwise r
· 使用引理 `Nat.pairwise_coprime_pow_primeFactors_factorization`：pairwise_coprime_po
w_primeFactors_factorization : Pairwise (Function.onFun Nat.Coprime fun (p : n.p
rimeFactors) => p ^ n.factorization p)
-/
theorem carmichael_factorization (n : ℕ) [NeZero n] :
    carmichael n = n.primeFactors.lcm fun p ↦ carmichael (p ^ n.factorization p) := by
  nth_rw 1 [← n.prod_factorization_pow_eq_self <| NeZero.ne _]
  exact carmichael_finsetProd pairwise_coprime_pow_primeFactors_factorization.set_of_subtype
/-
**ArithmeticFunction.carmichael_two_pow_of_le_two_eq_totient** 是 Mathlib 中的一个定理，
位于命名空间 `ArithmeticFunction`。
形式化陈述：carmichael_two_pow_of_le_two_eq_totient {n : Nat} (hn : n <= 2) : carmicha
el (2 ^ n) = (2 ^ n).totient
参数：hn : n <= 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.carmichael_eq_exponent'`：carmichael_eq_exponent' (n :
 Nat) [NeZero n] : carmichael n = exponent (ZMod n)ˣ
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.card_units_eq_totient`：∀ (n : ℕ) [NeZero n] [inst : Fintype (ZMod n
)ˣ], Fintype.card (ZMod n)ˣ = n.totient
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsCyclic.iff_exponent_eq_card`：IsCyclic.iff_exponent_eq_card [CommGroup 
α] [Finite α] : IsCyclic α ↔ exponent α = Nat.card α
· 使用定理 `ZMod.instFiniteZModUnits`：∀ (n : ℕ), Finite (ZMod n)ˣ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZMod.isCyclic_units_two_pow_iff`：isCyclic_units_two_pow_iff (n : Nat) : 
IsCyclic (ZMod (2 ^ n))ˣ ↔ n <= 2
-/
theorem carmichael_two_pow_of_le_two_eq_totient {n : ℕ} (hn : n ≤ 2) :
    carmichael (2 ^ n) = (2 ^ n).totient := by
  rw [carmichael_eq_exponent', ← ZMod.card_units_eq_totient, Fintype.card_eq_nat_card]
  exact IsCyclic.iff_exponent_eq_card.mp <| ZMod.isCyclic_units_two_pow_iff n |>.mpr hn

/-- Note that `2 ^ (n - 1) = 1` when `n = 0`. -/
@[simp]
/-
**ArithmeticFunction.carmichael_two_pow_of_le_two** 是 Mathlib 中的一个定理，位于命名空间 `Ari
thmeticFunction`。
形式化陈述：carmichael_two_pow_of_le_two {n : Nat} (hn : n <= 2) : carmichael (2 ^ n) 
= 2 ^ (n - 1)
参数：hn : n <= 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.carmichael_two_pow_of_le_two_eq_totient`：carmichael_t
wo_pow_of_le_two_eq_totient {n : Nat} (hn : n <= 2) : carmichael (2 ^ n) = (2 ^ 
n).totient
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Mathlib.Tactic.IntervalCases.of_le_right`：of_le_right [LE α] (h : (a : α
) <= b) (eq : b = b') : a <= b'
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.ge_of_not_lt`：∀ {n m : ℕ}, ¬n < m → n ≥ m
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n

--- 原说明 ---
Note that `2 ^ (n - 1) = 1` when `n = 0`.
-/
theorem carmichael_two_pow_of_le_two {n : ℕ} (hn : n ≤ 2) :
    carmichael (2 ^ n) = 2 ^ (n - 1) := by
  rw [carmichael_two_pow_of_le_two_eq_totient hn]
  interval_cases n <;> decide

/-- Note that `2 ^ (n - 2) = 1` when `n ≤ 1`. -/
@[simp]
/-
**ArithmeticFunction.carmichael_two_pow_of_ne_two** 是 Mathlib 中的一个定理，位于命名空间 `Ari
thmeticFunction`。
形式化陈述：carmichael_two_pow_of_ne_two {n : Nat} (hn : n != 2) : carmichael (2 ^ n) 
= 2 ^ (n - 2)
参数：hn : n != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ArithmeticFunction.carmichael_eq_exponent'`：carmichael_eq_exponent' (n :
 Nat) [NeZero n] : carmichael n = exponent (ZMod n)ˣ
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `ZMod.card_units_eq_totient`：∀ (n : ℕ) [NeZero n] [inst : Fintype (ZMod n
)ˣ], Fintype.card (ZMod n)ˣ = n.totient
· 使用定理 `Nat.totient_prime_pow`：totient_prime_pow {p : Nat} (hp : p.Prime) {n : N
at} (hn : 0 < n) : φ (p ^ n) = p ^ (n - 1) * (p - 1)
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Nat.add_one_sub_one`：∀ (n : ℕ), n + 1 - 1 = n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_prime_pow`：dvd_prime_pow {p : Nat} (pp : Prime p) {m i : Nat} : 
i ∣ p ^ m ↔ exists k <= m, i = p ^ k
· 使用定理 `Group.exponent_dvd_nat_card`：Group.exponent_dvd_nat_card : Monoid.expone
nt G ∣ Nat.card G
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `IsCyclic.iff_exponent_eq_card`：IsCyclic.iff_exponent_eq_card [CommGroup 
α] [Finite α] : IsCyclic α ↔ exponent α = Nat.card α
· 使用定理 `ZMod.instFiniteZModUnits`：∀ (n : ℕ), Finite (ZMod n)ˣ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZMod.isCyclic_units_two_pow_iff`：isCyclic_units_two_pow_iff (n : Nat) : 
IsCyclic (ZMod (2 ^ n))ˣ ↔ n <= 2
· 使用定理 `Nat.pow_dvd_pow`：∀ {m n : ℕ} (a : ℕ), m ≤ n → a ^ m ∣ a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.gcd_pow_right_of_gcd_eq_one`：∀ {k n m : ℕ}, n.gcd m = 1 → n.gcd (m ^
 k) = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `ZMod.orderOf_five`：orderOf_five (n : Nat) : orderOf (5 : ZMod (2 ^ (n + 
2))) = 2 ^ n
· 使用定理 `orderOf_units`：orderOf_units {y : Gˣ} : orderOf (y : G) = orderOf y
· 使用定理 `Monoid.order_dvd_exponent`：order_dvd_exponent (g : G) : orderOf g ∣ expo
nent G

--- 原说明 ---
Note that `2 ^ (n - 2) = 1` when `n ≤ 1`.
-/
theorem carmichael_two_pow_of_ne_two {n : ℕ} (hn : n ≠ 2) :
    carmichael (2 ^ n) = 2 ^ (n - 2) := by
  by_cases hn' : n ≤ 2
  · grind [carmichael_two_pow_of_le_two]
  refine carmichael_eq_exponent' _ |>.trans <| dvd_antisymm ?_ ?_
  · have hcard : Nat.card (ZMod (2 ^ n))ˣ = 2 ^ (n - 1) := by
      rw [card_eq_fintype_card, ZMod.card_units_eq_totient, totient_prime_pow prime_two <| by lia,
        Nat.add_one_sub_one, mul_one]
    have ⟨k, hk, h⟩ := dvd_prime_pow prime_two |>.mp <| hcard ▸ Group.exponent_dvd_nat_card
    have := IsCyclic.iff_exponent_eq_card.not.mp <| ZMod.isCyclic_units_two_pow_iff n |>.not.mpr hn'
    exact h ▸ Nat.pow_dvd_pow 2 (by grind)
  · let five : (ZMod (2 ^ n))ˣ := ZMod.unitOfCoprime 5 <| gcd_pow_right_of_gcd_eq_one rfl
    rw [← ZMod.orderOf_five (n - 2), show n - 2 + 2 = n by lia,
      show (5 : ZMod (2 ^ n)) = five by rfl, orderOf_units]
    exact order_dvd_exponent five
/-
**ArithmeticFunction.two_mul_carmichael_two_pow_of_three_le_eq_totient** 是 Mathl
ib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：two_mul_carmichael_two_pow_of_three_le_eq_totient {n : Nat} (hn : 3 <= n) 
: 2 * carmichael (2 ^ n) = (2 ^ n).totient
参数：hn : 3 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.carmichael_two_pow_of_ne_two`：carmichael_two_pow_of_n
e_two {n : Nat} (hn : n != 2) : carmichael (2 ^ n) = 2 ^ (n - 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `Nat.totient_prime_pow`：totient_prime_pow {p : Nat} (hp : p.Prime) {n : N
at} (hn : 0 < n) : φ (p ^ n) = p ^ (n - 1) * (p - 1)
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
-/
theorem two_mul_carmichael_two_pow_of_three_le_eq_totient {n : ℕ} (hn : 3 ≤ n) :
    2 * carmichael (2 ^ n) = (2 ^ n).totient := by
  rw [carmichael_two_pow_of_ne_two, ← pow_succ', totient_prime_pow prime_two] <;>
  · #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
    we need to re-enable model-based theory combination in `lia` for this to go through. -/
    lia +mbtc

@[simp]
/-
**ArithmeticFunction.carmichael_pow_of_prime_ne_two** 是 Mathlib 中的一个定理，位于命名空间 `A
rithmeticFunction`。
形式化陈述：carmichael_pow_of_prime_ne_two {p : Nat} (n : Nat) (hp : p.Prime) (hp₂ : p
 != 2) : carmichael (p ^ n) = (p ^ n).totient
参数：n : Nat；hp : p.Prime；hp₂ : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.carmichael_eq_exponent'`：carmichael_eq_exponent' (n :
 Nat) [NeZero n] : carmichael n = exponent (ZMod n)ˣ
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.card_units_eq_totient`：∀ (n : ℕ) [NeZero n] [inst : Fintype (ZMod n
)ˣ], Fintype.card (ZMod n)ˣ = n.totient
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsCyclic.iff_exponent_eq_card`：IsCyclic.iff_exponent_eq_card [CommGroup 
α] [Finite α] : IsCyclic α ↔ exponent α = Nat.card α
· 使用定理 `ZMod.instFiniteZModUnits`：∀ (n : ℕ), Finite (ZMod n)ˣ
· 使用定理 `ZMod.isCyclic_units_of_prime_pow`：isCyclic_units_of_prime_pow (p : Nat) 
(hp : p.Prime) (hp2 : p != 2) (n : Nat) : IsCyclic (ZMod (p ^ n))ˣ
-/
theorem carmichael_pow_of_prime_ne_two {p : ℕ} (n : ℕ) (hp : p.Prime) (hp₂ : p ≠ 2) :
    carmichael (p ^ n) = (p ^ n).totient := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [carmichael_eq_exponent', ← ZMod.card_units_eq_totient, Fintype.card_eq_nat_card]
  exact IsCyclic.iff_exponent_eq_card.mp <| ZMod.isCyclic_units_of_prime_pow p hp hp₂ n

end ArithmeticFunction

