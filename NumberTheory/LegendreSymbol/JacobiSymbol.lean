/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Thomas Zhu, Mario Carneiro
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# The Jacobi Symbol

We define the Jacobi symbol and prove its main properties.

## Main definitions

We define the Jacobi symbol, `jacobiSym a b`, for integers `a` and natural numbers `b`
as the product over the prime factors `p` of `b` of the Legendre symbols `legendreSym p a`.
This agrees with the mathematical definition when `b` is odd.

The prime factors are obtained via `Nat.factors`. Since `Nat.factors 0 = []`,
this implies in particular that `jacobiSym a 0 = 1` for all `a`.

## Main statements

We prove the main properties of the Jacobi symbol, including the following.

* Multiplicativity in both arguments (`jacobiSym.mul_left`, `jacobiSym.mul_right`)

* The value of the symbol is `1` or `-1` when the arguments are coprime
  (`jacobiSym.eq_one_or_neg_one`)

* The symbol vanishes if and only if `b ≠ 0` and the arguments are not coprime
  (`jacobiSym.eq_zero_iff_not_coprime`)

* If the symbol has the value `-1`, then `a : ZMod b` is not a square
  (`ZMod.nonsquare_of_jacobiSym_eq_neg_one`); the converse holds when `b = p` is a prime
  (`ZMod.nonsquare_iff_jacobiSym_eq_neg_one`); in particular, in this case `a` is a
  square mod `p` when the symbol has the value `1` (`ZMod.isSquare_of_jacobiSym_eq_one`).

* Quadratic reciprocity (`jacobiSym.quadratic_reciprocity`,
  `jacobiSym.quadratic_reciprocity_one_mod_four`,
  `jacobiSym.quadratic_reciprocity_three_mod_four`)

* The supplementary laws for `a = -1`, `a = 2`, `a = -2` (`jacobiSym.at_neg_one`,
  `jacobiSym.at_two`, `jacobiSym.at_neg_two`)

* The symbol depends on `a` only via its residue class mod `b` (`jacobiSym.mod_left`)
  and on `b` only via its residue class mod `4*a` (`jacobiSym.mod_right`)

* A `csimp` rule for `jacobiSym` and `legendreSym` that evaluates `J(a | b)` efficiently by
  reducing to the case `0 ≤ a < b` and `a`, `b` odd, and then swaps `a`, `b` and recurses using
  quadratic reciprocity.

## Notation

We define the notation `J(a | b)` for `jacobiSym a b`, localized to `NumberTheorySymbols`.

## Tags
Jacobi symbol, quadratic reciprocity
-/

@[expose] public section


section Jacobi

/-!
### Definition of the Jacobi symbol

We define the Jacobi symbol $\Bigl(\frac{a}{b}\Bigr)$ for integers `a` and natural numbers `b`
as the product of the Legendre symbols $\Bigl(\frac{a}{p}\Bigr)$, where `p` runs through the
prime divisors (with multiplicity) of `b`, as provided by `b.factors`. This agrees with the
Jacobi symbol when `b` is odd and gives less meaningful values when it is not (e.g., the symbol
is `1` when `b = 0`). This is called `jacobiSym a b`.

We define localized notation (scope `NumberTheorySymbols`) `J(a | b)` for the Jacobi
symbol `jacobiSym a b`.
-/


open Nat ZMod

-- Since we need the fact that the factors are prime, we use `List.pmap`.
/-- The Jacobi symbol of `a` and `b` -/
/-
**jacobiSym** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：jacobiSym (a : Int) (b : Nat) : Int
参数：a : Int；b : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p

--- 原说明 ---
The Jacobi symbol of `a` and `b`
-/
def jacobiSym (a : ℤ) (b : ℕ) : ℤ :=
  (b.primeFactorsList.pmap (fun p pp => @legendreSym p ⟨pp⟩ a) fun _ pf =>
    prime_of_mem_primeFactorsList pf).prod

-- Notation for the Jacobi symbol.
@[inherit_doc]
scoped[NumberTheorySymbols] notation "J(" a " | " b ")" => jacobiSym a b

open NumberTheorySymbols

/-!
### Properties of the Jacobi symbol
-/


namespace jacobiSym

/-- The symbol `J(a | 0)` has the value `1`. -/
@[simp]
/-
**jacobiSym.zero_right** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：zero_right (a : Int) : J(a | 0) = 1
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Nat.primeFactorsList_zero`：primeFactorsList_zero : primeFactorsList 0 = 
[]
· 使用定理 `List.pmap.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {P : α → Prop} (f 
f_1 : (a : α) → P a → β),   f = f_1 → ∀ (l l_1 : List α) (e_l : l = l_1) (H : ∀ 
a ∈ l, P a…
· 使用定理 `List.pmap.eq_1`：∀ {α : Type u_1} {β : Type u_2} {P : α → Prop} (f : (a :
 α) → P a → β) (x_2 : ∀ a ∈ [], P a), List.pmap f [] x_2 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The symbol `J(a | 0)` has the value `1`.
-/
theorem zero_right (a : ℤ) : J(a | 0) = 1 := by
  simp only [jacobiSym, primeFactorsList_zero, List.prod_nil, List.pmap]

/-- The symbol `J(a | 1)` has the value `1`. -/
@[simp]
/-
**jacobiSym.one_right** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：one_right (a : Int) : J(a | 1) = 1
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Nat.primeFactorsList_one`：primeFactorsList_one : primeFactorsList 1 = []
· 使用定理 `List.pmap.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {P : α → Prop} (f 
f_1 : (a : α) → P a → β),   f = f_1 → ∀ (l l_1 : List α) (e_l : l = l_1) (H : ∀ 
a ∈ l, P a…
· 使用定理 `List.pmap.eq_1`：∀ {α : Type u_1} {β : Type u_2} {P : α → Prop} (f : (a :
 α) → P a → β) (x_2 : ∀ a ∈ [], P a), List.pmap f [] x_2 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The symbol `J(a | 1)` has the value `1`.
-/
theorem one_right (a : ℤ) : J(a | 1) = 1 := by
  simp only [jacobiSym, primeFactorsList_one, List.prod_nil, List.pmap]

/-- The Legendre symbol `legendreSym p a` with an integer `a` and a prime number `p`
is the same as the Jacobi symbol `J(a | p)`. -/
/-
**jacobiSym.legendreSym.to_jacobiSym** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym.legend
reSym`。
形式化陈述：∀ (p : ℕ) [fp : Fact (Nat.Prime p)] (a : ℤ), legendreSym p a = jacobiSym a
 p
参数：p : ℕ；Nat.Prime p；a : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Nat.primeFactorsList_prime`：primeFactorsList_prime {p : Nat} (hp : Nat.P
rime p) : p.primeFactorsList = [p]
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.pmap.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {P : α → Prop} (f 
f_1 : (a : α) → P a → β),   f = f_1 → ∀ (l l_1 : List α) (e_l : l = l_1) (H : ∀ 
a ∈ l, P a…
· 使用定理 `List.pmap.eq_2`：∀ {α : Type u_1} {β : Type u_2} {P : α → Prop} (f : (a :
 α) → P a → β) (a : α) (l : List α) (H : ∀ a_1 ∈ a :: l, P a_1),   List.pmap f (
a ::…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Legendre symbol `legendreSym p a` with an integer `a` and a prime number `p`
is the same as the Jacobi symbol `J(a | p)`.
-/
theorem legendreSym.to_jacobiSym (p : ℕ) [fp : Fact p.Prime] (a : ℤ) :
    legendreSym p a = J(a | p) := by
  simp only [jacobiSym, primeFactorsList_prime fp.1, List.prod_cons, List.prod_nil, mul_one,
    List.pmap]

/-- The Jacobi symbol is multiplicative in its second argument. -/
/-
**jacobiSym.mul_right'** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：mul_right' (a : Int) {b₁ b₂ : Nat} (hb₁ : b₁ != 0) (hb₂ : b₂ != 0) : J(a |
 b₁ * b₂) = J(a | b₁) * J(a | b₂)
参数：a : Int；hb₁ : b₁ != 0；hb₂ : b₂ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `jacobiSym.eq_1`：∀ (a : ℤ) (b : ℕ), jacobiSym a b = (List.pmap (fun p pp 
=> legendreSym p a) b.primeFactorsList ⋯).prod
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_append`：∀ {α : Type u_1} {a : α} {s t : List α}, a ∈ s ++ t ↔ a
 ∈ s ∨ a ∈ t
· 使用定理 `List.Perm.prod_eq`：∀ {M : Type u_4} [inst : CommMonoid M] {l₁ l₂ : List 
M}, l₁.Perm l₂ → l₁.prod = l₂.prod
· 使用定理 `List.Perm.pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a :
 α) → p a → β) {l₁ l₂ : List α},   l₁.Perm l₂ → ∀ {H₁ : ∀ a ∈ l₁, p a} {H₂ : ∀ a
 ∈ l…
· 使用定理 `Nat.perm_primeFactorsList_mul`：perm_primeFactorsList_mul {a b : Nat} (ha
 : a != 0) (hb : b != 0) : (a * b).primeFactorsList ~ a.primeFactorsList ++ b.pr
imeFactorsList
· 使用定理 `List.mem_append_left`：∀ {α : Type u} {a : α} {as : List α} (bs : List α)
, a ∈ as → a ∈ as ++ bs
· 使用定理 `List.mem_append_right`：∀ {α : Type u} {b : α} (as : List α) {bs : List α
}, b ∈ bs → b ∈ as ++ bs
· 使用定理 `List.pmap_append`：∀ {ι : Type u_1} {α : Type u_2} {p : ι → Prop} {f : (a
 : ι) → p a → α} {l₁ l₂ : List ι} (h : ∀ a ∈ l₁ ++ l₂, p a),   List.pmap f (l₁ +
+ l₂) …
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `Int.instLawfulIdentityHMulOfNat`：Std.LawfulIdentity (fun x1 x2 => x1 * x
2) 1
· 使用定理 `Int.instAssociativeHMul`：Std.Associative fun x1 x2 => x1 * x2

--- 原说明 ---
The Jacobi symbol is multiplicative in its second argument.
-/
theorem mul_right' (a : ℤ) {b₁ b₂ : ℕ} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂) := by
  rw [jacobiSym, ((perm_primeFactorsList_mul hb₁ hb₂).pmap _).prod_eq, List.pmap_append,
    List.prod_append]
  pick_goal 2
  · exact fun p hp =>
      (List.mem_append.mp hp).elim prime_of_mem_primeFactorsList prime_of_mem_primeFactorsList
  · rfl

/-- The Jacobi symbol is multiplicative in its second argument. -/
/-
**jacobiSym.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：mul_right (a : Int) (b₁ b₂ : Nat) [NeZero b₁] [NeZero b₂] : J(a | b₁ * b₂)
 = J(a | b₁) * J(a | b₂)
参数：a : Int；b₁ b₂ : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `jacobiSym.mul_right'`：mul_right' (a : Int) {b₁ b₂ : Nat} (hb₁ : b₁ != 0)
 (hb₂ : b₂ != 0) : J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂)
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0

--- 原说明 ---
The Jacobi symbol is multiplicative in its second argument.
-/
theorem mul_right (a : ℤ) (b₁ b₂ : ℕ) [NeZero b₁] [NeZero b₂] :
    J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂) :=
  mul_right' a (NeZero.ne b₁) (NeZero.ne b₂)

/-- The Jacobi symbol takes only the values `0`, `1` and `-1`. -/
/-
**jacobiSym.trichotomy** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：trichotomy (a : Int) (b : Nat) : J(a | b) = 0 ∨ J(a | b) = 1 ∨ J(a | b) = 
-1
参数：a : Int；b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.list_prod_mem`：list_prod_mem {l : List M} (hl : forall x in l,
 x in s) : l.prod in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SignType.range_eq`：range_eq {α} (f : SignType -> α) : Set.range f = {f z
ero, f neg, f pos}
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a : 
α) → p a → β} {l : List α} {H : ∀ a ∈ l, p a} {b : β},   b ∈ List.pmap f l H ↔ ∃
 a,…
· 使用定理 `quadraticChar_isQuadratic`：quadraticChar_isQuadratic : (quadraticChar F)
.IsQuadratic
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)

--- 原说明 ---
The Jacobi symbol takes only the values `0`, `1` and `-1`.
-/
theorem trichotomy (a : ℤ) (b : ℕ) : J(a | b) = 0 ∨ J(a | b) = 1 ∨ J(a | b) = -1 :=
  ((MonoidHom.mrange (@SignType.castHom ℤ _ _).toMonoidHom).copy {0, 1, -1} <| by
    rw [Set.pair_comm]
    exact (SignType.range_eq SignType.castHom).symm).list_prod_mem
      (by
        intro _ ha'
        rcases List.mem_pmap.mp ha' with ⟨p, hp, rfl⟩
        have : Fact p.Prime := ⟨prime_of_mem_primeFactorsList hp⟩
        exact quadraticChar_isQuadratic (ZMod p) a)

/-- The symbol `J(1 | b)` has the value `1`. -/
@[simp]
/-
**jacobiSym.one_left** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：one_left (b : Nat) : J(1 | b) = 1
参数：b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.prod_eq_one`：∀ {M : Type u_4} [inst : Monoid M] {l : List M}, (∀ x 
∈ l, x = 1) → l.prod = 1
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a : 
α) → p a → β} {l : List α} {H : ∀ a ∈ l, p a} {b : β},   b ∈ List.pmap f l H ↔ ∃
 a,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `legendreSym.at_one`：at_one : legendreSym p 1 = 1

--- 原说明 ---
The symbol `J(1 | b)` has the value `1`.
-/
theorem one_left (b : ℕ) : J(1 | b) = 1 :=
  List.prod_eq_one fun z hz => by
    let ⟨p, hp, he⟩ := List.mem_pmap.1 hz
    rw [← he, legendreSym.at_one]

/-- The Jacobi symbol is multiplicative in its first argument. -/
/-
**jacobiSym.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：mul_left (a₁ a₂ : Int) (b : Nat) : J(a₁ * a₂ | b) = J(a₁ | b) * J(a₂ | b)
参数：a₁ a₂ : Int；b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.pmap_eq_map_attach`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} 
{f : (a : α) → p a → β} {l : List α} (H : ∀ a ∈ l, p a),   List.pmap f l H = Lis
t.map (fun x …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `legendreSym.mul`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a b : ℤ), legend
reSym p (a * b) = legendreSym p a * legendreSym p b
· 使用定理 `List.prod_map_mul`：prod_map_mul {M : Type*} [CommMonoid M] {l : List ι} 
{f g : ι -> M} : (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).pr
od

--- 原说明 ---
The Jacobi symbol is multiplicative in its first argument.
-/
theorem mul_left (a₁ a₂ : ℤ) (b : ℕ) : J(a₁ * a₂ | b) = J(a₁ | b) * J(a₂ | b) := by
  simp_rw [jacobiSym, List.pmap_eq_map_attach, legendreSym.mul]
  exact List.prod_map_mul (l := (primeFactorsList b).attach)
    (f := fun x ↦ @legendreSym x { out := prime_of_mem_primeFactorsList x.2 } a₁)
    (g := fun x ↦ @legendreSym x { out := prime_of_mem_primeFactorsList x.2 } a₂)

/-- The symbol `J(a | b)` vanishes iff `a` and `b` are not coprime (assuming `b ≠ 0`). -/
/-
**jacobiSym.eq_zero_iff_not_coprime** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：eq_zero_iff_not_coprime {a : Int} {b : Nat} [NeZero b] : J(a | b) = 0 ↔ a.
gcd b != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `List.prod_eq_zero_iff`：∀ {M₀ : Type u_4} [inst : MonoidWithZero M₀] [Non
trivial M₀] [NoZeroDivisors M₀] {l : List M₀}, l.prod = 0 ↔ 0 ∈ l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a : 
α) → p a → β} {l : List α} {H : ∀ a ∈ l, p a} {b : β},   b ∈ List.pmap f l H ↔ ∃
 a,…
· 使用定理 `Int.gcd_eq_natAbs`：gcd_eq_natAbs {a b : Int} : Int.gcd a b = Nat.gcd a.n
atAbs b.natAbs
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Nat.Prime.not_coprime_iff_dvd`：∀ {m n : ℕ}, ¬m.Coprime n ↔ ∃ p, Nat.Prim
e p ∧ p ∣ m ∧ p ∣ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `legendreSym.eq_zero_iff`：eq_zero_iff (a : Int) : legendreSym p a = 0 ↔ (
a : ZMod p) = 0
· 使用定理 `Nat.mem_primeFactorsList`：mem_primeFactorsList {n p} (hn : n != 0) : p i
n primeFactorsList n ↔ Prime p ∧ p ∣ n
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The symbol `J(a | b)` vanishes iff `a` and `b` are not coprime (assuming `b ≠ 0`
).
-/
theorem eq_zero_iff_not_coprime {a : ℤ} {b : ℕ} [NeZero b] : J(a | b) = 0 ↔ a.gcd b ≠ 1 :=
  List.prod_eq_zero_iff.trans
    (by
      rw [List.mem_pmap, Int.gcd_eq_natAbs, Ne, Prime.not_coprime_iff_dvd]
      simp_rw [legendreSym.eq_zero_iff _ _, intCast_zmod_eq_zero_iff_dvd,
        mem_primeFactorsList (NeZero.ne b), ← Int.natCast_dvd, Int.natCast_dvd_natCast, exists_prop,
        and_assoc, _root_.and_comm])

/-- The symbol `J(a | b)` is nonzero when `a` and `b` are coprime. -/
/-
**jacobiSym.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：∀ {a : ℤ} {b : ℕ}, a.gcd ↑b = 1 → jacobiSym a b ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `jacobiSym.zero_right`：zero_right (a : Int) : J(a | 0) = 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `jacobiSym.eq_zero_iff_not_coprime`：eq_zero_iff_not_coprime {a : Int} {b 
: Nat} [NeZero b] : J(a | b) = 0 ↔ a.gcd b != 1

--- 原说明 ---
The symbol `J(a | b)` is nonzero when `a` and `b` are coprime.
-/
protected theorem ne_zero {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a | b) ≠ 0 := by
  rcases eq_zero_or_neZero b with hb | _
  · rw [hb, zero_right]
    exact one_ne_zero
  · contrapose! h; exact eq_zero_iff_not_coprime.1 h

/-- The symbol `J(a | b)` vanishes if and only if `b ≠ 0` and `a` and `b` are not coprime. -/
/-
**jacobiSym.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：eq_zero_iff {a : Int} {b : Nat} : J(a | b) = 0 ↔ b != 0 ∧ a.gcd b != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `jacobiSym.zero_right`：zero_right (a : Int) : J(a | 0) = 1
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `jacobiSym.ne_zero`：∀ {a : ℤ} {b : ℕ}, a.gcd ↑b = 1 → jacobiSym a b ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `jacobiSym.eq_zero_iff_not_coprime`：eq_zero_iff_not_coprime {a : Int} {b 
: Nat} [NeZero b] : J(a | b) = 0 ↔ a.gcd b != 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neZero_iff`：∀ {R : Type u_1} [inst : Zero R] {n : R}, NeZero n ↔ n ≠ 0

--- 原说明 ---
The symbol `J(a | b)` vanishes if and only if `b ≠ 0` and `a` and `b` are not co
prime.
-/
theorem eq_zero_iff {a : ℤ} {b : ℕ} : J(a | b) = 0 ↔ b ≠ 0 ∧ a.gcd b ≠ 1 :=
  ⟨fun h => by
    rcases eq_or_ne b 0 with hb | hb
    · rw [hb, zero_right] at h; cases h
    exact ⟨hb, mt jacobiSym.ne_zero <| Classical.not_not.2 h⟩, fun ⟨hb, h⟩ => by
    rw [← neZero_iff] at hb; exact eq_zero_iff_not_coprime.2 h⟩

/-- The symbol `J(0 | b)` vanishes when `b > 1`. -/
/-
**jacobiSym.zero_left** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：zero_left {b : Nat} (hb : 1 < b) : J(0 | b) = 0
参数：hb : 1 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `jacobiSym.eq_zero_iff_not_coprime`：eq_zero_iff_not_coprime {a : Int} {b 
: Nat} [NeZero b] : J(a | b) = 0 ↔ a.gcd b != 1
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.gcd_zero_left`：∀ (a : ℤ), Int.gcd 0 a = a.natAbs
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
The symbol `J(0 | b)` vanishes when `b > 1`.
-/
theorem zero_left {b : ℕ} (hb : 1 < b) : J(0 | b) = 0 :=
  (@eq_zero_iff_not_coprime 0 b ⟨ne_zero_of_lt hb⟩).mpr <| by
    rw [Int.gcd_zero_left, Int.natAbs_natCast]; exact hb.ne'

/-- The symbol `J(a | b)` takes the value `1` or `-1` if `a` and `b` are coprime. -/
/-
**jacobiSym.eq_one_or_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：eq_one_or_neg_one {a : Int} {b : Nat} (h : a.gcd b = 1) : J(a | b) = 1 ∨ J
(a | b) = -1
参数：h : a.gcd b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `jacobiSym.trichotomy`：trichotomy (a : Int) (b : Nat) : J(a | b) = 0 ∨ J(
a | b) = 1 ∨ J(a | b) = -1
· 使用定理 `jacobiSym.ne_zero`：∀ {a : ℤ} {b : ℕ}, a.gcd ↑b = 1 → jacobiSym a b ≠ 0

--- 原说明 ---
The symbol `J(a | b)` takes the value `1` or `-1` if `a` and `b` are coprime.
-/
theorem eq_one_or_neg_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a | b) = 1 ∨ J(a | b) = -1 :=
  (trichotomy a b).resolve_left <| jacobiSym.ne_zero h

/-- We have that `J(a^e | b) = J(a | b)^e`. -/
/-
**jacobiSym.pow_left** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：pow_left (a : Int) (e b : Nat) : J(a ^ e | b) = J(a | b) ^ e
参数：a : Int；e b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `jacobiSym.one_left`：one_left (b : Nat) : J(1 | b) = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `jacobiSym.mul_left`：mul_left (a₁ a₂ : Int) (b : Nat) : J(a₁ * a₂ | b) = 
J(a₁ | b) * J(a₂ | b)

--- 原说明 ---
We have that `J(a^e | b) = J(a | b)^e`.
-/
theorem pow_left (a : ℤ) (e b : ℕ) : J(a ^ e | b) = J(a | b) ^ e :=
  Nat.recOn e (by rw [_root_.pow_zero, _root_.pow_zero, one_left]) fun _ ih => by
    rw [_root_.pow_succ, _root_.pow_succ, mul_left, ih]

/-- We have that `J(a | b^e) = J(a | b)^e`. -/
/-
**jacobiSym.pow_right** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：pow_right (a : Int) (b e : Nat) : J(a | b ^ e) = J(a | b) ^ e
参数：a : Int；b e : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_zero`：∀ (n : ℕ), n ^ 0 = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `jacobiSym.one_right`：one_right (a : Int) : J(a | 1) = 1
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `jacobiSym.zero_right`：zero_right (a : Int) : J(a | 0) = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `jacobiSym.mul_right`：mul_right (a : Int) (b₁ b₂ : Nat) [NeZero b₁] [NeZe
ro b₂] : J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂)
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)

--- 原说明 ---
We have that `J(a | b^e) = J(a | b)^e`.
-/
theorem pow_right (a : ℤ) (b e : ℕ) : J(a | b ^ e) = J(a | b) ^ e := by
  induction e with
  | zero => rw [Nat.pow_zero, _root_.pow_zero, one_right]
  | succ e ih =>
    rcases eq_zero_or_neZero b with hb | _
    · rw [hb, zero_pow e.succ_ne_zero, zero_right, one_pow]
    · rw [_root_.pow_succ, _root_.pow_succ, mul_right, ih]

/-- The square of `J(a | b)` is `1` when `a` and `b` are coprime. -/
/-
**jacobiSym.sq_one** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：sq_one {a : Int} {b : Nat} (h : a.gcd b = 1) : J(a | b) ^ 2 = 1
参数：h : a.gcd b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `jacobiSym.eq_one_or_neg_one`：eq_one_or_neg_one {a : Int} {b : Nat} (h : 
a.gcd b = 1) : J(a | b) = 1 ∨ J(a | b) = -1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The square of `J(a | b)` is `1` when `a` and `b` are coprime.
-/
theorem sq_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a | b) ^ 2 = 1 := by
  rcases eq_one_or_neg_one h with h₁ | h₁ <;> rw [h₁] <;> rfl

/-- The symbol `J(a^2 | b)` is `1` when `a` and `b` are coprime. -/
/-
**jacobiSym.sq_one'** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：sq_one' {a : Int} {b : Nat} (h : a.gcd b = 1) : J(a ^ 2 | b) = 1
参数：h : a.gcd b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `jacobiSym.pow_left`：pow_left (a : Int) (e b : Nat) : J(a ^ e | b) = J(a 
| b) ^ e
· 使用定理 `jacobiSym.sq_one`：sq_one {a : Int} {b : Nat} (h : a.gcd b = 1) : J(a | b
) ^ 2 = 1

--- 原说明 ---
The symbol `J(a^2 | b)` is `1` when `a` and `b` are coprime.
-/
theorem sq_one' {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a ^ 2 | b) = 1 := by rw [pow_left, sq_one h]

/-- The symbol `J(a | b)` depends only on `a` mod `b`. -/
/-
**jacobiSym.mod_left** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：mod_left (a : Int) (b : Nat) : J(a | b) = J(a % b | b)
参数：a : Int；b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `List.pmap_congr_left`：∀ {α : Type u_1} {β : Type u_2} {p q : α → Prop} {
f : (a : α) → p a → β} {g : (a : α) → q a → β} (l : List α)   {H₁ : ∀ a ∈ l, p a
} {H₂ : ∀ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `legendreSym.mod`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a : ℤ), legendre
Sym p a = legendreSym p (a % ↑p)
· 使用定理 `Int.emod_emod_of_dvd`：∀ (n : ℤ) {m k : ℤ}, m ∣ k → n % k % m = n % m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Nat.dvd_of_mem_primeFactorsList`：dvd_of_mem_primeFactorsList {n p : Nat}
 (h : p in n.primeFactorsList) : p ∣ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The symbol `J(a | b)` depends only on `a` mod `b`.
-/
theorem mod_left (a : ℤ) (b : ℕ) : J(a | b) = J(a % b | b) :=
  congr_arg List.prod <|
    List.pmap_congr_left _
      (by
        rintro p hp _ h₂
        conv_rhs =>
          rw [legendreSym.mod, Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.2 <|
            dvd_of_mem_primeFactorsList hp), ← legendreSym.mod])

/-- The symbol `J(a | b)` depends only on `a` mod `b`. -/
/-
**jacobiSym.mod_left'** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：mod_left' {a₁ a₂ : Int} {b : Nat} (h : a₁ % b = a₂ % b) : J(a₁ | b) = J(a₂
 | b)
参数：h : a₁ % b = a₂ % b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `jacobiSym.mod_left`：mod_left (a : Int) (b : Nat) : J(a | b) = J(a % b | 
b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The symbol `J(a | b)` depends only on `a` mod `b`.
-/
theorem mod_left' {a₁ a₂ : ℤ} {b : ℕ} (h : a₁ % b = a₂ % b) : J(a₁ | b) = J(a₂ | b) := by
  rw [mod_left, h, ← mod_left]

/-- If `p` is prime, `J(a | p) = -1` and `p` divides `x^2 - a*y^2`, then `p` must divide
`x` and `y`. -/
/-
**jacobiSym.prime_dvd_of_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：prime_dvd_of_eq_neg_one {p : Nat} [Fact p.Prime] {a : Int} (h : J(a | p) =
 -1) {x y : Int} (hxy : ↑p ∣ (x ^ 2 - a * y ^ 2 : Int)) : ↑p ∣ x ∧ ↑p ∣ y
参数：h : J(a | p) = -1；hxy : ↑p ∣ (x ^ 2 - a * y ^ 2 : Int)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `legendreSym.prime_dvd_of_eq_neg_one`：prime_dvd_of_eq_neg_one {p : Nat} [
Fact p.Prime] {a : Int} (h : legendreSym p a = -1) {x y : Int} (hxy : (p : Int) 
∣ x ^ 2 - a * y ^ 2) : ↑p…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `jacobiSym.legendreSym.to_jacobiSym`：∀ (p : ℕ) [fp : Fact (Nat.Prime p)] 
(a : ℤ), legendreSym p a = jacobiSym a p

--- 原说明 ---
If `p` is prime, `J(a | p) = -1` and `p` divides `x^2 - a*y^2`, then `p` must di
vide
`x` and `y`.
-/
theorem prime_dvd_of_eq_neg_one {p : ℕ} [Fact p.Prime] {a : ℤ} (h : J(a | p) = -1) {x y : ℤ}
    (hxy : ↑p ∣ (x ^ 2 - a * y ^ 2 : ℤ)) : ↑p ∣ x ∧ ↑p ∣ y := by
  rw [← legendreSym.to_jacobiSym] at h
  exact legendreSym.prime_dvd_of_eq_neg_one h hxy

/-- We can pull out a product over a list in the first argument of the Jacobi symbol. -/
/-
**jacobiSym.list_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：list_prod_left {l : List Int} {n : Nat} : J(l.prod | n) = (l.map fun a => 
J(a | n)).prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `jacobiSym.one_left`：one_left (b : Nat) : J(1 | b) = 1
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map.eq_2`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (head : α) (t
ail : List α),   List.map f (head :: tail) = f head :: List.map f tail
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `jacobiSym.mul_left`：mul_left (a₁ a₂ : Int) (b : Nat) : J(a₁ * a₂ | b) = 
J(a₁ | b) * J(a₂ | b)

--- 原说明 ---
We can pull out a product over a list in the first argument of the Jacobi symbol
.
-/
theorem list_prod_left {l : List ℤ} {n : ℕ} : J(l.prod | n) = (l.map fun a => J(a | n)).prod := by
  induction l with
  | nil => simp only [List.prod_nil, List.map_nil, one_left]
  | cons n l' ih => rw [List.map, List.prod_cons, List.prod_cons, mul_left, ih]

/-- We can pull out a product over a list in the second argument of the Jacobi symbol. -/
/-
**jacobiSym.list_prod_right** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：list_prod_right {a : Int} {l : List Nat} (hl : forall n in l, n != 0) : J(
a | l.prod) = (l.map fun n => J(a | n)).prod
参数：hl : forall n in l, n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `jacobiSym.one_right`：one_right (a : Int) : J(a | 1) = 1
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用引理 `List.prod_ne_zero`：prod_ne_zero (hL : (0 : M₀) ∉ l) : l.prod != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `List.map.eq_2`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (head : α) (t
ail : List α),   List.map f (head :: tail) = f head :: List.map f tail
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `jacobiSym.mul_right'`：mul_right' (a : Int) {b₁ b₂ : Nat} (hb₁ : b₁ != 0)
 (hb₂ : b₂ != 0) : J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂)

--- 原说明 ---
We can pull out a product over a list in the second argument of the Jacobi symbo
l.
-/
theorem list_prod_right {a : ℤ} {l : List ℕ} (hl : ∀ n ∈ l, n ≠ 0) :
    J(a | l.prod) = (l.map fun n => J(a | n)).prod := by
  induction l with
  | nil => simp only [List.prod_nil, one_right, List.map_nil]
  | cons n l' ih =>
    have hn := hl n List.mem_cons_self
    -- `n ≠ 0`
    have hl' := List.prod_ne_zero fun hf => hl 0 (List.mem_cons_of_mem _ hf) rfl
    -- `l'.prod ≠ 0`
    have h := fun m hm => hl m (List.mem_cons_of_mem _ hm)
    -- `∀ (m : ℕ), m ∈ l' → m ≠ 0`
    rw [List.map, List.prod_cons, List.prod_cons, mul_right' a hn hl', ih h]

/-- If `J(a | n) = -1`, then `n` has a prime divisor `p` such that `J(a | p) = -1`. -/
/-
**jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 
`jacobiSym`。
形式化陈述：eq_neg_one_at_prime_divisor_of_eq_neg_one {a : Int} {n : Nat} (h : J(a | n
) = -1) : exists p : Nat, p.Prime ∧ p ∣ n ∧ J(a | p) = -1
参数：h : J(a | n) = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharZero.eq_neg_self_iff`：∀ {R : Type u_2} [inst : NonAssocRing R] [NoZe
roDivisors R] [CharZero R] {a : R}, a = -a ↔ a = 0
· 使用定理 `jacobiSym.zero_right`：zero_right (a : Int) : J(a | 0) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Nat.pos_of_mem_primeFactorsList`：pos_of_mem_primeFactorsList {n p : Nat}
 (h : p in primeFactorsList n) : 0 < p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `List.neg_one_mem_of_prod_eq_neg_one`：neg_one_mem_of_prod_eq_neg_one {l :
 List Int} (h : l.prod = -1) : (-1 : Int) in l
· 使用定理 `jacobiSym.list_prod_right`：list_prod_right {a : Int} {l : List Nat} (hl 
: forall n in l, n != 0) : J(a | l.prod) = (l.map fun n => J(a | n)).prod
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Nat.dvd_of_mem_primeFactorsList`：dvd_of_mem_primeFactorsList {n p : Nat}
 (h : p in n.primeFactorsList) : p ∣ n

--- 原说明 ---
If `J(a | n) = -1`, then `n` has a prime divisor `p` such that `J(a | p) = -1`.
-/
theorem eq_neg_one_at_prime_divisor_of_eq_neg_one {a : ℤ} {n : ℕ} (h : J(a | n) = -1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ J(a | p) = -1 := by
  have hn₀ : n ≠ 0 := by
    rintro rfl
    rw [zero_right, CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h
  have hf₀ (p) (hp : p ∈ n.primeFactorsList) : p ≠ 0 := (Nat.pos_of_mem_primeFactorsList hp).ne.symm
  rw [← Nat.prod_primeFactorsList hn₀, list_prod_right hf₀] at h
  obtain ⟨p, hmem, hj⟩ := List.mem_map.mp (List.neg_one_mem_of_prod_eq_neg_one h)
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hmem, Nat.dvd_of_mem_primeFactorsList hmem, hj⟩

end jacobiSym

namespace ZMod

open jacobiSym

/-- If `J(a | b)` is `-1`, then `a` is not a square modulo `b`. -/
/-
**ZMod.nonsquare_of_jacobiSym_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：nonsquare_of_jacobiSym_eq_neg_one {a : Int} {b : Nat} (h : J(a | b) = -1) 
: ¬IsSquare (a : ZMod b)
参数：h : J(a | b) = -1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `jacobiSym.mod_left`：mod_left (a : Int) (b : Nat) : J(a | b) = J(a % b | 
b)
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `ZMod.intCast_eq_intCast_iff'`：intCast_eq_intCast_iff' (a b : Int) (c : N
at) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `ZMod.coe_valMinAbs`：∀ {n : ℕ} (x : ZMod n), ↑x.valMinAbs = x
· 使用定理 `jacobiSym.pow_left`：pow_left (a : Int) (e b : Nat) : J(a ^ e | b) = J(a 
| b) ^ e
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R

--- 原说明 ---
If `J(a | b)` is `-1`, then `a` is not a square modulo `b`.
-/
theorem nonsquare_of_jacobiSym_eq_neg_one {a : ℤ} {b : ℕ} (h : J(a | b) = -1) :
    ¬IsSquare (a : ZMod b) := fun ⟨r, ha⟩ => by
  rw [← r.coe_valMinAbs, ← Int.cast_mul, intCast_eq_intCast_iff', ← sq] at ha
  apply (by simp : ¬(0 : ℤ) ≤ -1)
  rw [← h, mod_left, ha, ← mod_left, pow_left]
  apply sq_nonneg

/-- If `p` is prime, then `J(a | p)` is `-1` iff `a` is not a square modulo `p`. -/
/-
**ZMod.nonsquare_iff_jacobiSym_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：nonsquare_iff_jacobiSym_eq_neg_one {a : Int} {p : Nat} [Fact p.Prime] : J(
a | p) = -1 ↔ ¬IsSquare (a : ZMod p)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `jacobiSym.legendreSym.to_jacobiSym`：∀ (p : ℕ) [fp : Fact (Nat.Prime p)] 
(a : ℤ), legendreSym p a = jacobiSym a p
· 使用定理 `legendreSym.eq_neg_one_iff`：eq_neg_one_iff {a : Int} : legendreSym p a =
 -1 ↔ ¬IsSquare (a : ZMod p)

--- 原说明 ---
If `p` is prime, then `J(a | p)` is `-1` iff `a` is not a square modulo `p`.
-/
theorem nonsquare_iff_jacobiSym_eq_neg_one {a : ℤ} {p : ℕ} [Fact p.Prime] :
    J(a | p) = -1 ↔ ¬IsSquare (a : ZMod p) := by
  rw [← legendreSym.to_jacobiSym]
  exact legendreSym.eq_neg_one_iff p

/-- If `p` is prime and `J(a | p) = 1`, then `a` is a square mod `p`. -/
/-
**ZMod.isSquare_of_jacobiSym_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isSquare_of_jacobiSym_eq_one {a : Int} {p : Nat} [Fact p.Prime] (h : J(a |
 p) = 1) : IsSquare (a : ZMod p)
参数：h : J(a | p) = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.nonsquare_iff_jacobiSym_eq_neg_one`：nonsquare_iff_jacobiSym_eq_neg_
one {a : Int} {p : Nat} [Fact p.Prime] : J(a | p) = -1 ↔ ¬IsSquare (a : ZMod p)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p

--- 原说明 ---
If `p` is prime and `J(a | p) = 1`, then `a` is a square mod `p`.
-/
theorem isSquare_of_jacobiSym_eq_one {a : ℤ} {p : ℕ} [Fact p.Prime] (h : J(a | p) = 1) :
    IsSquare (a : ZMod p) :=
  Classical.not_not.mp <| by rw [← nonsquare_iff_jacobiSym_eq_neg_one, h]; decide

end ZMod

/-!
### Values at `-1`, `2` and `-2`
-/


namespace jacobiSym

/-- If `χ` is a multiplicative function such that `J(a | p) = χ p` for all odd primes `p`,
then `J(a | b)` equals `χ b` for all odd natural numbers `b`. -/
/-
**jacobiSym.value_at** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：value_at (a : Int) {R : Type*} [Semiring R] (χ : R ->* Int) (hp : forall (
p : Nat) (pp : p.Prime), p != 2 -> @legendreSym p ⟨pp⟩ a = χ p) {b : Nat} (hb : 
Odd b) : J(a | b) = χ b
参数：a : Int；χ : R ->* Int；hp : forall (p : Nat) (pp : p.Prime), p != 2 -> @legend
reSym p ⟨pp⟩ a = χ p；hb : Odd b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Odd.pos`：Odd.pos [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
 [Nontrivial R] {a : R} : Odd a -> 0 < a
· 使用引理 `Nat.cast_list_prod`：cast_list_prod [Semiring R] (s : List Nat) : (↑s.pro
d : R) = (s.map (↑)).prod
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `jacobiSym.eq_1`：∀ (a : ℤ) (b : ℕ), jacobiSym a b = (List.pmap (fun p pp 
=> legendreSym p a) b.primeFactorsList ⋯).prod
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.pmap_eq_map`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : α 
→ β} {l : List α} (H : ∀ a ∈ l, p a),   List.pmap (fun a x => f a) l H = List.ma
p f l
· 使用定理 `List.pmap_congr_left`：∀ {α : Type u_1} {β : Type u_2} {p q : α → Prop} {
f : (a : α) → p a → β} {g : (a : α) → q a → β} (l : List α)   {H₁ : ∀ a ∈ l, p a
} {H₂ : ∀ …
· 使用引理 `Odd.ne_two_of_dvd_nat`：Odd.ne_two_of_dvd_nat {m n : Nat} (hn : Odd n) (h
m : m ∣ n) : m != 2
· 使用定理 `Nat.dvd_of_mem_primeFactorsList`：dvd_of_mem_primeFactorsList {n p : Nat}
 (h : p in n.primeFactorsList) : p ∣ n

--- 原说明 ---
If `χ` is a multiplicative function such that `J(a | p) = χ p` for all odd prime
s `p`,
then `J(a | b)` equals `χ b` for all odd natural numbers `b`.
-/
theorem value_at (a : ℤ) {R : Type*} [Semiring R] (χ : R →* ℤ)
    (hp : ∀ (p : ℕ) (pp : p.Prime), p ≠ 2 → @legendreSym p ⟨pp⟩ a = χ p) {b : ℕ} (hb : Odd b) :
    J(a | b) = χ b := by
  conv_rhs => rw [← prod_primeFactorsList hb.pos.ne', cast_list_prod, map_list_prod χ]
  rw [jacobiSym, List.map_map, ← List.pmap_eq_map
    fun _ => prime_of_mem_primeFactorsList]
  congr 1; apply List.pmap_congr_left
  exact fun p h pp _ => hp p pp (hb.ne_two_of_dvd_nat <| dvd_of_mem_primeFactorsList h)

/-- If `b` is odd, then `J(-1 | b)` is given by `χ₄ b`. -/
/-
**jacobiSym.at_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：at_neg_one {b : Nat} (hb : Odd b) : J(-1 | b) = χ₄ b
参数：hb : Odd b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `jacobiSym.value_at`：value_at (a : Int) {R : Type*} [Semiring R] (χ : R -
>* Int) (hp : forall (p : Nat) (pp : p.Prime), p != 2 -> @legendreSym p ⟨pp⟩ a =
 χ p) {b…
· 使用定理 `legendreSym.at_neg_one`：legendreSym.at_neg_one (hp : p != 2) : legendreS
ym p (-1) = χ₄ p

--- 原说明 ---
If `b` is odd, then `J(-1 | b)` is given by `χ₄ b`.
-/
theorem at_neg_one {b : ℕ} (hb : Odd b) : J(-1 | b) = χ₄ b :=
  -- Porting note: In mathlib3, it was written `χ₄` and Lean could guess that it had to use
  -- `χ₄.to_monoid_hom`. This is not the case with Lean 4.
  value_at (-1) χ₄.toMonoidHom (fun p pp => @legendreSym.at_neg_one p ⟨pp⟩) hb

/-- If `b` is odd, then `J(-a | b) = χ₄ b * J(a | b)`. -/
/-
**jacobiSym.neg** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：∀ (a : ℤ) {b : ℕ}, Odd b → jacobiSym (-a) b = ZMod.χ₄ ↑b * jacobiSym a b
参数：a : ℤ；-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_eq_neg_one_mul`：neg_eq_neg_one_mul (a : α) : -a = -1 * a
· 使用定理 `jacobiSym.mul_left`：mul_left (a₁ a₂ : Int) (b : Nat) : J(a₁ * a₂ | b) = 
J(a₁ | b) * J(a₂ | b)
· 使用定理 `jacobiSym.at_neg_one`：at_neg_one {b : Nat} (hb : Odd b) : J(-1 | b) = χ₄
 b

--- 原说明 ---
If `b` is odd, then `J(-a | b) = χ₄ b * J(a | b)`.
-/
protected theorem neg (a : ℤ) {b : ℕ} (hb : Odd b) : J(-a | b) = χ₄ b * J(a | b) := by
  rw [neg_eq_neg_one_mul, mul_left, at_neg_one hb]

/-- If `b` is odd, then `J(2 | b)` is given by `χ₈ b`. -/
/-
**jacobiSym.at_two** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：at_two {b : Nat} (hb : Odd b) : J(2 | b) = χ₈ b
参数：hb : Odd b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `jacobiSym.value_at`：value_at (a : Int) {R : Type*} [Semiring R] (χ : R -
>* Int) (hp : forall (p : Nat) (pp : p.Prime), p != 2 -> @legendreSym p ⟨pp⟩ a =
 χ p) {b…
· 使用定理 `legendreSym.at_two`：at_two (hp : p != 2) : legendreSym p 2 = χ₈ p

--- 原说明 ---
If `b` is odd, then `J(2 | b)` is given by `χ₈ b`.
-/
theorem at_two {b : ℕ} (hb : Odd b) : J(2 | b) = χ₈ b :=
  value_at 2 χ₈.toMonoidHom (fun p pp => @legendreSym.at_two p ⟨pp⟩) hb

/-- If `b` is odd, then `J(-2 | b)` is given by `χ₈' b`. -/
/-
**jacobiSym.at_neg_two** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：at_neg_two {b : Nat} (hb : Odd b) : J(-2 | b) = χ₈' b
参数：hb : Odd b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `jacobiSym.value_at`：value_at (a : Int) {R : Type*} [Semiring R] (χ : R -
>* Int) (hp : forall (p : Nat) (pp : p.Prime), p != 2 -> @legendreSym p ⟨pp⟩ a =
 χ p) {b…
· 使用定理 `legendreSym.at_neg_two`：at_neg_two (hp : p != 2) : legendreSym p (-2) = 
χ₈' p

--- 原说明 ---
If `b` is odd, then `J(-2 | b)` is given by `χ₈' b`.
-/
theorem at_neg_two {b : ℕ} (hb : Odd b) : J(-2 | b) = χ₈' b :=
  value_at (-2) χ₈'.toMonoidHom (fun p pp => @legendreSym.at_neg_two p ⟨pp⟩) hb
/-
**jacobiSym.div_four_left** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：div_four_left {a : Int} {b : Nat} (ha4 : a % 4 = 0) (hb2 : b % 2 = 1) : J(
a / 4 | b) = J(a | b)
参数：ha4 : a % 4 = 0；hb2 : b % 2 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.dvd_of_emod_eq_zero`：∀ {a b : ℤ}, b % a = 0 → a ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.gcd_natCast_natCast`：∀ (a b : ℕ), (↑a).gcd ↑b = a.gcd b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `Nat.gcd_add_mul_left_right`：∀ (m n k : ℕ), m.gcd (n + m * k) = m.gcd n
· 使用定理 `Nat.gcd_one_right`：∀ (n : ℕ), n.gcd 1 = 1
· 使用定理 `Int.mul_ediv_cancel_left`：∀ {a : ℤ} (b : ℤ), a ≠ 0 → a * b / a = b
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `jacobiSym.mul_left`：mul_left (a₁ a₂ : Int) (b : Nat) : J(a₁ * a₂ | b) = 
J(a₁ | b) * J(a₂ | b)
· 使用定理 `jacobiSym.sq_one'`：sq_one' {a : Int} {b : Nat} (h : a.gcd b = 1) : J(a ^
 2 | b) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem div_four_left {a : ℤ} {b : ℕ} (ha4 : a % 4 = 0) (hb2 : b % 2 = 1) :
    J(a / 4 | b) = J(a | b) := by
  obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero ha4
  have : Int.gcd (2 : ℕ) b = 1 := by
    rw [Int.gcd_natCast_natCast, ← b.mod_add_div 2, hb2, Nat.gcd_add_mul_left_right,
      Nat.gcd_one_right]
  rw [Int.mul_ediv_cancel_left _ (by decide), jacobiSym.mul_left,
    (by decide : (4 : ℤ) = (2 : ℕ) ^ 2), jacobiSym.sq_one' this, one_mul]

/-- If `b` is odd, then `J(4 | b) = 1`. -/
/-
**jacobiSym.at_four** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：at_four {b : Nat} (hb : Odd b) : J(4 | b) = 1
参数：hb : Odd b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `jacobiSym.div_four_left`：div_four_left {a : Int} {b : Nat} (ha4 : a % 4 
= 0) (hb2 : b % 2 = 1) : J(a / 4 | b) = J(a | b)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EuclideanDomain.div_self`：div_self {a : R} (a0 : a != 0) : a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `jacobiSym.one_left`：one_left (b : Nat) : J(1 | b) = 1

--- 原说明 ---
If `b` is odd, then `J(4 | b) = 1`.
-/
theorem at_four {b : ℕ} (hb : Odd b) : J(4 | b) = 1 := by
  have : J((4 : ℤ) | b) = J((4 : ℤ) / 4 | b) :=
    (div_four_left (by decide) (Nat.odd_iff.mp hb)).symm
  simpa [one_left]
/-
**jacobiSym.even_odd** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：even_odd {a : Int} {b : Nat} (ha2 : a % 2 = 0) (hb2 : b % 2 = 1) : (if b %
 8 = 3 ∨ b % 8 = 5 then -J(a / 2 | b) else J(a / 2 | b)) = J(a | b)
参数：ha2 : a % 2 = 0；hb2 : b % 2 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.dvd_of_emod_eq_zero`：∀ {a b : ℤ}, b % a = 0 → a ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.mul_ediv_cancel_left`：∀ {a : ℤ} (b : ℤ), a ≠ 0 → a * b / a = b
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `jacobiSym.mul_left`：mul_left (a₁ a₂ : Int) (b : Nat) : J(a₁ * a₂ | b) = 
J(a₁ | b) * J(a₂ | b)
· 使用定理 `jacobiSym.at_two`：at_two {b : Nat} (hb : Odd b) : J(2 | b) = χ₈ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1
· 使用定理 `ZMod.χ₈_nat_eq_if_mod_eight`：χ₈_nat_eq_if_mod_eight (n : Nat) : χ₈ n = i
f n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.mod_two_ne_zero`：∀ {n : ℕ}, n % 2 ≠ 0 ↔ n % 2 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem even_odd {a : ℤ} {b : ℕ} (ha2 : a % 2 = 0) (hb2 : b % 2 = 1) :
    (if b % 8 = 3 ∨ b % 8 = 5 then -J(a / 2 | b) else J(a / 2 | b)) = J(a | b) := by
  obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero ha2
  rw [Int.mul_ediv_cancel_left _ (by decide), jacobiSym.mul_left,
    jacobiSym.at_two (Nat.odd_iff.mpr hb2), ZMod.χ₈_nat_eq_if_mod_eight,
    if_neg (Nat.mod_two_ne_zero.mpr hb2)]
  grind

end jacobiSym

/-!
### Quadratic Reciprocity
-/


/-- The bi-multiplicative map giving the sign in the Law of Quadratic Reciprocity -/
/-
**qrSign** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：qrSign (m n : Nat) : Int
参数：m n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bi-multiplicative map giving the sign in the Law of Quadratic Reciprocity
-/
def qrSign (m n : ℕ) : ℤ :=
  J(χ₄ m | n)

namespace qrSign

/-- We can express `qrSign m n` as a power of `-1` when `m` and `n` are odd. -/
/-
**qrSign.neg_one_pow** 是 Mathlib 中的一个定理，位于命名空间 `qrSign`。
形式化陈述：neg_one_pow {m n : Nat} (hm : Odd m) (hn : Odd n) : qrSign m n = (-1) ^ (m
 / 2 * (n / 2))
参数：hm : Odd m；hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `qrSign.eq_1`：∀ (m n : ℕ), qrSign m n = jacobiSym (ZMod.χ₄ ↑m) n
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.χ₄_eq_neg_one_pow`：χ₄_eq_neg_one_pow {n : Nat} (hn : n % 2 = 1) : χ
₄ n = (-1) ^ (n / 2)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1
· 使用定理 `Nat.odd_mod_four_iff`：odd_mod_four_iff {n : Nat} : n % 2 = 1 ↔ n % 4 = 1
 ∨ n % 4 = 3
· 使用定理 `ZMod.χ₄_nat_one_mod_four`：χ₄_nat_one_mod_four {n : Nat} (hn : n % 4 = 1)
 : χ₄ n = 1
· 使用定理 `jacobiSym.one_left`：one_left (b : Nat) : J(1 | b) = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `ZMod.χ₄_nat_three_mod_four`：χ₄_nat_three_mod_four {n : Nat} (hn : n % 4 
= 3) : χ₄ n = -1
· 使用定理 `jacobiSym.at_neg_one`：at_neg_one {b : Nat} (hb : Odd b) : J(-1 | b) = χ₄
 b

--- 原说明 ---
We can express `qrSign m n` as a power of `-1` when `m` and `n` are odd.
-/
theorem neg_one_pow {m n : ℕ} (hm : Odd m) (hn : Odd n) :
    qrSign m n = (-1) ^ (m / 2 * (n / 2)) := by
  rw [qrSign, pow_mul, ← χ₄_eq_neg_one_pow (odd_iff.mp hm)]
  rcases odd_mod_four_iff.mp (odd_iff.mp hm) with h | h
  · rw [χ₄_nat_one_mod_four h, jacobiSym.one_left, one_pow]
  · rw [χ₄_nat_three_mod_four h, ← χ₄_eq_neg_one_pow (odd_iff.mp hn), jacobiSym.at_neg_one hn]

/-- When `m` and `n` are odd, then the square of `qrSign m n` is `1`. -/
/-
**qrSign.sq_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `qrSign`。
形式化陈述：sq_eq_one {m n : Nat} (hm : Odd m) (hn : Odd n) : qrSign m n ^ 2 = 1
参数：hm : Odd m；hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `qrSign.neg_one_pow`：neg_one_pow {m n : Nat} (hm : Odd m) (hn : Odd n) : 
qrSign m n = (-1) ^ (m / 2 * (n / 2))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `neg_one_sq`：neg_one_sq : (-1 : R) ^ 2 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a

--- 原说明 ---
When `m` and `n` are odd, then the square of `qrSign m n` is `1`.
-/
theorem sq_eq_one {m n : ℕ} (hm : Odd m) (hn : Odd n) : qrSign m n ^ 2 = 1 := by
  rw [neg_one_pow hm hn, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

/-- `qrSign` is multiplicative in the first argument. -/
/-
**qrSign.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `qrSign`。
形式化陈述：mul_left (m₁ m₂ n : Nat) : qrSign (m₁ * m₂) n = qrSign m₁ n * qrSign m₂ n
参数：m₁ m₂ n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `jacobiSym.mul_left`：mul_left (a₁ a₂ : Int) (b : Nat) : J(a₁ * a₂ | b) = 
J(a₁ | b) * J(a₂ | b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`qrSign` is multiplicative in the first argument.
-/
theorem mul_left (m₁ m₂ n : ℕ) : qrSign (m₁ * m₂) n = qrSign m₁ n * qrSign m₂ n := by
  simp_rw [qrSign, Nat.cast_mul, map_mul, jacobiSym.mul_left]

/-- `qrSign` is multiplicative in the second argument. -/
/-
**qrSign.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `qrSign`。
形式化陈述：mul_right (m n₁ n₂ : Nat) [NeZero n₁] [NeZero n₂] : qrSign m (n₁ * n₂) = q
rSign m n₁ * qrSign m n₂
参数：m n₁ n₂ : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `jacobiSym.mul_right`：mul_right (a : Int) (b₁ b₂ : Nat) [NeZero b₁] [NeZe
ro b₂] : J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂)

--- 原说明 ---
`qrSign` is multiplicative in the second argument.
-/
theorem mul_right (m n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] :
    qrSign m (n₁ * n₂) = qrSign m n₁ * qrSign m n₂ :=
  jacobiSym.mul_right (χ₄ m) n₁ n₂

/-- `qrSign` is symmetric when both arguments are odd. -/
/-
**qrSign.symm** 是 Mathlib 中的一个定理，位于命名空间 `qrSign`。
形式化陈述：∀ {m n : ℕ}, Odd m → Odd n → qrSign m n = qrSign n m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `qrSign.neg_one_pow`：neg_one_pow {m n : Nat} (hm : Odd m) (hn : Odd n) : 
qrSign m n = (-1) ^ (m / 2 * (n / 2))
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
`qrSign` is symmetric when both arguments are odd.
-/
protected theorem symm {m n : ℕ} (hm : Odd m) (hn : Odd n) : qrSign m n = qrSign n m := by
  rw [neg_one_pow hm hn, neg_one_pow hn hm, mul_comm (m / 2)]

/-- We can move `qrSign m n` from one side of an equality to the other when `m` and `n` are odd. -/
/-
**qrSign.eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `qrSign`。
形式化陈述：eq_iff_eq {m n : Nat} (hm : Odd m) (hn : Odd n) (x y : Int) : qrSign m n *
 x = y ↔ x = qrSign m n * y
参数：hm : Odd m；hn : Odd n；x y : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `qrSign.sq_eq_one`：sq_eq_one {m n : Nat} (hm : Odd m) (hn : Odd n) : qrSi
gn m n ^ 2 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
We can move `qrSign m n` from one side of an equality to the other when `m` and 
`n` are odd.
-/
theorem eq_iff_eq {m n : ℕ} (hm : Odd m) (hn : Odd n) (x y : ℤ) :
    qrSign m n * x = y ↔ x = qrSign m n * y := by
  refine
      ⟨fun h' =>
        let h := h'.symm
        ?_,
        fun h => ?_⟩ <;>
    rw [h, ← mul_assoc, ← pow_two, sq_eq_one hm hn, one_mul]

end qrSign

namespace jacobiSym

/-- The **Law of Quadratic Reciprocity for the Jacobi symbol**, version with `qrSign` -/
/-
**jacobiSym.quadratic_reciprocity'** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：quadratic_reciprocity' {a b : Nat} (ha : Odd a) (hb : Odd b) : J(a | b) = 
qrSign b a * J(b | a)
参数：ha : Odd a；hb : Odd b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `jacobiSym.one_left`：one_left (b : Nat) : J(1 | b) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `qrSign.mul_left`：mul_left (m₁ m₂ n : Nat) : qrSign (m₁ * m₂) n = qrSign 
m₁ n * qrSign m₂ n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `jacobiSym.mul_left`：mul_left (a₁ a₂ : Int) (b : Nat) : J(a₁ * a₂ | b) = 
J(a₁ | b) * J(a₂ | b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `jacobiSym.value_at`：value_at (a : Int) {R : Type*} [Semiring R] (χ : R -
>* Int) (hp : forall (p : Nat) (pp : p.Prime), p != 2 -> @legendreSym p ⟨pp⟩ a =
 χ p) {b…
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.Prime.eq_two_or_odd'`：∀ {p : ℕ}, Nat.Prime p → p = 2 ∨ Odd p
· 使用定理 `jacobiSym.legendreSym.to_jacobiSym`：∀ (p : ℕ) [fp : Fact (Nat.Prime p)] 
(a : ℤ), legendreSym p a = jacobiSym a p
· 使用定理 `Nat.cast_id`：Nat.cast_id (n : Nat) : n.cast = n
· 使用定理 `qrSign.eq_iff_eq`：eq_iff_eq {m n : Nat} (hm : Odd m) (hn : Odd n) (x y :
 Int) : qrSign m n * x = y ↔ x = qrSign m n * y
· 使用定理 `qrSign.symm`：∀ {m n : ℕ}, Odd m → Odd n → qrSign m n = qrSign n m
· 使用定理 `qrSign.neg_one_pow`：neg_one_pow {m n : Nat} (hm : Odd m) (hn : Odd n) : 
qrSign m n = (-1) ^ (m / 2 * (n / 2))
· 使用定理 `legendreSym.quadratic_reciprocity'`：quadratic_reciprocity' (hp : p != 2)
 (hq : q != 2) : legendreSym q p = (-1) ^ (p / 2 * (q / 2)) * legendreSym p q

--- 原说明 ---
The **Law of Quadratic Reciprocity for the Jacobi symbol**, version with `qrSign
`
-/
theorem quadratic_reciprocity' {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    J(a | b) = qrSign b a * J(b | a) := by
  -- define the right-hand side for fixed `a` as a `ℕ →* ℤ`
  let rhs : ℕ → ℕ →* ℤ := fun a =>
    { toFun := fun x => qrSign x a * J(x | a)
      map_one' := by convert! ← mul_one (M := ℤ) _; (on_goal 1 => symm); all_goals apply one_left
      map_mul' := fun x y => by
        simp_rw [qrSign.mul_left x y a, Nat.cast_mul, mul_left, mul_mul_mul_comm] }
  have rhs_apply : ∀ a b : ℕ, rhs a b = qrSign b a * J(b | a) := fun a b => rfl
  refine value_at a (rhs a) (fun p pp hp => Eq.symm ?_) hb
  have hpo := pp.eq_two_or_odd'.resolve_left hp
  rw [@legendreSym.to_jacobiSym p ⟨pp⟩, rhs_apply, Nat.cast_id, qrSign.eq_iff_eq hpo ha,
    qrSign.symm hpo ha]
  refine value_at p (rhs p) (fun q pq hq => ?_) ha
  have hqo := pq.eq_two_or_odd'.resolve_left hq
  rw [rhs_apply, Nat.cast_id, ← @legendreSym.to_jacobiSym p ⟨pp⟩, qrSign.symm hqo hpo,
    qrSign.neg_one_pow hpo hqo, @legendreSym.quadratic_reciprocity' p q ⟨pp⟩ ⟨pq⟩ hp hq]

/-- The Law of Quadratic Reciprocity for the Jacobi symbol -/
/-
**jacobiSym.quadratic_reciprocity** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：quadratic_reciprocity {a b : Nat} (ha : Odd a) (hb : Odd b) : J(a | b) = (
-1) ^ (a / 2 * (b / 2)) * J(b | a)
参数：ha : Odd a；hb : Odd b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `qrSign.neg_one_pow`：neg_one_pow {m n : Nat} (hm : Odd m) (hn : Odd n) : 
qrSign m n = (-1) ^ (m / 2 * (n / 2))
· 使用定理 `qrSign.symm`：∀ {m n : ℕ}, Odd m → Odd n → qrSign m n = qrSign n m
· 使用定理 `jacobiSym.quadratic_reciprocity'`：quadratic_reciprocity' {a b : Nat} (ha
 : Odd a) (hb : Odd b) : J(a | b) = qrSign b a * J(b | a)

--- 原说明 ---
The Law of Quadratic Reciprocity for the Jacobi symbol
-/
theorem quadratic_reciprocity {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    J(a | b) = (-1) ^ (a / 2 * (b / 2)) * J(b | a) := by
  rw [← qrSign.neg_one_pow ha hb, qrSign.symm ha hb, quadratic_reciprocity' ha hb]

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natural numbers
with `a % 4 = 1` and `b` odd, then `J(a | b) = J(b | a)`. -/
/-
**jacobiSym.quadratic_reciprocity_one_mod_four** 是 Mathlib 中的一个定理，位于命名空间 `jacobi
Sym`。
形式化陈述：quadratic_reciprocity_one_mod_four {a b : Nat} (ha : a % 4 = 1) (hb : Odd 
b) : J(a | b) = J(b | a)
参数：ha : a % 4 = 1；hb : Odd b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `jacobiSym.quadratic_reciprocity`：quadratic_reciprocity {a b : Nat} (ha :
 Odd a) (hb : Odd b) : J(a | b) = (-1) ^ (a / 2 * (b / 2)) * J(b | a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1
· 使用定理 `Nat.odd_of_mod_four_eq_one`：odd_of_mod_four_eq_one {n : Nat} : n % 4 = 1
 -> n % 2 = 1
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `ZMod.neg_one_pow_div_two_of_one_mod_four`：neg_one_pow_div_two_of_one_mod
_four {n : Nat} (hn : n % 4 = 1) : (-1 : Int) ^ (n / 2) = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natur
al numbers
with `a % 4 = 1` and `b` odd, then `J(a | b) = J(b | a)`.
-/
theorem quadratic_reciprocity_one_mod_four {a b : ℕ} (ha : a % 4 = 1) (hb : Odd b) :
    J(a | b) = J(b | a) := by
  rw [quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb, pow_mul,
    neg_one_pow_div_two_of_one_mod_four ha, one_pow, one_mul]

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natural numbers
with `a` odd and `b % 4 = 1`, then `J(a | b) = J(b | a)`. -/
/-
**jacobiSym.quadratic_reciprocity_one_mod_four'** 是 Mathlib 中的一个定理，位于命名空间 `jacob
iSym`。
形式化陈述：quadratic_reciprocity_one_mod_four' {a b : Nat} (ha : Odd a) (hb : b % 4 =
 1) : J(a | b) = J(b | a)
参数：ha : Odd a；hb : b % 4 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `jacobiSym.quadratic_reciprocity_one_mod_four`：quadratic_reciprocity_one_
mod_four {a b : Nat} (ha : a % 4 = 1) (hb : Odd b) : J(a | b) = J(b | a)

--- 原说明 ---
The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natur
al numbers
with `a` odd and `b % 4 = 1`, then `J(a | b) = J(b | a)`.
-/
theorem quadratic_reciprocity_one_mod_four' {a b : ℕ} (ha : Odd a) (hb : b % 4 = 1) :
    J(a | b) = J(b | a) :=
  (quadratic_reciprocity_one_mod_four hb ha).symm

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natural numbers
both congruent to `3` mod `4`, then `J(a | b) = -J(b | a)`. -/
/-
**jacobiSym.quadratic_reciprocity_three_mod_four** 是 Mathlib 中的一个定理，位于命名空间 `jaco
biSym`。
形式化陈述：quadratic_reciprocity_three_mod_four {a b : Nat} (ha : a % 4 = 3) (hb : b 
% 4 = 3) : J(a | b) = -J(b | a)
参数：ha : a % 4 = 3；hb : b % 4 = 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.neg_one_pow_div_two_of_three_mod_four`：neg_one_pow_div_two_of_three
_mod_four {n : Nat} (hn : n % 4 = 3) : (-1 : Int) ^ (n / 2) = -1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `jacobiSym.quadratic_reciprocity`：quadratic_reciprocity {a b : Nat} (ha :
 Odd a) (hb : Odd b) : J(a | b) = (-1) ^ (a / 2 * (b / 2)) * J(b | a)
· 使用引理 `Nat.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1
· 使用定理 `Nat.odd_of_mod_four_eq_three`：odd_of_mod_four_eq_three {n : Nat} : n % 4
 = 3 -> n % 2 = 1
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a

--- 原说明 ---
The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natur
al numbers
both congruent to `3` mod `4`, then `J(a | b) = -J(b | a)`.
-/
theorem quadratic_reciprocity_three_mod_four {a b : ℕ} (ha : a % 4 = 3) (hb : b % 4 = 3) :
    J(a | b) = -J(b | a) := by
  let nop := @neg_one_pow_div_two_of_three_mod_four
  rw [quadratic_reciprocity, pow_mul, nop ha, nop hb, neg_one_mul] <;>
    rwa [odd_iff, odd_of_mod_four_eq_three]
/-
**jacobiSym.quadratic_reciprocity_if** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：quadratic_reciprocity_if {a b : Nat} (ha2 : a % 2 = 1) (hb2 : b % 2 = 1) :
 (if a % 4 = 3 ∧ b % 4 = 3 then -J(b | a) else J(b | a)) = J(a | b)
参数：ha2 : a % 2 = 1；hb2 : b % 2 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.odd_mod_four_iff`：odd_mod_four_iff {n : Nat} : n % 2 = 1 ↔ n % 4 = 1
 ∨ n % 4 = 3
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `jacobiSym.quadratic_reciprocity_one_mod_four'`：quadratic_reciprocity_one
_mod_four' {a b : Nat} (ha : Odd a) (hb : b % 4 = 1) : J(a | b) = J(b | a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `jacobiSym.quadratic_reciprocity_one_mod_four`：quadratic_reciprocity_one_
mod_four {a b : Nat} (ha : a % 4 = 1) (hb : Odd b) : J(a | b) = J(b | a)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `jacobiSym.quadratic_reciprocity_three_mod_four`：quadratic_reciprocity_th
ree_mod_four {a b : Nat} (ha : a % 4 = 3) (hb : b % 4 = 3) : J(a | b) = -J(b | a
)
-/
theorem quadratic_reciprocity_if {a b : ℕ} (ha2 : a % 2 = 1) (hb2 : b % 2 = 1) :
    (if a % 4 = 3 ∧ b % 4 = 3 then -J(b | a) else J(b | a)) = J(a | b) := by
  rcases Nat.odd_mod_four_iff.mp ha2 with ha1 | ha3
  · simpa [ha1] using jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hb2) ha1
  rcases Nat.odd_mod_four_iff.mp hb2 with hb1 | hb3
  · simpa [hb1] using jacobiSym.quadratic_reciprocity_one_mod_four hb1 (Nat.odd_iff.mpr ha2)
  simpa [ha3, hb3] using (jacobiSym.quadratic_reciprocity_three_mod_four ha3 hb3).symm

/-- The Jacobi symbol `J(a | b)` depends only on `b` mod `4*a` (version for `a : ℕ`). -/
/-
**jacobiSym.mod_right'** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：mod_right' (a : Nat) {b : Nat} (hb : Odd b) : J(a | b) = J(a | b % (4 * a)
)
参数：a : Nat；hb : Odd b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Odd.mod_even`：Odd.mod_even (hn : Odd n) (ha : Even a) : Odd (n % a)
· 使用定理 `Even.mul_right`：∀ {α : Type u_2} [inst : Add α] [inst_1 : Mul α] {a : α}
 [RightDistribClass α], Even a → ∀ (b : α), Even (a * b)
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.exists_eq_pow_mul_and_not_dvd`：exists_eq_pow_mul_and_not_dvd {n : Na
t} (hn : n != 0) (p : Nat) (hp : p != 1) : exists e n' : Nat, ¬p ∣ n' ∧ n = p ^ 
e * n'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.two_dvd_ne_zero`：∀ {n : ℕ}, ¬2 ∣ n ↔ n % 2 = 1
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `jacobiSym.mul_left`：mul_left (a₁ a₂ : Int) (b : Nat) : J(a₁ * a₂ | b) = 
J(a₁ | b) * J(a₂ | b)
· 使用定理 `jacobiSym.quadratic_reciprocity'`：quadratic_reciprocity' {a b : Nat} (ha
 : Odd a) (hb : Odd b) : J(a | b) = qrSign b a * J(b | a)
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `jacobiSym.pow_left`：pow_left (a : Int) (e b : Nat) : J(a ^ e | b) = J(a 
| b) ^ e
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `jacobiSym.at_two`：at_two {b : Nat} (hb : Odd b) : J(2 | b) = χ₈ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZMod.χ₈_apply`：∀ (a : ZMod 8),   ZMod.χ₈ a =     match a with     | 0 =>
 0     | 2 => 0     | 4 => 0     | 6 => 0     | 1 => 1     | 7 => 1     | 3 => -
1  …
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
The Jacobi symbol `J(a | b)` depends only on `b` mod `4*a` (version for `a : ℕ`)
.
-/
theorem mod_right' (a : ℕ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a)) := by
  rcases eq_or_ne a 0 with (rfl | ha₀)
  · rw [mul_zero, mod_zero]
  have hb' : Odd (b % (4 * a)) := hb.mod_even (Even.mul_right (by decide) _)
  rcases exists_eq_pow_mul_and_not_dvd ha₀ 2 (by simp) with ⟨e, a', ha₁', ha₂⟩
  have ha₁ := odd_iff.mpr (two_dvd_ne_zero.mp ha₁')
  nth_rw 2 [ha₂]; nth_rw 1 [ha₂]
  rw [Nat.cast_mul, mul_left, mul_left, quadratic_reciprocity' ha₁ hb,
    quadratic_reciprocity' ha₁ hb', Nat.cast_pow, pow_left, pow_left, Nat.cast_two, at_two hb,
    at_two hb']
  congr 1; swap
  · congr 1
    · simp_rw [qrSign]
      rw [χ₄_nat_mod_four, χ₄_nat_mod_four (b % (4 * a)), mod_mod_of_dvd b (dvd_mul_right 4 a)]
    · rw [mod_left ↑(b % _), mod_left b, Int.natCast_mod, Int.emod_emod_of_dvd b]
      simp only [ha₂, Nat.cast_mul, ← mul_assoc]
      apply dvd_mul_left
  rcases e with - | e; · simp
  · rw [χ₈_nat_mod_eight, χ₈_nat_mod_eight (b % (4 * a)), mod_mod_of_dvd b]
    use 2 ^ e * a'; rw [ha₂, Nat.pow_succ]; ring

/-- The Jacobi symbol `J(a | b)` depends only on `b` mod `4*a`. -/
/-
**jacobiSym.mod_right** 是 Mathlib 中的一个定理，位于命名空间 `jacobiSym`。
形式化陈述：mod_right (a : Int) {b : Nat} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.n
atAbs))
参数：a : Int；hb : Odd b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_eq`：∀ (a : ℤ), a = ↑a.natAbs ∨ a = -↑a.natAbs
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `jacobiSym.mod_right'`：mod_right' (a : Nat) {b : Nat} (hb : Odd b) : J(a 
| b) = J(a | b % (4 * a))
· 使用引理 `Odd.mod_even`：Odd.mod_even (hn : Odd n) (ha : Even a) : Odd (n % a)
· 使用定理 `Even.mul_right`：∀ {α : Type u_2} [inst : Add α] [inst_1 : Mul α] {a : α}
 [RightDistribClass α], Even a → ∀ (b : α), Even (a * b)
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `jacobiSym.neg`：∀ (a : ℤ) {b : ℕ}, Odd b → jacobiSym (-a) b = ZMod.χ₄ ↑b 
* jacobiSym a b
· 使用定理 `ZMod.χ₄_nat_mod_four`：χ₄_nat_mod_four (n : Nat) : χ₄ n = χ₄ (n % 4 : Nat
)
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b

--- 原说明 ---
The Jacobi symbol `J(a | b)` depends only on `b` mod `4*a`.
-/
theorem mod_right (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  rcases Int.natAbs_eq a with ha | ha <;> nth_rw 2 [ha] <;> nth_rw 1 [ha]
  · exact mod_right' a.natAbs hb
  · have hb' : Odd (b % (4 * a.natAbs)) := hb.mod_even (Even.mul_right (by decide) _)
    rw [jacobiSym.neg _ hb, jacobiSym.neg _ hb', mod_right' _ hb, χ₄_nat_mod_four,
      χ₄_nat_mod_four (b % (4 * _)), mod_mod_of_dvd b (dvd_mul_right 4 _)]

end jacobiSym

end Jacobi


section FastJacobi

/-!
### Fast computation of the Jacobi symbol
We follow the implementation as in `Mathlib/Tactic/NormNum/LegendreSymbol.lean`.
-/

-- `fastLegendreSym` is used for computing the Legendre symbol in a `norm_num` extension,
-- i.e. needs to be used publicly.
set_option backward.privateInPublic true

open NumberTheorySymbols jacobiSym

/-- Computes `J(a | b)` (or `-J(a | b)` if `flip` is set to `true`) given assumptions, by reducing
`a` to odd by repeated division and then using quadratic reciprocity to swap `a`, `b`. -/
/-
**fastJacobiSymAux** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computes `J(a | b)` (or `-J(a | b)` if `flip` is set to `true`) given assumption
s, by reducing
`a` to odd by repeated division and then using quadratic reciprocity to swap `a`
, `b`.
-/
private def fastJacobiSymAux (a b : ℕ) (flip : Bool) (ha0 : a > 0) : ℤ :=
  if ha4 : a % 4 = 0 then
    fastJacobiSymAux (a / 4) b flip
      (Nat.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero ha4)) (by decide))
  else if ha2 : a % 2 = 0 then
    fastJacobiSymAux (a / 2) b (xor (b % 8 = 3 ∨ b % 8 = 5) flip)
      (Nat.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero ha2)) (by decide))
  else if ha1 : a = 1 then
    if flip then -1 else 1
  else if hba : b % a = 0 then
    0
  else
    fastJacobiSymAux (b % a) a (xor (a % 4 = 3 ∧ b % 4 = 3) flip) (Nat.pos_of_ne_zero hba)
termination_by a
decreasing_by
  · exact a.div_lt_self ha0 (by decide)
  · exact a.div_lt_self ha0 (by decide)
  · exact b.mod_lt ha0
/-
**fastJacobiSymAux.eq_jacobiSym** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem fastJacobiSymAux.eq_jacobiSym {a b : ℕ} {flip : Bool} {ha0 : a > 0}
    (hb2 : b % 2 = 1) (hb1 : b > 1) :
    fastJacobiSymAux a b flip ha0 = if flip then -J(a | b) else J(a | b) := by
  induction a using Nat.strongRecOn generalizing b flip with | ind a IH =>
  unfold fastJacobiSymAux
  split <;> rename_i ha4
  · rw [IH (a / 4) (a.div_lt_self ha0 (by decide)) hb2 hb1]
    simp only [Int.natCast_ediv, Nat.cast_ofNat, div_four_left (a := a) (mod_cast ha4) hb2]
  split <;> rename_i ha2
  · rw [IH (a / 2) (a.div_lt_self ha0 (by decide)) hb2 hb1]
    simp only [Int.natCast_ediv, Nat.cast_ofNat, ← even_odd (a := a) (mod_cast ha2) hb2]
    by_cases h : b % 8 = 3 ∨ b % 8 = 5 <;> simp [h]; cases flip <;> simp
  split <;> rename_i ha1
  · subst ha1; simp
  split <;> rename_i hba
  · suffices J(a | b) = 0 by simp [this]
    refine eq_zero_iff.mpr ⟨fun h ↦ absurd (h ▸ hb1) (by decide), ?_⟩
    rwa [Int.gcd_natCast_natCast, Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero hba)]
  rw [IH (b % a) (b.mod_lt ha0) (Nat.mod_two_ne_zero.mp ha2) (lt_of_le_of_ne ha0 (Ne.symm ha1))]
  simp only [Int.natCast_mod, ← mod_left]
  rw [← quadratic_reciprocity_if (Nat.mod_two_ne_zero.mp ha2) hb2]
  by_cases h : a % 4 = 3 ∧ b % 4 = 3 <;> simp [h]; cases flip <;> simp

/-- Computes `J(a | b)` by reducing `b` to odd by repeated division and then using
`fastJacobiSymAux`. -/
/-
**fastJacobiSym** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computes `J(a | b)` by reducing `b` to odd by repeated division and then using
`fastJacobiSymAux`.
-/
private def fastJacobiSym (a : ℤ) (b : ℕ) : ℤ :=
  if hb0 : b = 0 then
    1
  else if _ : b % 2 = 0 then
    if a % 2 = 0 then
      0
    else
      have : b / 2 < b := b.div_lt_self (Nat.pos_of_ne_zero hb0) one_lt_two
      fastJacobiSym a (b / 2)
  else if b = 1 then
    1
  else if hab : a % b = 0 then
    0
  else
    fastJacobiSymAux (a % b).natAbs b false (Int.natAbs_pos.mpr hab)

set_option backward.privateInPublic.warn false in
/-
**fastJacobiSym.eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[csimp] private theorem fastJacobiSym.eq : jacobiSym = fastJacobiSym := by
  ext a b
  induction b using Nat.strongRecOn with | ind b IH =>
  unfold fastJacobiSym
  split_ifs with hb0 hb2 ha2 hb1 hab
  · rw [hb0, zero_right]
  · refine eq_zero_iff.mpr ⟨hb0, ne_of_gt ?_⟩
    refine Nat.le_of_dvd (Int.gcd_pos_iff.mpr (mod_cast .inr hb0)) ?_
    refine Nat.dvd_gcd (Int.ofNat_dvd_left.mp (Int.dvd_of_emod_eq_zero ha2)) ?_
    exact Int.ofNat_dvd_left.mp (Int.dvd_of_emod_eq_zero (mod_cast hb2))
  · dsimp only
    rw [← IH (b / 2) (b.div_lt_self (Nat.pos_of_ne_zero hb0) one_lt_two)]
    obtain ⟨b, rfl⟩ := Nat.dvd_of_mod_eq_zero hb2
    rw [mul_right' a (by decide) fun h ↦ hb0 (mul_eq_zero_of_right 2 h),
      b.mul_div_cancel_left (by decide), mod_left a 2, Nat.cast_ofNat,
      Int.emod_two_ne_zero.mp ha2, one_left, one_mul]
  · rw [hb1, one_right]
  · rw [mod_left, hab, zero_left (lt_of_le_of_ne (Nat.pos_of_ne_zero hb0) (Ne.symm hb1))]
  · rw [fastJacobiSymAux.eq_jacobiSym, if_neg Bool.false_ne_true, mod_left a b,
      Int.natAbs_of_nonneg (a.emod_nonneg (mod_cast hb0))]
    · exact Nat.mod_two_ne_zero.mp hb2
    · exact lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hb0) (Ne.symm hb1)

/-- Computes `legendreSym p a` using `fastJacobiSym`. -/
@[inline, nolint unusedArguments]
/-
**fastLegendreSym** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computes `legendreSym p a` using `fastJacobiSym`.
-/
private def fastLegendreSym (p : ℕ) [Fact p.Prime] (a : ℤ) : ℤ := J(a | p)

set_option backward.privateInPublic.warn false in
/-
**fastLegendreSym.eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[csimp] private theorem fastLegendreSym.eq : legendreSym = fastLegendreSym := by
  ext p _ a; rw [legendreSym.to_jacobiSym, fastLegendreSym]

end FastJacobi

