/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Degree
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Degrees of polynomials

This file establishes many results about the degree of a multivariate polynomial.

The *degree set* of a polynomial $P \in R[X]$ is a `Multiset` containing, for each $x$ in the
variable set, $n$ copies of $x$, where $n$ is the maximum number of copies of $x$ appearing in a
monomial of $P$.

## Main declarations

* `MvPolynomial.degrees p` : the multiset of variables representing the union of the multisets
  corresponding to each non-zero monomial in `p`.
  For example if `7 ≠ 0` in `R` and `p = x²y+7y³` then `degrees p = {x, x, y, y, y}`

* `MvPolynomial.degreeOf n p : ℕ` : the total degree of `p` with respect to the variable `n`.
  For example if `p = x⁴y+yz` then `degreeOf y p = 1`.

* `MvPolynomial.totalDegree p : ℕ` :
  the max of the sizes of the multisets `s` whose monomials `X^s` occur in `p`.
  For example if `p = x⁴y+yz` then `totalDegree p = 5`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`.

+ `r : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

-/

@[expose] public section


noncomputable section

open Set Function Finsupp AddMonoidAlgebra

universe u v w

variable {R : Type u} {S : Type v}

namespace MvPolynomial

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] {p q : MvPolynomial σ R}

section Degrees

/-! ### `degrees` -/


/-- The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset.

(For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
-/
/-
**MvPolynomial.degrees** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：degrees (p : MvPolynomial σ R) : Multiset σ
参数：p : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal degrees of each variable in a multi-variable polynomial, expressed a
s a multiset.

(For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
-/
def degrees (p : MvPolynomial σ R) : Multiset σ :=
  letI := Classical.decEq σ
  p.support.sup fun s : σ →₀ ℕ => toMultiset s
/-
**MvPolynomial.degrees_def** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_def [DecidableEq σ] (p : MvPolynomial σ R) : p.degrees = p.support
.sup fun s : σ ->₀ Nat => Finsupp.toMultiset s
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degrees.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : CommSem
iring R] (p : MvPolynomial σ R),   p.degrees = p.support.sup fun s => Finsupp.to
Multiset s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem degrees_def [DecidableEq σ] (p : MvPolynomial σ R) :
    p.degrees = p.support.sup fun s : σ →₀ ℕ => Finsupp.toMultiset s := by rw [degrees]; convert!
      rfl
/-
**MvPolynomial.degrees_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_monomial (s : σ ->₀ Nat) (a : R) : degrees (monomial s a) <= toMul
tiset s
参数：s : σ ->₀ Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `AddMonoidAlgebra.supDegree_single`：supDegree_single (a : A) (r : R) : (s
ingle a r).supDegree D = if r = 0 then ⊥ else D a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem degrees_monomial (s : σ →₀ ℕ) (a : R) : degrees (monomial s a) ≤ toMultiset s := by
  classical
    refine (supDegree_single s a).trans_le ?_
    split_ifs
    exacts [bot_le, le_rfl]
/-
**MvPolynomial.degrees_monomial_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_monomial_eq (s : σ ->₀ Nat) (a : R) (ha : a != 0) : degrees (monom
ial s a) = toMultiset s
参数：s : σ ->₀ Nat；a : R；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddMonoidAlgebra.supDegree_single`：supDegree_single (a : A) (r : R) : (s
ingle a r).supDegree D = if r = 0 then ⊥ else D a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem degrees_monomial_eq (s : σ →₀ ℕ) (a : R) (ha : a ≠ 0) :
    degrees (monomial s a) = toMultiset s := by
  classical
    exact (supDegree_single s a).trans (if_neg ha)
/-
**MvPolynomial.degrees_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_C (a : R) : degrees (C a : MvPolynomial σ R) = 0
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.le_zero`：le_zero : s <= 0 ↔ s = 0
· 使用定理 `MvPolynomial.degrees_monomial`：degrees_monomial (s : σ ->₀ Nat) (a : R) 
: degrees (monomial s a) <= toMultiset s
-/
theorem degrees_C (a : R) : degrees (C a : MvPolynomial σ R) = 0 :=
  Multiset.le_zero.1 <| degrees_monomial _ _
/-
**MvPolynomial.degrees_X'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_X' (n : σ) : degrees (X n : MvPolynomial σ R) <= {n}
参数：n : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MvPolynomial.degrees_monomial`：degrees_monomial (s : σ ->₀ Nat) (a : R) 
: degrees (monomial s a) <= toMultiset s
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finsupp.toMultiset_single`：toMultiset_single (a : α) (n : Nat) : toMulti
set (single a n) = n • {a}
-/
theorem degrees_X' (n : σ) : degrees (X n : MvPolynomial σ R) ≤ {n} :=
  le_trans (degrees_monomial _ _) <| le_of_eq <| toMultiset_single _ _

@[simp]
/-
**MvPolynomial.degrees_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_X [Nontrivial R] (n : σ) : degrees (X n : MvPolynomial σ R) = {n}
参数：n : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.degrees_monomial_eq`：degrees_monomial_eq (s : σ ->₀ Nat) (a
 : R) (ha : a != 0) : degrees (monomial s a) = toMultiset s
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Finsupp.toMultiset_single`：toMultiset_single (a : α) (n : Nat) : toMulti
set (single a n) = n • {a}
-/
theorem degrees_X [Nontrivial R] (n : σ) : degrees (X n : MvPolynomial σ R) = {n} :=
  (degrees_monomial_eq _ (1 : R) one_ne_zero).trans (toMultiset_single _ _)

@[simp]
/-
**MvPolynomial.degrees_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_zero : degrees (0 : MvPolynomial σ R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.C_0`：C_0 : C 0 = (0 : MvPolynomial σ R)
· 使用定理 `MvPolynomial.degrees_C`：degrees_C (a : R) : degrees (C a : MvPolynomial 
σ R) = 0
-/
theorem degrees_zero : degrees (0 : MvPolynomial σ R) = 0 := by
  rw [← C_0]
  exact degrees_C 0

@[simp]
/-
**MvPolynomial.degrees_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_one : degrees (1 : MvPolynomial σ R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.degrees_C`：degrees_C (a : R) : degrees (C a : MvPolynomial 
σ R) = 0
-/
theorem degrees_one : degrees (1 : MvPolynomial σ R) = 0 :=
  degrees_C 1
/-
**MvPolynomial.degrees_add_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_add_le [DecidableEq σ] {p q : MvPolynomial σ R} : (p + q).degrees 
<= p.degrees ⊔ q.degrees
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degrees_def`：degrees_def [DecidableEq σ] (p : MvPolynomial 
σ R) : p.degrees = p.support.sup fun s : σ ->₀ Nat => Finsupp.toMultiset s
· 使用定理 `AddMonoidAlgebra.supDegree_add_le`：supDegree_add_le {f g : R[A]} : (f + 
g).supDegree D <= (f.supDegree D) ⊔ (g.supDegree D)
-/
theorem degrees_add_le [DecidableEq σ] {p q : MvPolynomial σ R} :
    (p + q).degrees ≤ p.degrees ⊔ q.degrees := by
  simp_rw [degrees_def]; exact supDegree_add_le
/-
**MvPolynomial.degrees_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_sum_le {ι : Type*} [DecidableEq σ] (s : Finset ι) (f : ι -> MvPoly
nomial σ R) : (∑ i in s, f i).degrees <= s.sup fun i => (f i).degrees
参数：s : Finset ι；f : ι -> MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degrees_def`：degrees_def [DecidableEq σ] (p : MvPolynomial 
σ R) : p.degrees = p.support.sup fun s : σ ->₀ Nat => Finsupp.toMultiset s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddMonoidAlgebra.supDegree_sum_le`：supDegree_sum_le {ι} {s : Finset ι} {
f : ι -> R[A]} : (∑ i in s, f i).supDegree D <= s.sup (fun i => (f i).supDegree 
D)
-/
theorem degrees_sum_le {ι : Type*} [DecidableEq σ] (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (∑ i ∈ s, f i).degrees ≤ s.sup fun i => (f i).degrees := by
  simp_rw [degrees_def]; exact supDegree_sum_le
/-
**MvPolynomial.degrees_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_mul_le {p q : MvPolynomial σ R} : (p * q).degrees <= p.degrees + q
.degrees
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degrees_def`：degrees_def [DecidableEq σ] (p : MvPolynomial 
σ R) : p.degrees = p.support.sup fun s : σ ->₀ Nat => Finsupp.toMultiset s
· 使用定理 `AddMonoidAlgebra.supDegree_mul_le`：supDegree_mul_le (hadd : forall a1 a2
, D (a1 + a2) = D a1 + D a2) [AddLeftMono B] [AddRightMono B] : (p * q).supDegre
e D <= p.supDegree D + …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem degrees_mul_le {p q : MvPolynomial σ R} : (p * q).degrees ≤ p.degrees + q.degrees := by
  classical
  simp_rw [degrees_def]
  exact supDegree_mul_le (map_add _)
/-
**MvPolynomial.degrees_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_prod_le {ι : Type*} {s : Finset ι} {f : ι -> MvPolynomial σ R} : (
∏ i in s, f i).degrees <= ∑ i in s, (f i).degrees
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.supDegree_prod_le`：supDegree_prod_le {R A B : Type*} [C
ommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [SemilatticeSup B] [OrderBot 
B] [AddLeftMono B] [AddR…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
-/
theorem degrees_prod_le {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial σ R} :
    (∏ i ∈ s, f i).degrees ≤ ∑ i ∈ s, (f i).degrees := by
  classical exact supDegree_prod_le (map_zero _) (map_add _)
/-
**MvPolynomial.degrees_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_pow_le {p : MvPolynomial σ R} {n : Nat} : (p ^ n).degrees <= n • p
.degrees
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.degrees_prod_le`：degrees_prod_le {ι : Type*} {s : Finset ι}
 {f : ι -> MvPolynomial σ R} : (∏ i in s, f i).degrees <= ∑ i in s, (f i).degree
s
-/
theorem degrees_pow_le {p : MvPolynomial σ R} {n : ℕ} : (p ^ n).degrees ≤ n • p.degrees := by
  simpa using degrees_prod_le (s := .range n) (f := fun _ ↦ p)
/-
**MvPolynomial.mem_degrees** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_degrees {p : MvPolynomial σ R} {i : σ} : i in p.degrees ↔ exists d, p.
coeff d != 0 ∧ i in d.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.degrees_def`：degrees_def [DecidableEq σ] (p : MvPolynomial 
σ R) : p.degrees = p.support.sup fun s : σ ->₀ Nat => Finsupp.toMultiset s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_degrees {p : MvPolynomial σ R} {i : σ} :
    i ∈ p.degrees ↔ ∃ d, p.coeff d ≠ 0 ∧ i ∈ d.support := by
  classical
  simp only [degrees_def, Multiset.mem_sup, ← mem_support_iff, Finsupp.mem_toMultiset]
/-
**MvPolynomial.degrees_eq_zero_iff_support_subset_zero** 是 Mathlib 中的一个定理，位于命名空间
 `MvPolynomial`。
形式化陈述：degrees_eq_zero_iff_support_subset_zero : p.degrees = 0 ↔ p.support subset
eq {0}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.subset_singleton_iff'`：subset_singleton_iff' {s : Finset α} {a : 
α} : s subseteq {a} ↔ forall b in s, b = a
· 使用定理 `Multiset.eq_zero_iff_forall_notMem`：eq_zero_iff_forall_notMem {s : Multi
set α} : s = 0 ↔ forall a, a ∉ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.support_eq_empty`：support_eq_empty {f : α ->₀ M} : f.support = ∅
 ↔ f = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.mem_degrees`：mem_degrees {p : MvPolynomial σ R} {i : σ} : i
 in p.degrees ↔ exists d, p.coeff d != 0 ∧ i in d.support
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
-/
theorem degrees_eq_zero_iff_support_subset_zero : p.degrees = 0 ↔ p.support ⊆ {0} := by
  rw [Finset.subset_singleton_iff', Multiset.eq_zero_iff_forall_notMem]
  refine ⟨fun h s hs ↦ ?_, fun h i hi ↦ ?_⟩
  · rw [← Finsupp.support_eq_empty]
    simp only [mem_degrees] at h
    grind
  rcases mem_degrees.mp hi with ⟨s, hs1, hs2⟩
  have := Finsupp.support_eq_empty.mpr (h s <| mem_support_iff.mpr hs1) ▸ hs2
  grind

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.le_degrees_add_left** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：le_degrees_add_left (h : Disjoint p.degrees q.degrees) : p.degrees <= (p +
 q).degrees
参数：h : Disjoint p.degrees q.degrees。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.toMultiset_zero`：toMultiset_zero : toMultiset (0 : α ->₀ Nat) = 
0
· 使用定理 `Multiset.zero_le`：zero_le (s : Multiset α) : 0 <= s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.le_sup_of_le`：le_sup_of_le {b : β} (hb : b in s) (h : a <= f b) :
 a <= s.sup f
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Finsupp.support_eq_empty`：support_eq_empty {f : α ->₀ M} : f.support = ∅
 ↔ f = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.mem_degrees`：mem_degrees {p : MvPolynomial σ R} {i : σ} : i
 in p.degrees ↔ exists d, p.coeff d != 0 ∧ i in d.support
· 使用定理 `Multiset.disjoint_iff_ne`：disjoint_iff_ne {s t : Multiset α} : Disjoint 
s t ↔ forall a in s, forall b in t, a != b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MvPolynomial.coeff.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : CommSemir
ing R] (m : σ →₀ ℕ) (p : MvPolynomial σ R),   MvPolynomial.coeff m p = p.coeff m
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_degrees_add_left (h : Disjoint p.degrees q.degrees) : p.degrees ≤ (p + q).degrees := by
  classical
  apply Finset.sup_le
  intro d hd
  rw [Multiset.disjoint_iff_ne] at h
  obtain rfl | h0 := eq_or_ne d 0
  · rw [toMultiset_zero]; apply Multiset.zero_le
  · refine Finset.le_sup_of_le (b := d) ?_ le_rfl
    rw [mem_support_iff, coeff_add]
    suffices q.coeff d = 0 by rwa [this, add_zero, coeff, ← Finsupp.mem_support_iff]
    rw [Ne, ← Finsupp.support_eq_empty, ← Ne, ← Finset.nonempty_iff_ne_empty] at h0
    obtain ⟨j, hj⟩ := h0
    contrapose! h
    rw [mem_support_iff] at hd
    refine ⟨j, ?_, j, ?_, rfl⟩
    all_goals rw [mem_degrees]; refine ⟨d, ?_, hj⟩; assumption
/-
**MvPolynomial.le_degrees_add_right** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：le_degrees_add_right (h : Disjoint p.degrees q.degrees) : q.degrees <= (p 
+ q).degrees
参数：h : Disjoint p.degrees q.degrees。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MvPolynomial.le_degrees_add_left`：le_degrees_add_left (h : Disjoint p.de
grees q.degrees) : p.degrees <= (p + q).degrees
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
lemma le_degrees_add_right (h : Disjoint p.degrees q.degrees) : q.degrees ≤ (p + q).degrees := by
  simpa [add_comm] using le_degrees_add_left h.symm
/-
**MvPolynomial.degrees_add_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_add_of_disjoint [DecidableEq σ] (h : Disjoint p.degrees q.degrees)
 : (p + q).degrees = p.degrees union q.degrees
参数：h : Disjoint p.degrees q.degrees。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MvPolynomial.degrees_add_le`：degrees_add_le [DecidableEq σ] {p q : MvPol
ynomial σ R} : (p + q).degrees <= p.degrees ⊔ q.degrees
· 使用引理 `Multiset.union_le`：union_le (h₁ : s <= u) (h₂ : t <= u) : s union t <= u
· 使用定理 `MvPolynomial.le_degrees_add_left`：le_degrees_add_left (h : Disjoint p.de
grees q.degrees) : p.degrees <= (p + q).degrees
· 使用引理 `MvPolynomial.le_degrees_add_right`：le_degrees_add_right (h : Disjoint p.
degrees q.degrees) : q.degrees <= (p + q).degrees
-/
theorem degrees_add_of_disjoint [DecidableEq σ] (h : Disjoint p.degrees q.degrees) :
    (p + q).degrees = p.degrees ∪ q.degrees :=
  degrees_add_le.antisymm <| Multiset.union_le (le_degrees_add_left h) (le_degrees_add_right h)
/-
**MvPolynomial.degrees_map_le** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_map_le [CommSemiring S] {f : R ->+* S} : (map f p).degrees <= p.de
grees
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `MvPolynomial.support_map_subset`：support_map_subset (p : MvPolynomial σ 
R) : (map f p).support subseteq p.support
-/
lemma degrees_map_le [CommSemiring S] {f : R →+* S} : (map f p).degrees ≤ p.degrees := by
  classical exact Finset.sup_mono <| support_map_subset ..
/-
**MvPolynomial.degrees_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_rename (f : σ -> τ) (φ : MvPolynomial σ R) : (rename f φ).degrees 
subseteq φ.degrees.map f
参数：f : σ -> τ；φ : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.mem_degrees`：mem_degrees {p : MvPolynomial σ R} {i : σ} : i
 in p.degrees ↔ exists d, p.coeff d != 0 ∧ i in d.support
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `MvPolynomial.coeff_rename_ne_zero`：coeff_rename_ne_zero (f : σ -> τ) (φ 
: MvPolynomial σ R) (d : τ ->₀ Nat) (h : (rename f φ).coeff d != 0) : exists u :
 σ ->₀ Nat, u.mapDomain…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
-/
theorem degrees_rename (f : σ → τ) (φ : MvPolynomial σ R) :
    (rename f φ).degrees ⊆ φ.degrees.map f := by
  classical
  intro i
  rw [mem_degrees, Multiset.mem_map]
  rintro ⟨d, hd, hi⟩
  obtain ⟨x, rfl, hx⟩ := coeff_rename_ne_zero _ _ _ hd
  simp only [Finsupp.mapDomain, Finsupp.mem_support_iff] at hi
  rw [sum_apply, Finsupp.sum] at hi
  contrapose! hi
  rw [Finset.sum_eq_zero]
  intro j hj
  simp only [mem_degrees] at hi
  specialize hi j ⟨x, hx, hj⟩
  rw [Finsupp.single_apply, if_neg hi]
/-
**MvPolynomial.degrees_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：degrees_map_of_injective [CommSemiring S] (p : MvPolynomial σ R) {f : R ->
+* S} (hf : Injective f) : (map f p).degrees = p.degrees
参数：p : MvPolynomial σ R；hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.support_map_of_injective`：support_map_of_injective (p : MvP
olynomial σ R) {f : R ->+* S₁} (hf : Injective f) : (map f p).support = p.suppor
t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degrees_map_of_injective [CommSemiring S] (p : MvPolynomial σ R) {f : R →+* S}
    (hf : Injective f) : (map f p).degrees = p.degrees := by
  simp only [degrees, MvPolynomial.support_map_of_injective _ hf]
/-
**MvPolynomial.degrees_rename_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：degrees_rename_of_injective {p : MvPolynomial σ R} {f : σ -> τ} (h : Funct
ion.Injective f) : degrees (rename f p) = (degrees p).map f
参数：h : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.support_rename_of_injective`：support_rename_of_injective {p
 : MvPolynomial σ R} {f : σ -> τ} [DecidableEq τ] (h : Function.Injective f) : (
rename f p).support = Finset.i…
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Multiset.map_finset_sup`：map_finset_sup [DecidableEq α] [DecidableEq β] 
(s : Finset γ) (f : γ -> Multiset β) (g : β -> α) (hg : Function.Injective g) : 
map g (s.sup …
· 使用定理 `Finset.sup_congr`：sup_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall 
a in s₂, f a = g a) : s₁.sup f = s₂.sup g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.toMultiset_map`：toMultiset_map (f : α ->₀ Nat) (g : α -> β) : f.
toMultiset.map g = toMultiset (f.mapDomain g)
-/
theorem degrees_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} (h : Function.Injective f) :
    degrees (rename f p) = (degrees p).map f := by
  classical
  simp only [degrees, Multiset.map_finset_sup p.support Finsupp.toMultiset f h,
    support_rename_of_injective h, Finset.sup_image]
  refine Finset.sup_congr rfl fun x _ => ?_
  exact (Finsupp.toMultiset_map _ _).symm

end Degrees

section DegreeOf

/-! ### `degreeOf` -/


/-- `degreeOf n p` gives the highest power of $X_n$ that appears in `p` -/
/-
**MvPolynomial.degreeOf** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf (n : σ) (p : MvPolynomial σ R) : Nat
参数：n : σ；p : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`degreeOf n p` gives the highest power of $X_n$ that appears in `p`
-/
def degreeOf (n : σ) (p : MvPolynomial σ R) : ℕ :=
  letI := Classical.decEq σ
  p.degrees.count n
/-
**MvPolynomial.degreeOf_def** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_def [DecidableEq σ] (n : σ) (p : MvPolynomial σ R) : p.degreeOf n
 = p.degrees.count n
参数：n : σ；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : CommSe
miring R] (n : σ) (p : MvPolynomial σ R),   MvPolynomial.degreeOf n p = Multiset
.count n p.degre…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
theorem degreeOf_def [DecidableEq σ] (n : σ) (p : MvPolynomial σ R) :
    p.degreeOf n = p.degrees.count n := by rw [degreeOf]; convert! rfl
/-
**MvPolynomial.degreeOf_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_eq_sup (n : σ) (f : MvPolynomial σ R) : degreeOf n f = f.support.
sup fun m => m n
参数：n : σ；f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_def`：degreeOf_def [DecidableEq σ] (n : σ) (p : MvP
olynomial σ R) : p.degreeOf n = p.degrees.count n
· 使用定理 `MvPolynomial.degrees.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : CommSem
iring R] (p : MvPolynomial σ R),   p.degrees = p.support.sup fun s => Finsupp.to
Multiset s
· 使用定理 `Multiset.count_finset_sup`：count_finset_sup [DecidableEq β] (s : Finset 
α) (f : α -> Multiset β) (b : β) : count b (s.sup f) = s.sup fun a => count b (f
 a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.count_toMultiset`：count_toMultiset [DecidableEq α] (f : α ->₀ Na
t) (a : α) : (toMultiset f).count a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degreeOf_eq_sup (n : σ) (f : MvPolynomial σ R) :
    degreeOf n f = f.support.sup fun m => m n := by
  classical
  rw [degreeOf_def, degrees, Multiset.count_finset_sup]
  congr
  ext
  simp only [count_toMultiset]
/-
**MvPolynomial.degreeOf_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_lt_iff {n : σ} {f : MvPolynomial σ R} {d : Nat} (h : 0 < d) : deg
reeOf n f < d ↔ forall m : σ ->₀ Nat, m in f.support -> m n < d
参数：h : 0 < d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem degreeOf_lt_iff {n : σ} {f : MvPolynomial σ R} {d : ℕ} (h : 0 < d) :
    degreeOf n f < d ↔ ∀ m : σ →₀ ℕ, m ∈ f.support → m n < d := by
  rwa [degreeOf_eq_sup, Finset.sup_lt_iff]
/-
**MvPolynomial.degreeOf_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_le_iff {n : σ} {f : MvPolynomial σ R} {d : Nat} : degreeOf n f <=
 d ↔ forall m in support f, m n <= d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma degreeOf_le_iff {n : σ} {f : MvPolynomial σ R} {d : ℕ} :
    degreeOf n f ≤ d ↔ ∀ m ∈ support f, m n ≤ d := by
  rw [degreeOf_eq_sup, Finset.sup_le_iff]

@[simp]
/-
**MvPolynomial.degreeOf_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_zero (n : σ) : degreeOf n (0 : MvPolynomial σ R) = 0
参数：n : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_def`：degreeOf_def [DecidableEq σ] (n : σ) (p : MvP
olynomial σ R) : p.degreeOf n = p.degrees.count n
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `MvPolynomial.degrees_zero`：degrees_zero : degrees (0 : MvPolynomial σ R)
 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degreeOf_zero (n : σ) : degreeOf n (0 : MvPolynomial σ R) = 0 := by
  classical simp only [degreeOf_def, degrees_zero, Multiset.count_zero]

@[simp]
/-
**MvPolynomial.degreeOf_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_one (n : σ) : degreeOf n (1 : MvPolynomial σ R) = 0
参数：n : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_def`：degreeOf_def [DecidableEq σ] (n : σ) (p : MvP
olynomial σ R) : p.degreeOf n = p.degrees.count n
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `MvPolynomial.degrees_one`：degrees_one : degrees (1 : MvPolynomial σ R) =
 0
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degreeOf_one (n : σ) : degreeOf n (1 : MvPolynomial σ R) = 0 := by
  classical simp [degreeOf_def, degrees_one]

@[simp]
/-
**MvPolynomial.degreeOf_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_C (a : R) (x : σ) : degreeOf x (C a : MvPolynomial σ R) = 0
参数：a : R；x : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_def`：degreeOf_def [DecidableEq σ] (n : σ) (p : MvP
olynomial σ R) : p.degreeOf n = p.degrees.count n
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `MvPolynomial.degrees_C`：degrees_C (a : R) : degrees (C a : MvPolynomial 
σ R) = 0
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degreeOf_C (a : R) (x : σ) : degreeOf x (C a : MvPolynomial σ R) = 0 := by
  classical simp [degreeOf_def, degrees_C]
/-
**MvPolynomial.degreeOf_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_X [DecidableEq σ] (i j : σ) [Nontrivial R] : degreeOf i (X j : Mv
Polynomial σ R) = if i = j then 1 else 0
参数：i j : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.degreeOf_def`：degreeOf_def [DecidableEq σ] (n : σ) (p : MvP
olynomial σ R) : p.degreeOf n = p.degrees.count n
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `MvPolynomial.degrees_X`：degrees_X [Nontrivial R] (n : σ) : degrees (X n 
: MvPolynomial σ R) = {n}
· 使用定理 `Multiset.count_singleton`：count_singleton (a b : α) : count a ({b} : Mul
tiset α) = if a = b then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
theorem degreeOf_X [DecidableEq σ] (i j : σ) [Nontrivial R] :
    degreeOf i (X j : MvPolynomial σ R) = if i = j then 1 else 0 := by
  by_cases c : i = j
  · simp only [c, if_true, degreeOf_def, degrees_X, Multiset.count_singleton]
  simp [c, degreeOf_def, degrees_X]
/-
**MvPolynomial.degreeOf_X_self** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring R] [Nontrivial R] (i : 
σ),   MvPolynomial.degreeOf i (MvPolynomial.X i) = 1
参数：i : σ；MvPolynomial.X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_X`：degreeOf_X [DecidableEq σ] (i j : σ) [Nontrivia
l R] : degreeOf i (X j : MvPolynomial σ R) = if i = j then 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem degreeOf_X_self [Nontrivial R] (i : σ) :
    (X i : MvPolynomial σ R).degreeOf i = 1 := by
  classical simp [degreeOf_X]
/-
**MvPolynomial.ne_zero_of_degreeOf_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomi
al`。
形式化陈述：ne_zero_of_degreeOf_ne_zero {i : σ} : p.degreeOf i != 0 -> p != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.degreeOf_zero`：degreeOf_zero (n : σ) : degreeOf n (0 : MvPo
lynomial σ R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ne_zero_of_degreeOf_ne_zero {i : σ} : p.degreeOf i ≠ 0 → p ≠ 0 := by
  aesop
/-
**MvPolynomial.degreeOf_add_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_add_le (n : σ) (f g : MvPolynomial σ R) : degreeOf n (f + g) <= m
ax (degreeOf n f) (degreeOf n g)
参数：n : σ；f g : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用定理 `AddMonoidAlgebra.supDegree_add_le`：supDegree_add_le {f g : R[A]} : (f + 
g).supDegree D <= (f.supDegree D) ⊔ (g.supDegree D)
-/
theorem degreeOf_add_le (n : σ) (f g : MvPolynomial σ R) :
    degreeOf n (f + g) ≤ max (degreeOf n f) (degreeOf n g) := by
  simp_rw [degreeOf_eq_sup]; exact supDegree_add_le
/-
**MvPolynomial.monomial_le_degreeOf** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_le_degreeOf (i : σ) {f : MvPolynomial σ R} {m : σ ->₀ Nat} (h_m :
 m in f.support) : m i <= degreeOf i f
参数：i : σ；h_m : m in f.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem monomial_le_degreeOf (i : σ) {f : MvPolynomial σ R} {m : σ →₀ ℕ} (h_m : m ∈ f.support) :
    m i ≤ degreeOf i f := by
  rw [degreeOf_eq_sup i]
  apply Finset.le_sup h_m
/-
**MvPolynomial.degreeOf_monomial_eq** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_monomial_eq (s : σ ->₀ Nat) (i : σ) {a : R} (ha : a != 0) : (mono
mial s a).degreeOf i = s i
参数：s : σ ->₀ Nat；i : σ；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_def`：degreeOf_def [DecidableEq σ] (n : σ) (p : MvP
olynomial σ R) : p.degreeOf n = p.degrees.count n
· 使用定理 `MvPolynomial.degrees_monomial_eq`：degrees_monomial_eq (s : σ ->₀ Nat) (a
 : R) (ha : a != 0) : degrees (monomial s a) = toMultiset s
· 使用定理 `Finsupp.count_toMultiset`：count_toMultiset [DecidableEq α] (f : α ->₀ Na
t) (a : α) : (toMultiset f).count a = f a
-/
lemma degreeOf_monomial_eq (s : σ →₀ ℕ) (i : σ) {a : R} (ha : a ≠ 0) :
    (monomial s a).degreeOf i = s i := by
  classical rw [degreeOf_def, degrees_monomial_eq _ _ ha, Finsupp.count_toMultiset]
/-
**MvPolynomial.degreeOf_X_self_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring R] [Nontrivial R] (i : 
σ) (k : ℕ),   MvPolynomial.degreeOf i (MvPolynomial.X i ^ k) = k
参数：i : σ；k : ℕ；MvPolynomial.X i ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.X_pow_eq_monomial`：X_pow_eq_monomial : X n ^ e = monomial (
Finsupp.single n e) (1 : R)
· 使用引理 `MvPolynomial.degreeOf_monomial_eq`：degreeOf_monomial_eq (s : σ ->₀ Nat) 
(i : σ) {a : R} (ha : a != 0) : (monomial s a).degreeOf i = s i
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
@[simp] theorem degreeOf_X_self_pow [Nontrivial R] (i : σ) (k : ℕ) :
    ((X i : MvPolynomial σ R) ^ k).degreeOf i = k := by
  rw [X_pow_eq_monomial, degreeOf_monomial_eq _ _ one_ne_zero, Finsupp.single_eq_same]
/-
**MvPolynomial.le_degreeOf_of_mem_support** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomia
l`。
形式化陈述：le_degreeOf_of_mem_support (i : σ) {s : σ ->₀ Nat} : s in p.support -> s i
 <= p.degreeOf i
参数：i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用定理 `Finset.le_sup_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (a ≤ s.sup
 f ↔ ∃ …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma le_degreeOf_of_mem_support (i : σ) {s : σ →₀ ℕ} :
    s ∈ p.support → s i ≤ p.degreeOf i := fun h ↦ by
  obtain si | si := eq_or_lt_of_le <| Nat.zero_le (s i)
  · simp [← si]
  rw [degreeOf_eq_sup, Finset.le_sup_iff si]
  use s
/-
**MvPolynomial.notMem_support_of_degreeOf_lt** 是 Mathlib 中的一个引理，位于命名空间 `MvPolyno
mial`。
形式化陈述：notMem_support_of_degreeOf_lt (i : σ) {s : σ ->₀ Nat} : p.degreeOf i < s i
 -> s ∉ p.support
参数：i : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `MvPolynomial.le_degreeOf_of_mem_support`：le_degreeOf_of_mem_support (i :
 σ) {s : σ ->₀ Nat} : s in p.support -> s i <= p.degreeOf i
-/
lemma notMem_support_of_degreeOf_lt (i : σ) {s : σ →₀ ℕ} :
    p.degreeOf i < s i → s ∉ p.support := fun h ↦ by
  contrapose! h
  exact le_degreeOf_of_mem_support i h

/--
Note that `degreeOf_prod_eq` proves equality with `NoZeroDivisors R` and nonzero polynomials.
-/
/-
**MvPolynomial.degreeOf_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_mul_le (i : σ) (f g : MvPolynomial σ R) : degreeOf i (f * g) <= d
egreeOf i f + degreeOf i g
参数：i : σ；f g : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `Multiset.count_le_of_le`：count_le_of_le (a : α) {s t} : s <= t -> count 
a s <= count a t
· 使用定理 `MvPolynomial.degrees_mul_le`：degrees_mul_le {p q : MvPolynomial σ R} : (
p * q).degrees <= p.degrees + q.degrees

--- 原说明 ---
Note that `degreeOf_prod_eq` proves equality with `NoZeroDivisors R` and nonzero
 polynomials.
-/
theorem degreeOf_mul_le (i : σ) (f g : MvPolynomial σ R) :
    degreeOf i (f * g) ≤ degreeOf i f + degreeOf i g := by
  classical
  simp only [degreeOf]
  convert! Multiset.count_le_of_le i degrees_mul_le
  rw [Multiset.count_add]
/-
**MvPolynomial.degreeOf_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_sum_le {ι : Type*} (i : σ) (s : Finset ι) (f : ι -> MvPolynomial 
σ R) : degreeOf i (∑ j in s, f j) <= s.sup fun j => degreeOf i (f j)
参数：i : σ；s : Finset ι；f : ι -> MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddMonoidAlgebra.supDegree_sum_le`：supDegree_sum_le {ι} {s : Finset ι} {
f : ι -> R[A]} : (∑ i in s, f i).supDegree D <= s.sup (fun i => (f i).supDegree 
D)
-/
theorem degreeOf_sum_le {ι : Type*} (i : σ) (s : Finset ι) (f : ι → MvPolynomial σ R) :
    degreeOf i (∑ j ∈ s, f j) ≤ s.sup fun j => degreeOf i (f j) := by
  simp_rw [degreeOf_eq_sup]
  exact supDegree_sum_le

/--
Note that `degreeOf_mul_eq` proves equality with `NoZeroDivisors R` and nonzero polynomials.
-/
/-
**MvPolynomial.degreeOf_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_prod_le {ι : Type*} (i : σ) (s : Finset ι) (f : ι -> MvPolynomial
 σ R) : degreeOf i (∏ j in s, f j) <= ∑ j in s, (f j).degreeOf i
参数：i : σ；s : Finset ι；f : ι -> MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AddMonoidAlgebra.supDegree_prod_le`：supDegree_prod_le {R A B : Type*} [C
ommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [SemilatticeSup B] [OrderBot 
B] [AddLeftMono B] [AddR…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Note that `degreeOf_mul_eq` proves equality with `NoZeroDivisors R` and nonzero 
polynomials.
-/
theorem degreeOf_prod_le {ι : Type*} (i : σ) (s : Finset ι) (f : ι → MvPolynomial σ R) :
    degreeOf i (∏ j ∈ s, f j) ≤ ∑ j ∈ s, (f j).degreeOf i := by
  simp_rw [degreeOf_eq_sup]
  exact supDegree_prod_le (by simp only [coe_zero, Pi.zero_apply]) (by simp)

/--
Note that `degreeOf_pow_eq` proves equality with `NoZeroDivisors R` and nonzero polynomials.
-/
/-
**MvPolynomial.degreeOf_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_pow_le (i : σ) (p : MvPolynomial σ R) (n : Nat) : degreeOf i (p ^
 n) <= n * degreeOf i p
参数：i : σ；p : MvPolynomial σ R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.degreeOf_prod_le`：degreeOf_prod_le {ι : Type*} (i : σ) (s :
 Finset ι) (f : ι -> MvPolynomial σ R) : degreeOf i (∏ j in s, f j) <= ∑ j in s,
 (f j).degreeOf i

--- 原说明 ---
Note that `degreeOf_pow_eq` proves equality with `NoZeroDivisors R` and nonzero 
polynomials.
-/
theorem degreeOf_pow_le (i : σ) (p : MvPolynomial σ R) (n : ℕ) :
    degreeOf i (p ^ n) ≤ n * degreeOf i p := by
  simpa using degreeOf_prod_le i (Finset.range n) (fun _ => p)
/-
**MvPolynomial.degreeOf_mul_X_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_mul_X_of_ne {i j : σ} (f : MvPolynomial σ R) (h : i != j) : degre
eOf i (f * X j) = degreeOf i f
参数：f : MvPolynomial σ R；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.support_mul_X`：support_mul_X (s : σ) (p : MvPolynomial σ R)
 : (p * X s).support = p.support.map (addRightEmbedding (Finsupp.single s 1))
· 使用定理 `Finset.sup_map`：sup_map (s : Finset γ) (f : γ ↪ β) (g : β -> α) : (s.map
 f).sup g = s.sup (g ∘ f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `addRightEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRig
htCancelAdd G] (g h : G), (addRightEmbedding g) h = h + g
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degreeOf_mul_X_of_ne {i j : σ} (f : MvPolynomial σ R) (h : i ≠ j) :
    degreeOf i (f * X j) = degreeOf i f := by
  classical
  simp only [degreeOf_eq_sup i, support_mul_X, Finset.sup_map]
  congr
  ext
  simp only [Finsupp.single, addRightEmbedding_apply, coe_mk,
    Pi.add_apply, comp_apply, Finsupp.coe_add, Pi.single_eq_of_ne h, add_zero]
/-
**MvPolynomial.degreeOf_mul_X_self** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_mul_X_self (j : σ) (f : MvPolynomial σ R) : degreeOf j (f * X j) 
<= degreeOf j f + 1
参数：j : σ；f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Multiset.count_le_of_le`：count_le_of_le (a : α) {s t} : s <= t -> count 
a s <= count a t
· 使用定理 `MvPolynomial.degrees_mul_le`：degrees_mul_le {p q : MvPolynomial σ R} : (
p * q).degrees <= p.degrees + q.degrees
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.count_singleton_self`：count_singleton_self (a : α) : count a ({
a} : Multiset α) = 1
· 使用定理 `MvPolynomial.degrees_X'`：degrees_X' (n : σ) : degrees (X n : MvPolynomia
l σ R) <= {n}
-/
theorem degreeOf_mul_X_self (j : σ) (f : MvPolynomial σ R) :
    degreeOf j (f * X j) ≤ degreeOf j f + 1 := by
  classical
  simp only [degreeOf]
  apply (Multiset.count_le_of_le j degrees_mul_le).trans
  simp only [Multiset.count_add, add_le_add_iff_left]
  convert! Multiset.count_le_of_le j <| degrees_X' j
  rw [Multiset.count_singleton_self]
/-
**MvPolynomial.degreeOf_X_pow_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_X_pow_of_ne {i j : σ} (k : Nat) (h : i != j) : ((X j : MvPolynomi
al σ R) ^ k).degreeOf i = 0
参数：k : Nat；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.C_1`：C_1 : C 1 = (1 : MvPolynomial σ R)
· 使用定理 `MvPolynomial.degreeOf_C`：degreeOf_C (a : R) (x : σ) : degreeOf x (C a : 
MvPolynomial σ R) = 0
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `MvPolynomial.degreeOf_mul_X_of_ne`：degreeOf_mul_X_of_ne {i j : σ} (f : M
vPolynomial σ R) (h : i != j) : degreeOf i (f * X j) = degreeOf i f
-/
theorem degreeOf_X_pow_of_ne {i j : σ} (k : ℕ) (h : i ≠ j) :
    ((X j : MvPolynomial σ R) ^ k).degreeOf i = 0 := by
  induction k with
  | zero => rw [pow_zero, ← C_1, degreeOf_C]
  | succ k hk => rw [pow_add, pow_one, degreeOf_mul_X_of_ne _ h, hk]
/-
**MvPolynomial.degreeOf_X_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_X_of_ne {i j : σ} (h : i != j) : (X j : MvPolynomial σ R).degreeO
f i = 0
参数：h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.degreeOf_X_pow_of_ne`：degreeOf_X_pow_of_ne {i j : σ} (k : N
at) (h : i != j) : ((X j : MvPolynomial σ R) ^ k).degreeOf i = 0
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem degreeOf_X_of_ne {i j : σ} (h : i ≠ j) : (X j : MvPolynomial σ R).degreeOf i = 0 :=
  pow_one (X j : MvPolynomial σ R) ▸ degreeOf_X_pow_of_ne 1 h
/-
**MvPolynomial.degreeOf_mul_X_eq_degreeOf_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 
`MvPolynomial`。
形式化陈述：degreeOf_mul_X_eq_degreeOf_add_one_iff (j : σ) (f : MvPolynomial σ R) : de
greeOf j (f * X j) = degreeOf j f + 1 ↔ f != 0
参数：j : σ；f : MvPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MvPolynomial.degreeOf_zero`：degreeOf_zero (n : σ) : degreeOf n (0 : MvPo
lynomial σ R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.le_antisymm`：∀ {n m : ℕ}, n ≤ m → m ≤ n → n = m
· 使用定理 `MvPolynomial.degreeOf_mul_X_self`：degreeOf_mul_X_self (j : σ) (f : MvPol
ynomial σ R) : degreeOf j (f * X j) <= degreeOf j f + 1
· 使用定理 `Finset.apply_sup_eq_sup_comp_of_nonempty`：apply_sup_eq_sup_comp_of_nonem
pty [OrderBot α] [SemilatticeSup β] [OrderBot β] {g : α -> β} (mono_g : Monotone
 g) (H : s.Nonempty) : g (s.su…
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MvPolynomial.support_nonempty`：support_nonempty {p : MvPolynomial σ R} :
 p.support.Nonempty ↔ p != 0
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用定理 `MvPolynomial.support_mul_X`：support_mul_X (s : σ) (p : MvPolynomial σ R)
 : (p * X s).support = p.support.map (addRightEmbedding (Finsupp.single s 1))
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Finset.sup_map`：sup_map (s : Finset γ) (f : γ ↪ β) (g : β -> α) : (s.map
 f).sup g = s.sup (g ∘ f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `addRightEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRig
htCancelAdd G] (g h : G), (addRightEmbedding g) h = h + g
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 31 条，此处仅展示前 30 条）
-/
theorem degreeOf_mul_X_eq_degreeOf_add_one_iff (j : σ) (f : MvPolynomial σ R) :
    degreeOf j (f * X j) = degreeOf j f + 1 ↔ f ≠ 0 := by
  refine ⟨fun h => by by_contra ha; simp [ha] at h, fun h => ?_⟩
  apply Nat.le_antisymm (degreeOf_mul_X_self j f)
  have : (f.support.sup fun m ↦ m j) + 1 = (f.support.sup fun m ↦ (m j + 1)) :=
    Finset.apply_sup_eq_sup_comp_of_nonempty @Nat.succ_le_succ (support_nonempty.mpr h)
  simp only [degreeOf_eq_sup, support_mul_X, this]
  apply Finset.sup_le
  intro x hx
  simp only [Finset.sup_map, bot_eq_zero', add_pos_iff, zero_lt_one, or_true, Finset.le_sup_iff]
  use x
  simpa using mem_support_iff.mp hx
/-
**MvPolynomial.degreeOf_mul_X_self_pow_eq_add_of_ne_zero** 是 Mathlib 中的一个定理，位于命名
空间 `MvPolynomial`。
形式化陈述：degreeOf_mul_X_self_pow_eq_add_of_ne_zero (i : σ) (k : Nat) (h : p != 0) :
 (p * X i ^ k).degreeOf i = p.degreeOf i + k
参数：i : σ；k : Nat；h : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.ne_zero_iff`：ne_zero_iff {p : MvPolynomial σ R} : p != 0 ↔ 
exists d, coeff d p != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPolynomial.X_pow_eq_monomial`：X_pow_eq_monomial : X n ^ e = monomial (
Finsupp.single n e) (1 : R)
· 使用定理 `MvPolynomial.coeff_mul_monomial`：coeff_mul_monomial (m) (s : σ ->₀ Nat) 
(r : R) (p : MvPolynomial σ R) : coeff (m + s) (p * monomial s r) = coeff m p * 
r
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MvPolynomial.degreeOf_mul_X_eq_degreeOf_add_one_iff`：degreeOf_mul_X_eq_d
egreeOf_add_one_iff (j : σ) (f : MvPolynomial σ R) : degreeOf j (f * X j) = degr
eeOf j f + 1 ↔ f != 0
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem degreeOf_mul_X_self_pow_eq_add_of_ne_zero (i : σ) (k : ℕ) (h : p ≠ 0) :
    (p * X i ^ k).degreeOf i = p.degreeOf i + k := by
  induction k with
  | zero => rw [pow_zero, mul_one, add_zero]
  | succ k hk =>
    have : p * X i ^ k ≠ 0 := by
      rcases ne_zero_iff.mp h with ⟨s, hs⟩
      refine ne_zero_iff.mpr ⟨s + Finsupp.single i k, ?_⟩
      rwa [X_pow_eq_monomial, coeff_mul_monomial, mul_one]
    rw [pow_add, pow_one, ← mul_assoc,
      (degreeOf_mul_X_eq_degreeOf_add_one_iff i _).mpr this, hk, add_assoc]
/-
**MvPolynomial.degreeOf_mul_X_pow_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：degreeOf_mul_X_pow_of_ne {i j : σ} (k : Nat) (h : i != j) : (p * X j ^ k).
degreeOf i = p.degreeOf i
参数：k : Nat；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MvPolynomial.degreeOf_mul_X_of_ne`：degreeOf_mul_X_of_ne {i j : σ} (f : M
vPolynomial σ R) (h : i != j) : degreeOf i (f * X j) = degreeOf i f
-/
theorem degreeOf_mul_X_pow_of_ne {i j : σ} (k : ℕ) (h : i ≠ j) :
    (p * X j ^ k).degreeOf i = p.degreeOf i := by
  induction k with
  | zero => rw [pow_zero, mul_one]
  | succ k hk => rw [pow_add, pow_one, ← mul_assoc, degreeOf_mul_X_of_ne _ h, hk]
/-
**MvPolynomial.degreeOf_add_eq_of_degreeOf_lt** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyn
omial`。
形式化陈述：degreeOf_add_eq_of_degreeOf_lt {i : σ} (h : q.degreeOf i < p.degreeOf i) :
 (p + q).degreeOf i = p.degreeOf i
参数：h : q.degreeOf i < p.degreeOf i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_eq_left_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b 
< a → max a b = a
· 使用定理 `MvPolynomial.degreeOf_add_le`：degreeOf_add_le (n : σ) (f g : MvPolynomia
l σ R) : degreeOf n (f + g) <= max (degreeOf n f) (degreeOf n g)
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.le_sup_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (a ≤ s.sup
 f ↔ ∃ …
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.degreeOf_zero`：degreeOf_zero (n : σ) : degreeOf n (0 : MvPo
lynomial σ R) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Finset.exists_mem_eq_sup`：exists_mem_eq_sup [OrderBot α] (s : Finset ι) 
(h : s.Nonempty) (f : ι -> α) : exists i, i in s ∧ s.sup f = f i
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `MvPolynomial.le_degreeOf_of_mem_support`：le_degreeOf_of_mem_support (i :
 σ) {s : σ ->₀ Nat} : s in p.support -> s i <= p.degreeOf i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem degreeOf_add_eq_of_degreeOf_lt {i : σ} (h : q.degreeOf i < p.degreeOf i) :
    (p + q).degreeOf i = p.degreeOf i := by
  apply le_antisymm
  · rw [← max_eq_left_of_lt h]
    exact degreeOf_add_le i p q
  nth_rw 2 [degreeOf_eq_sup]
  apply (Finset.le_sup_iff <| Nat.zero_lt_of_lt h).mpr
  have : p.support.Nonempty := by aesop
  have ⟨s, hs1, hs2⟩ := Finset.exists_mem_eq_sup _ this (fun s ↦ s i)
  rw [← degreeOf_eq_sup i p] at hs2
  refine ⟨s, ?_, by rw [hs2]⟩
  have : s ∉ q.support := by
    contrapose! h
    rw [hs2]
    exact le_degreeOf_of_mem_support i h
  simp only [mem_support_iff, ne_eq, coeff_add, not_not] at hs1 ⊢ this
  rwa [this, add_zero]
/-
**MvPolynomial.degreeOf_eq_of_degreeOf_add_lt** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyn
omial`。
形式化陈述：degreeOf_eq_of_degreeOf_add_lt {i : σ} (h : (p + q).degreeOf i < p.degreeO
f i) : p.degreeOf i = q.degreeOf i
参数：h : (p + q).degreeOf i < p.degreeOf i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_max_left`：∀ (a b : ℕ), a ≤ max a b
· 使用定理 `Nat.lt_or_lt_of_ne`：∀ {a b : ℕ}, a ≠ b → a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a
 < b → max a b = b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MvPolynomial.degreeOf_add_eq_of_degreeOf_lt`：degreeOf_add_eq_of_degreeOf
_lt {i : σ} (h : q.degreeOf i < p.degreeOf i) : (p + q).degreeOf i = p.degreeOf 
i
· 使用定理 `max_eq_left_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b 
< a → max a b = a
-/
theorem degreeOf_eq_of_degreeOf_add_lt {i : σ} (h : (p + q).degreeOf i < p.degreeOf i) :
    p.degreeOf i = q.degreeOf i := by
  contrapose! h
  apply le_trans (Nat.le_max_left _ (q.degreeOf i))
  rcases Nat.lt_or_lt_of_ne h with h | h
  · simp [add_comm p q, degreeOf_add_eq_of_degreeOf_lt h, max_eq_right_of_lt h]
  · simp [degreeOf_add_eq_of_degreeOf_lt h, max_eq_left_of_lt h]
/-
**MvPolynomial.degreeOf_C_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_C_mul_le (p : MvPolynomial σ R) (i : σ) (c : R) : (C c * p).degre
eOf i <= p.degreeOf i
参数：p : MvPolynomial σ R；i : σ；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.degrees_C`：degrees_C (a : R) : degrees (C a : MvPolynomial 
σ R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.count_le_of_le`：count_le_of_le (a : α) {s t} : s <= t -> count 
a s <= count a t
· 使用定理 `MvPolynomial.degrees_mul_le`：degrees_mul_le {p q : MvPolynomial σ R} : (
p * q).degrees <= p.degrees + q.degrees
-/
theorem degreeOf_C_mul_le (p : MvPolynomial σ R) (i : σ) (c : R) :
    (C c * p).degreeOf i ≤ p.degreeOf i := by
  unfold degreeOf
  convert! Multiset.count_le_of_le i degrees_mul_le
  simp only [degrees_C, zero_add]
/-
**MvPolynomial.degreeOf_mul_C_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_mul_C_le (p : MvPolynomial σ R) (i : σ) (c : R) : (p * C c).degre
eOf i <= p.degreeOf i
参数：p : MvPolynomial σ R；i : σ；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degrees_C`：degrees_C (a : R) : degrees (C a : MvPolynomial 
σ R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.count_le_of_le`：count_le_of_le (a : α) {s t} : s <= t -> count 
a s <= count a t
· 使用定理 `MvPolynomial.degrees_mul_le`：degrees_mul_le {p q : MvPolynomial σ R} : (
p * q).degrees <= p.degrees + q.degrees
-/
theorem degreeOf_mul_C_le (p : MvPolynomial σ R) (i : σ) (c : R) :
    (p * C c).degreeOf i ≤ p.degreeOf i := by
  unfold degreeOf
  convert! Multiset.count_le_of_le i degrees_mul_le
  simp only [degrees_C, add_zero]
/-
**MvPolynomial.degreeOf_rename_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynom
ial`。
形式化陈述：degreeOf_rename_of_injective {p : MvPolynomial σ R} {f : σ -> τ} (h : Func
tion.Injective f) (i : σ) : degreeOf (f i) (rename f p) = degreeOf i p
参数：h : Function.Injective f；i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `MvPolynomial.degrees_rename_of_injective`：degrees_rename_of_injective {p
 : MvPolynomial σ R} {f : σ -> τ} (h : Function.Injective f) : degrees (rename f
 p) = (degrees p).map f
· 使用定理 `Multiset.count_map_eq_count'`：count_map_eq_count' [DecidableEq β] (f : α
 -> β) (s : Multiset α) (hf : Function.Injective f) (x : α) : (s.map f).count (f
 x) = s.count x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degreeOf_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} (h : Function.Injective f)
    (i : σ) : degreeOf (f i) (rename f p) = degreeOf i p := by
  classical
  simp only [degreeOf, degrees_rename_of_injective h, Multiset.count_map_eq_count' f p.degrees h]

end DegreeOf

section TotalDegree

/-! ### `totalDegree` -/


/-- `totalDegree p` gives the maximum |s| over the monomials X^s in `p` -/
/-
**MvPolynomial.totalDegree** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree (p : MvPolynomial σ R) : Nat
参数：p : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`totalDegree p` gives the maximum |s| over the monomials X^s in `p`
-/
def totalDegree (p : MvPolynomial σ R) : ℕ :=
  p.support.sup fun s => s.sum fun _ e => e
/-
**MvPolynomial.totalDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_eq (p : MvPolynomial σ R) : p.totalDegree = p.support.sup fun 
m => Multiset.card (toMultiset m)
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.totalDegree.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : Com
mSemiring R] (p : MvPolynomial σ R),   p.totalDegree = p.support.sup fun s => s.
sum fun x e => e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.card_toMultiset`：card_toMultiset (f : α ->₀ Nat) : Multiset.card
 (toMultiset f) = f.sum fun _ => id
-/
theorem totalDegree_eq (p : MvPolynomial σ R) :
    p.totalDegree = p.support.sup fun m => Multiset.card (toMultiset m) := by
  rw [totalDegree]
  congr; funext m
  exact (Finsupp.card_toMultiset _).symm
/-
**MvPolynomial.le_totalDegree** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：le_totalDegree {p : MvPolynomial σ R} {s : σ ->₀ Nat} (h : s in p.support)
 : (s.sum fun _ e => e) <= totalDegree p
参数：h : s in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem le_totalDegree {p : MvPolynomial σ R} {s : σ →₀ ℕ} (h : s ∈ p.support) :
    (s.sum fun _ e => e) ≤ totalDegree p :=
  Finset.le_sup (α := ℕ) (f := fun s => sum s fun _ e => e) h
/-
**MvPolynomial.totalDegree_le_degrees_card** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：totalDegree_le_degrees_card (p : MvPolynomial σ R) : p.totalDegree <= Mult
iset.card p.degrees
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.totalDegree_eq`：totalDegree_eq (p : MvPolynomial σ R) : p.t
otalDegree = p.support.sup fun m => Multiset.card (toMultiset m)
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Multiset.card_le_card`：card_le_card {s t : Multiset α} (h : s <= t) : ca
rd s <= card t
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem totalDegree_le_degrees_card (p : MvPolynomial σ R) :
    p.totalDegree ≤ Multiset.card p.degrees := by
  classical
  rw [totalDegree_eq]
  exact Finset.sup_le fun s hs => Multiset.card_le_card <| Finset.le_sup hs
/-
**MvPolynomial.totalDegree_le_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial`。
形式化陈述：totalDegree_le_of_support_subset (h : p.support subseteq q.support) : tota
lDegree p <= totalDegree q
参数：h : p.support subseteq q.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
-/
theorem totalDegree_le_of_support_subset (h : p.support ⊆ q.support) :
    totalDegree p ≤ totalDegree q :=
  Finset.sup_mono h

@[simp]
/-
**MvPolynomial.totalDegree_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_C (a : R) : (C a : MvPolynomial σ R).totalDegree = 0
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddMonoidAlgebra.supDegree_single`：supDegree_single (a : A) (r : R) : (s
ingle a r).supDegree D = if r = 0 then ⊥ else D a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_zero_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : Zero M] [inst_1 : AddCommMonoid N] {h : α → M → N},   Finsupp.sum 0 h = 
0
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem totalDegree_C (a : R) : (C a : MvPolynomial σ R).totalDegree = 0 :=
  (supDegree_single 0 a).trans <| by rw [sum_zero_index, bot_eq_zero', ite_self]

@[simp]
/-
**MvPolynomial.totalDegree_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_zero : (0 : MvPolynomial σ R).totalDegree = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.C_0`：C_0 : C 0 = (0 : MvPolynomial σ R)
· 使用定理 `MvPolynomial.totalDegree_C`：totalDegree_C (a : R) : (C a : MvPolynomial 
σ R).totalDegree = 0
-/
theorem totalDegree_zero : (0 : MvPolynomial σ R).totalDegree = 0 := by
  rw [← C_0]; exact totalDegree_C (0 : R)

@[simp]
/-
**MvPolynomial.totalDegree_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_one : (1 : MvPolynomial σ R).totalDegree = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.totalDegree_C`：totalDegree_C (a : R) : (C a : MvPolynomial 
σ R).totalDegree = 0
-/
theorem totalDegree_one : (1 : MvPolynomial σ R).totalDegree = 0 :=
  totalDegree_C (1 : R)

@[simp]
/-
**MvPolynomial.totalDegree_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_X {R} [CommSemiring R] [Nontrivial R] (s : σ) : (X s : MvPolyn
omial σ R).totalDegree = 1
参数：s : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.totalDegree.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : Com
mSemiring R] (p : MvPolynomial σ R),   p.totalDegree = p.support.sup fun s => s.
sum fun x e => e
· 使用定理 `MvPolynomial.support_X`：support_X [Nontrivial R] : (X n : MvPolynomial σ
 R).support = {Finsupp.single n 1}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
-/
theorem totalDegree_X {R} [CommSemiring R] [Nontrivial R] (s : σ) :
    (X s : MvPolynomial σ R).totalDegree = 1 := by
  rw [totalDegree, support_X]
  simp only [Finset.sup, Finsupp.sum_single_index, Finset.fold_singleton, sup_bot_eq]
/-
**MvPolynomial.totalDegree_add** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_add (a b : MvPolynomial σ R) : (a + b).totalDegree <= max a.to
talDegree b.totalDegree
参数：a b : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.sup_support_coeff_add_le`：sup_support_coeff_add_le : (f
 + g).coeff.support.sup degb <= f.coeff.support.sup degb ⊔ g.coeff.support.sup d
egb
-/
theorem totalDegree_add (a b : MvPolynomial σ R) :
    (a + b).totalDegree ≤ max a.totalDegree b.totalDegree :=
  sup_support_coeff_add_le _ _ _
/-
**MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt** 是 Mathlib 中的一个定理，位于命名
空间 `MvPolynomial`。
形式化陈述：totalDegree_add_eq_left_of_totalDegree_lt {p q : MvPolynomial σ R} (h : q.
totalDegree < p.totalDegree) : (p + q).totalDegree = p.totalDegree
参数：h : q.totalDegree < p.totalDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_eq_left_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b 
< a → max a b = a
· 使用定理 `MvPolynomial.totalDegree_add`：totalDegree_add (a b : MvPolynomial σ R) :
 (a + b).totalDegree <= max a.totalDegree b.totalDegree
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.totalDegree_zero`：totalDegree_zero : (0 : MvPolynomial σ R)
.totalDegree = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Finset.exists_mem_eq_sup`：exists_mem_eq_sup [OrderBot α] (s : Finset ι) 
(h : s.Nonempty) (f : ι -> α) : exists i, i in s ∧ s.sup f = f i
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MvPolynomial.totalDegree_eq`：totalDegree_eq (p : MvPolynomial σ R) : p.t
otalDegree = p.support.sup fun m => Multiset.card (toMultiset m)
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `MvPolynomial.support_sdiff_support_subset_support_add`：support_sdiff_sup
port_subset_support_add [DecidableEq σ] (p q : MvPolynomial σ R) : p.support \ q
.support subseteq (p + q).support
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
-/
theorem totalDegree_add_eq_left_of_totalDegree_lt {p q : MvPolynomial σ R}
    (h : q.totalDegree < p.totalDegree) : (p + q).totalDegree = p.totalDegree := by
  classical
    apply le_antisymm
    · rw [← max_eq_left_of_lt h]
      exact totalDegree_add p q
    by_cases hp : p = 0
    · simp [hp]
    obtain ⟨b, hb₁, hb₂⟩ :=
      p.support.exists_mem_eq_sup (by simpa) fun m : σ →₀ ℕ => Multiset.card (toMultiset m)
    have hb : b ∉ q.support := by
      contrapose! h
      rw [totalDegree_eq p, hb₂, totalDegree_eq]
      apply Finset.le_sup h
    have hbb : b ∈ (p + q).support := by
      apply support_sdiff_support_subset_support_add
      rw [Finset.mem_sdiff]
      exact ⟨hb₁, hb⟩
    rw [totalDegree_eq, hb₂, totalDegree_eq]
    exact Finset.le_sup (f := fun m => Multiset.card (Finsupp.toMultiset m)) hbb
/-
**MvPolynomial.totalDegree_add_eq_right_of_totalDegree_lt** 是 Mathlib 中的一个定理，位于命
名空间 `MvPolynomial`。
形式化陈述：totalDegree_add_eq_right_of_totalDegree_lt {p q : MvPolynomial σ R} (h : q
.totalDegree < p.totalDegree) : (q + p).totalDegree = p.totalDegree
参数：h : q.totalDegree < p.totalDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt`：totalDegree_add_
eq_left_of_totalDegree_lt {p q : MvPolynomial σ R} (h : q.totalDegree < p.totalD
egree) : (p + q).totalDegree = p.totalDegree
-/
theorem totalDegree_add_eq_right_of_totalDegree_lt {p q : MvPolynomial σ R}
    (h : q.totalDegree < p.totalDegree) : (q + p).totalDegree = p.totalDegree := by
  rw [add_comm, totalDegree_add_eq_left_of_totalDegree_lt h]
/-
**MvPolynomial.totalDegree_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_mul (a b : MvPolynomial σ R) : (a * b).totalDegree <= a.totalD
egree + b.totalDegree
参数：a b : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.sup_support_coeff_mul_le`：sup_support_coeff_mul_le {deg
b : A -> B} (degbm : forall a b, degb (a + b) <= degb a + degb b) (f g : R[A]) :
 (f * g).coeff.support.sup degb…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_add_index'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : AddZeroClass M] [inst_1 : AddCommMonoid N] {f g : α →₀ M}   {h : α → M →
 N},   (∀ (a…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem totalDegree_mul (a b : MvPolynomial σ R) :
    (a * b).totalDegree ≤ a.totalDegree + b.totalDegree :=
  sup_support_coeff_mul_le (fun _ _ ↦ by simp [Finsupp.sum_add_index']) _ _
/-
**MvPolynomial.totalDegree_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_smul_le [CommSemiring S] [DistribMulAction R S] (a : R) (f : M
vPolynomial σ S) : (a • f).totalDegree <= f.totalDegree
参数：a : R；f : MvPolynomial σ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `MvPolynomial.support_smul`：support_smul {S₁ : Type*} [SMulZeroClass S₁ R
] {a : S₁} {f : MvPolynomial σ R} : (a • f).support subseteq f.support
-/
theorem totalDegree_smul_le [CommSemiring S] [DistribMulAction R S] (a : R) (f : MvPolynomial σ S) :
    (a • f).totalDegree ≤ f.totalDegree :=
  Finset.sup_mono support_smul
/-
**MvPolynomial.totalDegree_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_pow (a : MvPolynomial σ R) (n : Nat) : (a ^ n).totalDegree <= 
n * a.totalDegree
参数：a : MvPolynomial σ R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.pow_eq_prod_const`：pow_eq_prod_const (b : M) : forall n, b ^ n = 
∏ _k in range n, b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.nsmul_eq_mul`：∀ (m n : ℕ), m • n = m * n
· 使用定理 `Finset.nsmul_eq_sum_const`：∀ {M : Type u_4} [inst : AddCommMonoid M] (b 
: M) (n : ℕ), n • b = ∑ _k ∈ Finset.range n, b
· 使用定理 `AddMonoidAlgebra.supDegree_prod_le`：supDegree_prod_le {R A B : Type*} [C
ommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [SemilatticeSup B] [OrderBot 
B] [AddLeftMono B] [AddR…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finsupp.sum_add_index'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : AddZeroClass M] [inst_1 : AddCommMonoid N] {f g : α →₀ M}   {h : α → M →
 N},   (∀ (a…
-/
theorem totalDegree_pow (a : MvPolynomial σ R) (n : ℕ) :
    (a ^ n).totalDegree ≤ n * a.totalDegree := by
  rw [Finset.pow_eq_prod_const, ← Nat.nsmul_eq_mul, Finset.nsmul_eq_sum_const]
  refine supDegree_prod_le rfl (fun _ _ => ?_)
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

@[simp]
/-
**MvPolynomial.totalDegree_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_monomial (s : σ ->₀ Nat) {c : R} (hc : c != 0) : (monomial s c
 : MvPolynomial σ R).totalDegree = s.sum fun _ e => e
参数：s : σ ->₀ Nat；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.support_monomial`：support_monomial [h : Decidable (a = 0)] 
: (monomial s a).support = if a = 0 then ∅ else {s}
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem totalDegree_monomial (s : σ →₀ ℕ) {c : R} (hc : c ≠ 0) :
    (monomial s c : MvPolynomial σ R).totalDegree = s.sum fun _ e => e := by
  classical simp [totalDegree, support_monomial, if_neg hc]
/-
**MvPolynomial.totalDegree_monomial_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_monomial_le (s : σ ->₀ Nat) (c : R) : (monomial s c).totalDegr
ee <= s.sum fun _ => id
参数：s : σ ->₀ Nat；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `MvPolynomial.totalDegree_zero`：totalDegree_zero : (0 : MvPolynomial σ R)
.totalDegree = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `MvPolynomial.totalDegree_monomial`：totalDegree_monomial (s : σ ->₀ Nat) 
{c : R} (hc : c != 0) : (monomial s c : MvPolynomial σ R).totalDegree = s.sum fu
n _ e => e
· 使用定理 `Function.id_def`：∀ {α : Sort u_1}, id = fun x => x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem totalDegree_monomial_le (s : σ →₀ ℕ) (c : R) :
    (monomial s c).totalDegree ≤ s.sum fun _ ↦ id := by
  if hc : c = 0 then
    simp only [hc, map_zero, totalDegree_zero, zero_le]
  else
    rw [totalDegree_monomial _ hc, Function.id_def]

@[simp]
/-
**MvPolynomial.totalDegree_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_X_pow [Nontrivial R] (s : σ) (n : Nat) : (X s ^ n : MvPolynomi
al σ R).totalDegree = n
参数：s : σ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.X_pow_eq_monomial`：X_pow_eq_monomial : X n ^ e = monomial (
Finsupp.single n e) (1 : R)
· 使用定理 `MvPolynomial.totalDegree_monomial`：totalDegree_monomial (s : σ ->₀ Nat) 
{c : R} (hc : c != 0) : (monomial s c : MvPolynomial σ R).totalDegree = s.sum fu
n _ e => e
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem totalDegree_X_pow [Nontrivial R] (s : σ) (n : ℕ) :
    (X s ^ n : MvPolynomial σ R).totalDegree = n := by simp [X_pow_eq_monomial, one_ne_zero]
/-
**MvPolynomial.totalDegree_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_list_prod (l : List (MvPolynomial σ R)) : l.prod.totalDegree <
= (l.map MvPolynomial.totalDegree).sum
参数：l : List (MvPolynomial σ R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.apply_prod_le_sum_map`：apply_prod_le_sum_map (h_one : f 1 <= 0) (h_
mul : forall (a b : α), f (a * b) <= f a + f b) : f l.prod <= (l.map f).sum
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MvPolynomial.totalDegree_one`：totalDegree_one : (1 : MvPolynomial σ R).t
otalDegree = 0
· 使用定理 `MvPolynomial.totalDegree_mul`：totalDegree_mul (a b : MvPolynomial σ R) :
 (a * b).totalDegree <= a.totalDegree + b.totalDegree
-/
theorem totalDegree_list_prod (l : List (MvPolynomial σ R)) :
    l.prod.totalDegree ≤ (l.map MvPolynomial.totalDegree).sum :=
  l.apply_prod_le_sum_map _ totalDegree_one.le totalDegree_mul
/-
**MvPolynomial.totalDegree_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：totalDegree_multiset_prod (s : Multiset (MvPolynomial σ R)) : s.prod.total
Degree <= (s.map MvPolynomial.totalDegree).sum
参数：s : Multiset (MvPolynomial σ R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.apply_prod_le_sum_map`：apply_prod_le_sum_map (h_one : f 1 <= 0)
 (h_mul : forall (a b : α), f (a * b) <= f a + f b) : f m.prod <= (m.map f).sum
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MvPolynomial.totalDegree_one`：totalDegree_one : (1 : MvPolynomial σ R).t
otalDegree = 0
· 使用定理 `MvPolynomial.totalDegree_mul`：totalDegree_mul (a b : MvPolynomial σ R) :
 (a * b).totalDegree <= a.totalDegree + b.totalDegree
-/
theorem totalDegree_multiset_prod (s : Multiset (MvPolynomial σ R)) :
    s.prod.totalDegree ≤ (s.map MvPolynomial.totalDegree).sum :=
  s.apply_prod_le_sum_map _ totalDegree_one.le totalDegree_mul
/-
**MvPolynomial.totalDegree_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_finsetProd {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ
 R) : (s.prod f).totalDegree <= ∑ i in s, (f i).totalDegree
参数：s : Finset ι；f : ι -> MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_prod_le_sum_apply`：apply_prod_le_sum_apply (h_one : g 1 <= 
0) (h_mul : forall (a b : α), g (a * b) <= g a + g b) : g (∏ x in s, f x) <= ∑ x
 in s, g (f x)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MvPolynomial.totalDegree_one`：totalDegree_one : (1 : MvPolynomial σ R).t
otalDegree = 0
· 使用定理 `MvPolynomial.totalDegree_mul`：totalDegree_mul (a b : MvPolynomial σ R) :
 (a * b).totalDegree <= a.totalDegree + b.totalDegree
-/
theorem totalDegree_finsetProd {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (s.prod f).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree :=
  s.apply_prod_le_sum_apply _ totalDegree_one.le totalDegree_mul

@[deprecated (since := "2026-04-08")] alias totalDegree_finset_prod := totalDegree_finsetProd
/-
**MvPolynomial.totalDegree_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_finsetSum {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ 
R) : (s.sum f).totalDegree <= Finset.sup s fun i => (f i).totalDegree
参数：s : Finset ι；f : ι -> MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MvPolynomial.totalDegree_add`：totalDegree_add (a b : MvPolynomial σ R) :
 (a + b).totalDegree <= max a.totalDegree b.totalDegree
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem totalDegree_finsetSum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (s.sum f).totalDegree ≤ Finset.sup s fun i => (f i).totalDegree := by
  induction s using Finset.cons_induction with
  | empty => exact zero_le
  | cons a s has hind =>
    rw [Finset.sum_cons, Finset.sup_cons]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max le_rfl hind)

@[deprecated (since := "2026-04-08")] alias totalDegree_finset_sum := totalDegree_finsetSum
/-
**MvPolynomial.totalDegree_finsetSum_le** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`
。
形式化陈述：totalDegree_finsetSum_le {ι : Type*} {s : Finset ι} {f : ι -> MvPolynomial
 σ R} {d : Nat} (hf : forall i in s, (f i).totalDegree <= d) : (s.sum f).totalDe
gree <= d
参数：hf : forall i in s, (f i).totalDegree <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MvPolynomial.totalDegree_finsetSum`：totalDegree_finsetSum {ι : Type*} (s
 : Finset ι) (f : ι -> MvPolynomial σ R) : (s.sum f).totalDegree <= Finset.sup s
 fun i => (f i).totalDeg…
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
-/
lemma totalDegree_finsetSum_le {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial σ R} {d : ℕ}
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ d) : (s.sum f).totalDegree ≤ d :=
  (totalDegree_finsetSum ..).trans <| Finset.sup_le hf
/-
**MvPolynomial.degreeOf_le_totalDegree** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_le_totalDegree (f : MvPolynomial σ R) (i : σ) : f.degreeOf i <= f
.totalDegree
参数：f : MvPolynomial σ R；i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MvPolynomial.degreeOf_le_iff`：degreeOf_le_iff {n : σ} {f : MvPolynomial 
σ R} {d : Nat} : degreeOf n f <= d ↔ forall m in support f, m n <= d
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `MvPolynomial.le_totalDegree`：le_totalDegree {p : MvPolynomial σ R} {s : 
σ ->₀ Nat} (h : s in p.support) : (s.sum fun _ e => e) <= totalDegree p
-/
lemma degreeOf_le_totalDegree (f : MvPolynomial σ R) (i : σ) : f.degreeOf i ≤ f.totalDegree :=
  degreeOf_le_iff.mpr fun d hd ↦ (eq_or_ne (d i) 0).elim (by lia) fun h ↦
    (Finset.single_le_sum (by lia) <| Finsupp.mem_support_iff.mpr h).trans
    (le_totalDegree hd)
/-
**MvPolynomial.exists_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：exists_degree_lt [Fintype σ] (f : MvPolynomial σ R) (n : Nat) (h : f.total
Degree < n * Fintype.card σ) {d : σ ->₀ Nat} (hd : d in f.support) : exists i, d
 i < n
参数：f : MvPolynomial σ R；n : Nat；h : f.totalDegree < n * Fintype.card σ；hd : d in
 f.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Nat.nsmul_eq_mul`：∀ (m n : ℕ), m • n = m * n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MvPolynomial.le_totalDegree`：le_totalDegree {p : MvPolynomial σ R} {s : 
σ ->₀ Nat} (h : s in p.support) : (s.sum fun _ e => e) <= totalDegree p
-/
theorem exists_degree_lt [Fintype σ] (f : MvPolynomial σ R) (n : ℕ)
    (h : f.totalDegree < n * Fintype.card σ) {d : σ →₀ ℕ} (hd : d ∈ f.support) : ∃ i, d i < n := by
  contrapose! h
  calc
    n * Fintype.card σ = ∑ _s : σ, n := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm, Finset.card_univ]
    _ ≤ ∑ s, d s := Finset.sum_le_sum fun s _ => h s
    _ ≤ d.sum fun _ e => e := by
      rw [Finsupp.sum_fintype]
      intros
      rfl
    _ ≤ f.totalDegree := le_totalDegree hd
/-
**MvPolynomial.coeff_eq_zero_of_totalDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `MvPoly
nomial`。
形式化陈述：coeff_eq_zero_of_totalDegree_lt {f : MvPolynomial σ R} {d : σ ->₀ Nat} (h 
: f.totalDegree < ∑ i in d.support, d i) : coeff d f = 0
参数：h : f.totalDegree < ∑ i in d.support, d i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `MvPolynomial.totalDegree.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : Com
mSemiring R] (p : MvPolynomial σ R),   p.totalDegree = p.support.sup fun s => s.
sum fun x e => e
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
theorem coeff_eq_zero_of_totalDegree_lt {f : MvPolynomial σ R} {d : σ →₀ ℕ}
    (h : f.totalDegree < ∑ i ∈ d.support, d i) : coeff d f = 0 := by
  rw [totalDegree, Finset.sup_lt_iff] at h
  · specialize h d
    rw [mem_support_iff] at h
    refine not_not.mp (mt h ?_)
    exact lt_irrefl _
  · exact lt_of_le_of_lt (Nat.zero_le _) h
/-
**MvPolynomial.totalDegree_eq_zero_iff_eq_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynom
ial`。
形式化陈述：totalDegree_eq_zero_iff_eq_C {p : MvPolynomial σ R} : p.totalDegree = 0 ↔ 
p = C (p.coeff 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MvPolynomial.coeff_eq_zero_of_totalDegree_lt`：coeff_eq_zero_of_totalDegr
ee_lt {f : MvPolynomial σ R} {d : σ ->₀ Nat} (h : f.totalDegree < ∑ i in d.suppo
rt, d i) : coeff d f = 0
· 使用定理 `Finset.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M]
 [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι}
 [Ad…
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
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.support_nonempty_iff`：support_nonempty_iff {f : α ->₀ M} : f.sup
port.Nonempty ↔ f != 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MvPolynomial.totalDegree_C`：totalDegree_C (a : R) : (C a : MvPolynomial 
σ R).totalDegree = 0
-/
theorem totalDegree_eq_zero_iff_eq_C {p : MvPolynomial σ R} :
    p.totalDegree = 0 ↔ p = C (p.coeff 0) := by
  constructor <;> intro h
  · ext m; classical rw [coeff_C]; split_ifs with hm; · rw [← hm]
    apply coeff_eq_zero_of_totalDegree_lt; rw [h]
    exact Finset.sum_pos (fun i hi ↦ Nat.pos_of_ne_zero <| Finsupp.mem_support_iff.mp hi)
      (Finsupp.support_nonempty_iff.mpr <| Ne.symm hm)
  · rw [h, totalDegree_C]
/-
**MvPolynomial.totalDegree_rename_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_rename_le (f : σ -> τ) (p : MvPolynomial σ R) : (rename f p).t
otalDegree <= p.totalDegree
参数：f : σ -> τ；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Finsupp.mapDomain_support`：mapDomain_support [DecidableEq β] {f : α -> β
} {s : α ->₀ M} : (s.mapDomain f).support subseteq s.support.image f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `MvPolynomial.le_totalDegree`：le_totalDegree {p : MvPolynomial σ R} {s : 
σ ->₀ Nat} (h : s in p.support) : (s.sum fun _ e => e) <= totalDegree p
-/
theorem totalDegree_rename_le (f : σ → τ) (p : MvPolynomial σ R) :
    (rename f p).totalDegree ≤ p.totalDegree :=
  Finset.sup_le fun b h => by
    classical
    have h' := Finsupp.mapDomain_support h
    rw [Finset.mem_image] at h'
    rcases h' with ⟨s, hs, rfl⟩
    exact (sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)).trans_le (le_totalDegree hs)
/-
**MvPolynomial.totalDegree_renameEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_renameEquiv (f : σ ≃ τ) (p : MvPolynomial σ R) : (renameEquiv 
R f p).totalDegree = p.totalDegree
参数：f : σ ≃ τ；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MvPolynomial.totalDegree_rename_le`：totalDegree_rename_le (f : σ -> τ) (
p : MvPolynomial σ R) : (rename f p).totalDegree <= p.totalDegree
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_rename`：rename_rename (f : σ -> τ) (g : τ -> α) (p :
 MvPolynomial σ R) : rename g (rename f p) = rename (g ∘ f) p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `MvPolynomial.rename_id`：rename_id : rename id = AlgHom.id R (MvPolynomia
l σ R)
-/
lemma totalDegree_renameEquiv (f : σ ≃ τ) (p : MvPolynomial σ R) :
    (renameEquiv R f p).totalDegree = p.totalDegree :=
  (totalDegree_rename_le f p).antisymm (le_trans (by simp) (totalDegree_rename_le f.symm _))

end TotalDegree

section degreesLE
variable {s t : Multiset σ}

variable (R σ s) in
set_option backward.isDefEq.respectTransparency false in
/-- The submodule of multivariate polynomials of degrees bounded by a monomial `s`. -/
/-
**MvPolynomial.degreesLE** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：degreesLE : Submodule R (MvPolynomial σ R) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of multivariate polynomials of degrees bounded by a monomial `s`.
-/
def degreesLE : Submodule R (MvPolynomial σ R) where
  carrier := {p | p.degrees ≤ s}
  add_mem' {a b} ha hb := by classical exact degrees_add_le.trans (sup_le ha hb)
  zero_mem' := by simp
  smul_mem' c {x} hx := by
    dsimp
    rw [Algebra.smul_def]
    refine degrees_mul_le.trans ?_
    simpa [degrees_C] using hx
/-
**MvPolynomial.mem_degreesLE** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring R] {p : MvPolynomial σ 
R} {s : Multiset σ},   p ∈ MvPolynomial.degreesLE R σ s ↔ p.degrees ≤ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_degreesLE : p ∈ degreesLE R σ s ↔ p.degrees ≤ s := Iff.rfl

variable (s t) in
set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.degreesLE_add** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：degreesLE_add : degreesLE R σ (s + t) = degreesLE R σ s * degreesLE R σ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `Submodule.mul_le`：mul_le : M * N <= P ↔ forall m in M, forall n in N, m 
* n in P
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.toFinsupp_symm_apply`：∀ {α : Type u_1} [inst : DecidableEq α] (
f : α →₀ ℕ), Multiset.toFinsupp.symm f = Finsupp.toMultiset f
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Multiset.toFinsupp_toMultiset`：toFinsupp_toMultiset (s : Multiset α) : F
insupp.toMultiset (toFinsupp s) = s
· 使用引理 `Multiset.sub_add_inter`：sub_add_inter (s t : Multiset α) : s - t + s int
er t = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.instOrderedSub`：∀ {α : Type u_1} [inst : DecidableEq α], Ordere
dSub (Multiset α)
· 使用定理 `MvPolynomial.monomial_mul`：monomial_mul {s s' : σ ->₀ Nat} {a b : R} : m
onomial s a * monomial s' b = monomial (s + s') (a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `MvPolynomial.degrees_monomial`：degrees_monomial (s : σ ->₀ Nat) (a : R) 
: degrees (monomial s a) <= toMultiset s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.as_sum`：as_sum (p : MvPolynomial σ R) : p = ∑ v in p.suppor
t, monomial v (coeff v p)
· 使用定理 `MvPolynomial.degrees_mul_le`：degrees_mul_le {p q : MvPolynomial σ R} : (
p * q).degrees <= p.degrees + q.degrees
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma degreesLE_add : degreesLE R σ (s + t) = degreesLE R σ s * degreesLE R σ t := by
  classical
  rw [le_antisymm_iff, Submodule.mul_le]
  refine ⟨fun x hx ↦ x.as_sum ▸ sum_mem fun i hi ↦ ?_,
    fun x hx y hy ↦ degrees_mul_le.trans (add_le_add hx hy)⟩
  replace hi : i.toMultiset ≤ s + t := (Finset.le_sup hi).trans hx
  let a := (i.toMultiset - t).toFinsupp
  let b := (i.toMultiset ⊓ t).toFinsupp
  have : a + b = i := Multiset.toFinsupp.symm.injective (by simp [a, b, Multiset.sub_add_inter])
  have ha : a.toMultiset ≤ s := by simpa [a, add_comm (a := t)] using hi
  have hb : b.toMultiset ≤ t := by simp [b, Multiset.inter_le_right]
  rw [show monomial i (x.coeff i) = monomial a (x.coeff i) * monomial b 1 by simp [this]]
  exact Submodule.mul_mem_mul ((degrees_monomial _ _).trans ha) ((degrees_monomial _ _).trans hb)

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.degreesLE_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring R], MvPolynomial.degree
sLE R σ 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.totalDegree_eq_zero_iff_eq_C`：totalDegree_eq_zero_iff_eq_C 
{p : MvPolynomial σ R} : p.totalDegree = 0 ↔ p = C (p.coeff 0)
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MvPolynomial.totalDegree_le_degrees_card`：totalDegree_le_degrees_card (p
 : MvPolynomial σ R) : p.totalDegree <= Multiset.card p.degrees
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Multiset.instCanonicallyOrderedAdd`：∀ {α : Type u_1}, CanonicallyOrdered
Add (Multiset α)
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.degrees_one`：degrees_one : degrees (1 : MvPolynomial σ R) =
 0
-/
@[simp] lemma degreesLE_zero : degreesLE R σ 0 = 1 := by
  refine le_antisymm (fun x hx ↦ ?_) (by simp)
  simp only [mem_degreesLE, nonpos_iff_eq_zero] at hx
  have := (totalDegree_eq_zero_iff_eq_C (p := x)).mp
    (Nat.eq_zero_of_le_zero (x.totalDegree_le_degrees_card.trans (by simp [hx])))
  exact ⟨x.coeff 0, by simp [Algebra.smul_def, ← this]⟩

variable (s) in
/-
**MvPolynomial.degreesLE_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring R] (s : Multiset σ) (n 
: ℕ),   MvPolynomial.degreesLE R σ (n • s) = MvPolynomial.degreesLE R σ s ^ n
参数：s : Multiset σ；n : ℕ；n • s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma degreesLE_nsmul : ∀ n, degreesLE R σ (n • s) = degreesLE R σ s ^ n
  | 0 => by simp
  | k + 1 => by simp only [pow_succ, degreesLE_nsmul, degreesLE_add, add_smul, one_smul]

end degreesLE
end CommSemiring

end MvPolynomial

