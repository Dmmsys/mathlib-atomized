/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Devon Tuma
-/
module

public import Mathlib.Algebra.Polynomial.Splits

/-!
# Scaling the roots of a polynomial

This file defines `scaleRoots p s` for a polynomial `p` in one variable and a ring element `s` to
be the polynomial with root `r * s` for each root `r` of `p` and proves some basic results about it.
-/

@[expose] public section


variable {R S A K : Type*}

namespace Polynomial

section Semiring

variable [Semiring R] [Semiring S]

/-- `scaleRoots p s` is a polynomial with root `r * s` for each root `r` of `p`. -/
/-
**Polynomial.scaleRoots** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：scaleRoots (p : R[X]) (s : R) : R[X]
参数：p : R[X]；s : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`scaleRoots p s` is a polynomial with root `r * s` for each root `r` of `p`.
-/
noncomputable def scaleRoots (p : R[X]) (s : R) : R[X] :=
  ∑ i ∈ p.support, monomial i (p.coeff i * s ^ (p.natDegree - i))

@[simp]
/-
**Polynomial.coeff_scaleRoots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_scaleRoots (p : R[X]) (s : R) (i : Nat) : (scaleRoots p s).coeff i =
 coeff p i * s ^ (p.natDegree - i)
参数：p : R[X]；s : R；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coeff_scaleRoots (p : R[X]) (s : R) (i : ℕ) :
    (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i) := by
  simp +contextual [scaleRoots, coeff_monomial]
/-
**Polynomial.coeff_scaleRoots_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_scaleRoots_natDegree (p : R[X]) (s : R) : (scaleRoots p s).coeff p.n
atDegree = p.leadingCoeff
参数：p : R[X]；s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem coeff_scaleRoots_natDegree (p : R[X]) (s : R) :
    (scaleRoots p s).coeff p.natDegree = p.leadingCoeff := by
  rw [leadingCoeff, coeff_scaleRoots, tsub_self, pow_zero, mul_one]

@[simp]
/-
**Polynomial.zero_scaleRoots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：zero_scaleRoots (s : R) : scaleRoots 0 s = 0
参数：s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_scaleRoots (s : R) : scaleRoots 0 s = 0 := by
  ext
  simp
/-
**Polynomial.scaleRoots_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：scaleRoots_ne_zero {p : R[X]} (hp : p != 0) (s : R) : scaleRoots p s != 0
参数：hp : p != 0；s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_scaleRoots_natDegree`：coeff_scaleRoots_natDegree (p : R
[X]) (s : R) : (scaleRoots p s).coeff p.natDegree = p.leadingCoeff
-/
theorem scaleRoots_ne_zero {p : R[X]} (hp : p ≠ 0) (s : R) : scaleRoots p s ≠ 0 := by
  intro h
  have : p.coeff p.natDegree ≠ 0 := mt leadingCoeff_eq_zero.mp hp
  have : (scaleRoots p s).coeff p.natDegree = 0 :=
    congr_fun (congr_arg (coeff : R[X] → ℕ → R) h) p.natDegree
  rw [coeff_scaleRoots_natDegree] at this
  contradiction
/-
**Polynomial.support_scaleRoots_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_scaleRoots_le (p : R[X]) (s : R) : (scaleRoots p s).support <= p.s
upport
参数：p : R[X]；s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
-/
theorem support_scaleRoots_le (p : R[X]) (s : R) : (scaleRoots p s).support ≤ p.support := by
  intro
  simpa using left_ne_zero_of_mul
/-
**Polynomial.support_scaleRoots_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_scaleRoots_eq (p : R[X]) {s : R} (hs : s in nonZeroDivisors R) : (
scaleRoots p s).support = p.support
参数：p : R[X]；hs : s in nonZeroDivisors R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.support_scaleRoots_le`：support_scaleRoots_le (p : R[X]) (s : 
R) : (scaleRoots p s).support <= p.support
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
theorem support_scaleRoots_eq (p : R[X]) {s : R} (hs : s ∈ nonZeroDivisors R) :
    (scaleRoots p s).support = p.support :=
  le_antisymm (support_scaleRoots_le p s)
    (by intro i
        simp only [coeff_scaleRoots, Polynomial.mem_support_iff]
        intro p_ne_zero ps_zero
        have := (pow_mem hs (p.natDegree - i)).2 _ ps_zero
        contradiction)

@[simp]
/-
**Polynomial.degree_scaleRoots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_scaleRoots (p : R[X]) {s : R} : degree (scaleRoots p s) = degree p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.zero_scaleRoots`：zero_scaleRoots (s : R) : scaleRoots 0 s = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `Polynomial.support_scaleRoots_le`：support_scaleRoots_le (p : R[X]) (s : 
R) : (scaleRoots p s).support <= p.support
· 使用定理 `Polynomial.degree_le_degree`：degree_le_degree (h : coeff q (natDegree p)
 != 0) : degree p <= degree q
· 使用定理 `Polynomial.coeff_scaleRoots_natDegree`：coeff_scaleRoots_natDegree (p : R
[X]) (s : R) : (scaleRoots p s).coeff p.natDegree = p.leadingCoeff
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
-/
theorem degree_scaleRoots (p : R[X]) {s : R} : degree (scaleRoots p s) = degree p := by
  have := Classical.propDecidable
  by_cases hp : p = 0
  · rw [hp, zero_scaleRoots]
  refine le_antisymm (Finset.sup_mono (support_scaleRoots_le p s)) (degree_le_degree ?_)
  rw [coeff_scaleRoots_natDegree]
  intro h
  have := leadingCoeff_eq_zero.mp h
  contradiction

@[simp]
/-
**Polynomial.natDegree_scaleRoots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_scaleRoots (p : R[X]) (s : R) : natDegree (scaleRoots p s) = nat
Degree p
参数：p : R[X]；s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_scaleRoots`：degree_scaleRoots (p : R[X]) {s : R} : deg
ree (scaleRoots p s) = degree p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natDegree_scaleRoots (p : R[X]) (s : R) : natDegree (scaleRoots p s) = natDegree p := by
  simp only [natDegree, degree_scaleRoots]

@[simp]
/-
**Polynomial.leadingCoeff_scaleRoots** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_scaleRoots (p : R[X]) (r : R) : (p.scaleRoots r).leadingCoeff
 = p.leadingCoeff
参数：p : R[X]；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.natDegree_scaleRoots`：natDegree_scaleRoots (p : R[X]) (s : R)
 : natDegree (scaleRoots p s) = natDegree p
· 使用定理 `Polynomial.coeff_scaleRoots_natDegree`：coeff_scaleRoots_natDegree (p : R
[X]) (s : R) : (scaleRoots p s).coeff p.natDegree = p.leadingCoeff
-/
lemma leadingCoeff_scaleRoots (p : R[X]) (r : R) :
    (p.scaleRoots r).leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]
/-
**Polynomial.monic_scaleRoots_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_scaleRoots_iff {p : R[X]} (s : R) : Monic (scaleRoots p s) ↔ Monic p
参数：s : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.leadingCoeff_scaleRoots`：leadingCoeff_scaleRoots (p : R[X]) (
r : R) : (p.scaleRoots r).leadingCoeff = p.leadingCoeff
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem monic_scaleRoots_iff {p : R[X]} (s : R) : Monic (scaleRoots p s) ↔ Monic p := by
  simp only [Monic, leadingCoeff_scaleRoots]
/-
**Polynomial.map_scaleRoots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_scaleRoots (p : R[X]) (x : R) (f : R ->+* S) (h : f p.leadingCoeff != 
0) : (p.scaleRoots x).map f = (p.map f).scaleRoots (f x)
参数：p : R[X]；x : R；f : R ->+* S；h : f p.leadingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.natDegree_map_of_leadingCoeff_ne_zero`：natDegree_map_of_leadi
ngCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) : natDegree (p.map
 f) = natDegree p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_scaleRoots (p : R[X]) (x : R) (f : R →+* S) (h : f p.leadingCoeff ≠ 0) :
    (p.scaleRoots x).map f = (p.map f).scaleRoots (f x) := by
  ext
  simp [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ h]

@[simp]
/-
**Polynomial.scaleRoots_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：scaleRoots_C (r c : R) : (C c).scaleRoots r = C c
参数：r c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma scaleRoots_C (r c : R) : (C c).scaleRoots r = C c := by
  ext; simp

@[simp]
/-
**Polynomial.scaleRoots_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：scaleRoots_one (p : R[X]) : p.scaleRoots 1 = p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma scaleRoots_one (p : R[X]) :
    p.scaleRoots 1 = p := by ext; simp

@[simp]
/-
**Polynomial.scaleRoots_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：scaleRoots_zero (p : R[X]) : p.scaleRoots 0 = p.leadingCoeff • X ^ p.natDe
gree
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用引理 `zero_pow_eq`：zero_pow_eq (n : Nat) : (0 : M₀) ^ n = if n = 0 then 1 else
 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
lemma scaleRoots_zero (p : R[X]) :
    p.scaleRoots 0 = p.leadingCoeff • X ^ p.natDegree := by
  ext n
  simp only [coeff_scaleRoots, tsub_eq_zero_iff_le, zero_pow_eq, mul_ite,
    mul_one, mul_zero, coeff_smul, coeff_X_pow, smul_eq_mul]
  split_ifs with h₁ h₂ h₂
  · subst h₂; rfl
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne h₁ (Ne.symm h₂))
  · exact (h₁ h₂.ge).elim
  · rfl

@[simp]
/-
**Polynomial.one_scaleRoots** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：one_scaleRoots (r : R) : (1 : R[X]).scaleRoots r = 1
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma one_scaleRoots (r : R) :
    (1 : R[X]).scaleRoots r = 1 := by ext; simp

@[simp]
/-
**Polynomial.X_add_C_scaleRoots** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：X_add_C_scaleRoots (r s : R) : (X + C r).scaleRoots s = (X + C (r * s))
参数：r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_X_one`：coeff_X_one : coeff (X : R[X]) 1 = 1
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.coeff_mul_C`：coeff_mul_C (p : R[X]) (n : Nat) (a : R) : coeff
 (p * C a) n = coeff p n * a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
（共 40 条，此处仅展示前 30 条）
-/
lemma X_add_C_scaleRoots (r s : R) : (X + C r).scaleRoots s = (X + C (r * s)) := by
  nontriviality R
  ext (_ | _ | i) <;> simp

end Semiring

section CommSemiring

variable [Semiring S] [CommSemiring R] [Semiring A] [Field K]

/-
**Polynomial.scaleRoots_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem scaleRoots_eval₂_mul_of_commute {p : S[X]} (f : S →+* A) (a : A) (s : S)
    (hsa : Commute (f s) a) (hf : ∀ s₁ s₂, Commute (f s₁) (f s₂)) :
    eval₂ f (f s * a) (scaleRoots p s) = f s ^ p.natDegree * eval₂ f a p := by
  calc
    _ = (scaleRoots p s).support.sum fun i =>
          f (coeff p i * s ^ (p.natDegree - i)) * (f s * a) ^ i := by
      simp [eval₂_eq_sum, sum_def]
    _ = p.support.sum fun i => f (coeff p i * s ^ (p.natDegree - i)) * (f s * a) ^ i :=
      (Finset.sum_subset (support_scaleRoots_le p s) fun i _hi hi' => by
        let : coeff p i * s ^ (p.natDegree - i) = 0 := by simpa using hi'
        simp [this])
    _ = p.support.sum fun i : ℕ => f (p.coeff i) * f s ^ (p.natDegree - i + i) * a ^ i :=
      (Finset.sum_congr rfl fun i _hi => by
        simp_rw [f.map_mul, f.map_pow, pow_add, hsa.mul_pow, mul_assoc])
    _ = p.support.sum fun i : ℕ => f s ^ p.natDegree * (f (p.coeff i) * a ^ i) :=
      Finset.sum_congr rfl fun i hi => by
        rw [mul_assoc, ← map_pow, (hf _ _).left_comm, map_pow, tsub_add_cancel_of_le]
        exact le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)
    _ = f s ^ p.natDegree * eval₂ f a p := by simp [← Finset.mul_sum, eval₂_eq_sum, sum_def]
/-
**Polynomial.scaleRoots_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem scaleRoots_eval₂_mul {p : S[X]} (f : S →+* R) (r : R) (s : S) :
    eval₂ f (f s * r) (scaleRoots p s) = f s ^ p.natDegree * eval₂ f r p :=
  scaleRoots_eval₂_mul_of_commute f r s (mul_comm _ _) fun _ _ ↦ mul_comm _ _
/-
**Polynomial.scaleRoots_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem scaleRoots_eval₂_eq_zero {p : S[X]} (f : S →+* R) {r : R} {s : S} (hr : eval₂ f r p = 0) :
    eval₂ f (f s * r) (scaleRoots p s) = 0 := by rw [scaleRoots_eval₂_mul, hr, mul_zero]
/-
**Polynomial.scaleRoots_eval_mul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：scaleRoots_eval_mul (p : R[X]) (r s : R) : eval (s * r) (p.scaleRoots s) =
 s ^ p.natDegree * eval r p
参数：p : R[X]；r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.scaleRoots_eval₂_mul`：scaleRoots_eval₂_mul {p : S[X]} (f : S 
->+* R) (r : R) (s : S) : eval₂ f (f s * r) (scaleRoots p s) = f s ^ p.natDegree
 * eval₂ f r p
-/
lemma scaleRoots_eval_mul (p : R[X]) (r s : R) :
    eval (s * r) (p.scaleRoots s) = s ^ p.natDegree * eval r p :=
  scaleRoots_eval₂_mul _ _ _
/-
**Polynomial.scaleRoots_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：scaleRoots_aeval_eq_zero [Algebra R A] {p : R[X]} {a : A} {r : R} (ha : ae
val a p = 0) : aeval (algebraMap R A r * a) (scaleRoots p r) = 0
参数：ha : aeval a p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.scaleRoots_eval₂_mul_of_commute`：scaleRoots_eval₂_mul_of_comm
ute {p : S[X]} (f : S ->+* A) (a : A) (s : S) (hsa : Commute (f s) a) (hf : fora
ll s₁ s₂, Commute (f s₁) (f s₂))…
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `Commute.eq_1`：∀ {S : Type u_3} [inst : Mul S] (a b : S), Commute a b = S
emiconjBy a b b
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem scaleRoots_aeval_eq_zero [Algebra R A] {p : R[X]} {a : A} {r : R} (ha : aeval a p = 0) :
    aeval (algebraMap R A r * a) (scaleRoots p r) = 0 := by
  rw [aeval_def, scaleRoots_eval₂_mul_of_commute, ← aeval_def, ha, mul_zero]
  · apply Algebra.commutes
  · intros; rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
/-
**Polynomial.scaleRoots_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero {p : S[X]} {f : S →+* K}
    (hf : Function.Injective f) {r s : S} (hr : eval₂ f (f r / f s) p = 0)
    (hs : s ∈ nonZeroDivisors S) : eval₂ f (f r) (scaleRoots p s) = 0 := by
  -- if we don't specify the type with `(_ : S)`, the proof is much slower
  nontriviality S using Subsingleton.eq_zero (α := S)
  convert! @scaleRoots_eval₂_eq_zero _ _ _ _ p f _ s hr
  rw [← mul_div_assoc, mul_comm, mul_div_cancel_right₀]
  exact map_ne_zero_of_mem_nonZeroDivisors _ hf hs
/-
**Polynomial.scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial`。
形式化陈述：scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero [Algebra R K] (inj : Functio
n.Injective (algebraMap R K)) {p : R[X]} {r s : R} (hr : aeval (algebraMap R K r
 / algebraMap R K s) p = 0) (hs : s in nonZeroDivisors R) : aeval (algebraMap R 
K r) (scaleRoots p s) = 0
参数：inj : Function.Injective (algebraMap R K)；hr : aeval (algebraMap R K r / alge
braMap R K s) p = 0；hs : s in nonZeroDivisors R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero`：scaleRoots_eva
l₂_eq_zero_of_eval₂_div_eq_zero {p : S[X]} {f : S ->+* K} (hf : Function.Injecti
ve f) {r s : S} (hr : eval₂ f (f r / f s) p = …
-/
theorem scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero [Algebra R K]
    (inj : Function.Injective (algebraMap R K)) {p : R[X]} {r s : R}
    (hr : aeval (algebraMap R K r / algebraMap R K s) p = 0) (hs : s ∈ nonZeroDivisors R) :
    aeval (algebraMap R K r) (scaleRoots p s) = 0 :=
  scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero inj hr hs

@[simp]
/-
**Polynomial.scaleRoots_mul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：scaleRoots_mul (p : R[X]) (r s) : p.scaleRoots (r * s) = (p.scaleRoots r).
scaleRoots s
参数：p : R[X]；r s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.natDegree_scaleRoots`：natDegree_scaleRoots (p : R[X]) (s : R)
 : natDegree (scaleRoots p s) = natDegree p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma scaleRoots_mul (p : R[X]) (r s) :
    p.scaleRoots (r * s) = (p.scaleRoots r).scaleRoots s := by
  ext; simp [mul_pow, mul_assoc]

/-- Multiplication and `scaleRoots` commute up to a power of `r`. The factor disappears if we
assume that the product of the leading coeffs does not vanish. See `Polynomial.mul_scaleRoots'`. -/
/-
**Polynomial.mul_scaleRoots** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mul_scaleRoots (p q : R[X]) (r : R) : r ^ (natDegree p + natDegree q - nat
Degree (p * q)) • (p * q).scaleRoots r = p.scaleRoots r * q.scaleRoots r
参数：p q : R[X]；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tsub_add_tsub_cancel`：tsub_add_tsub_cancel (hab : b <= a) (hcb : c <= b)
 : a - b + (b - c) = a - c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.natDegree_mul_le`：natDegree_mul_le {p q : R[X]} : natDegree (
p * q) <= natDegree p + natDegree q
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `tsub_add_tsub_comm`：tsub_add_tsub_comm (hba : b <= a) (hdc : d <= c) : a
 - b + (c - d) = a + c - (b + d)
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G

--- 原说明 ---
Multiplication and `scaleRoots` commute up to a power of `r`. The factor disappe
ars if we
assume that the product of the leading coeffs does not vanish. See `Polynomial.m
ul_scaleRoots'`.
-/
lemma mul_scaleRoots (p q : R[X]) (r : R) :
    r ^ (natDegree p + natDegree q - natDegree (p * q)) • (p * q).scaleRoots r =
      p.scaleRoots r * q.scaleRoots r := by
  ext n; simp only [coeff_scaleRoots, coeff_smul, smul_eq_mul]
  trans (∑ x ∈ Finset.antidiagonal n, coeff p x.1 * coeff q x.2) *
    r ^ (natDegree p + natDegree q - n)
  · rw [← coeff_mul]
    cases lt_or_ge (natDegree (p * q)) n with
    | inl h => simp only [coeff_eq_zero_of_natDegree_lt h, zero_mul, mul_zero]
    | inr h =>
      rw [mul_comm, mul_assoc, ← pow_add, add_comm, tsub_add_tsub_cancel natDegree_mul_le h]
  · rw [coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    simp only [Finset.mem_antidiagonal, coeff_scaleRoots, Prod.forall]
    intro a b e
    cases lt_or_ge (natDegree p) a with
    | inl h => simp only [coeff_eq_zero_of_natDegree_lt h, zero_mul]
    | inr ha =>
      cases lt_or_ge (natDegree q) b with
      | inl h => simp only [coeff_eq_zero_of_natDegree_lt h, zero_mul, mul_zero]
      | inr hb =>
        simp only [← e, mul_assoc, mul_comm (r ^ (_ - a)), ← pow_add]
        rw [add_comm (_ - _), tsub_add_tsub_comm ha hb]
/-
**Polynomial.mul_scaleRoots'** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mul_scaleRoots' (p q : R[X]) (r : R) (h : leadingCoeff p * leadingCoeff q 
!= 0) : (p * q).scaleRoots r = p.scaleRoots r * q.scaleRoots r
参数：p q : R[X]；r : R；h : leadingCoeff p * leadingCoeff q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.mul_scaleRoots`：mul_scaleRoots (p q : R[X]) (r : R) : r ^ (na
tDegree p + natDegree q - natDegree (p * q)) • (p * q).scaleRoots r = p.scaleRoo
ts r * q.scaleR…
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma mul_scaleRoots' (p q : R[X]) (r : R) (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    (p * q).scaleRoots r = p.scaleRoots r * q.scaleRoots r := by
  rw [← mul_scaleRoots, natDegree_mul' h, tsub_self, pow_zero, one_smul]
/-
**Polynomial.mul_scaleRoots_of_noZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 `Polynom
ial`。
形式化陈述：mul_scaleRoots_of_noZeroDivisors (p q : R[X]) (r : R) [NoZeroDivisors R] :
 (p * q).scaleRoots r = p.scaleRoots r * q.scaleRoots r
参数：p q : R[X]；r : R。
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.zero_scaleRoots`：zero_scaleRoots (s : R) : scaleRoots 0 s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `Polynomial.mul_scaleRoots'`：mul_scaleRoots' (p q : R[X]) (r : R) (h : le
adingCoeff p * leadingCoeff q != 0) : (p * q).scaleRoots r = p.scaleRoots r * q.
scaleRoots r
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma mul_scaleRoots_of_noZeroDivisors (p q : R[X]) (r : R) [NoZeroDivisors R] :
    (p * q).scaleRoots r = p.scaleRoots r * q.scaleRoots r := by
  by_cases hp : p = 0; · simp [hp]
  by_cases hq : q = 0; · simp [hq]
  apply mul_scaleRoots'
  simp only [ne_eq, mul_eq_zero, leadingCoeff_eq_zero, hp, hq, or_self, not_false_eq_true]
/-
**Polynomial.pow_scaleRoots'** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：pow_scaleRoots' (p : R[X]) (r : R) (n : Nat) (hp : p.leadingCoeff ^ n != 0
) : (p ^ n).scaleRoots r = p.scaleRoots r ^ n
参数：p : R[X]；r : R；n : Nat；hp : p.leadingCoeff ^ n != 0。
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
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `Polynomial.one_scaleRoots`：one_scaleRoots (r : R) : (1 : R[X]).scaleRoot
s r = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `Polynomial.mul_scaleRoots'`：mul_scaleRoots' (p q : R[X]) (r : R) (h : le
adingCoeff p * leadingCoeff q != 0) : (p * q).scaleRoots r = p.scaleRoots r * q.
scaleRoots r
· 使用定理 `Polynomial.leadingCoeff_pow'`：leadingCoeff_pow' : leadingCoeff p ^ n != 
0 -> leadingCoeff (p ^ n) = leadingCoeff p ^ n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pow_scaleRoots' (p : R[X]) (r : R) (n : ℕ)
    (hp : p.leadingCoeff ^ n ≠ 0) :
    (p ^ n).scaleRoots r = p.scaleRoots r ^ n := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [pow_succ, mul_scaleRoots', IH, pow_succ]
    · refine mt (by simp +contextual [pow_succ]) hp
    · rwa [leadingCoeff_pow' (mt (by simp +contextual [pow_succ]) hp), ← pow_succ]
/-
**Polynomial.pow_scaleRoots_of_isReduced** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：pow_scaleRoots_of_isReduced [IsReduced R] (p : R[X]) (r : R) (n : Nat) : (
p ^ n).scaleRoots r = p.scaleRoots r ^ n
参数：p : R[X]；r : R；n : Nat。
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
· 使用引理 `zero_pow_eq`：zero_pow_eq (n : Nat) : (0 : M₀) ^ n = if n = 0 then 1 else
 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `Polynomial.one_scaleRoots`：one_scaleRoots (r : R) : (1 : R[X]).scaleRoot
s r = 1
· 使用定理 `Polynomial.zero_scaleRoots`：zero_scaleRoots (s : R) : scaleRoots 0 s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `Polynomial.pow_scaleRoots'`：pow_scaleRoots' (p : R[X]) (r : R) (n : Nat)
 (hp : p.leadingCoeff ^ n != 0) : (p ^ n).scaleRoots r = p.scaleRoots r ^ n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma pow_scaleRoots_of_isReduced [IsReduced R] (p : R[X]) (r : R) (n : ℕ) :
    (p ^ n).scaleRoots r = p.scaleRoots r ^ n := by
  by_cases hp : p = 0
  · simp [hp, zero_pow_eq, apply_ite (scaleRoots · r)]
  by_cases hn : n = 0
  · simp [hn]
  exact pow_scaleRoots' _ _ _ (by simp_all)
/-
**Polynomial.add_scaleRoots_of_natDegree_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l`。
形式化陈述：add_scaleRoots_of_natDegree_eq (p q : R[X]) (r : R) (h : natDegree p = nat
Degree q) : r ^ (natDegree p - natDegree (p + q)) • (p + q).scaleRoots r = p.sca
leRoots r + q.scaleRoots r
参数：p q : R[X]；r : R；h : natDegree p = natDegree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tsub_add_tsub_cancel`：tsub_add_tsub_cancel (hab : b <= a) (hcb : c <= b)
 : a - b + (b - c) = a - c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.natDegree_add_le_of_degree_le`：natDegree_add_le_of_degree_le 
{p q : R[X]} {n : Nat} (hp : natDegree p <= n) (hq : natDegree q <= n) : natDegr
ee (p + q) <= n
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
lemma add_scaleRoots_of_natDegree_eq (p q : R[X]) (r : R) (h : natDegree p = natDegree q) :
    r ^ (natDegree p - natDegree (p + q)) • (p + q).scaleRoots r =
      p.scaleRoots r + q.scaleRoots r := by
  ext n; simp only [coeff_smul, coeff_scaleRoots, coeff_add, smul_eq_mul,
    mul_comm (r ^ _), ← h, ← add_mul]
  #adaptation_note /-- v4.7.0-rc1
  Previously `mul_assoc` was part of the `simp only` above, and this `rw` was not needed.
  but this now causes a max rec depth error. -/
  rw [mul_assoc, ← pow_add]
  cases lt_or_ge (natDegree (p + q)) n with
  | inl hn => simp only [← coeff_add, coeff_eq_zero_of_natDegree_lt hn, zero_mul]
  | inr hn =>
      rw [add_comm (_ - n), tsub_add_tsub_cancel (natDegree_add_le_of_degree_le le_rfl h.ge) hn]
/-
**Polynomial.scaleRoots_dvd'** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：scaleRoots_dvd' (p q : R[X]) {r : R} (hr : IsUnit r) (hpq : p ∣ q) : p.sca
leRoots r ∣ q.scaleRoots r
参数：p q : R[X]；hr : IsUnit r；hpq : p ∣ q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.dvd_mul_left`：dvd_mul_left (hu : IsUnit u) : a ∣ u * b ↔ a ∣ b
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用引理 `Polynomial.mul_scaleRoots`：mul_scaleRoots (p q : R[X]) (r : R) : r ^ (na
tDegree p + natDegree q - natDegree (p * q)) • (p * q).scaleRoots r = p.scaleRoo
ts r * q.scaleR…
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
lemma scaleRoots_dvd' (p q : R[X]) {r : R} (hr : IsUnit r)
    (hpq : p ∣ q) : p.scaleRoots r ∣ q.scaleRoots r := by
  obtain ⟨a, rfl⟩ := hpq
  rw [← ((hr.pow (natDegree p + natDegree a - natDegree (p * a))).map
    (algebraMap R R[X])).dvd_mul_left, ← Algebra.smul_def, mul_scaleRoots]
  exact dvd_mul_right (scaleRoots p r) (scaleRoots a r)
/-
**Polynomial.scaleRoots_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：scaleRoots_dvd (p q : R[X]) {r : R} [NoZeroDivisors R] (hpq : p ∣ q) : p.s
caleRoots r ∣ q.scaleRoots r
参数：p q : R[X]；hpq : p ∣ q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.mul_scaleRoots_of_noZeroDivisors`：mul_scaleRoots_of_noZeroDiv
isors (p q : R[X]) (r : R) [NoZeroDivisors R] : (p * q).scaleRoots r = p.scaleRo
ots r * q.scaleRoots r
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma scaleRoots_dvd (p q : R[X]) {r : R} [NoZeroDivisors R] (hpq : p ∣ q) :
    p.scaleRoots r ∣ q.scaleRoots r := by
  obtain ⟨a, rfl⟩ := hpq
  rw [mul_scaleRoots_of_noZeroDivisors]
  exact dvd_mul_right (scaleRoots p r) (scaleRoots a r)
alias _root_.Dvd.dvd.scaleRoots := scaleRoots_dvd
/-
**Polynomial.scaleRoots_dvd_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：scaleRoots_dvd_iff (p q : R[X]) {r : R} (hr : IsUnit r) : p.scaleRoots r ∣
 q.scaleRoots r ↔ p ∣ q
参数：p q : R[X]；hr : IsUnit r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用引理 `Polynomial.scaleRoots_one`：scaleRoots_one (p : R[X]) : p.scaleRoots 1 = 
p
· 使用引理 `Polynomial.scaleRoots_dvd'`：scaleRoots_dvd' (p q : R[X]) {r : R} (hr : I
sUnit r) (hpq : p ∣ q) : p.scaleRoots r ∣ q.scaleRoots r
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
lemma scaleRoots_dvd_iff (p q : R[X]) {r : R} (hr : IsUnit r) :
    p.scaleRoots r ∣ q.scaleRoots r ↔ p ∣ q := by
  refine ⟨?_ ∘ scaleRoots_dvd' _ _ (hr.unit⁻¹).isUnit, scaleRoots_dvd' p q hr⟩
  simp [← scaleRoots_mul, scaleRoots_one]
alias _root_.IsUnit.scaleRoots_dvd_iff := scaleRoots_dvd_iff
/-
**Polynomial.isCoprime_scaleRoots** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isCoprime_scaleRoots (p q : R[X]) (r : R) (hr : IsUnit r) (h : IsCoprime p
 q) : IsCoprime (p.scaleRoots r) (q.scaleRoots r)
参数：p q : R[X]；r : R；hr : IsUnit r；h : IsCoprime p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.natDegree_eq_of_natDegree_add_eq_zero`：natDegree_eq_of_natDeg
ree_add_eq_zero (p q : R[X]) (H : natDegree (p + q) = 0) : natDegree p = natDegr
ee q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.add_scaleRoots_of_natDegree_eq`：add_scaleRoots_of_natDegree_e
q (p q : R[X]) (r : R) (h : natDegree p = natDegree q) : r ^ (natDegree p - natD
egree (p + q)) • (p + q).scaleR…
· 使用引理 `Polynomial.one_scaleRoots`：one_scaleRoots (r : R) : (1 : R[X]).scaleRoot
s r = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isCoprime_scaleRoots (p q : R[X]) (r : R) (hr : IsUnit r) (h : IsCoprime p q) :
    IsCoprime (p.scaleRoots r) (q.scaleRoots r) := by
  obtain ⟨a, b, e⟩ := h
  let s : R := ↑hr.unit⁻¹
  have : natDegree (a * p) = natDegree (b * q) := by
    apply natDegree_eq_of_natDegree_add_eq_zero
    rw [e, natDegree_one]
  use s ^ natDegree (a * p) • s ^ (natDegree a + natDegree p - natDegree (a * p)) • a.scaleRoots r
  use s ^ natDegree (a * p) • s ^ (natDegree b + natDegree q - natDegree (b * q)) • b.scaleRoots r
  simp only [smul_smul, smul_mul_assoc, ← mul_scaleRoots, mul_assoc, ← mul_pow, IsUnit.val_inv_mul,
    one_pow, mul_one, ← smul_add, ← add_scaleRoots_of_natDegree_eq _ _ _ this, e, natDegree_one,
    Nat.sub_zero, one_scaleRoots, one_smul, s]

alias _root_.IsCoprime.scaleRoots := isCoprime_scaleRoots
/-
**Polynomial.Splits.scaleRoots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {p : Polynomial R}, p.Splits → ∀ 
(r : R), (p.scaleRoots r).Splits
参数：r : R；p.scaleRoots r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.zero_scaleRoots`：zero_scaleRoots (s : R) : scaleRoots 0 s = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.splits_iff_exists_multiset'`：splits_iff_exists_multiset' {f :
 R[X]} : Splits f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X + C 
·)).prod
· 使用引理 `Polynomial.mul_scaleRoots'`：mul_scaleRoots' (p q : R[X]) (r : R) (h : le
adingCoeff p * leadingCoeff q != 0) : (p * q).scaleRoots r = p.scaleRoots r * q.
scaleRoots r
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.monic_multiset_prod_of_monic`：monic_multiset_prod_of_monic (t
 : Multiset ι) (f : ι -> R[X]) (ht : forall i in t, Monic (f i)) : Monic (t.map 
f).prod
· 使用定理 `Polynomial.monic_X_add_C`：monic_X_add_C (x : R) : Monic (X + C x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Polynomial.scaleRoots_C`：scaleRoots_C (r c : R) : (C c).scaleRoots r = C
 c
· 使用定理 `Polynomial.Splits.mul`：∀ {R : Type u_1} [inst : Semiring R] {f g : Polyn
omial R}, f.Splits → g.Splits → (f * g).Splits
· 使用定理 `Polynomial.Splits.C`：∀ {R : Type u_1} [inst : Semiring R] (a : R), (Poly
nomial.C a).Splits
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用引理 `Polynomial.one_scaleRoots`：one_scaleRoots (r : R) : (1 : R[X]).scaleRoot
s r = 1
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Polynomial.leadingCoeff_X_add_C`：leadingCoeff_X_add_C [Semiring S] (r : 
S) : (X + C r).leadingCoeff = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用引理 `Polynomial.X_add_C_scaleRoots`：X_add_C_scaleRoots (r s : R) : (X + C r).
scaleRoots s = (X + C (r * s))
· 使用定理 `Polynomial.Splits.X_add_C`：∀ {R : Type u_1} [inst : Semiring R] (a : R),
 (Polynomial.X + Polynomial.C a).Splits
-/
lemma Splits.scaleRoots {p : R[X]} (hp : p.Splits) (r : R) :
    (p.scaleRoots r).Splits := by
  cases subsingleton_or_nontrivial R
  · rwa [Subsingleton.elim (p.scaleRoots r) p]
  obtain rfl | hp0 := eq_or_ne p 0
  · simp
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hp
  rw [hm, mul_scaleRoots', scaleRoots_C]
  · clear hm
    refine .mul (.C _) ?_
    induction m using Multiset.induction_on with
    | empty => simp
    | cons a s IH =>
      rw [Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots', X_add_C_scaleRoots]
      · exact .mul (.X_add_C _) IH
      · simp only [leadingCoeff_X_add_C, one_mul, ne_eq, leadingCoeff_eq_zero]
        exact (monic_multiset_prod_of_monic _ _ fun a _ ↦ monic_X_add_C _).ne_zero
  · rw [(monic_multiset_prod_of_monic _ _ fun a _ ↦ monic_X_add_C _).leadingCoeff]
    simpa

end CommSemiring

section Ring

@[simp]
/-
**Polynomial.X_sub_C_scaleRoots** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：X_sub_C_scaleRoots [Ring R] (r s : R) : (X - C r).scaleRoots s = (X - C (r
 * s))
参数：r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.coeff_X_one`：coeff_X_one : coeff (X : R[X]) 1 = 1
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 42 条，此处仅展示前 30 条）
-/
lemma X_sub_C_scaleRoots [Ring R] (r s : R) :
    (X - C r).scaleRoots s = (X - C (r * s)) := by
  nontriviality R
  ext (_ | _ | i) <;> simp

end Ring

section CommRing

variable [CommRing R]

/-
**Polynomial.rootMultiplicity_scaleRoots** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_scaleRoots (p : R[X]) {r a : R} (hr : IsLeftRegular r) : 
rootMultiplicity (r * a) (p.scaleRoots r) = rootMultiplicity a p
参数：p : R[X]；hr : IsLeftRegular r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Polynomial.zero_scaleRoots`：zero_scaleRoots (s : R) : scaleRoots 0 s = 0
· 使用定理 `Polynomial.rootMultiplicity_zero`：rootMultiplicity_zero {x : R} : rootMu
ltiplicity x 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`：exists_eq_pow
_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p != 0) (a : R) : exists q : 
R[X], p = (X - C a) ^ p.rootMultiplicity a * q …
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用引理 `Polynomial.mul_scaleRoots'`：mul_scaleRoots' (p q : R[X]) (r : R) (h : le
adingCoeff p * leadingCoeff q != 0) : (p * q).scaleRoots r = p.scaleRoots r * q.
scaleRoots r
· 使用定理 `Polynomial.leadingCoeff_pow'`：leadingCoeff_pow' : leadingCoeff p ^ n != 
0 -> leadingCoeff (p ^ n) = leadingCoeff p ^ n
· 使用定理 `Polynomial.leadingCoeff_X_sub_C`：leadingCoeff_X_sub_C [Ring S] (r : S) :
 (X - C r).leadingCoeff = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用引理 `Polynomial.pow_scaleRoots'`：pow_scaleRoots' (p : R[X]) (r : R) (n : Nat)
 (hp : p.leadingCoeff ^ n != 0) : (p ^ n).scaleRoots r = p.scaleRoots r ^ n
· 使用引理 `Polynomial.X_sub_C_scaleRoots`：X_sub_C_scaleRoots [Ring R] (r s : R) : (
X - C r).scaleRoots s = (X - C (r * s))
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.rootMultiplicity_mul_X_sub_C_pow`：rootMultiplicity_mul_X_sub_
C_pow {p : R[X]} {a : R} {n : Nat} (h : p != 0) : (p * (X - C a) ^ n).rootMultip
licity a = p.rootMultiplicity a +…
· 使用定理 `Polynomial.scaleRoots_ne_zero`：scaleRoots_ne_zero {p : R[X]} (hp : p != 
0) (s : R) : scaleRoots p s != 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 35 条，此处仅展示前 30 条）
-/
lemma rootMultiplicity_scaleRoots (p : R[X]) {r a : R} (hr : IsLeftRegular r) :
    rootMultiplicity (r * a) (p.scaleRoots r) = rootMultiplicity a p := by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.elim p 0]
  obtain rfl | hp := eq_or_ne p 0
  · simp
  obtain ⟨q, e, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp a
  have hq0 : q ≠ 0 := by contrapose hp; simp_all
  conv_lhs => rw [e]
  rw [mul_scaleRoots', pow_scaleRoots', X_sub_C_scaleRoots, mul_comm, mul_comm _ (q.scaleRoots r),
    rootMultiplicity_mul_X_sub_C_pow (q.scaleRoots_ne_zero hq0 _)]
  · rw [dvd_iff_isRoot, IsRoot.def] at hq
    simp only [Nat.add_eq_right, rootMultiplicity_eq_zero_iff, IsRoot.def]
    rw [mul_comm, scaleRoots_eval_mul, (hr.pow q.natDegree).mul_left_eq_zero_iff]
    tauto
  · simp
  · rwa [leadingCoeff_pow' (by simp), leadingCoeff_X_sub_C,
      one_pow, one_mul, ne_eq, leadingCoeff_eq_zero]
/-
**Polynomial.roots_scaleRoots** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：roots_scaleRoots [IsDomain R] (p : R[X]) {r : R} (hr : IsUnit r) : (p.scal
eRoots r).roots = p.roots.map (r * ·)
参数：p : R[X]；hr : IsUnit r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.isUnit_iff_mulLeft_bijective`：isUnit_iff_mulLeft_bijective {a : M
} : IsUnit a ↔ Function.Bijective (a * ·)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用引理 `Polynomial.rootMultiplicity_scaleRoots`：rootMultiplicity_scaleRoots (p :
 R[X]) {r a : R} (hr : IsLeftRegular r) : rootMultiplicity (r * a) (p.scaleRoots
 r) = rootMultiplicity a p
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `IsUnit.isRegular`：IsUnit.isRegular (ua : IsUnit a) : IsRegular a
· 使用定理 `Multiset.count_map_eq_count'`：count_map_eq_count' [DecidableEq β] (f : α
 -> β) (s : Multiset α) (hf : Function.Injective f) (x : α) : (s.map f).count (f
 x) = s.count x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma roots_scaleRoots [IsDomain R] (p : R[X]) {r : R} (hr : IsUnit r) :
    (p.scaleRoots r).roots = p.roots.map (r * ·) := by
  classical
  ext a
  have : Function.Bijective (α := R) (r * ·) := IsUnit.isUnit_iff_mulLeft_bijective.mp hr
  obtain ⟨a, rfl⟩ := this.2 a
  simp [Multiset.count_map_eq_count' _ p.roots this.1 a,
    rootMultiplicity_scaleRoots _ hr.isRegular.left]

end CommRing

end Polynomial

