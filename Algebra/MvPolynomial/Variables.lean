/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Variables of polynomials

This file establishes many results about the variable sets of a multivariate polynomial.

The *variable set* of a polynomial $P \in R[X]$ is a `Finset` containing each $x \in X$
that appears in a monomial in $P$.


## Main declarations

* `MvPolynomial.vars p` : the finset of variables occurring in `p`.
  For example if `p = x⁴y+yz` then `vars p = {x, y, z}`

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

section Vars

/-! ### `vars` -/


/-- `vars p` is the set of variables appearing in the polynomial `p` -/
/-
**MvPolynomial.vars** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：vars (p : MvPolynomial σ R) : Finset σ
参数：p : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`vars p` is the set of variables appearing in the polynomial `p`
-/
def vars (p : MvPolynomial σ R) : Finset σ :=
  letI := Classical.decEq σ
  p.degrees.toFinset
/-
**MvPolynomial.vars_def** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_def [DecidableEq σ] (p : MvPolynomial σ R) : p.vars = p.degrees.toFin
set
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.vars.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiri
ng R] (p : MvPolynomial σ R), p.vars = p.degrees.toFinset
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
theorem vars_def [DecidableEq σ] (p : MvPolynomial σ R) : p.vars = p.degrees.toFinset := by
  rw [vars]
  convert! rfl

@[simp]
/-
**MvPolynomial.vars_0** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_0 : (0 : MvPolynomial σ R).vars = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.vars_def`：vars_def [DecidableEq σ] (p : MvPolynomial σ R) :
 p.vars = p.degrees.toFinset
· 使用定理 `MvPolynomial.degrees_zero`：degrees_zero : degrees (0 : MvPolynomial σ R)
 = 0
· 使用定理 `Multiset.toFinset_zero`：toFinset_zero : toFinset (0 : Multiset α) = ∅
-/
theorem vars_0 : (0 : MvPolynomial σ R).vars = ∅ := by
  classical rw [vars_def, degrees_zero, Multiset.toFinset_zero]

@[simp]
/-
**MvPolynomial.vars_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_monomial (h : r != 0) : (monomial s r).vars = s.support
参数：h : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.vars_def`：vars_def [DecidableEq σ] (p : MvPolynomial σ R) :
 p.vars = p.degrees.toFinset
· 使用定理 `MvPolynomial.degrees_monomial_eq`：degrees_monomial_eq (s : σ ->₀ Nat) (a
 : R) (ha : a != 0) : degrees (monomial s a) = toMultiset s
· 使用定理 `Finsupp.toFinset_toMultiset`：toFinset_toMultiset [DecidableEq α] (f : α 
->₀ Nat) : f.toMultiset.toFinset = f.support
-/
theorem vars_monomial (h : r ≠ 0) : (monomial s r).vars = s.support := by
  classical rw [vars_def, degrees_monomial_eq _ _ h, Finsupp.toFinset_toMultiset]

@[simp]
/-
**MvPolynomial.vars_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_C : (C r : MvPolynomial σ R).vars = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.vars_def`：vars_def [DecidableEq σ] (p : MvPolynomial σ R) :
 p.vars = p.degrees.toFinset
· 使用定理 `MvPolynomial.degrees_C`：degrees_C (a : R) : degrees (C a : MvPolynomial 
σ R) = 0
· 使用定理 `Multiset.toFinset_zero`：toFinset_zero : toFinset (0 : Multiset α) = ∅
-/
theorem vars_C : (C r : MvPolynomial σ R).vars = ∅ := by
  classical rw [vars_def, degrees_C, Multiset.toFinset_zero]

@[simp]
/-
**MvPolynomial.vars_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_X [Nontrivial R] : (X n : MvPolynomial σ R).vars = {n}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.X.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring 
R] (n : σ),   MvPolynomial.X n = (MvPolynomial.monomial fun₀ | n => 1) 1
· 使用定理 `MvPolynomial.vars_monomial`：vars_monomial (h : r != 0) : (monomial s r).
vars = s.support
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem vars_X [Nontrivial R] : (X n : MvPolynomial σ R).vars = {n} := by
  rw [X, vars_monomial (one_ne_zero' R), Finsupp.support_single _ (one_ne_zero' ℕ)]
/-
**MvPolynomial.mem_vars_iff_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：mem_vars_iff_mem_support (i : σ) : i in p.vars ↔ exists d in p.support, i 
in d.support
参数：i : σ。
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
· 使用定理 `MvPolynomial.vars_def`：vars_def [DecidableEq σ] (p : MvPolynomial σ R) :
 p.vars = p.degrees.toFinset
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_vars_iff_mem_support (i : σ) : i ∈ p.vars ↔ ∃ d ∈ p.support, i ∈ d.support := by
  classical simp only [vars_def, Multiset.mem_toFinset, mem_degrees, mem_support_iff]

@[deprecated (since := "2026-04-24")] alias mem_vars := mem_vars_iff_mem_support
/-
**MvPolynomial.mem_vars_iff_degreeOf_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyno
mial`。
形式化陈述：mem_vars_iff_degreeOf_ne_zero {i : σ} : i in p.vars ↔ p.degreeOf i != 0
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
· 使用定理 `MvPolynomial.vars_def`：vars_def [DecidableEq σ] (p : MvPolynomial σ R) :
 p.vars = p.degrees.toFinset
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_vars_iff_degreeOf_ne_zero {i : σ} : i ∈ p.vars ↔ p.degreeOf i ≠ 0 := by
  classical simp [degreeOf, vars_def]
/-
**MvPolynomial.mem_support_notMem_vars_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynom
ial`。
形式化陈述：mem_support_notMem_vars_zero {f : MvPolynomial σ R} {x : σ ->₀ Nat} (H : x
 in f.support) {v : σ} (h : v ∉ vars f) : x v = 0
参数：H : x in f.support；h : v ∉ vars f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPolynomial.mem_vars_iff_mem_support`：mem_vars_iff_mem_support (i : σ) 
: i in p.vars ↔ exists d in p.support, i in d.support
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
-/
theorem mem_support_notMem_vars_zero {f : MvPolynomial σ R} {x : σ →₀ ℕ} (H : x ∈ f.support)
    {v : σ} (h : v ∉ vars f) : x v = 0 := by
  contrapose! h
  exact (mem_vars_iff_mem_support v).mpr ⟨x, H, Finsupp.mem_support_iff.mpr h⟩
/-
**MvPolynomial.support_subset_vars_of_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `MvP
olynomial`。
形式化陈述：support_subset_vars_of_mem_support {s : σ ->₀ Nat} (h : s in p.support) : 
s.support subseteq p.vars
参数：h : s in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.mem_support_notMem_vars_zero`：mem_support_notMem_vars_zero 
{f : MvPolynomial σ R} {x : σ ->₀ Nat} (H : x in f.support) {v : σ} (h : v ∉ var
s f) : x v = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem support_subset_vars_of_mem_support {s : σ →₀ ℕ} (h : s ∈ p.support) :
    s.support ⊆ p.vars := fun i hi ↦ by
  contrapose! hi
  simp [mem_support_notMem_vars_zero h hi]
/-
**MvPolynomial.vars_eq_empty_iff_eq_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_eq_empty_iff_eq_C : p.vars = ∅ ↔ p = C (p.coeff 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.totalDegree_eq_zero_iff_eq_C`：totalDegree_eq_zero_iff_eq_C 
{p : MvPolynomial σ R} : p.totalDegree = 0 ↔ p = C (p.coeff 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.toFinset_eq_empty`：toFinset_eq_empty {m : Multiset α} : m.toFin
set = ∅ ↔ m = 0
· 使用定理 `MvPolynomial.vars_def`：vars_def [DecidableEq σ] (p : MvPolynomial σ R) :
 p.vars = p.degrees.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.vars_C`：vars_C : (C r : MvPolynomial σ R).vars = ∅
-/
theorem vars_eq_empty_iff_eq_C : p.vars = ∅ ↔ p = C (p.coeff 0) := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; simp⟩
  rw [← totalDegree_eq_zero_iff_eq_C]
  suffices p.degrees.card = 0 by grind [totalDegree_le_degrees_card p]
  classical rw [vars_def, Multiset.toFinset_eq_empty] at h
  simp_all
/-
**MvPolynomial.vars_add_subset** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_add_subset [DecidableEq σ] (p q : MvPolynomial σ R) : (p + q).vars su
bseteq p.vars union q.vars
参数：p q : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.vars_def`：vars_def [DecidableEq σ] (p : MvPolynomial σ R) :
 p.vars = p.degrees.toFinset
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
· 使用定理 `MvPolynomial.degrees_add_le`：degrees_add_le [DecidableEq σ] {p q : MvPol
ynomial σ R} : (p + q).degrees <= p.degrees ⊔ q.degrees
-/
theorem vars_add_subset [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p + q).vars ⊆ p.vars ∪ q.vars := by
  intro x hx
  simp only [vars_def, Finset.mem_union, Multiset.mem_toFinset] at hx ⊢
  simpa using Multiset.mem_of_le degrees_add_le hx
/-
**MvPolynomial.vars_add_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_add_of_disjoint [DecidableEq σ] (h : Disjoint p.vars q.vars) : (p + q
).vars = p.vars union q.vars
参数：h : Disjoint p.vars q.vars。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MvPolynomial.vars_add_subset`：vars_add_subset [DecidableEq σ] (p q : MvP
olynomial σ R) : (p + q).vars subseteq p.vars union q.vars
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.vars_def`：vars_def [DecidableEq σ] (p : MvPolynomial σ R) :
 p.vars = p.degrees.toFinset
· 使用定理 `MvPolynomial.degrees_add_of_disjoint`：degrees_add_of_disjoint [Decidable
Eq σ] (h : Disjoint p.degrees q.degrees) : (p + q).degrees = p.degrees union q.d
egrees
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.toFinset_union`：toFinset_union (s t : Multiset α) : (s union t)
.toFinset = s.toFinset union t.toFinset
-/
theorem vars_add_of_disjoint [DecidableEq σ] (h : Disjoint p.vars q.vars) :
    (p + q).vars = p.vars ∪ q.vars := by
  refine (vars_add_subset p q).antisymm fun x hx => ?_
  simp only [vars_def, Multiset.disjoint_toFinset] at h hx ⊢
  rwa [degrees_add_of_disjoint h, Multiset.toFinset_union]

section Mul

/-
**MvPolynomial.vars_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_mul [DecidableEq σ] (φ ψ : MvPolynomial σ R) : (φ * ψ).vars subseteq 
φ.vars union ψ.vars
参数：φ ψ : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.vars_def`：vars_def [DecidableEq σ] (p : MvPolynomial σ R) :
 p.vars = p.degrees.toFinset
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用定理 `MvPolynomial.degrees_mul_le`：degrees_mul_le {p q : MvPolynomial σ R} : (
p * q).degrees <= p.degrees + q.degrees
-/
theorem vars_mul [DecidableEq σ] (φ ψ : MvPolynomial σ R) : (φ * ψ).vars ⊆ φ.vars ∪ ψ.vars := by
  simp_rw [vars_def, ← Multiset.toFinset_add, Multiset.toFinset_subset]
  exact Multiset.subset_of_le degrees_mul_le

@[simp]
/-
**MvPolynomial.vars_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_one : (1 : MvPolynomial σ R).vars = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.vars_C`：vars_C : (C r : MvPolynomial σ R).vars = ∅
-/
theorem vars_one : (1 : MvPolynomial σ R).vars = ∅ :=
  vars_C
/-
**MvPolynomial.vars_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_pow (φ : MvPolynomial σ R) (n : Nat) : (φ ^ n).vars subseteq φ.vars
参数：φ : MvPolynomial σ R；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MvPolynomial.vars_one`：vars_one : (1 : MvPolynomial σ R).vars = ∅
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `MvPolynomial.vars_mul`：vars_mul [DecidableEq σ] (φ ψ : MvPolynomial σ R)
 : (φ * ψ).vars subseteq φ.vars union ψ.vars
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem vars_pow (φ : MvPolynomial σ R) (n : ℕ) : (φ ^ n).vars ⊆ φ.vars := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    apply Finset.Subset.trans (vars_mul _ _)
    exact Finset.union_subset (Finset.Subset.refl _) ih

/-- The variables of the product of a family of polynomials
are a subset of the union of the sets of variables of each polynomial.
-/
/-
**MvPolynomial.vars_prod** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_prod {ι : Type*} [DecidableEq σ] {s : Finset ι} (f : ι -> MvPolynomia
l σ R) : (∏ i in s, f i).vars subseteq s.biUnion fun i => (f i).vars
参数：f : ι -> MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.vars_one`：vars_one : (1 : MvPolynomial σ R).vars = ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `Finset.biUnion_insert`：biUnion_insert [DecidableEq α] {a : α} : (insert 
a s).biUnion t = t a union s.biUnion t
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `MvPolynomial.vars_mul`：vars_mul [DecidableEq σ] (φ ψ : MvPolynomial σ R)
 : (φ * ψ).vars subseteq φ.vars union ψ.vars
· 使用定理 `Finset.union_subset_union`：union_subset_union (hsu : s subseteq u) (htv 
: t subseteq v) : s union t subseteq u union v
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s

--- 原说明 ---
The variables of the product of a family of polynomials
are a subset of the union of the sets of variables of each polynomial.
-/
theorem vars_prod {ι : Type*} [DecidableEq σ] {s : Finset ι} (f : ι → MvPolynomial σ R) :
    (∏ i ∈ s, f i).vars ⊆ s.biUnion fun i => (f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ hs hsub =>
    simp only [hs, Finset.biUnion_insert, Finset.prod_insert, not_false_iff]
    apply Finset.Subset.trans (vars_mul _ _)
    exact Finset.union_subset_union (Finset.Subset.refl _) hsub

section IsDomain

variable {A : Type*} [CommRing A] [NoZeroDivisors A]

/-
**MvPolynomial.vars_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_C_mul (a : A) (ha : a != 0) (φ : MvPolynomial σ A) : (C a * φ : MvPol
ynomial σ A).vars = φ.vars
参数：a : A；ha : a != 0；φ : MvPolynomial σ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `MvPolynomial.coeff_C_mul`：coeff_C_mul (m) (a : R) (p : MvPolynomial σ R)
 : coeff m (C a * p) = a * coeff m p
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem vars_C_mul (a : A) (ha : a ≠ 0) (φ : MvPolynomial σ A) :
    (C a * φ : MvPolynomial σ A).vars = φ.vars := by
  ext1 i
  simp only [mem_vars_iff_mem_support, mem_support_iff]
  apply exists_congr
  intro d
  rw [coeff_C_mul, mul_ne_zero_iff, eq_true ha, true_and]

end IsDomain

end Mul

section Sum

variable {ι : Type*} (t : Finset ι) (φ : ι → MvPolynomial σ R)

/-
**MvPolynomial.vars_sum_subset** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_sum_subset [DecidableEq σ] : (∑ i in t, φ i).vars subseteq Finset.biU
nion t fun i => (φ i).vars
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.vars_0`：vars_0 : (0 : MvPolynomial σ R).vars = ∅
· 使用引理 `Finset.biUnion_insert`：biUnion_insert [DecidableEq α] {a : α} : (insert 
a s).biUnion t = t a union s.biUnion t
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `MvPolynomial.vars_add_subset`：vars_add_subset [DecidableEq σ] (p q : MvP
olynomial σ R) : (p + q).vars subseteq p.vars union q.vars
· 使用定理 `Finset.union_subset_union`：union_subset_union (hsu : s subseteq u) (htv 
: t subseteq v) : s union t subseteq u union v
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem vars_sum_subset [DecidableEq σ] :
    (∑ i ∈ t, φ i).vars ⊆ Finset.biUnion t fun i => (φ i).vars := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ has hsum =>
    rw [Finset.biUnion_insert, Finset.sum_insert has]
    refine Finset.Subset.trans
      (vars_add_subset _ _) (Finset.union_subset_union (Finset.Subset.refl _) ?_)
    assumption
/-
**MvPolynomial.vars_sum_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_sum_of_disjoint [DecidableEq σ] (h : Pairwise <| (Disjoint on fun i =
> (φ i).vars)) : (∑ i in t, φ i).vars = Finset.biUnion t fun i => (φ i).vars
参数：h : Pairwise <| (Disjoint on fun i => (φ i).vars)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.vars_0`：vars_0 : (0 : MvPolynomial σ R).vars = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.biUnion_insert`：biUnion_insert [DecidableEq α] {a : α} : (insert 
a s).biUnion t = t a union s.biUnion t
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `MvPolynomial.vars_add_of_disjoint`：vars_add_of_disjoint [DecidableEq σ] 
(h : Disjoint p.vars q.vars) : (p + q).vars = p.vars union q.vars
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem vars_sum_of_disjoint [DecidableEq σ] (h : Pairwise <| (Disjoint on fun i => (φ i).vars)) :
    (∑ i ∈ t, φ i).vars = Finset.biUnion t fun i => (φ i).vars := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ has hsum =>
    rw [Finset.biUnion_insert, Finset.sum_insert has, vars_add_of_disjoint, hsum]
    unfold Pairwise onFun at h
    simp only [Finset.disjoint_iff_ne] at h ⊢
    grind

end Sum

section Map

variable [CommSemiring S] (f : R →+* S)
variable (p)

/-
**MvPolynomial.vars_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_map : (map f p).vars subseteq p.vars
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.vars_def`：vars_def [DecidableEq σ] (p : MvPolynomial σ R) :
 p.vars = p.degrees.toFinset
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用引理 `MvPolynomial.degrees_map_le`：degrees_map_le [CommSemiring S] {f : R ->+*
 S} : (map f p).degrees <= p.degrees
-/
theorem vars_map : (map f p).vars ⊆ p.vars := by
  classical simp [vars_def, Multiset.subset_of_le degrees_map_le]

variable {f}
/-
**MvPolynomial.vars_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_map_of_injective (hf : Injective f) : (map f p).vars = p.vars
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degrees_map_of_injective`：degrees_map_of_injective [CommSem
iring S] (p : MvPolynomial σ R) {f : R ->+* S} (hf : Injective f) : (map f p).de
grees = p.degrees
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vars_map_of_injective (hf : Injective f) : (map f p).vars = p.vars := by
  simp [vars, degrees_map_of_injective _ hf]
/-
**MvPolynomial.vars_monomial_single** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_monomial_single (i : σ) {e : Nat} {r : R} (he : e != 0) (hr : r != 0)
 : (monomial (Finsupp.single i e) r).vars = {i}
参数：i : σ；he : e != 0；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.vars_monomial`：vars_monomial (h : r != 0) : (monomial s r).
vars = s.support
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
-/
theorem vars_monomial_single (i : σ) {e : ℕ} {r : R} (he : e ≠ 0) (hr : r ≠ 0) :
    (monomial (Finsupp.single i e) r).vars = {i} := by
  rw [vars_monomial hr, Finsupp.support_single _ he]
/-
**MvPolynomial.vars_eq_support_biUnion_support** 是 Mathlib 中的一个定理，位于命名空间 `MvPoly
nomial`。
形式化陈述：vars_eq_support_biUnion_support [DecidableEq σ] : p.vars = p.support.biUni
on Finsupp.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.mem_vars_iff_mem_support`：mem_vars_iff_mem_support (i : σ) 
: i in p.vars ↔ exists d in p.support, i in d.support
· 使用定理 `Finset.mem_biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : 
α → Finset β} [inst : DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t
 a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem vars_eq_support_biUnion_support [DecidableEq σ] :
    p.vars = p.support.biUnion Finsupp.support := by
  ext i
  rw [mem_vars_iff_mem_support, Finset.mem_biUnion]

end Map

end Vars

section EvalVars

/-! ### `vars` and `eval` -/


variable [CommSemiring S]

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_eq_constantCoeff_of_vars (f : R →+* S) {g : σ → S} {p : MvPolynomial σ R}
    (hp : ∀ i ∈ p.vars, g i = 0) : eval₂Hom f g p = f (constantCoeff p) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, eval₂Hom_monomial]
  by_cases h0 : constantCoeff p = 0
  on_goal 1 =>
    rw [h0, f.map_zero, Finset.sum_eq_zero]
    intro d hd
  on_goal 2 =>
    rw [Finset.sum_eq_single (0 : σ →₀ ℕ)]
    · rw [Finsupp.prod_zero_index, mul_one]
      rfl
    on_goal 1 => intro d hd hd0
  on_goal 3 =>
    rw [constantCoeff_eq, coeff, ← Ne, ← Finsupp.mem_support_iff] at h0
    intro
    contradiction
  repeat'
    obtain ⟨i, hi⟩ : Finset.Nonempty (Finsupp.support d) := by
      rw [constantCoeff_eq, coeff, ← Finsupp.notMem_support_iff] at h0
      rw [Finset.nonempty_iff_ne_empty, Ne, Finsupp.support_eq_empty]
      rintro rfl
      contradiction
    rw [Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
    rw [hp, zero_pow (Finsupp.mem_support_iff.1 hi)]
    rw [mem_vars_iff_mem_support]
    exact ⟨d, hd, hi⟩
/-
**MvPolynomial.aeval_eq_constantCoeff_of_vars** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyn
omial`。
形式化陈述：aeval_eq_constantCoeff_of_vars [Algebra R S] {g : σ -> S} {p : MvPolynomia
l σ R} (hp : forall i in p.vars, g i = 0) : aeval g p = algebraMap _ _ (constant
Coeff p)
参数：hp : forall i in p.vars, g i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars`：eval₂Hom_eq_constantCoef
f_of_vars (f : R ->+* S) {g : σ -> S} {p : MvPolynomial σ R} (hp : forall i in p
.vars, g i = 0) : eval₂Hom f g p = f…
-/
theorem aeval_eq_constantCoeff_of_vars [Algebra R S] {g : σ → S} {p : MvPolynomial σ R}
    (hp : ∀ i ∈ p.vars, g i = 0) : aeval g p = algebraMap _ _ (constantCoeff p) :=
  eval₂Hom_eq_constantCoeff_of_vars _ hp
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_congr' {f₁ f₂ : R →+* S} {g₁ g₂ : σ → S} {p₁ p₂ : MvPolynomial σ R} :
    f₁ = f₂ →
      (∀ i, i ∈ p₁.vars → i ∈ p₂.vars → g₁ i = g₂ i) →
        p₁ = p₂ → eval₂Hom f₁ g₁ p₁ = eval₂Hom f₂ g₂ p₂ := by
  rintro rfl h rfl
  rw [p₁.as_sum]
  simp only [map_sum, eval₂Hom_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  simp only [Finsupp.prod]
  apply Finset.prod_congr rfl
  intro i hi
  have : i ∈ p₁.vars := by
    rw [mem_vars_iff_mem_support]
    exact ⟨d, hd, hi⟩
  rw [h i this this]

/-- If `f₁` and `f₂` are ring homs out of the polynomial ring and `p₁` and `p₂` are polynomials,
  then `f₁ p₁ = f₂ p₂` if `p₁ = p₂` and `f₁` and `f₂` are equal on `R` and on the variables
  of `p₁`. -/
/-
**MvPolynomial.hom_congr_vars** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：hom_congr_vars {f₁ f₂ : MvPolynomial σ R ->+* S} {p₁ p₂ : MvPolynomial σ R
} (hC : f₁.comp C = f₂.comp C) (hv : forall i, i in p₁.vars -> i in p₂.vars -> f
₁ (X i) = f₂ (X i)) (hp : p₁ = p₂) : f₁ p₁ = f₂ p₂
参数：hC : f₁.comp C = f₂.comp C；hv : forall i, i in p₁.vars -> i in p₂.vars -> f₁ 
(X i) = f₂ (X i)；hp : p₁ = p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `MvPolynomial.ringHom_ext'`：ringHom_ext' {A : Type*} [Semiring A] {f g : 
MvPolynomial σ R ->+* A} (hC : f.comp C = g.comp C) (hX : forall i, f (X i) = g 
(X i)) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.eval₂_C`：eval₂_C (a) : (C a).eval₂ f g = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.eval₂Hom_X'`：eval₂Hom_X' (f : R ->+* S₁) (g : σ -> S₁) (i :
 σ) : eval₂Hom f g (X i) = g i
· 使用定理 `MvPolynomial.eval₂Hom_congr'`：eval₂Hom_congr' {f₁ f₂ : R ->+* S} {g₁ g₂ 
: σ -> S} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> (forall i, i in p₁.vars -> i i
n p₂.vars -> g₁ i …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
If `f₁` and `f₂` are ring homs out of the polynomial ring and `p₁` and `p₂` are 
polynomials,
  then `f₁ p₁ = f₂ p₂` if `p₁ = p₂` and `f₁` and `f₂` are equal on `R` and on th
e variables
  of `p₁`.
-/
theorem hom_congr_vars {f₁ f₂ : MvPolynomial σ R →+* S} {p₁ p₂ : MvPolynomial σ R}
    (hC : f₁.comp C = f₂.comp C) (hv : ∀ i, i ∈ p₁.vars → i ∈ p₂.vars → f₁ (X i) = f₂ (X i))
    (hp : p₁ = p₂) : f₁ p₁ = f₂ p₂ :=
  calc
    f₁ p₁ = eval₂Hom (f₁.comp C) (f₁ ∘ X) p₁ := RingHom.congr_fun (by ext <;> simp) _
    _ = eval₂Hom (f₂.comp C) (f₂ ∘ X) p₂ := eval₂Hom_congr' hC hv hp
    _ = f₂ p₂ := RingHom.congr_fun (by ext <;> simp) _
/-
**MvPolynomial.exists_rename_eq_of_vars_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `
MvPolynomial`。
形式化陈述：exists_rename_eq_of_vars_subset_range (p : MvPolynomial σ R) (f : τ -> σ) 
(hfi : Injective f) (hf : ↑p.vars subseteq Set.range f) : exists q : MvPolynomia
l τ R, rename f q = p
参数：p : MvPolynomial σ R；f : τ -> σ；hfi : Injective f；hf : ↑p.vars subseteq Set.r
ange f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `MvPolynomial.hom_congr_vars`：hom_congr_vars {f₁ f₂ : MvPolynomial σ R ->
+* S} {p₁ p₂ : MvPolynomial σ R} (hC : f₁.comp C = f₂.comp C) (hv : forall i, i 
in p₁.vars -> i i…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Function.partialInv_left`：partialInv_left {α β} {f : α -> β} (I : Inject
ive f) : forall x, partialInv f (f x) = some x
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
-/
theorem exists_rename_eq_of_vars_subset_range (p : MvPolynomial σ R) (f : τ → σ) (hfi : Injective f)
    (hf : ↑p.vars ⊆ Set.range f) : ∃ q : MvPolynomial τ R, rename f q = p :=
  ⟨aeval (fun i : σ => Option.elim' 0 X <| partialInv f i) p,
    by
      change (rename f).toRingHom.comp _ p = RingHom.id _ p
      refine hom_congr_vars ?_ ?_ ?_
      · ext1
        simp [algebraMap_eq]
      · intro i hip _
        rcases hf hip with ⟨i, rfl⟩
        simp [partialInv_left hfi]
      · rfl⟩
/-
**MvPolynomial.vars_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_rename [DecidableEq τ] (f : σ -> τ) (φ : MvPolynomial σ R) : (rename 
f φ).vars subseteq φ.vars.image f
参数：f : σ -> τ；φ : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.vars_def`：vars_def [DecidableEq σ] (p : MvPolynomial σ R) :
 p.vars = p.degrees.toFinset
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.degrees_rename`：degrees_rename (f : σ -> τ) (φ : MvPolynomi
al σ R) : (rename f φ).degrees subseteq φ.degrees.map f
-/
theorem vars_rename [DecidableEq τ] (f : σ → τ) (φ : MvPolynomial σ R) :
    (rename f φ).vars ⊆ φ.vars.image f := by
  classical
  intro i hi
  simp only [vars_def, Multiset.mem_toFinset, Finset.mem_image] at hi ⊢
  simpa only [Multiset.mem_map] using degrees_rename _ _ hi
/-
**MvPolynomial.mem_vars_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_vars_rename (f : σ -> τ) (φ : MvPolynomial σ R) {j : τ} (h : j in (ren
ame f φ).vars) : exists i : σ, i in φ.vars ∧ f i = j
参数：f : σ -> τ；φ : MvPolynomial σ R；h : j in (rename f φ).vars。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.vars_rename`：vars_rename [DecidableEq τ] (f : σ -> τ) (φ : 
MvPolynomial σ R) : (rename f φ).vars subseteq φ.vars.image f
-/
theorem mem_vars_rename (f : σ → τ) (φ : MvPolynomial σ R) {j : τ} (h : j ∈ (rename f φ).vars) :
    ∃ i : σ, i ∈ φ.vars ∧ f i = j := by
  classical
  simpa only [exists_prop, Finset.mem_image] using vars_rename f φ h
/-
**MvPolynomial.aeval_ite_mem_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_ite_mem_eq_self (q : MvPolynomial σ R) {s : Set σ} (hs : (q.vars : S
et σ) subseteq s) [forall i, Decidable (i in s)] : MvPolynomial.aeval (fun i => 
if i in s then .X i else 0) q = q
参数：q : MvPolynomial σ R；hs : (q.vars : Set σ) subseteq s；i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.as_sum`：as_sum (p : MvPolynomial σ R) : p = ∑ v in p.suppor
t, monomial v (coeff v p)
· 使用定理 `MvPolynomial.aeval_sum`：aeval_sum {ι : Type*} (s : Finset ι) (φ : ι -> M
vPolynomial σ R) : aeval f (∑ i in s, φ i) = ∑ i in s, aeval f (φ i)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.aeval_monomial`：aeval_monomial (g : σ -> S₁) (d : σ ->₀ Nat
) (r : R) : aeval g (monomial d r) = algebraMap _ _ r * d.prod fun i k => g i ^ 
k
· 使用定理 `MvPolynomial.monomial_eq`：monomial_eq : monomial s a = C a * (s.prod fun
 n e => X n ^ e : MvPolynomial σ R)
· 使用定理 `Finsupp.prod_congr`：prod_congr {f : α ->₀ M} {g1 g2 : α -> M -> N} (h : 
forall x in f.support, g1 x (f x) = g2 x (f x)) : f.prod g1 = f.prod g2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPolynomial.mem_vars_iff_mem_support`：mem_vars_iff_mem_support (i : σ) 
: i in p.vars ↔ exists d in p.support, i in d.support
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma aeval_ite_mem_eq_self (q : MvPolynomial σ R) {s : Set σ} (hs : (q.vars : Set σ) ⊆ s)
    [∀ i, Decidable (i ∈ s)] :
    MvPolynomial.aeval (fun i ↦ if i ∈ s then .X i else 0) q = q := by
  rw [MvPolynomial.as_sum q, MvPolynomial.aeval_sum]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  congr 1
  exact Finsupp.prod_congr (fun i hi ↦ by simp [hs ((mem_vars_iff_mem_support _).mpr ⟨u, hu, hi⟩)])

end EvalVars

section Lex

variable [LinearOrder σ]

/-
**MvPolynomial.leadingCoeff_toLex** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：leadingCoeff_toLex : p.leadingCoeff toLex = p.coeff (ofLex <| p.supDegree 
toLex)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.leadingCoeff.eq_1`：∀ {R : Type u_1} {A : Type u_3} {B :
 Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   
(D : A → B) [inst_3 : No…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Function.rightInverse_invFun`：rightInverse_invFun (hf : Surjective f) : 
RightInverse (invFun f) f
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `toLex_ofLex`：toLex_ofLex (a : Lex α) : toLex (ofLex a) = a
-/
lemma leadingCoeff_toLex : p.leadingCoeff toLex = p.coeff (ofLex <| p.supDegree toLex) := by
  rw [leadingCoeff]
  apply congr_arg p.coeff
  apply toLex.injective
  rw [Function.rightInverse_invFun toLex.surjective, toLex_ofLex]
/-
**MvPolynomial.supDegree_toLex_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：supDegree_toLex_C (r : R) : supDegree toLex (C (σ
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `AddMonoidAlgebra.supDegree_single`：supDegree_single (a : A) (r : R) : (s
ingle a r).supDegree D = if r = 0 then ⊥ else D a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ite_eq_iff'`：ite_eq_iff' : ite P a b = c ↔ (P -> a = c) ∧ (¬P -> b = c)
-/
lemma supDegree_toLex_C (r : R) : supDegree toLex (C (σ := σ) r) = 0 := by
  classical
    exact (supDegree_single _ r).trans (ite_eq_iff'.mpr ⟨fun _ => rfl, fun _ => rfl⟩)
/-
**MvPolynomial.leadingCoeff_toLex_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：leadingCoeff_toLex_C (r : R) : leadingCoeff toLex (C (σ
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.leadingCoeff_single`：leadingCoeff_single [Nonempty A] (
hD : D.Injective) (a : A) (r : R) : (single a r).leadingCoeff D = r
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma leadingCoeff_toLex_C (r : R) : leadingCoeff toLex (C (σ := σ) r) = r :=
  leadingCoeff_single toLex.injective _ r

end Lex

end CommSemiring

end MvPolynomial

