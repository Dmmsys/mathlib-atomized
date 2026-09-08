/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Multivariate polynomials over a ring

Many results about polynomials hold when the coefficient ring is a commutative semiring.
Some stronger results can be derived when we assume this semiring is a ring.

This file does not define any new operations, but proves some of these stronger results.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommRing R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`.

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

-/

@[expose] public section


noncomputable section

open Set Function Finsupp

universe u v

variable {R : Type u} {S : Type v}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommRing

variable [CommRing R]
variable {p q : MvPolynomial σ R}

variable (σ a a')

@[simp]
/-
**MvPolynomial.C_sub** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_sub : (C (a - a') : MvPolynomial σ R) = C a - C a'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem C_sub : (C (a - a') : MvPolynomial σ R) = C a - C a' :=
  map_sub _ _ _

@[simp]
/-
**MvPolynomial.C_neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：C_neg : (C (-a) : MvPolynomial σ R) = -C a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem C_neg : (C (-a) : MvPolynomial σ R) = -C a :=
  map_neg _ _

@[simp]
/-
**MvPolynomial.coeff_neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_neg (m : σ ->₀ Nat) (p : MvPolynomial σ R) : coeff m (-p) = -coeff m
 p
参数：m : σ ->₀ Nat；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.neg_apply`：neg_apply [NegZeroClass G] (g : ι ->₀ G) (a : ι) : (-
g) a = -g a
-/
theorem coeff_neg (m : σ →₀ ℕ) (p : MvPolynomial σ R) : coeff m (-p) = -coeff m p :=
  Finsupp.neg_apply _ _

@[simp, grind =]
/-
**MvPolynomial.coeff_sub** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ R) : coeff m (p - q) = coe
ff m p - coeff m q
参数：m : σ ->₀ Nat；p q : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.sub_apply`：sub_apply [SubNegZeroMonoid G] (g₁ g₂ : ι ->₀ G) (a :
 ι) : (g₁ - g₂) a = g₁ a - g₂ a
-/
theorem coeff_sub (m : σ →₀ ℕ) (p q : MvPolynomial σ R) : coeff m (p - q) = coeff m p - coeff m q :=
  Finsupp.sub_apply _ _ _
/-
**MvPolynomial.support_neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} (σ : Type u_1) [inst : CommRing R] {p : MvPolynomial σ R}, 
(-p).support = p.support
参数：σ : Type u_1；-p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.coeff_neg`：coeff_neg (m : σ ->₀ Nat) (p : MvPolynomial σ R)
 : coeff m (-p) = -coeff m p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma support_neg : (-p).support = p.support := by ext; simp
/-
**MvPolynomial.support_sub** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_sub [DecidableEq σ] (p q : MvPolynomial σ R) : (p - q).support sub
seteq p.support union q.support
参数：p q : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.support_sub`：support_sub [DecidableEq ι] {f g : ι ->₀ G} : suppo
rt (f - g) subseteq support f union support g
-/
theorem support_sub [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p - q).support ⊆ p.support ∪ q.support :=
  Finsupp.support_sub

variable {σ} (p)

/-- Subtracting `monomial d c - monomial d' c` from `p`, where `c = coeff d p` and `d ≠ d'`,
removes `d` from the support. -/
/-
**MvPolynomial.notMem_support_sub_monomial_sub_monomial** 是 Mathlib 中的一个定理，位于命名空
间 `MvPolynomial`。
形式化陈述：notMem_support_sub_monomial_sub_monomial (d d' : σ ->₀ Nat) (c : R) (hdd' 
: d != d') (hc : coeff d p = c) : d ∉ (p - (monomial d c - monomial d' c)).suppo
rt
参数：d d' : σ ->₀ Nat；c : R；hdd' : d != d'；hc : coeff d p = c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.notMem_support_iff`：notMem_support_iff {p : MvPolynomial σ 
R} {m : σ ->₀ Nat} : m ∉ p.support ↔ p.coeff m = 0
· 使用定理 `MvPolynomial.coeff_sub`：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p - q) = coeff m p - coeff m q
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
Subtracting `monomial d c - monomial d' c` from `p`, where `c = coeff d p` and `
d ≠ d'`,
removes `d` from the support.
-/
theorem notMem_support_sub_monomial_sub_monomial (d d' : σ →₀ ℕ) (c : R)
    (hdd' : d ≠ d') (hc : coeff d p = c) :
    d ∉ (p - (monomial d c - monomial d' c)).support := by
  classical
  rw [notMem_support_iff, coeff_sub, coeff_sub, coeff_monomial, coeff_monomial,
    if_pos rfl, if_neg hdd'.symm, sub_zero, hc, sub_self]

/-- Subtracting `monomial d c - monomial d' c` from `p`, where `c = coeff d p` and `d ≠ d'`,
leaves the support inside `p.support.erase d ∪ {d'}`. -/
/-
**MvPolynomial.support_sub_monomial_sub_monomial_subset** 是 Mathlib 中的一个定理，位于命名空
间 `MvPolynomial`。
形式化陈述：support_sub_monomial_sub_monomial_subset [DecidableEq σ] (d d' : σ ->₀ Nat
) (c : R) (hdd' : d != d') (hc : coeff d p = c) : (p - (monomial d c - monomial 
d' c)).support subseteq p.support.erase d union {d'}
参数：d d' : σ ->₀ Nat；c : R；hdd' : d != d'；hc : coeff d p = c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.notMem_support_sub_monomial_sub_monomial`：notMem_support_su
b_monomial_sub_monomial (d d' : σ ->₀ Nat) (c : R) (hdd' : d != d') (hc : coeff 
d p = c) : d ∉ (p - (monomial d c - monomia…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `MvPolynomial.support_sub`：support_sub [DecidableEq σ] (p q : MvPolynomia
l σ R) : (p - q).support subseteq p.support union q.support
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_union_left`：mem_union_left (t : Finset α) (h : a in s) : a in
 s union t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MvPolynomial.support_monomial`：support_monomial [h : Decidable (a = 0)] 
: (monomial s a).support = if a = 0 then ∅ else {s}
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.mem_union_right`：mem_union_right (s : Finset α) (h : a in t) : a 
in s union t

--- 原说明 ---
Subtracting `monomial d c - monomial d' c` from `p`, where `c = coeff d p` and `
d ≠ d'`,
leaves the support inside `p.support.erase d ∪ {d'}`.
-/
theorem support_sub_monomial_sub_monomial_subset [DecidableEq σ] (d d' : σ →₀ ℕ) (c : R)
    (hdd' : d ≠ d') (hc : coeff d p = c) :
    (p - (monomial d c - monomial d' c)).support ⊆ p.support.erase d ∪ {d'} := by
  classical
  intro x hx
  have hd_not := notMem_support_sub_monomial_sub_monomial p d d' c hdd' hc
  rcases Finset.mem_union.mp (support_sub σ p _ hx) with hp | hdelta
  · by_cases hxd : x = d
    · exact absurd (hxd ▸ hx) hd_not
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxd, hp⟩)
  rcases Finset.mem_union.mp (support_sub σ _ _ hdelta) with h1 | h2
  · rw [support_monomial] at h1
    split_ifs at h1
    · exact absurd h1 (Finset.notMem_empty _)
    exact absurd ((Finset.mem_singleton.mp h1) ▸ hx) hd_not
  rw [support_monomial] at h2
  split_ifs at h2
  · exact absurd h2 (Finset.notMem_empty _)
  exact Finset.mem_union_right _ (by rwa [Finset.mem_singleton] at h2 ⊢)

section Degrees

@[simp]
/-
**MvPolynomial.degrees_neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_neg (p : MvPolynomial σ R) : (-p).degrees = p.degrees
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degrees.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : CommSem
iring R] (p : MvPolynomial σ R),   p.degrees = p.support.sup fun s => Finsupp.to
Multiset s
· 使用定理 `MvPolynomial.support_neg`：∀ {R : Type u} (σ : Type u_1) [inst : CommRing
 R] {p : MvPolynomial σ R}, (-p).support = p.support
-/
theorem degrees_neg (p : MvPolynomial σ R) : (-p).degrees = p.degrees := by
  rw [degrees, support_neg]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.degrees_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_sub_le [DecidableEq σ] {p q : MvPolynomial σ R} : (p - q).degrees 
<= p.degrees union q.degrees
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degrees_def`：degrees_def [DecidableEq σ] (p : MvPolynomial 
σ R) : p.degrees = p.support.sup fun s : σ ->₀ Nat => Finsupp.toMultiset s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.coeff_sub`：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p - q) = coeff m p - coeff m q
· 使用定理 `AddMonoidAlgebra.supDegree_sub_le`：supDegree_sub_le {f g : R'[A]} : (f -
 g).supDegree D <= f.supDegree D ⊔ g.supDegree D
-/
theorem degrees_sub_le [DecidableEq σ] {p q : MvPolynomial σ R} :
    (p - q).degrees ≤ p.degrees ∪ q.degrees := by
  simpa [degrees_def] using! AddMonoidAlgebra.supDegree_sub_le

end Degrees

section Degrees

@[simp]
/-
**MvPolynomial.degreeOf_neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_neg (i : σ) (p : MvPolynomial σ R) : degreeOf i (-p) = degreeOf i
 p
参数：i : σ；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : CommSe
miring R] (n : σ) (p : MvPolynomial σ R),   MvPolynomial.degreeOf n p = Multiset
.count n p.degre…
· 使用定理 `MvPolynomial.degrees_neg`：degrees_neg (p : MvPolynomial σ R) : (-p).degr
ees = p.degrees
-/
theorem degreeOf_neg (i : σ) (p : MvPolynomial σ R) : degreeOf i (-p) = degreeOf i p := by
  rw [degreeOf, degreeOf, degrees_neg]
/-
**MvPolynomial.degreeOf_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_sub_le (i : σ) (p q : MvPolynomial σ R) : degreeOf i (p - q) <= m
ax (degreeOf i p) (degreeOf i q)
参数：i : σ；p q : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MvPolynomial.degreeOf_neg`：degreeOf_neg (i : σ) (p : MvPolynomial σ R) :
 degreeOf i (-p) = degreeOf i p
· 使用定理 `MvPolynomial.degreeOf_add_le`：degreeOf_add_le (n : σ) (f g : MvPolynomia
l σ R) : degreeOf n (f + g) <= max (degreeOf n f) (degreeOf n g)
-/
theorem degreeOf_sub_le (i : σ) (p q : MvPolynomial σ R) :
    degreeOf i (p - q) ≤ max (degreeOf i p) (degreeOf i q) := by
  simpa only [sub_eq_add_neg, degreeOf_neg] using degreeOf_add_le i p (-q)

end Degrees

section Vars

@[simp]
/-
**MvPolynomial.vars_neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_neg : (-p).vars = p.vars
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degrees_neg`：degrees_neg (p : MvPolynomial σ R) : (-p).degr
ees = p.degrees
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vars_neg : (-p).vars = p.vars := by simp [vars, degrees_neg]
/-
**MvPolynomial.vars_sub_subset** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_sub_subset [DecidableEq σ] : (p - q).vars subseteq p.vars union q.var
s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.vars_neg`：vars_neg : (-p).vars = p.vars
· 使用定理 `MvPolynomial.vars_add_subset`：vars_add_subset [DecidableEq σ] (p q : MvP
olynomial σ R) : (p + q).vars subseteq p.vars union q.vars
-/
theorem vars_sub_subset [DecidableEq σ] : (p - q).vars ⊆ p.vars ∪ q.vars := by
  convert! vars_add_subset p (-q) using 2 <;> simp [sub_eq_add_neg]

@[simp]
/-
**MvPolynomial.vars_sub_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：vars_sub_of_disjoint [DecidableEq σ] (hpq : Disjoint p.vars q.vars) : (p -
 q).vars = p.vars union q.vars
参数：hpq : Disjoint p.vars q.vars。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.vars_neg`：vars_neg : (-p).vars = p.vars
· 使用定理 `MvPolynomial.vars_add_of_disjoint`：vars_add_of_disjoint [DecidableEq σ] 
(h : Disjoint p.vars q.vars) : (p + q).vars = p.vars union q.vars
-/
theorem vars_sub_of_disjoint [DecidableEq σ] (hpq : Disjoint p.vars q.vars) :
    (p - q).vars = p.vars ∪ q.vars := by
  rw [← vars_neg q] at hpq
  convert! vars_add_of_disjoint hpq using 2 <;> simp [sub_eq_add_neg]

end Vars

section Eval

variable [CommRing S]
variable (f : R →+* S) (g : σ → S)

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_sub : (p - q).eval₂ f g = p.eval₂ f g - q.eval₂ f g :=
  (eval₂Hom f g).map_sub _ _
/-
**MvPolynomial.eval_sub** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_sub (f : σ -> R) : eval f (p - q) = eval f p - eval f q
参数：f : σ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_sub`：eval₂_sub : (p - q).eval₂ f g = p.eval₂ f g - q.
eval₂ f g
-/
theorem eval_sub (f : σ → R) : eval f (p - q) = eval f p - eval f q :=
  eval₂_sub _ _ _

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_neg : (-p).eval₂ f g = -p.eval₂ f g :=
  (eval₂Hom f g).map_neg _
/-
**MvPolynomial.eval_neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eval_neg (f : σ -> R) : eval f (-p) = -eval f p
参数：f : σ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eval₂_neg`：eval₂_neg : (-p).eval₂ f g = -p.eval₂ f g
-/
theorem eval_neg (f : σ → R) : eval f (-p) = -eval f p :=
  eval₂_neg _ _ _
/-
**MvPolynomial.hom_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：hom_C (f : MvPolynomial σ Int ->+* S) (n : Int) : f (C n) = (n : S)
参数：f : MvPolynomial σ Int ->+* S；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
-/
theorem hom_C (f : MvPolynomial σ ℤ →+* S) (n : ℤ) : f (C n) = (n : S) :=
  eq_intCast (f.comp C) n

/-- A ring homomorphism `f : Z[X_1, X_2, ...] → R`
is determined by the evaluations `f(X_1)`, `f(X_2)`, ... -/
@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `f : Z[X_1, X_2, ...] → R`
is determined by the evaluations `f(X_1)`, `f(X_2)`, ...
-/
theorem eval₂Hom_X {R : Type u} (c : ℤ →+* S) (f : MvPolynomial R ℤ →+* S) (x : MvPolynomial R ℤ) :
    eval₂ c (f ∘ X) x = f x := by
  apply MvPolynomial.induction_on x
    (fun n => by
      rw [hom_C f, eval₂_C]
      exact eq_intCast c n)
    (fun p q hp hq => by
      rw [eval₂_add, hp, hq]
      exact (f.map_add _ _).symm)
    (fun p n hp => by
      rw [eval₂_mul, eval₂_X, hp]
      exact (f.map_mul _ _).symm)

/-- Ring homomorphisms out of integer polynomials on a type `σ` are the same as
functions out of the type `σ`. -/
/-
**MvPolynomial.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：homEquiv : (MvPolynomial σ Int ->+* S) ≃ (σ -> S) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring homomorphisms out of integer polynomials on a type `σ` are the same as
functions out of the type `σ`.
-/
def homEquiv : (MvPolynomial σ ℤ →+* S) ≃ (σ → S) where
  toFun f := f ∘ X
  invFun f := eval₂Hom (Int.castRingHom S) f
  left_inv _ := RingHom.ext <| eval₂Hom_X _ _
  right_inv f := funext fun x => by simp only [coe_eval₂Hom, Function.comp_apply, eval₂_X]

end Eval

section DegreeOf

/-
**MvPolynomial.degreeOf_sub_lt** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_sub_lt {x : σ} {f g : MvPolynomial σ R} {k : Nat} (h : 0 < k) (hf
 : forall m : σ ->₀ Nat, m in f.support -> k <= m x -> coeff m f = coeff m g) (h
g : forall m : σ ->₀ Nat, m in g.support -> k <= m x -> coeff m f = coeff m g) :
 degreeOf x (f - g) < k
参数：h : 0 < k；hf : forall m : σ ->₀ Nat, m in f.support -> k <= m x -> coeff m f 
= coeff m g；hg : forall m : σ ->₀ Nat, m in g.support -> k <= m x -> coeff m f =
 coeff m g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degreeOf_lt_iff`：degreeOf_lt_iff {n : σ} {f : MvPolynomial 
σ R} {d : Nat} (h : 0 < d) : degreeOf n f < d ↔ forall m : σ ->₀ Nat, m in f.sup
port -> m n < d
-/
theorem degreeOf_sub_lt {x : σ} {f g : MvPolynomial σ R} {k : ℕ} (h : 0 < k)
    (hf : ∀ m : σ →₀ ℕ, m ∈ f.support → k ≤ m x → coeff m f = coeff m g)
    (hg : ∀ m : σ →₀ ℕ, m ∈ g.support → k ≤ m x → coeff m f = coeff m g) :
    degreeOf x (f - g) < k := by
  rw [degreeOf_lt_iff h]
  grind [degreeOf_lt_iff]

end DegreeOf

section TotalDegree

@[simp]
/-
**MvPolynomial.totalDegree_neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_neg (a : MvPolynomial σ R) : (-a).totalDegree = a.totalDegree
参数：a : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.support_neg`：∀ {R : Type u} (σ : Type u_1) [inst : CommRing
 R] {p : MvPolynomial σ R}, (-p).support = p.support
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem totalDegree_neg (a : MvPolynomial σ R) : (-a).totalDegree = a.totalDegree := by
  simp only [totalDegree, support_neg]
/-
**MvPolynomial.totalDegree_sub** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_sub (a b : MvPolynomial σ R) : (a - b).totalDegree <= max a.to
talDegree b.totalDegree
参数：a b : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MvPolynomial.totalDegree_add`：totalDegree_add (a b : MvPolynomial σ R) :
 (a + b).totalDegree <= max a.totalDegree b.totalDegree
· 使用定理 `MvPolynomial.totalDegree_neg`：totalDegree_neg (a : MvPolynomial σ R) : (
-a).totalDegree = a.totalDegree
-/
theorem totalDegree_sub (a b : MvPolynomial σ R) :
    (a - b).totalDegree ≤ max a.totalDegree b.totalDegree :=
  calc
    (a - b).totalDegree = (a + -b).totalDegree := by rw [sub_eq_add_neg]
    _ ≤ max a.totalDegree (-b).totalDegree := totalDegree_add a (-b)
    _ = max a.totalDegree b.totalDegree := by rw [totalDegree_neg]
/-
**MvPolynomial.totalDegree_sub_C_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_sub_C_le (p : MvPolynomial σ R) (r : R) : totalDegree (p - C r
) <= totalDegree p
参数：p : MvPolynomial σ R；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MvPolynomial.totalDegree_sub`：totalDegree_sub (a b : MvPolynomial σ R) :
 (a - b).totalDegree <= max a.totalDegree b.totalDegree
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.totalDegree_C`：totalDegree_C (a : R) : (C a : MvPolynomial 
σ R).totalDegree = 0
· 使用定理 `Nat.max_zero`：∀ (a : ℕ), max a 0 = a
-/
theorem totalDegree_sub_C_le (p : MvPolynomial σ R) (r : R) :
    totalDegree (p - C r) ≤ totalDegree p :=
  (totalDegree_sub _ _).trans_eq <| by rw [totalDegree_C, Nat.max_zero]

end TotalDegree

end CommRing

end MvPolynomial

