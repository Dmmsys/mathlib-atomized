/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Tactic.Order

/-!
# Weighted homogeneous polynomials

It is possible to assign weights (in a commutative additive monoid `M`) to the variables of a
multivariate polynomial ring, so that monomials of the ring then have a weighted degree with
respect to the weights of the variables. The weights are represented by a function `w : σ → M`,
where `σ` are the indeterminates.

A multivariate polynomial `φ` is weighted homogeneous of weighted degree `m : M` if all monomials
occurring in `φ` have the same weighted degree `m`.

## Main definitions/lemmas

* `weightedTotalDegree' w φ` : the weighted total degree of a multivariate polynomial with respect
  to the weights `w`, taking values in `WithBot M`.

* `weightedTotalDegree w φ` : When `M` has a `⊥` element, we can define the weighted total degree
  of a multivariate polynomial as a function taking values in `M`.

* `IsWeightedHomogeneous w φ m`: a predicate that asserts that `φ` is weighted homogeneous
  of weighted degree `m` with respect to the weights `w`.

* `weightedHomogeneousSubmodule R w m`: the submodule of homogeneous polynomials
  of weighted degree `m`.

* `weightedHomogeneousComponent w m`: the additive morphism that projects polynomials
  onto their summand that is weighted homogeneous of degree `n` with respect to `w`.

* `sum_weightedHomogeneousComponent`: every polynomial is the sum of its weighted homogeneous
  components.
-/

@[expose] public section


noncomputable section

open Set Function Finset Finsupp AddMonoidAlgebra

variable {R M : Type*} [CommSemiring R]

namespace MvPolynomial

variable {σ : Type*}

section AddCommMonoid

variable [AddCommMonoid M]

/-! ### `weight` -/


section SemilatticeSup

variable [SemilatticeSup M]

/-- The weighted total degree of a multivariate polynomial, taking values in `WithBot M`. -/
/-
**MvPolynomial.weightedTotalDegree'** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：weightedTotalDegree' (w : σ -> M) (p : MvPolynomial σ R) : WithBot M
参数：w : σ -> M；p : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weighted total degree of a multivariate polynomial, taking values in `WithBo
t M`.
-/
def weightedTotalDegree' (w : σ → M) (p : MvPolynomial σ R) : WithBot M :=
  p.support.sup fun s => weight w s

/-- The `weightedTotalDegree'` of a polynomial `p` is `⊥` if and only if `p = 0`. -/
/-
**MvPolynomial.weightedTotalDegree'_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPoly
nomial`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} [in
st_1 : AddCommMonoid M]   [inst_2 : SemilatticeSup M] (w : σ → M) (p : MvPolynom
ial σ R), MvPolynomial.weightedTotalDegree' w p = ⊥ ↔ p = 0
参数：w : σ → M；p : MvPolynomial σ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a

--- 原说明 ---
The `weightedTotalDegree'` of a polynomial `p` is `⊥` if and only if `p = 0`.
-/
theorem weightedTotalDegree'_eq_bot_iff (w : σ → M) (p : MvPolynomial σ R) :
    weightedTotalDegree' w p = ⊥ ↔ p = 0 := by
  simp only [weightedTotalDegree', Finset.sup_eq_bot_iff, mem_support_iff, WithBot.coe_ne_bot,
    MvPolynomial.eq_zero_iff]
  exact forall_congr' fun _ => Classical.not_not

/-- The `weightedTotalDegree'` of the zero polynomial is `⊥`. -/
/-
**MvPolynomial.weightedTotalDegree'_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} [in
st_1 : AddCommMonoid M]   [inst_2 : SemilatticeSup M] (w : σ → M), MvPolynomial.
weightedTotalDegree' w 0 = ⊥
参数：w : σ → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `weightedTotalDegree'` of the zero polynomial is `⊥`.
-/
theorem weightedTotalDegree'_zero (w : σ → M) :
    weightedTotalDegree' w (0 : MvPolynomial σ R) = ⊥ := by
  simp only [weightedTotalDegree', support_zero, Finset.sup_empty]

section OrderBot

variable [OrderBot M]

/-- When `M` has a `⊥` element, we can define the weighted total degree of a multivariate
  polynomial as a function taking values in `M`. -/
/-
**MvPolynomial.weightedTotalDegree** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：weightedTotalDegree (w : σ -> M) (p : MvPolynomial σ R) : M
参数：w : σ -> M；p : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `M` has a `⊥` element, we can define the weighted total degree of a multiva
riate
  polynomial as a function taking values in `M`.
-/
def weightedTotalDegree (w : σ → M) (p : MvPolynomial σ R) : M :=
  p.support.sup fun s => weight w s

/-- This lemma relates `weightedTotalDegree` and `weightedTotalDegree'`. -/
/-
**MvPolynomial.weightedTotalDegree_coe** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：weightedTotalDegree_coe (w : σ -> M) (p : MvPolynomial σ R) (hp : p != 0) 
: weightedTotalDegree' w p = ↑(weightedTotalDegree w p)
参数：w : σ -> M；p : MvPolynomial σ R；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithBot.ne_bot_iff_exists`：ne_bot_iff_exists {x : WithBot α} : x != ⊥ ↔ 
exists a : α, ↑a = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MvPolynomial.weightedTotalDegree'_eq_bot_iff`：∀ {R : Type u_1} {M : Type
 u_2} [inst : CommSemiring R] {σ : Type u_3} [inst_1 : AddCommMonoid M]   [inst_
2 : SemilatticeSup M] (w : σ → M) …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
This lemma relates `weightedTotalDegree` and `weightedTotalDegree'`.
-/
theorem weightedTotalDegree_coe (w : σ → M) (p : MvPolynomial σ R) (hp : p ≠ 0) :
    weightedTotalDegree' w p = ↑(weightedTotalDegree w p) := by
  rw [Ne, ← weightedTotalDegree'_eq_bot_iff w p, ← Ne, WithBot.ne_bot_iff_exists] at hp
  obtain ⟨m, hm⟩ := hp
  apply le_antisymm
  · simp only [weightedTotalDegree, weightedTotalDegree', Finset.sup_le_iff, WithBot.coe_le_coe]
    intro b
    exact Finset.le_sup
  · simp only [weightedTotalDegree]
    have hm' : weightedTotalDegree' w p ≤ m := le_of_eq hm.symm
    rw [← hm]
    simpa [weightedTotalDegree'] using hm'

/-- The `weightedTotalDegree` of the zero polynomial is `⊥`. -/
/-
**MvPolynomial.weightedTotalDegree_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：weightedTotalDegree_zero (w : σ -> M) : weightedTotalDegree w (0 : MvPolyn
omial σ R) = ⊥
参数：w : σ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `weightedTotalDegree` of the zero polynomial is `⊥`.
-/
theorem weightedTotalDegree_zero (w : σ → M) :
    weightedTotalDegree w (0 : MvPolynomial σ R) = ⊥ := by
  simp only [weightedTotalDegree, support_zero, Finset.sup_empty]
/-
**MvPolynomial.le_weightedTotalDegree** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：le_weightedTotalDegree (w : σ -> M) {φ : MvPolynomial σ R} {d : σ ->₀ Nat}
 (hd : d in φ.support) : weight w d <= φ.weightedTotalDegree w
参数：w : σ -> M；hd : d in φ.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem le_weightedTotalDegree (w : σ → M) {φ : MvPolynomial σ R} {d : σ →₀ ℕ}
    (hd : d ∈ φ.support) : weight w d ≤ φ.weightedTotalDegree w :=
  le_sup hd

end OrderBot

end SemilatticeSup

/-- A multivariate polynomial `φ` is weighted homogeneous of weighted degree `m` if all monomials
  occurring in `φ` have weighted degree `m`. -/
/-
**MvPolynomial.IsWeightedHomogeneous** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：IsWeightedHomogeneous (w : σ -> M) (φ : MvPolynomial σ R) (m : M) : Prop
参数：w : σ -> M；φ : MvPolynomial σ R；m : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multivariate polynomial `φ` is weighted homogeneous of weighted degree `m` if 
all monomials
  occurring in `φ` have weighted degree `m`.
-/
def IsWeightedHomogeneous (w : σ → M) (φ : MvPolynomial σ R) (m : M) : Prop :=
  ∀ ⦃d⦄, coeff d φ ≠ 0 → weight w d = m

variable (R)

set_option backward.isDefEq.respectTransparency false in
/-- The submodule of homogeneous `MvPolynomial`s of degree `n`. -/
/-
**MvPolynomial.weightedHomogeneousSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynom
ial`。
形式化陈述：weightedHomogeneousSubmodule (w : σ -> M) (m : M) : Submodule R (MvPolynom
ial σ R) where carrier
参数：w : σ -> M；m : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of homogeneous `MvPolynomial`s of degree `n`.
-/
def weightedHomogeneousSubmodule (w : σ → M) (m : M) : Submodule R (MvPolynomial σ R) where
  carrier := { x | x.IsWeightedHomogeneous w m }
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc
    exact ha (right_ne_zero_of_mul hc)
  zero_mem' _ hd := False.elim (hd <| coeff_zero _)
  add_mem' {a} {b} ha hb c hc := by
    rw [coeff_add] at hc
    obtain h | h : coeff c a ≠ 0 ∨ coeff c b ≠ 0 := by
      contrapose! hc
      simp only [hc, add_zero]
    · exact ha h
    · exact hb h

@[simp]
/-
**MvPolynomial.mem_weightedHomogeneousSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial`。
形式化陈述：mem_weightedHomogeneousSubmodule (w : σ -> M) (m : M) (p : MvPolynomial σ 
R) : p in weightedHomogeneousSubmodule R w m ↔ p.IsWeightedHomogeneous w m
参数：w : σ -> M；m : M；p : MvPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_weightedHomogeneousSubmodule (w : σ → M) (m : M) (p : MvPolynomial σ R) :
    p ∈ weightedHomogeneousSubmodule R w m ↔ p.IsWeightedHomogeneous w m :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- The submodule `weightedHomogeneousSubmodule R w m` of homogeneous `MvPolynomial`s of
  degree `n` is equal to the `R`-submodule of all `p : (σ →₀ ℕ) →₀ R` such that
  `p.support ⊆ {d | weight w d = m}`. While equal, the former has a
  convenient definitional reduction. -/
/-
**MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported** 是 Mathlib 中的一
个定理，位于命名空间 `MvPolynomial`。
形式化陈述：weightedHomogeneousSubmodule_eq_finsupp_supported (w : σ -> M) (m : M) : w
eightedHomogeneousSubmodule R w m = AddMonoidAlgebra.supported R R {d | weight w
 d = m}
参数：w : σ -> M；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The submodule `weightedHomogeneousSubmodule R w m` of homogeneous `MvPolynomial`
s of
  degree `n` is equal to the `R`-submodule of all `p : (σ →₀ ℕ) →₀ R` such that
  `p.support ⊆ {d | weight w d = m}`. While equal, the former has a
  convenient definitional reduction.
-/
theorem weightedHomogeneousSubmodule_eq_finsupp_supported (w : σ → M) (m : M) :
    weightedHomogeneousSubmodule R w m = AddMonoidAlgebra.supported R R {d | weight w d = m} := by
  ext x
  simp [IsWeightedHomogeneous]
  simp [AddMonoidAlgebra.mem_supported, Set.subset_def, MvPolynomial, coeff]
/-
**MvPolynomial.weightedHomogeneousSubmodule_fg** 是 Mathlib 中的一个引理，位于命名空间 `MvPoly
nomial`。
形式化陈述：weightedHomogeneousSubmodule_fg [Finite σ] (w : σ -> Nat) (hw : forall (x 
: σ), w x != 0) (n : Nat) : (weightedHomogeneousSubmodule R w n).FG
参数：w : σ -> Nat；hw : forall (x : σ), w x != 0；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported`：weighted
HomogeneousSubmodule_eq_finsupp_supported (w : σ -> M) (m : M) : weightedHomogen
eousSubmodule R w m = AddMonoidAlgebra.supported R R…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Finsupp.finite_of_nat_weight_eq`：finite_of_nat_weight_eq [Finite σ] (w :
 σ -> Nat) (hw : forall x, w x != 0) (n : Nat) : {d : σ ->₀ Nat | weight w d = n
}.Finite
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
-/
lemma weightedHomogeneousSubmodule_fg [Finite σ] (w : σ → ℕ) (hw : ∀ (x : σ), w x ≠ 0) (n : ℕ) :
    (weightedHomogeneousSubmodule R w n).FG := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported, ← Module.Finite.iff_fg]
  have := (Finsupp.finite_of_nat_weight_eq w hw n).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport R {d | Finsupp.weight w d = n})

variable {R}

set_option backward.isDefEq.respectTransparency false in
/-- The submodule generated by products `Pm * Pn` of weighted homogeneous polynomials of degrees `m`
  and `n` is contained in the submodule of weighted homogeneous polynomials of degree `m + n`. -/
/-
**MvPolynomial.weightedHomogeneousSubmodule_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial`。
形式化陈述：weightedHomogeneousSubmodule_mul (w : σ -> M) (m n : M) : weightedHomogene
ousSubmodule R w m * weightedHomogeneousSubmodule R w n <= weightedHomogeneousSu
bmodule R w (m + n)
参数：w : σ -> M；m n : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mul_le`：mul_le : M * N <= P ↔ forall m in M, forall n in N, m 
* n in P
· 使用定理 `Finset.exists_ne_zero_of_sum_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : ι → M}, ∑ x ∈ s, f x ≠ 0 → ∃ a ∈ s, f
 a ≠ 0
· 使用定理 `MvPolynomial.coeff_mul`：coeff_mul [DecidableEq σ] (p q : MvPolynomial σ 
R) (n : σ ->₀ Nat) : coeff n (p * q) = ∑ x in Finset.antidiagonal n, coeff x.1 p
 * coeff x.2…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
The submodule generated by products `Pm * Pn` of weighted homogeneous polynomial
s of degrees `m`
  and `n` is contained in the submodule of weighted homogeneous polynomials of d
egree `m + n`.
-/
theorem weightedHomogeneousSubmodule_mul (w : σ → M) (m n : M) :
    weightedHomogeneousSubmodule R w m * weightedHomogeneousSubmodule R w n ≤
      weightedHomogeneousSubmodule R w (m + n) := by
  classical
  rw [Submodule.mul_le]
  intro φ hφ ψ hψ c hc
  rw [coeff_mul] at hc
  obtain ⟨⟨d, e⟩, hde, H⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have aux : coeff d φ ≠ 0 ∧ coeff e ψ ≠ 0 := by
    contrapose! H
    by_cases h : coeff d φ = 0 <;>
      simp_all only [Ne, not_false_iff, zero_mul, mul_zero]
  rw [← mem_antidiagonal.mp hde, ← hφ aux.1, ← hψ aux.2, map_add]

/-- Monomials are weighted homogeneous. -/
/-
**MvPolynomial.isWeightedHomogeneous_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyn
omial`。
形式化陈述：isWeightedHomogeneous_monomial (w : σ -> M) (d : σ ->₀ Nat) (r : R) {m : M
} (hm : weight w d = m) : IsWeightedHomogeneous w (monomial d r) m
参数：w : σ -> M；d : σ ->₀ Nat；r : R；hm : weight w d = m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0

--- 原说明 ---
Monomials are weighted homogeneous.
-/
theorem isWeightedHomogeneous_monomial (w : σ → M) (d : σ →₀ ℕ) (r : R) {m : M}
    (hm : weight w d = m) : IsWeightedHomogeneous w (monomial d r) m := by
  classical
  intro c hc
  rw [coeff_monomial] at hc
  split_ifs at hc with h
  · subst c
    exact hm
  · contradiction

/-- A polynomial of weightedTotalDegree `⊥` is weighted homogeneous of degree `⊥`. -/
/-
**MvPolynomial.isWeightedHomogeneous_of_total_degree_zero** 是 Mathlib 中的一个定理，位于命
名空间 `MvPolynomial`。
形式化陈述：isWeightedHomogeneous_of_total_degree_zero [SemilatticeSup M] [OrderBot M]
 (w : σ -> M) {p : MvPolynomial σ R} (hp : weightedTotalDegree w p = (⊥ : M)) : 
IsWeightedHomogeneous w p (⊥ : M)
参数：w : σ -> M；hp : weightedTotalDegree w p = (⊥ : M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.weightedTotalDegree_coe`：weightedTotalDegree_coe (w : σ -> 
M) (p : MvPolynomial σ R) (hp : p != 0) : weightedTotalDegree' w p = ↑(weightedT
otalDegree w p)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPolynomial.ne_zero_iff`：ne_zero_iff {p : MvPolynomial σ R} : p != 0 ↔ 
exists d, coeff d p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0

--- 原说明 ---
A polynomial of weightedTotalDegree `⊥` is weighted homogeneous of degree `⊥`.
-/
theorem isWeightedHomogeneous_of_total_degree_zero [SemilatticeSup M] [OrderBot M] (w : σ → M)
    {p : MvPolynomial σ R} (hp : weightedTotalDegree w p = (⊥ : M)) :
    IsWeightedHomogeneous w p (⊥ : M) := by
  intro d hd
  have h := weightedTotalDegree_coe w p (MvPolynomial.ne_zero_iff.mpr ⟨d, hd⟩)
  simp only [weightedTotalDegree', hp] at h
  rw [eq_bot_iff, ← WithBot.coe_le_coe, ← h]
  apply Finset.le_sup (mem_support_iff.mpr hd)

/-- Constant polynomials are weighted homogeneous of degree 0. -/
/-
**MvPolynomial.isWeightedHomogeneous_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：isWeightedHomogeneous_C (w : σ -> M) (r : R) : IsWeightedHomogeneous w (C 
r : MvPolynomial σ R) 0
参数：w : σ -> M；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.isWeightedHomogeneous_monomial`：isWeightedHomogeneous_monom
ial (w : σ -> M) (d : σ ->₀ Nat) (r : R) {m : M} (hm : weight w d = m) : IsWeigh
tedHomogeneous w (monomial d r) m
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
Constant polynomials are weighted homogeneous of degree 0.
-/
theorem isWeightedHomogeneous_C (w : σ → M) (r : R) :
    IsWeightedHomogeneous w (C r : MvPolynomial σ R) 0 :=
  isWeightedHomogeneous_monomial _ _ _ (map_zero _)

variable (R)

/-- 0 is weighted homogeneous of any degree. -/
/-
**MvPolynomial.isWeightedHomogeneous_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：isWeightedHomogeneous_zero (w : σ -> M) (m : M) : IsWeightedHomogeneous w 
(0 : MvPolynomial σ R) m
参数：w : σ -> M；m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p

--- 原说明 ---
0 is weighted homogeneous of any degree.
-/
theorem isWeightedHomogeneous_zero (w : σ → M) (m : M) :
    IsWeightedHomogeneous w (0 : MvPolynomial σ R) m :=
  (weightedHomogeneousSubmodule R w m).zero_mem

/-- 1 is weighted homogeneous of degree 0. -/
/-
**MvPolynomial.isWeightedHomogeneous_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：isWeightedHomogeneous_one (w : σ -> M) : IsWeightedHomogeneous w (1 : MvPo
lynomial σ R) 0
参数：w : σ -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.isWeightedHomogeneous_C`：isWeightedHomogeneous_C (w : σ -> 
M) (r : R) : IsWeightedHomogeneous w (C r : MvPolynomial σ R) 0

--- 原说明 ---
1 is weighted homogeneous of degree 0.
-/
theorem isWeightedHomogeneous_one (w : σ → M) : IsWeightedHomogeneous w (1 : MvPolynomial σ R) 0 :=
  isWeightedHomogeneous_C _ _
/-
**MvPolynomial.isWeightedHomogeneous_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `MvPol
ynomial`。
形式化陈述：isWeightedHomogeneous_of_isEmpty [IsEmpty σ] (w : σ -> M) (f : MvPolynomia
l σ R) : IsWeightedHomogeneous w f 0
参数：w : σ -> M；f : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.eq_C_of_isEmpty`：eq_C_of_isEmpty [IsEmpty σ] (p : MvPolynom
ial σ R) : p = C (p.coeff 0)
· 使用定理 `MvPolynomial.isWeightedHomogeneous_C`：isWeightedHomogeneous_C (w : σ -> 
M) (r : R) : IsWeightedHomogeneous w (C r : MvPolynomial σ R) 0
-/
lemma isWeightedHomogeneous_of_isEmpty [IsEmpty σ] (w : σ → M) (f : MvPolynomial σ R) :
    IsWeightedHomogeneous w f 0 := by
  rw [eq_C_of_isEmpty f]
  exact isWeightedHomogeneous_C _ _

/-- An indeterminate `i : σ` is weighted homogeneous of degree `w i`. -/
/-
**MvPolynomial.isWeightedHomogeneous_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：isWeightedHomogeneous_X (w : σ -> M) (i : σ) : IsWeightedHomogeneous w (X 
i : MvPolynomial σ R) (w i)
参数：w : σ -> M；i : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.isWeightedHomogeneous_monomial`：isWeightedHomogeneous_monom
ial (w : σ -> M) (d : σ ->₀ Nat) (r : R) {m : M} (hm : weight w d = m) : IsWeigh
tedHomogeneous w (monomial d r) m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `one_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 1 • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An indeterminate `i : σ` is weighted homogeneous of degree `w i`.
-/
theorem isWeightedHomogeneous_X (w : σ → M) (i : σ) :
    IsWeightedHomogeneous w (X i : MvPolynomial σ R) (w i) := by
  apply isWeightedHomogeneous_monomial
  simp only [weight, LinearMap.toAddMonoidHom_coe, linearCombination_single, one_nsmul]

namespace IsWeightedHomogeneous

variable {R}
variable {φ ψ : MvPolynomial σ R} {m n : M}

/-- The weighted degree of a weighted homogeneous polynomial controls its support. -/
/-
**MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mv
Polynomial.IsWeightedHomogeneous`。
形式化陈述：coeff_eq_zero {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n) (d : σ ->₀ N
at) (hd : weight w d != n) : coeff d φ = 0
参数：hφ : IsWeightedHomogeneous w φ n；d : σ ->₀ Nat；hd : weight w d != n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a

--- 原说明 ---
The weighted degree of a weighted homogeneous polynomial controls its support.
-/
theorem coeff_eq_zero {w : σ → M} (hφ : IsWeightedHomogeneous w φ n) (d : σ →₀ ℕ)
    (hd : weight w d ≠ n) : coeff d φ = 0 := by
  have aux := mt (@hφ d) hd
  rwa [Classical.not_not] at aux

/-- The weighted degree of a nonzero weighted homogeneous polynomial is well-defined. -/
/-
**MvPolynomial.IsWeightedHomogeneous.inj_right** 是 Mathlib 中的一个定理，位于命名空间 `MvPoly
nomial.IsWeightedHomogeneous`。
形式化陈述：inj_right {w : σ -> M} (hφ : φ != 0) (hm : IsWeightedHomogeneous w φ m) (h
n : IsWeightedHomogeneous w φ n) : m = n
参数：hφ : φ != 0；hm : IsWeightedHomogeneous w φ m；hn : IsWeightedHomogeneous w φ n
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.exists_coeff_ne_zero`：exists_coeff_ne_zero {p : MvPolynomia
l σ R} (h : p != 0) : exists d, coeff d p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The weighted degree of a nonzero weighted homogeneous polynomial is well-defined
.
-/
theorem inj_right {w : σ → M} (hφ : φ ≠ 0) (hm : IsWeightedHomogeneous w φ m)
    (hn : IsWeightedHomogeneous w φ n) : m = n := by
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ
  rw [← hm hd, ← hn hd]

/-- The sum of two weighted homogeneous polynomials of degree `n` is weighted homogeneous of
  weighted degree `n`. -/
/-
**MvPolynomial.IsWeightedHomogeneous.add** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
.IsWeightedHomogeneous`。
形式化陈述：add {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomoge
neous w ψ n) : IsWeightedHomogeneous w (φ + ψ) n
参数：hφ : IsWeightedHomogeneous w φ n；hψ : IsWeightedHomogeneous w ψ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…

--- 原说明 ---
The sum of two weighted homogeneous polynomials of degree `n` is weighted homoge
neous of
  weighted degree `n`.
-/
theorem add {w : σ → M} (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ + ψ) n :=
  (weightedHomogeneousSubmodule R w n).add_mem hφ hψ

section CommRing

-- In this section we shadow the semiring `R` with a ring `R`.
variable {R : Type*} [CommRing R] {w : σ → M} {φ ψ : MvPolynomial σ R}

/-- The negation of a weighted homogeneous polynomial of degree `n` is weighted homogeneous
  of weighted degree `n`. -/
/-
**MvPolynomial.IsWeightedHomogeneous.neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
.IsWeightedHomogeneous`。
形式化陈述：neg (hφ : IsWeightedHomogeneous w φ n) : IsWeightedHomogeneous w (-φ) n
参数：hφ : IsWeightedHomogeneous w φ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …

--- 原说明 ---
The negation of a weighted homogeneous polynomial of degree `n` is weighted homo
geneous
  of weighted degree `n`.
-/
theorem neg (hφ : IsWeightedHomogeneous w φ n) : IsWeightedHomogeneous w (-φ) n :=
  (weightedHomogeneousSubmodule R w n).neg_mem hφ

/-- The difference of two weighted homogeneous polynomials of degree `n` is weighted homogeneous
  of weighted degree `n`. -/
/-
**MvPolynomial.IsWeightedHomogeneous.sub** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
.IsWeightedHomogeneous`。
形式化陈述：sub (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) 
: IsWeightedHomogeneous w (φ - ψ) n
参数：hφ : IsWeightedHomogeneous w φ n；hψ : IsWeightedHomogeneous w ψ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …

--- 原说明 ---
The difference of two weighted homogeneous polynomials of degree `n` is weighted
 homogeneous
  of weighted degree `n`.
-/
theorem sub (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ - ψ) n :=
  (weightedHomogeneousSubmodule R w n).sub_mem hφ hψ

end CommRing

/-- A weighted homogeneous polynomial of degree `n` is zero if no monomial has weight `n`. -/
/-
**MvPolynomial.IsWeightedHomogeneous.eq_zero_of_no_monomials** 是 Mathlib 中的一个定理，
位于命名空间 `MvPolynomial.IsWeightedHomogeneous`。
形式化陈述：eq_zero_of_no_monomials {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n) (h
no : forall d : σ ->₀ Nat, weight w d != n) : φ = 0
参数：hφ : IsWeightedHomogeneous w φ n；hno : forall d : σ ->₀ Nat, weight w d != n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.support_eq_empty`：support_eq_empty {p : MvPolynomial σ R} :
 p.support = ∅ ↔ p = 0
· 使用定理 `Finset.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem {s : Finset 
α} (H : forall x, x ∉ s) : s = ∅
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0

--- 原说明 ---
A weighted homogeneous polynomial of degree `n` is zero if no monomial has weigh
t `n`.
-/
theorem eq_zero_of_no_monomials {w : σ → M} (hφ : IsWeightedHomogeneous w φ n)
    (hno : ∀ d : σ →₀ ℕ, weight w d ≠ n) : φ = 0 :=
  support_eq_empty.mp <| Finset.eq_empty_of_forall_notMem
    fun _ hd ↦ hno _ (hφ (mem_support_iff.mp hd))

/-- A weighted homogeneous polynomial of degree `n` whose support degrees are all equal to a
fixed `d₀` is a single monomial. -/
/-
**MvPolynomial.IsWeightedHomogeneous.eq_monomial_of_unique_weight** 是 Mathlib 中的
一个定理，位于命名空间 `MvPolynomial.IsWeightedHomogeneous`。
形式化陈述：eq_monomial_of_unique_weight {w : σ -> M} {d₀ : σ ->₀ Nat} (hφ : IsWeighte
dHomogeneous w φ n) (huniq : forall d, weight w d = n -> d = d₀) : φ = monomial 
d₀ (coeff d₀ φ)
参数：hφ : IsWeightedHomogeneous w φ n；huniq : forall d, weight w d = n -> d = d₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.eq_monomial_of_support_subset_singleton`：eq_monomial_of_sup
port_subset_singleton {φ : MvPolynomial σ R} {d₀ : σ ->₀ Nat} (h : forall d in φ
.support, d = d₀) : φ = monomial d₀ (coeff…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0

--- 原说明 ---
A weighted homogeneous polynomial of degree `n` whose support degrees are all eq
ual to a
fixed `d₀` is a single monomial.
-/
theorem eq_monomial_of_unique_weight {w : σ → M} {d₀ : σ →₀ ℕ} (hφ : IsWeightedHomogeneous w φ n)
    (huniq : ∀ d, weight w d = n → d = d₀) : φ = monomial d₀ (coeff d₀ φ) :=
  eq_monomial_of_support_subset_singleton fun d hd ↦ huniq d (hφ (mem_support_iff.mp hd))

/-- The sum of weighted homogeneous polynomials of degree `n` is weighted homogeneous of
  weighted degree `n`. -/
/-
**MvPolynomial.IsWeightedHomogeneous.sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
.IsWeightedHomogeneous`。
形式化陈述：sum {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) (n : M) {w : σ 
-> M} (h : forall i in s, IsWeightedHomogeneous w (φ i) n) : IsWeightedHomogeneo
us w (∑ i in s, φ i) n
参数：s : Finset ι；φ : ι -> MvPolynomial σ R；n : M；h : forall i in s, IsWeightedHom
ogeneous w (φ i) n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…

--- 原说明 ---
The sum of weighted homogeneous polynomials of degree `n` is weighted homogeneou
s of
  weighted degree `n`.
-/
theorem sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : M) {w : σ → M}
    (h : ∀ i ∈ s, IsWeightedHomogeneous w (φ i) n) : IsWeightedHomogeneous w (∑ i ∈ s, φ i) n :=
  (weightedHomogeneousSubmodule R w n).sum_mem h

set_option backward.isDefEq.respectTransparency false in
/-- The product of weighted homogeneous polynomials of weighted degrees `m` and `n` is weighted
  homogeneous of weighted degree `m + n`. -/
/-
**MvPolynomial.IsWeightedHomogeneous.mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
.IsWeightedHomogeneous`。
形式化陈述：mul {w : σ -> M} (hφ : IsWeightedHomogeneous w φ m) (hψ : IsWeightedHomoge
neous w ψ n) : IsWeightedHomogeneous w (φ * ψ) (m + n)
参数：hφ : IsWeightedHomogeneous w φ m；hψ : IsWeightedHomogeneous w ψ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.weightedHomogeneousSubmodule_mul`：weightedHomogeneousSubmod
ule_mul (w : σ -> M) (m n : M) : weightedHomogeneousSubmodule R w m * weightedHo
mogeneousSubmodule R w n <= weighte…
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
The product of weighted homogeneous polynomials of weighted degrees `m` and `n` 
is weighted
  homogeneous of weighted degree `m + n`.
-/
theorem mul {w : σ → M} (hφ : IsWeightedHomogeneous w φ m) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ * ψ) (m + n) :=
  weightedHomogeneousSubmodule_mul w m n <| Submodule.mul_mem_mul hφ hψ
/-
**MvPolynomial.IsWeightedHomogeneous.C_mul** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomi
al.IsWeightedHomogeneous`。
形式化陈述：C_mul {w : σ -> M} (hφ : IsWeightedHomogeneous w φ m) (r : R) : IsWeighted
Homogeneous w (C r * φ) m
参数：hφ : IsWeightedHomogeneous w φ m；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MvPolynomial.IsWeightedHomogeneous.mul`：mul {w : σ -> M} (hφ : IsWeighte
dHomogeneous w φ m) (hψ : IsWeightedHomogeneous w ψ n) : IsWeightedHomogeneous w
 (φ * ψ) (m + n)
· 使用定理 `MvPolynomial.isWeightedHomogeneous_C`：isWeightedHomogeneous_C (w : σ -> 
M) (r : R) : IsWeightedHomogeneous w (C r : MvPolynomial σ R) 0
-/
lemma C_mul {w : σ → M} (hφ : IsWeightedHomogeneous w φ m) (r : R) :
    IsWeightedHomogeneous w (C r * φ) m := by
  rw [← zero_add m]
  exact (isWeightedHomogeneous_C w r).mul hφ
/-
**MvPolynomial.IsWeightedHomogeneous.pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
.IsWeightedHomogeneous`。
形式化陈述：pow {w : σ -> M} (hφ : IsWeightedHomogeneous w φ m) (n : Nat) : IsWeighted
Homogeneous w (φ ^ n) (n • m)
参数：hφ : IsWeightedHomogeneous w φ m；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MvPolynomial.isWeightedHomogeneous_one`：isWeightedHomogeneous_one (w : σ
 -> M) : IsWeightedHomogeneous w (1 : MvPolynomial σ R) 0
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `MvPolynomial.IsWeightedHomogeneous.mul`：mul {w : σ -> M} (hφ : IsWeighte
dHomogeneous w φ m) (hψ : IsWeightedHomogeneous w ψ n) : IsWeightedHomogeneous w
 (φ * ψ) (m + n)
-/
theorem pow {w : σ → M} (hφ : IsWeightedHomogeneous w φ m) (n : ℕ) :
    IsWeightedHomogeneous w (φ ^ n) (n • m) := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact isWeightedHomogeneous_one R w
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul hφ

/-- A product of weighted homogeneous polynomials is weighted homogeneous, with weighted degree
  equal to the sum of the weighted degrees. -/
/-
**MvPolynomial.IsWeightedHomogeneous.prod** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l.IsWeightedHomogeneous`。
形式化陈述：prod {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) (n : ι -> M) {
w : σ -> M} : (forall i in s, IsWeightedHomogeneous w (φ i) (n i)) -> IsWeighted
Homogeneous w (∏ i in s, φ i) (∑ i in s, n i)
参数：s : Finset ι；φ : ι -> MvPolynomial σ R；n : ι -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `MvPolynomial.IsWeightedHomogeneous.mul`：mul {w : σ -> M} (hφ : IsWeighte
dHomogeneous w φ m) (hψ : IsWeightedHomogeneous w ψ n) : IsWeightedHomogeneous w
 (φ * ψ) (m + n)
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s

--- 原说明 ---
A product of weighted homogeneous polynomials is weighted homogeneous, with weig
hted degree
  equal to the sum of the weighted degrees.
-/
theorem prod {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ι → M) {w : σ → M} :
    (∀ i ∈ s, IsWeightedHomogeneous w (φ i) (n i)) →
      IsWeightedHomogeneous w (∏ i ∈ s, φ i) (∑ i ∈ s, n i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro
    simp only [isWeightedHomogeneous_one, Finset.sum_empty, Finset.prod_empty]
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (Finset.mem_insert_self _ _)).mul (IH _)
    intro j hjs
    exact h j (Finset.mem_insert_of_mem hjs)

/-- A nonzero weighted-homogeneous polynomial of weighted degree `n` has weighted total degree
  `n`. -/
/-
**MvPolynomial.IsWeightedHomogeneous.weighted_total_degree** 是 Mathlib 中的一个定理，位于
命名空间 `MvPolynomial.IsWeightedHomogeneous`。
形式化陈述：weighted_total_degree [SemilatticeSup M] {w : σ -> M} (hφ : IsWeightedHomo
geneous w φ n) (h : φ != 0) : weightedTotalDegree' w φ = n
参数：hφ : IsWeightedHomogeneous w φ n；h : φ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MvPolynomial.exists_coeff_ne_zero`：exists_coeff_ne_zero {p : MvPolynomia
l σ R} (h : p != 0) : exists d, coeff d p != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f

--- 原说明 ---
A nonzero weighted-homogeneous polynomial of weighted degree `n` has weighted to
tal degree
  `n`.
-/
theorem weighted_total_degree [SemilatticeSup M] {w : σ → M} (hφ : IsWeightedHomogeneous w φ n)
    (h : φ ≠ 0) : weightedTotalDegree' w φ = n := by
  simp only [weightedTotalDegree']
  apply le_antisymm
  · simp only [Finset.sup_le_iff, mem_support_iff, WithBot.coe_le_coe]
    exact fun d hd => le_of_eq (hφ hd)
  · obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h
    simp only [← hφ hd]
    replace hd := Finsupp.mem_support_iff.mpr hd
    apply Finset.le_sup hd

set_option backward.isDefEq.respectTransparency false in
/-- Induction principle for weighted homogeneous polynomials. -/
/-
**MvPolynomial.IsWeightedHomogeneous.induction_on** 是 Mathlib 中的一个引理，位于命名空间 `MvP
olynomial.IsWeightedHomogeneous`。
形式化陈述：induction_on {w : σ -> M} {m : M} {motive : (p : MvPolynomial σ R) -> p.Is
WeightedHomogeneous w m -> Prop} (zero : motive 0 (isWeightedHomogeneous_zero R 
w m)) (add : forall p q hp hq, motive p hp -> motive q hq -> motive (p + q) (hp.
add hq)) (monomial : forall (d : σ ->₀ Nat) (r : R) (hr : Finsupp.weight w d = m
), motive ((monomial d) r) (isWeightedHomogeneous_monomial w d r hr)) {p : MvPol
ynomial σ R} (hp : p.IsWeightedHomogeneous w m) : motive p hp
参数：p : MvPolynomial σ R；zero : motive 0 (isWeightedHomogeneous_zero R w m)；add :
 forall p q hp hq, motive p hp -> motive q hq -> motive (p + q) (hp.add hq)；mono
mial : forall (d : σ ->₀ Nat) (r : R) (hr : Finsupp.weight w d = m), motive ((mo
nomial d) r) (isWeightedHomogeneous_monomial w d r hr)；hp : p.IsWeightedHomogene
ous w m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.isWeightedHomogeneous_zero`：isWeightedHomogeneous_zero (w :
 σ -> M) (m : M) : IsWeightedHomogeneous w (0 : MvPolynomial σ R) m
· 使用定理 `MvPolynomial.IsWeightedHomogeneous.add`：add {w : σ -> M} (hφ : IsWeighte
dHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) : IsWeightedHomogeneous w
 (φ + ψ) n
· 使用定理 `MvPolynomial.isWeightedHomogeneous_monomial`：isWeightedHomogeneous_monom
ial (w : σ -> M) (d : σ ->₀ Nat) (r : R) {m : M} (hm : weight w d = m) : IsWeigh
tedHomogeneous w (monomial d r) m
· 使用引理 `MvPolynomial.IsWeightedHomogeneous.C_mul`：C_mul {w : σ -> M} (hφ : IsWei
ghtedHomogeneous w φ m) (r : R) : IsWeightedHomogeneous w (C r * φ) m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `AddSubsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Add M] (carrier 
carrier_1 : Set M) (e_carrier : carrier = carrier_1)   (add_mem' : ∀ {a b : M}, 
a ∈ carrier → b ∈ c…
· 使用定理 `AddSubmonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : AddZeroClass M] (to
AddSubsemigroup toAddSubsemigroup_1 : AddSubsemigroup M)   (e_toAddSubsemigroup 
: toAddSubsemigr…
· 使用定理 `Submodule.mk.congr_simp`：∀ {R : Type u} {M : Type v} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (toAddSubmonoid toAdd
Submonoid_1 :…
· 使用定理 `AddMonoidAlgebra.supported_eq_span_single`：∀ (R : Type u_1) {M : Type u_
3} [inst : Semiring R] (s : Set M),   AddMonoidAlgebra.supported R R s = Submodu
le.span R ((fun m => AddMonoidA…
· 使用定理 `MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported`：weighted
HomogeneousSubmodule_eq_finsupp_supported (w : σ -> M) (m : M) : weightedHomogen
eousSubmodule R w m = AddMonoidAlgebra.supported R R…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.mem_weightedHomogeneousSubmodule`：mem_weightedHomogeneousSu
bmodule (w : σ -> M) (m : M) (p : MvPolynomial σ R) : p in weightedHomogeneousSu
bmodule R w m ↔ p.IsWeightedHomogen…
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Induction principle for weighted homogeneous polynomials.
-/
lemma induction_on {w : σ → M} {m : M}
    {motive : (p : MvPolynomial σ R) → p.IsWeightedHomogeneous w m → Prop}
    (zero : motive 0 (isWeightedHomogeneous_zero R w m))
    (add : ∀ p q hp hq, motive p hp → motive q hq → motive (p + q) (hp.add hq))
    (monomial : ∀ (d : σ →₀ ℕ) (r : R) (hr : Finsupp.weight w d = m),
      motive ((monomial d) r) (isWeightedHomogeneous_monomial w d r hr))
    {p : MvPolynomial σ R} (hp : p.IsWeightedHomogeneous w m) :
    motive p hp := by
  suffices h : ∀ a, motive (C a * p) (.C_mul hp _) by simpa using h 1
  let A : Submodule R (MvPolynomial σ R) :=
    { carrier := { p | ∃ hp, ∀ a, motive (C a * p) (.C_mul hp _) }
      add_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ ↦
        ⟨.add ‹_› ‹_›, fun a ↦ by simp [mul_add, add _ _ _ _ (hx a) (hy a)]⟩
      zero_mem' := ⟨isWeightedHomogeneous_zero R w m, by simp [zero]⟩
      smul_mem' := fun a x ⟨_, hx⟩ ↦ ⟨by simp [Algebra.smul_def, C_mul ‹_› a], fun a ↦ by
        simp_rw [Algebra.smul_def, algebraMap_eq, ← mul_assoc, ← map_mul]
        apply hx⟩ }
  rw [← mem_weightedHomogeneousSubmodule, weightedHomogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single] at hp
  refine (Submodule.span_le (p := A) |>.mpr ?_ hp).2
  rw [Set.image_subset_iff]
  intro d hd
  simp only [MvPolynomial, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk,
    AddSubsemigroup.coe_set_mk, preimage_ofPred_eq, mem_ofPred_eq, A]
  refine ⟨isWeightedHomogeneous_monomial w d 1 hd, fun a ↦ ?_⟩
  simpa only [single_eq_monomial, ← MvPolynomial.C_mul_monomial] using monomial _ (a * 1) hd

end IsWeightedHomogeneous

variable {R}

/-- The weighted homogeneous submodules form a graded monoid. -/
/-
**MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid** 是 Mathlib 中的一个定理，位于命名
空间 `MvPolynomial.WeightedHomogeneousSubmodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} [in
st_1 : AddCommMonoid M] {w : σ → M},   SetLike.GradedMonoid (MvPolynomial.weight
edHomogeneousSubmodule R w)
参数：MvPolynomial.weightedHomogeneousSubmodule R w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.isWeightedHomogeneous_one`：isWeightedHomogeneous_one (w : σ
 -> M) : IsWeightedHomogeneous w (1 : MvPolynomial σ R) 0
· 使用定理 `MvPolynomial.IsWeightedHomogeneous.mul`：mul {w : σ -> M} (hφ : IsWeighte
dHomogeneous w φ m) (hψ : IsWeightedHomogeneous w ψ n) : IsWeightedHomogeneous w
 (φ * ψ) (m + n)

--- 原说明 ---
The weighted homogeneous submodules form a graded monoid.
-/
lemma WeightedHomogeneousSubmodule.gradedMonoid {w : σ → M} :
    SetLike.GradedMonoid (weightedHomogeneousSubmodule R w) where
  one_mem := isWeightedHomogeneous_one R w
  mul_mem _ _ _ _ := IsWeightedHomogeneous.mul

/-- `weightedHomogeneousComponent w n φ` is the part of `φ` that is weighted homogeneous of
  weighted degree `n`, with respect to the weights `w`.
  See `sum_weightedHomogeneousComponent` for the statement that `φ` is equal to the sum
  of all its weighted homogeneous components. -/
/-
**MvPolynomial.weightedHomogeneousComponent** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynom
ial`。
形式化陈述：weightedHomogeneousComponent (w : σ -> M) (n : M) : MvPolynomial σ R ->ₗ[R
] MvPolynomial σ R
参数：w : σ -> M；n : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`weightedHomogeneousComponent w n φ` is the part of `φ` that is weighted homogen
eous of
  weighted degree `n`, with respect to the weights `w`.
  See `sum_weightedHomogeneousComponent` for the statement that `φ` is equal to 
the sum
  of all its weighted homogeneous components.
-/
def weightedHomogeneousComponent (w : σ → M) (n : M) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  letI := Classical.decEq M
  (coeffLinearEquiv _).symm.toLinearMap ∘ₗ Submodule.subtype _ ∘ₗ
    Finsupp.restrictDom _ _ {d | weight w d = n} ∘ₗ (coeffLinearEquiv _).toLinearMap

section WeightedHomogeneousComponent

variable {w : σ → M} (n : M) (φ ψ : MvPolynomial σ R)

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.coeff_weightedHomogeneousComponent** 是 Mathlib 中的一个定理，位于命名空间 `MvP
olynomial`。
形式化陈述：coeff_weightedHomogeneousComponent [DecidableEq M] (d : σ ->₀ Nat) : coeff
 d (weightedHomogeneousComponent w n φ) = if weight w d = n then coeff d φ else 
0
参数：d : σ ->₀ Nat。
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
· 使用定理 `AddMonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2}
 {M : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Modul
e R S]   (a : AddMonoidAlgebr…
· 使用定理 `AddMonoidAlgebra.coeffLinearEquiv_symm_apply`：∀ (R : Type u_1) {S : Type
 u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.
Module R S]   (a : M →₀ S), (AddMo…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
theorem coeff_weightedHomogeneousComponent [DecidableEq M] (d : σ →₀ ℕ) :
    coeff d (weightedHomogeneousComponent w n φ) =
      if weight w d = n then coeff d φ else 0 := by
  simp [weightedHomogeneousComponent, MvPolynomial, coeff, Finsupp.filter_apply]

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.weightedHomogeneousComponent_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvP
olynomial`。
形式化陈述：weightedHomogeneousComponent_apply [DecidableEq M] : weightedHomogeneousCo
mponent w n φ = ∑ d in φ.support with weight w d = n, monomial d (coeff d φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddMonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2}
 {M : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Modul
e R S]   (a : AddMonoidAlgebr…
· 使用定理 `Finsupp.filter_eq_sum`：filter_eq_sum (p : α -> Prop) [DecidablePred p] (
f : α ->₀ M) : f.filter p = ∑ i in f.support.filter p, single i (f i)
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AddMonoidAlgebra.coeffLinearEquiv_symm_apply`：∀ (R : Type u_1) {S : Type
 u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.
Module R S]   (a : M →₀ S), (AddMo…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem weightedHomogeneousComponent_apply [DecidableEq M] :
    weightedHomogeneousComponent w n φ =
      ∑ d ∈ φ.support with weight w d = n, monomial d (coeff d φ) := by
  simp [weightedHomogeneousComponent, MvPolynomial, coeff, Finsupp.filter_eq_sum, support, monomial]
  congr

/-- The `n` weighted homogeneous component of a polynomial is weighted homogeneous of
weighted degree `n`. -/
/-
**MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous** 是 Mathlib 中的
一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：weightedHomogeneousComponent_isWeightedHomogeneous : (weightedHomogeneousC
omponent w n φ).IsWeightedHomogeneous w n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_weightedHomogeneousComponent`：coeff_weightedHomogeneo
usComponent [DecidableEq M] (d : σ ->₀ Nat) : coeff d (weightedHomogeneousCompon
ent w n φ) = if weight w d = n then c…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e

--- 原说明 ---
The `n` weighted homogeneous component of a polynomial is weighted homogeneous o
f
weighted degree `n`.
-/
theorem weightedHomogeneousComponent_isWeightedHomogeneous :
    (weightedHomogeneousComponent w n φ).IsWeightedHomogeneous w n := by
  classical
  intro d hd
  contrapose! hd
  rw [coeff_weightedHomogeneousComponent, if_neg hd]
/-
**MvPolynomial.weightedHomogeneousComponent_mem** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial`。
形式化陈述：weightedHomogeneousComponent_mem (w : σ -> M) (φ : MvPolynomial σ R) (m : 
M) : weightedHomogeneousComponent w m φ in weightedHomogeneousSubmodule R w m
参数：w : σ -> M；φ : MvPolynomial σ R；m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.mem_weightedHomogeneousSubmodule`：mem_weightedHomogeneousSu
bmodule (w : σ -> M) (m : M) (p : MvPolynomial σ R) : p in weightedHomogeneousSu
bmodule R w m ↔ p.IsWeightedHomogen…
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous`：weighte
dHomogeneousComponent_isWeightedHomogeneous : (weightedHomogeneousComponent w n 
φ).IsWeightedHomogeneous w n
-/
theorem weightedHomogeneousComponent_mem (w : σ → M) (φ : MvPolynomial σ R) (m : M) :
    weightedHomogeneousComponent w m φ ∈ weightedHomogeneousSubmodule R w m := by
  rw [mem_weightedHomogeneousSubmodule]
  exact weightedHomogeneousComponent_isWeightedHomogeneous m φ

@[simp]
/-
**MvPolynomial.weightedHomogeneousComponent_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvP
olynomial`。
形式化陈述：weightedHomogeneousComponent_C_mul (n : M) (r : R) : weightedHomogeneousCo
mponent w n (C r * φ) = C r * weightedHomogeneousComponent w n φ
参数：n : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.C_mul'`：C_mul' : MvPolynomial.C a * p = a • p
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedHomogeneousComponent_C_mul (n : M) (r : R) :
    weightedHomogeneousComponent w n (C r * φ) = C r * weightedHomogeneousComponent w n φ := by
  simp only [C_mul', map_smul]
/-
**MvPolynomial.weightedHomogeneousComponent_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `
MvPolynomial`。
形式化陈述：weightedHomogeneousComponent_eq_zero' (h : forall d : σ ->₀ Nat, d in φ.su
pport -> weight w d != n) : weightedHomogeneousComponent w n φ = 0
参数：h : forall d : σ ->₀ Nat, d in φ.support -> weight w d != n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_apply`：weightedHomogeneousComp
onent_apply [DecidableEq M] : weightedHomogeneousComponent w n φ = ∑ d in φ.supp
ort with weight w d = n, monomial d (…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem weightedHomogeneousComponent_eq_zero'
    (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → weight w d ≠ n) :
    weightedHomogeneousComponent w n φ = 0 := by
  classical
  rw [weightedHomogeneousComponent_apply, sum_eq_zero]
  intro d hd; rw [mem_filter] at hd
  exfalso; exact h _ hd.1 hd.2
/-
**MvPolynomial.weightedHomogeneousComponent_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `M
vPolynomial`。
形式化陈述：weightedHomogeneousComponent_eq_zero [SemilatticeSup M] [OrderBot M] (h : 
weightedTotalDegree w φ < n) : weightedHomogeneousComponent w n φ = 0
参数：h : weightedTotalDegree w φ < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_apply`：weightedHomogeneousComp
onent_apply [DecidableEq M] : weightedHomogeneousComponent w n φ = ∑ d in φ.supp
ort with weight w d = n, monomial d (…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MvPolynomial.le_weightedTotalDegree`：le_weightedTotalDegree (w : σ -> M)
 {φ : MvPolynomial σ R} {d : σ ->₀ Nat} (hd : d in φ.support) : weight w d <= φ.
weightedTotalDegree w
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem weightedHomogeneousComponent_eq_zero [SemilatticeSup M] [OrderBot M]
    (h : weightedTotalDegree w φ < n) : weightedHomogeneousComponent w n φ = 0 := by
  classical
  rw [weightedHomogeneousComponent_apply, sum_eq_zero]
  intro d hd
  rw [Finset.mem_filter] at hd
  exfalso
  apply lt_irrefl n
  nth_rw 1 [← hd.2]
  exact lt_of_le_of_lt (le_weightedTotalDegree w hd.1) h
/-
**MvPolynomial.weightedHomogeneousComponent_finsupp** 是 Mathlib 中的一个定理，位于命名空间 `M
vPolynomial`。
形式化陈述：weightedHomogeneousComponent_finsupp : (fun m => weightedHomogeneousCompon
ent w m φ).HasFiniteSupport
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_eq_zero'`：weightedHomogeneousC
omponent_eq_zero' (h : forall d : σ ->₀ Nat, d in φ.support -> weight w d != n) 
: weightedHomogeneousComponent w n φ = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem weightedHomogeneousComponent_finsupp :
    (fun m => weightedHomogeneousComponent w m φ).HasFiniteSupport := by
  apply ((fun d : σ →₀ ℕ => (weight w) d) '' (φ.support : Set (σ →₀ ℕ))).toFinite.subset
  intro m hm
  by_contra hm'
  apply hm (weightedHomogeneousComponent_eq_zero' m φ _)
  simpa only [Set.mem_image, not_exists, not_and] using! hm'

variable (w)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every polynomial is the sum of its weighted homogeneous components. -/
/-
**MvPolynomial.sum_weightedHomogeneousComponent** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial`。
形式化陈述：sum_weightedHomogeneousComponent : (finsum fun m => weightedHomogeneousCom
ponent w m φ) = φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_finsupp`：weightedHomogeneousCo
mponent_finsupp : (fun m => weightedHomogeneousComponent w m φ).HasFiniteSupport
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.coeff_sum`：coeff_sum {X : Type*} (s : Finset X) (f : X -> M
vPolynomial σ R) (m : σ ->₀ Nat) : coeff m (∑ x in s, f x) = ∑ x in s, coeff m (
f x)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.coeff_weightedHomogeneousComponent`：coeff_weightedHomogeneo
usComponent [DecidableEq M] (d : σ ->₀ Nat) : coeff d (weightedHomogeneousCompon
ent w n φ) = if weight w d = n then c…
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.coeff_zero`：coeff_zero (m : σ ->₀ Nat) : coeff m (0 : MvPol
ynomial σ R) = 0

--- 原说明 ---
Every polynomial is the sum of its weighted homogeneous components.
-/
theorem sum_weightedHomogeneousComponent :
    (finsum fun m => weightedHomogeneousComponent w m φ) = φ := by
  classical
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
  ext1 d
  simp only [coeff_sum, coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (weight w d)]
  · rw [if_pos rfl]
  · intro m _ hm'
    rw [if_neg hm'.symm]
  · intro hm
    rw [if_pos rfl]
    simp only [Finite.mem_toFinset, mem_support, Ne, Classical.not_not] at hm
    have := coeff_weightedHomogeneousComponent (w := w) (weight w d) φ d
    rw [hm, if_pos rfl, coeff_zero] at this
    exact this.symm
/-
**MvPolynomial.finsum_weightedHomogeneousComponent** 是 Mathlib 中的一个定理，位于命名空间 `Mv
Polynomial`。
形式化陈述：finsum_weightedHomogeneousComponent : (finsum fun m => weightedHomogeneous
Component w m φ) = φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.sum_weightedHomogeneousComponent`：sum_weightedHomogeneousCo
mponent : (finsum fun m => weightedHomogeneousComponent w m φ) = φ
-/
theorem finsum_weightedHomogeneousComponent :
    (finsum fun m => weightedHomogeneousComponent w m φ) = φ := by
  rw [sum_weightedHomogeneousComponent]

variable {w}
/-
**MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same** 是 Mathl
ib 中的一个定理，位于命名空间 `MvPolynomial.IsWeightedHomogeneous`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} [in
st_1 : AddCommMonoid M] {w : σ → M} {m : M}   {p : MvPolynomial σ R},   MvPolyno
mial.IsWeightedHomogeneous w p m → (MvPolynomial.weightedHomogeneousComponent w 
m) p = p
参数：MvPolynomial.weightedHomogeneousComponent w m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_weightedHomogeneousComponent`：coeff_weightedHomogeneo
usComponent [DecidableEq M] (d : σ ->₀ Nat) : coeff d (weightedHomogeneousCompon
ent w n φ) = if weight w d = n then c…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem IsWeightedHomogeneous.weightedHomogeneousComponent_same {m : M} {p : MvPolynomial σ R}
    (hp : IsWeightedHomogeneous w p m) :
    weightedHomogeneousComponent w m p = p := by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs
    · rfl
    rw [zero_coeff]
  · rw [hp zero_coeff, if_pos rfl]
/-
**MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne** 是 Mathlib
 中的一个定理，位于命名空间 `MvPolynomial.IsWeightedHomogeneous`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} [in
st_1 : AddCommMonoid M] {w : σ → M} {m : M}   (n : M) {p : MvPolynomial σ R},   
MvPolynomial.IsWeightedHomogeneous w p m → n ≠ m → (MvPolynomial.weightedHomogen
eousComponent w n) p = 0
参数：n : M；MvPolynomial.weightedHomogeneousComponent w n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_weightedHomogeneousComponent`：coeff_weightedHomogeneo
usComponent [DecidableEq M] (d : σ ->₀ Nat) : coeff d (weightedHomogeneousCompon
ent w n φ) = if weight w d = n then c…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MvPolynomial.coeff_zero`：coeff_zero (m : σ ->₀ Nat) : coeff m (0 : MvPol
ynomial σ R) = 0
-/
theorem IsWeightedHomogeneous.weightedHomogeneousComponent_ne {m : M} (n : M)
    {p : MvPolynomial σ R} (hp : IsWeightedHomogeneous w p m) :
    n ≠ m → weightedHomogeneousComponent w n p = 0 := by
  classical
  intro hn
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · simp [zero_coeff]
  · rw [if_neg]
    · rw [coeff_zero]
    · rw [hp zero_coeff]; exact Ne.symm hn

/-- The weighted homogeneous components of a weighted homogeneous polynomial. -/
/-
**MvPolynomial.weightedHomogeneousComponent_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Mv
Polynomial`。
形式化陈述：weightedHomogeneousComponent_of_mem [DecidableEq M] {m n : M} {p : MvPolyn
omial σ R} (h : p in weightedHomogeneousSubmodule R w n) : weightedHomogeneousCo
mponent w m p = if m = n then p else 0
参数：h : p in weightedHomogeneousSubmodule R w n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_weightedHomogeneousComponent`：coeff_weightedHomogeneo
usComponent [DecidableEq M] (d : σ ->₀ Nat) : coeff d (weightedHomogeneousCompon
ent w n φ) = if weight w d = n then c…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a

--- 原说明 ---
The weighted homogeneous components of a weighted homogeneous polynomial.
-/
theorem weightedHomogeneousComponent_of_mem [DecidableEq M] {m n : M}
    {p : MvPolynomial σ R} (h : p ∈ weightedHomogeneousSubmodule R w n) :
    weightedHomogeneousComponent w m p = if m = n then p else 0 := by
  simp only [mem_weightedHomogeneousSubmodule] at h
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs <;>
    simp only [zero_coeff, coeff_zero]
  · rw [h zero_coeff]
    simp only [show n = m ↔ m = n from eq_comm]
    split_ifs with h1
    · rfl
    · simp only [coeff_zero]
/-
**MvPolynomial.weightedHomogeneousComponent_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `M
vPolynomial`。
形式化陈述：weightedHomogeneousComponent_eq_self {n : M} {p : MvPolynomial σ R} (hp : 
p.IsWeightedHomogeneous w n) : weightedHomogeneousComponent w n p = p
参数：hp : p.IsWeightedHomogeneous w n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_of_mem`：weightedHomogeneousCom
ponent_of_mem [DecidableEq M] {m n : M} {p : MvPolynomial σ R} (h : p in weighte
dHomogeneousSubmodule R w n) : weighte…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weightedHomogeneousComponent_eq_self {n : M} {p : MvPolynomial σ R}
    (hp : p.IsWeightedHomogeneous w n) : weightedHomogeneousComponent w n p = p := by
  classical simp [weightedHomogeneousComponent_of_mem hp]
/-
**MvPolynomial.support_weightedHomogeneousComponent** 是 Mathlib 中的一个引理，位于命名空间 `M
vPolynomial`。
形式化陈述：support_weightedHomogeneousComponent [DecidableEq M] (n : M) (p : MvPolyno
mial σ R) : (weightedHomogeneousComponent w n p).support = {c in p.support | (we
ight w) c = n}
参数：n : M；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
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
· 使用定理 `MvPolynomial.coeff_weightedHomogeneousComponent`：coeff_weightedHomogeneo
usComponent [DecidableEq M] (d : σ ->₀ Nat) : coeff d (weightedHomogeneousCompon
ent w n φ) = if weight w d = n then c…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma support_weightedHomogeneousComponent [DecidableEq M] (n : M) (p : MvPolynomial σ R) :
    (weightedHomogeneousComponent w n p).support = {c ∈ p.support | (weight w) c = n} := by
  ext c
  simp [coeff_weightedHomogeneousComponent, And.comm]

variable (R w)

open DirectSum
/-
**MvPolynomial.DirectSum.coeLinearMap_eq_dfinsuppSum** 是 Mathlib 中的一个定理，位于命名空间 `
MvPolynomial.DirectSum`。
形式化陈述：∀ (R : Type u_1) {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} [in
st_1 : AddCommMonoid M] (w : σ → M)   [inst_2 : DecidableEq σ] [inst_3 : Decidab
leEq R] [inst_4 : DecidableEq M]   (x : DirectSum M fun i => ↥(MvPolynomial.weig
htedHomogeneousSubmodule R w i)),   (DirectSum.coeLinearMap fun i => MvPolynomia
l.weightedHomogeneousSubmodule R w i) x = DFinsupp.sum x fun x x_1 => ↑x_1
参数：R : Type u_1；w : σ → M；x : DirectSum M fun i => ↥(MvPolynomial.weightedHomoge
neousSubmodule R w i)；DirectSum.coeLinearMap fun i => MvPolynomial.weightedHomog
eneousSubmodule R w i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.coeLinearMap_eq_dfinsuppSum`：coeLinearMap_eq_dfinsuppSum [Deci
dableEq M] (x : DirectSum ι fun i => A i) : coeLinearMap A x = DFinsupp.sum x fu
n i => (fun x : A i => ↑x)
-/
theorem DirectSum.coeLinearMap_eq_dfinsuppSum [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x =
      DFinsupp.sum x (fun _ x => ↑x) := by
  rw [_root_.DirectSum.coeLinearMap_eq_dfinsuppSum]
/-
**MvPolynomial.DirectSum.coeAddMonoidHom_eq_support_sum** 是 Mathlib 中的一个定理，位于命名空
间 `MvPolynomial.DirectSum`。
形式化陈述：∀ (R : Type u_1) {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} [in
st_1 : AddCommMonoid M] (w : σ → M)   [inst_2 : DecidableEq σ] [inst_3 : Decidab
leEq R] [inst_4 : DecidableEq M]   (x : DirectSum M fun i => ↥(MvPolynomial.weig
htedHomogeneousSubmodule R w i)),   (DirectSum.coeAddMonoidHom fun i => MvPolyno
mial.weightedHomogeneousSubmodule R w i) x =     DFinsupp.sum x fun x x_1 => ↑x_
1
参数：R : Type u_1；w : σ → M；x : DirectSum M fun i => ↥(MvPolynomial.weightedHomoge
neousSubmodule R w i)；DirectSum.coeAddMonoidHom fun i => MvPolynomial.weightedHo
mogeneousSubmodule R w i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.DirectSum.coeLinearMap_eq_dfinsuppSum`：∀ (R : Type u_1) {M 
: Type u_2} [inst : CommSemiring R] {σ : Type u_3} [inst_1 : AddCommMonoid M] (w
 : σ → M)   [inst_2 : DecidableEq σ] [in…
-/
theorem DirectSum.coeAddMonoidHom_eq_support_sum [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeAddMonoidHom fun i : M => weightedHomogeneousSubmodule R w i) x =
      DFinsupp.sum x (fun _ x => ↑x) :=
  DirectSum.coeLinearMap_eq_dfinsuppSum R w x

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.DirectSum.coeLinearMap_eq_finsum** 是 Mathlib 中的一个定理，位于命名空间 `MvPol
ynomial.DirectSum`。
形式化陈述：∀ (R : Type u_1) {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} [in
st_1 : AddCommMonoid M] (w : σ → M)   [inst_2 : DecidableEq M] (x : DirectSum M 
fun i => ↥(MvPolynomial.weightedHomogeneousSubmodule R w i)),   (DirectSum.coeLi
nearMap fun i => MvPolynomial.weightedHomogeneousSubmodule R w i) x = ∑ᶠ (m : M)
, ↑(x m)
参数：R : Type u_1；w : σ → M；x : DirectSum M fun i => ↥(MvPolynomial.weightedHomoge
neousSubmodule R w i)；DirectSum.coeLinearMap fun i => MvPolynomial.weightedHomog
eneousSubmodule R w i；m : M；x m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.DirectSum.coeLinearMap_eq_dfinsuppSum`：∀ (R : Type u_1) {M 
: Type u_2} [inst : CommSemiring R] {σ : Type u_3} [inst_1 : AddCommMonoid M] (w
 : σ → M)   [inst_2 : DecidableEq σ] [in…
· 使用定理 `DFinsupp.sum.eq_1`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst : 
DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x : β i) →
 Decida…
· 使用定理 `finsum_eq_sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_5} [inst :
 AddCommMonoid M] (f : α → M) {s : Finset α},   Function.support f ⊆ ↑s → ∑ᶠ (i 
: α), f i = ∑ i ∈ s, …
· 使用定理 `DirectSum.support_subset`：support_subset [DecidableEq ι] [DecidableEq M]
 (A : ι -> S) (x : DirectSum ι fun i => A i) : (Function.support fun i => (x i :
 M)) subseteq …
-/
theorem DirectSum.coeLinearMap_eq_finsum [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x =
      finsum fun m => x m := by
  classical
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum, finsum_eq_sum_of_support_subset]
  apply DirectSum.support_subset

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.weightedHomogeneousComponent_directSum** 是 Mathlib 中的一个定理，位于命名空间 
`MvPolynomial`。
形式化陈述：weightedHomogeneousComponent_directSum [DecidableEq M] (x : DirectSum M fu
n i : M => ↥(weightedHomogeneousSubmodule R w i)) (m : M) : (weightedHomogeneous
Component w m) ((DirectSum.coeLinearMap fun i : M => weightedHomogeneousSubmodul
e R w i) x) = x m
参数：x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.DirectSum.coeLinearMap_eq_dfinsuppSum`：∀ (R : Type u_1) {M 
: Type u_2} [inst : CommSemiring R] {σ : Type u_3} [inst_1 : AddCommMonoid M] (w
 : σ → M)   [inst_2 : DecidableEq σ] [in…
· 使用定理 `DFinsupp.sum.eq_1`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst : 
DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x : β i) →
 Decida…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same`：∀ 
{R : Type u_1} {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} [inst_1 : A
ddCommMonoid M] {w : σ → M} {m : M}   {p : MvPolynomial σ …
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne`：∀ {R
 : Type u_1} {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} [inst_1 : Add
CommMonoid M] {w : σ → M} {m : M}   (n : M) {p : MvPolyn…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `DFinsupp.notMem_support_iff`：notMem_support_iff {f : Π₀ i, β i} {i : ι} 
: i ∉ f.support ↔ f i = 0
· 使用定理 `Submodule.coe_zero`：coe_zero : ((0 : p) : M) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
-/
theorem weightedHomogeneousComponent_directSum [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) (m : M) :
    (weightedHomogeneousComponent w m)
      ((DirectSum.coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x) = x m := by
  classical
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum, map_sum]
  convert! @Finset.sum_eq_single M (MvPolynomial σ R) _ (DFinsupp.support x) _ m _ _
  · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same (x m).prop]
  · intro n _ hmn
    exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne m (x n).prop hmn.symm
  · rw [DFinsupp.notMem_support_iff]
    intro hm; rw [hm, Submodule.coe_zero, map_zero]

end WeightedHomogeneousComponent

end AddCommMonoid

section OrderedAddCommMonoid

variable [AddCommMonoid M] [PartialOrder M]
  {w : σ → M} (φ : MvPolynomial σ R)

/-- If `M` is canonically ordered, then the `weightedHomogeneousComponent` of weighted degree `0`
of a polynomial is its constant coefficient. -/
@[simp]
/-
**MvPolynomial.weightedHomogeneousComponent_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
lynomial`。
形式化陈述：weightedHomogeneousComponent_zero [CanonicallyOrderedAdd M] [IsAddTorsionF
ree M] (hw : forall i : σ, w i != 0) : weightedHomogeneousComponent w 0 φ = C (c
oeff 0 φ)
参数：hw : forall i : σ, w i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_weightedHomogeneousComponent`：coeff_weightedHomogeneo
usComponent [DecidableEq M] (d : σ ->₀ Nat) : coeff d (weightedHomogeneousCompon
ent w n φ) = if weight w d = n then c…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MvPolynomial.coeff_zero_C`：coeff_zero_C (a) : coeff 0 (C a : MvPolynomia
l σ R) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
If `M` is canonically ordered, then the `weightedHomogeneousComponent` of weight
ed degree `0`
of a polynomial is its constant coefficient.
-/
theorem weightedHomogeneousComponent_zero [CanonicallyOrderedAdd M] [IsAddTorsionFree M]
    (hw : ∀ i : σ, w i ≠ 0) :
    weightedHomogeneousComponent w 0 φ = C (coeff 0 φ) := by
  classical
  ext1 d
  rcases Classical.em (d = 0) with (rfl | hd)
  · simp only [coeff_weightedHomogeneousComponent, if_pos, map_zero, coeff_zero_C]
  · rw [coeff_weightedHomogeneousComponent, if_neg, coeff_C, if_neg (Ne.symm hd)]
    simp only [weight, LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply, Finsupp.sum,
      sum_eq_zero_iff, Finsupp.mem_support_iff, Ne, smul_eq_zero, not_forall, not_or,
      and_self_left, exists_prop]
    simp only [DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply, not_forall] at hd
    obtain ⟨i, hi⟩ := hd
    exact ⟨i, hi, hw i⟩

/-- A weight function is nontorsion if its values are not torsion. -/
/-
**MvPolynomial.NonTorsionWeight** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：NonTorsionWeight (w : σ -> M)
参数：w : σ -> M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weight function is nontorsion if its values are not torsion.
-/
def NonTorsionWeight (w : σ → M) :=
  ∀ n x, n • w x = (0 : M) → n = 0

omit [PartialOrder M] in
/-
**MvPolynomial.nonTorsionWeight_of** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：nonTorsionWeight_of [IsAddTorsionFree M] (hw : forall i : σ, w i != 0) : N
onTorsionWeight w
参数：hw : forall i : σ, w i != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `smul_eq_zero_iff_left`：smul_eq_zero_iff_left (hm : m != 0) : r • m = 0 ↔
 r = 0
-/
theorem nonTorsionWeight_of [IsAddTorsionFree M] (hw : ∀ i : σ, w i ≠ 0) :
    NonTorsionWeight w :=
  fun _ x hnx => (smul_eq_zero_iff_left (hw x)).mp hnx

/-- If `w` is a nontorsion weight function, then the finitely supported function `m : σ →₀ ℕ`
  has weighted degree zero if and only if `∀ x : σ, m x = 0`. -/
/-
**MvPolynomial.weightedDegree_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：weightedDegree_eq_zero_iff [CanonicallyOrderedAdd M] (hw : NonTorsionWeigh
t w) {m : σ ->₀ Nat} : weight w m = 0 ↔ forall x : σ, m x = 0
参数：hw : NonTorsionWeight w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `Finset.sum_eq_zero_iff`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f : ι → M} [Subsingleton (AddUnits M)],   ∑ i ∈ s, f i 
= 0 ↔ ∀ i ∈ …
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
If `w` is a nontorsion weight function, then the finitely supported function `m 
: σ →₀ ℕ`
  has weighted degree zero if and only if `∀ x : σ, m x = 0`.
-/
theorem weightedDegree_eq_zero_iff [CanonicallyOrderedAdd M]
    (hw : NonTorsionWeight w) {m : σ →₀ ℕ} :
    weight w m = 0 ↔ ∀ x : σ, m x = 0 := by
  simp only [weight, Finsupp.linearCombination, LinearMap.toAddMonoidHom_coe, coe_lsum,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq]
  rw [Finsupp.sum, Finset.sum_eq_zero_iff]
  apply forall_congr'
  intro x
  rw [Finsupp.mem_support_iff]
  constructor
  · intro hx
    by_contra hx'
    exact absurd (hw _ _ (hx hx')) hx'
  · order

end OrderedAddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid M] [LinearOrder M] [OrderBot M] [CanonicallyOrderedAdd M]
  {w : σ → M} (φ : MvPolynomial σ R)

/-- A multivariate polynomial is weighted homogeneous of weighted degree zero if and only if
  its weighted total degree is equal to zero. -/
/-
**MvPolynomial.isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero** 是 Ma
thlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero {p : MvPolynomi
al σ R} : IsWeightedHomogeneous w p 0 ↔ p.weightedTotalDegree w = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.weightedTotalDegree.eq_1`：∀ {R : Type u_1} {M : Type u_2} [
inst : CommSemiring R] {σ : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : Sem
ilatticeSup M] [inst_3 : Or…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Finset.sup_eq_bot_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilatti
ceSup α] [inst_1 : OrderBot α] (f : β → α) (S : Finset β),   S.sup f = ⊥ ↔ ∀ s ∈
 S, f s = ⊥
· 使用定理 `MvPolynomial.IsWeightedHomogeneous.eq_1`：∀ {R : Type u_1} {M : Type u_2}
 [inst : CommSemiring R] {σ : Type u_3} [inst_1 : AddCommMonoid M] (w : σ → M)  
 (φ : MvPolynomial σ R) (m : …
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A multivariate polynomial is weighted homogeneous of weighted degree zero if and
 only if
  its weighted total degree is equal to zero.
-/
theorem isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero {p : MvPolynomial σ R} :
    IsWeightedHomogeneous w p 0 ↔ p.weightedTotalDegree w = 0 := by
  rw [weightedTotalDegree, ← bot_eq_zero, Finset.sup_eq_bot_iff, bot_eq_zero, IsWeightedHomogeneous]
  apply forall_congr'
  intro m
  rw [mem_support_iff]

/-- If `w` is a nontorsion weight function, then a multivariate polynomial has weighted total
  degree zero if and only if for every `m ∈ p.support` and `x : σ`, `m x = 0`. -/
/-
**MvPolynomial.weightedTotalDegree_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPoly
nomial`。
形式化陈述：weightedTotalDegree_eq_zero_iff (hw : NonTorsionWeight w) (p : MvPolynomia
l σ R) : p.weightedTotalDegree w = 0 ↔ forall (m : σ ->₀ Nat) (_ : m in p.suppor
t) (x : σ), m x = 0
参数：hw : NonTorsionWeight w；p : MvPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero`
：isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero {p : MvPolynomial σ 
R} : IsWeightedHomogeneous w p 0 ↔ p.weightedTotalDegree w = …
· 使用定理 `MvPolynomial.IsWeightedHomogeneous.eq_1`：∀ {R : Type u_1} {M : Type u_2}
 [inst : CommSemiring R] {σ : Type u_3} [inst_1 : AddCommMonoid M] (w : σ → M)  
 (φ : MvPolynomial σ R) (m : …
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `MvPolynomial.weightedDegree_eq_zero_iff`：weightedDegree_eq_zero_iff [Can
onicallyOrderedAdd M] (hw : NonTorsionWeight w) {m : σ ->₀ Nat} : weight w m = 0
 ↔ forall x : σ, m x = 0

--- 原说明 ---
If `w` is a nontorsion weight function, then a multivariate polynomial has weigh
ted total
  degree zero if and only if for every `m ∈ p.support` and `x : σ`, `m x = 0`.
-/
theorem weightedTotalDegree_eq_zero_iff (hw : NonTorsionWeight w) (p : MvPolynomial σ R) :
    p.weightedTotalDegree w = 0 ↔ ∀ (m : σ →₀ ℕ) (_ : m ∈ p.support) (x : σ), m x = 0 := by
  rw [← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero, IsWeightedHomogeneous]
  apply forall_congr'
  intro m
  rw [mem_support_iff]
  apply forall_congr'
  intro _
  exact weightedDegree_eq_zero_iff hw

end LinearOrderedAddCommMonoid

section GradedAlgebra

/- Here, given a weight `w : σ → M`, where `M` is an additive and commutative monoid, we endow the
  ring of multivariate polynomials `MvPolynomial σ R` with the structure of a graded algebra -/
variable (w : σ → M) [AddCommMonoid M]

/-
**MvPolynomial.weightedHomogeneousComponent_eq_zero_of_notMem** 是 Mathlib 中的一个定理
，位于命名空间 `MvPolynomial`。
形式化陈述：weightedHomogeneousComponent_eq_zero_of_notMem [DecidableEq M] (φ : MvPoly
nomial σ R) (i : M) (hi : i ∉ Finset.image (weight w) φ.support) : weightedHomog
eneousComponent w i φ = 0
参数：φ : MvPolynomial σ R；i : M；hi : i ∉ Finset.image (weight w) φ.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_eq_zero'`：weightedHomogeneousC
omponent_eq_zero' (h : forall d : σ ->₀ Nat, d in φ.support -> weight w d != n) 
: weightedHomogeneousComponent w n φ = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
-/
theorem weightedHomogeneousComponent_eq_zero_of_notMem [DecidableEq M]
    (φ : MvPolynomial σ R) (i : M) (hi : i ∉ Finset.image (weight w) φ.support) :
    weightedHomogeneousComponent w i φ = 0 := by
  apply weightedHomogeneousComponent_eq_zero'
  simp only [Finset.mem_image, mem_support_iff, ne_eq, not_exists, not_and] at hi
  exact fun m hm ↦ hi m (mem_support_iff.mp hm)

variable (R)

/-- The `decompose'` argument of `weightedDecomposition`. -/
/-
**MvPolynomial.decompose'** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：decompose' [DecidableEq M]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `decompose'` argument of `weightedDecomposition`.
-/
def decompose' [DecidableEq M] := fun φ : MvPolynomial σ R =>
  DirectSum.mk (fun i : M => ↥(weightedHomogeneousSubmodule R w i))
    (Finset.image (weight w) φ.support) fun m =>
      ⟨weightedHomogeneousComponent w m φ, weightedHomogeneousComponent_mem w φ m⟩
/-
**MvPolynomial.decompose'_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ (R : Type u_1) {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} (w 
: σ → M) [inst_1 : AddCommMonoid M]   [inst_2 : DecidableEq M] (φ : MvPolynomial
 σ R) (m : M),   ↑((MvPolynomial.decompose' R w φ) m) = (MvPolynomial.weightedHo
mogeneousComponent w m) φ
参数：R : Type u_1；w : σ → M；φ : MvPolynomial σ R；m : M；(MvPolynomial.decompose' R 
w φ) m；MvPolynomial.weightedHomogeneousComponent w m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.decompose'.eq_1`：∀ (R : Type u_1) {M : Type u_2} [inst : Co
mmSemiring R] {σ : Type u_3} (w : σ → M) [inst_1 : AddCommMonoid M]   [inst_2 : 
DecidableEq M] (φ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirectSum.mk_apply_of_mem`：mk_apply_of_mem {s : Finset ι} {f : forall i 
: (↑s : Set ι), β i.val} {n : ι} (hn : n in s) : mk β s f n = f ⟨n, hn⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DirectSum.mk_apply_of_notMem`：mk_apply_of_notMem {s : Finset ι} {f : for
all i : (↑s : Set ι), β i.val} {n : ι} (hn : n ∉ s) : mk β s f n = 0
· 使用定理 `Submodule.coe_zero`：coe_zero : ((0 : p) : M) = 0
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_eq_zero_of_notMem`：weightedHom
ogeneousComponent_eq_zero_of_notMem [DecidableEq M] (φ : MvPolynomial σ R) (i : 
M) (hi : i ∉ Finset.image (weight w) φ.support) :…
-/
theorem decompose'_apply [DecidableEq M] (φ : MvPolynomial σ R) (m : M) :
    (decompose' R w φ m : MvPolynomial σ R) = weightedHomogeneousComponent w m φ := by
  rw [decompose']
  by_cases hm : m ∈ Finset.image (weight w) φ.support
  · simp only [DirectSum.mk_apply_of_mem hm, Subtype.coe_mk]
  · rw [DirectSum.mk_apply_of_notMem hm, Submodule.coe_zero,
      weightedHomogeneousComponent_eq_zero_of_notMem w φ m hm]

set_option backward.isDefEq.respectTransparency false in
/-- Given a weight `w`, the decomposition of `MvPolynomial σ R` into weighted homogeneous
submodules -/
@[instance_reducible]
/-
**MvPolynomial.weightedDecomposition** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：weightedDecomposition [DecidableEq M] : DirectSum.Decomposition (weightedH
omogeneousSubmodule R w) where decompose'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a weight `w`, the decomposition of `MvPolynomial σ R` into weighted homoge
neous
submodules
-/
def weightedDecomposition [DecidableEq M] :
    DirectSum.Decomposition (weightedHomogeneousSubmodule R w) where
  decompose' := decompose' R w
  left_inv φ := by
    classical
    conv_rhs => rw [← sum_weightedHomogeneousComponent w φ]
    rw [← DirectSum.sum_support_of (decompose' R w φ)]
    simp only [DirectSum.coeAddMonoidHom_of, map_sum,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
    apply Finset.sum_congr _ (fun m _ ↦ by rw [decompose'_apply])
    ext m
    simp only [DFinsupp.mem_support_toFun, ne_eq, Set.Finite.mem_toFinset, Function.mem_support,
      not_iff_not]
    conv_lhs => rw [← Subtype.coe_inj]
    rw [decompose'_apply, Submodule.coe_zero]
  right_inv x := by
    apply DFinsupp.ext
    intro m
    rw [← Subtype.coe_inj, decompose'_apply]
    exact weightedHomogeneousComponent_directSum R w x m


set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Given a weight, `MvPolynomial` as a graded algebra -/
@[instance_reducible]
/-
**MvPolynomial.weightedGradedAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：weightedGradedAlgebra [DecidableEq M] : GradedAlgebra (weightedHomogeneous
Submodule R w) where toDecomposition
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid`：∀ {R : Type u_1}
 {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} [inst_1 : AddCommMonoid M
] {w : σ → M},   SetLike.GradedMonoid (MvPol…

--- 原说明 ---
Given a weight, `MvPolynomial` as a graded algebra
-/
def weightedGradedAlgebra [DecidableEq M] :
    GradedAlgebra (weightedHomogeneousSubmodule R w) where
  toDecomposition := weightedDecomposition R w
  toGradedMonoid  := WeightedHomogeneousSubmodule.gradedMonoid

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPolynomial.weightedDecomposition.decompose'_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mv
Polynomial.weightedDecomposition`。
形式化陈述：∀ (R : Type u_1) {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} (w 
: σ → M) [inst_1 : AddCommMonoid M]   [inst_2 : DecidableEq M],   DirectSum.Deco
mposition.decompose' = fun φ =>     (DirectSum.mk (fun i => ↥(MvPolynomial.weigh
tedHomogeneousSubmodule R w i))         (Finset.image (⇑(Finsupp.weight w)) φ.su
pport))       fun m => ⟨(MvPolynomial.weightedHomogeneousComponent w ↑m) φ, ⋯⟩
参数：R : Type u_1；w : σ → M；DirectSum.mk (fun i => ↥(MvPolynomial.weightedHomogene
ousSubmodule R w i))         (Finset.image (⇑(Finsupp.weight w)) φ.support)；MvPo
lynomial.weightedHomogeneousComponent w ↑m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weightedDecomposition.decompose'_eq [DecidableEq M] :
    (weightedDecomposition R w).decompose' = fun φ : MvPolynomial σ R =>
      DirectSum.mk (fun i : M => ↥(weightedHomogeneousSubmodule R w i))
        (Finset.image (weight w) φ.support) fun m =>
          ⟨weightedHomogeneousComponent w m φ, weightedHomogeneousComponent_mem w φ m⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPolynomial.weightedDecomposition.decompose'_apply** 是 Mathlib 中的一个定理，位于命名空间 
`MvPolynomial.weightedDecomposition`。
形式化陈述：∀ (R : Type u_1) {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} (w 
: σ → M) [inst_1 : AddCommMonoid M]   [inst_2 : DecidableEq M] (φ : MvPolynomial
 σ R) (m : M),   ↑((DirectSum.Decomposition.decompose' φ) m) = (MvPolynomial.wei
ghtedHomogeneousComponent w m) φ
参数：R : Type u_1；w : σ → M；φ : MvPolynomial σ R；m : M；(DirectSum.Decomposition.de
compose' φ) m；MvPolynomial.weightedHomogeneousComponent w m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.decompose'_apply`：∀ (R : Type u_1) {M : Type u_2} [inst : C
ommSemiring R] {σ : Type u_3} (w : σ → M) [inst_1 : AddCommMonoid M]   [inst_2 :
 DecidableEq M] (φ …
-/
theorem weightedDecomposition.decompose'_apply [DecidableEq M]
    (φ : MvPolynomial σ R) (m : M) :
    ((weightedDecomposition R w).decompose' φ m : MvPolynomial σ R) =
      weightedHomogeneousComponent w m φ :=
  MvPolynomial.decompose'_apply R w φ m

attribute [local instance] MvPolynomial.weightedGradedAlgebra
/-
**MvPolynomial.mem_iff_weightedHomogeneousComponent_mem** 是 Mathlib 中的一个引理，位于命名空
间 `MvPolynomial`。
形式化陈述：mem_iff_weightedHomogeneousComponent_mem [DecidableEq M] {I : Ideal (MvPol
ynomial σ R)} (h : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) (p : MvPo
lynomial σ R) : p in I ↔ forall m : M, (weightedHomogeneousComponent w m p) in I
参数：MvPolynomial σ R；h : I.IsHomogeneous (weightedHomogeneousSubmodule R w)；p : M
vPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ideal.IsHomogeneous.mem_iff`：Ideal.IsHomogeneous.mem_iff {I} (hI : Ideal
.IsHomogeneous 𝒜 I) {x} : x in I ↔ forall i, (decompose 𝒜 x i : A) in I
-/
lemma mem_iff_weightedHomogeneousComponent_mem [DecidableEq M] {I : Ideal (MvPolynomial σ R)}
    (h : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) (p : MvPolynomial σ R) :
    p ∈ I ↔ ∀ m : M, (weightedHomogeneousComponent w m p) ∈ I := by
  simp_rw [← weightedDecomposition.decompose'_apply]
  exact h.mem_iff
/-
**MvPolynomial.weightedHomogeneousComponent_mem_of_mem** 是 Mathlib 中的一个引理，位于命名空间
 `MvPolynomial`。
形式化陈述：weightedHomogeneousComponent_mem_of_mem [DecidableEq M] {I : Ideal (MvPoly
nomial σ R)} (h : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) {p : MvPol
ynomial σ R} (hp : p in I) (m : M) : (weightedHomogeneousComponent w m p) in I
参数：MvPolynomial σ R；h : I.IsHomogeneous (weightedHomogeneousSubmodule R w)；hp : 
p in I；m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MvPolynomial.mem_iff_weightedHomogeneousComponent_mem`：mem_iff_weightedH
omogeneousComponent_mem [DecidableEq M] {I : Ideal (MvPolynomial σ R)} (h : I.Is
Homogeneous (weightedHomogeneousSubmodule R…
-/
lemma weightedHomogeneousComponent_mem_of_mem [DecidableEq M] {I : Ideal (MvPolynomial σ R)}
    (h : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) {p : MvPolynomial σ R} (hp : p ∈ I)
    (m : M) : (weightedHomogeneousComponent w m p) ∈ I :=
  (mem_iff_weightedHomogeneousComponent_mem R w h p).mp hp m

end GradedAlgebra

end MvPolynomial

