/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
# Homogeneous polynomials

A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occurring in `φ` have degree `n`.

## Main definitions/lemmas

* `IsHomogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneousSubmodule σ R n`: the submodule of homogeneous polynomials of degree `n`.
* `homogeneousComponent n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneousComponent`: every polynomial is the sum of its homogeneous components.

## Library notes

* The `MvPolynomial.weightedGradedAlgebra` instance provides a `GradedAlgebra` structure, yielding
  the isomorphism `MvPolynomial σ R ≃ₐ[R] ⨁ m, weightedHomogeneousSubmodule R w m` for a weight
  function `w`.
* The special case with `w = 1` of the above yields the algebra isomorphism
  `MvPolynomial σ R ≃ₐ[R] ⨁ i, homogeneousSubmodule σ R i`.
-/

@[expose] public section


namespace MvPolynomial

variable {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

open Finsupp

/-- A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occurring in `φ` have degree `n`. -/
/-
**MvPolynomial.IsHomogeneous** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：IsHomogeneous [CommSemiring R] (φ : MvPolynomial σ R) (n : Nat)
参数：φ : MvPolynomial σ R；n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occurring in `φ` have degree `n`.
-/
def IsHomogeneous [CommSemiring R] (φ : MvPolynomial σ R) (n : ℕ) :=
  IsWeightedHomogeneous 1 φ n

variable [CommSemiring R]

/-- The `degrees` of a polynomial `p` is a special case of the `weightedTotalDegree` of `p` where
  the weights are singletons containing each variable. -/
@[simp]
/-
**MvPolynomial.weightedTotalDegree_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyno
mial`。
形式化陈述：weightedTotalDegree_singleton [DecidableEq σ] (p : MvPolynomial σ R) : wei
ghtedTotalDegree (fun i => {i}) p = degrees p
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.degrees_def`：degrees_def [DecidableEq σ] (p : MvPolynomial 
σ R) : p.degrees = p.support.sup fun s : σ ->₀ Nat => Finsupp.toMultiset s

--- 原说明 ---
The `degrees` of a polynomial `p` is a special case of the `weightedTotalDegree`
 of `p` where
  the weights are singletons containing each variable.
-/
theorem weightedTotalDegree_singleton [DecidableEq σ] (p : MvPolynomial σ R) :
    weightedTotalDegree (fun i => {i}) p = degrees p := by
  rw [degrees_def]; rfl

/-- The `totalDegree` of a polynomial `p` is a special case of the `weightedTotalDegree` of `p`
  where all of the weights are `1`. -/
/-
**MvPolynomial.weightedTotalDegree_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：weightedTotalDegree_one (φ : MvPolynomial σ R) : weightedTotalDegree (1 : 
σ -> Nat) φ = φ.totalDegree
参数：φ : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `totalDegree` of a polynomial `p` is a special case of the `weightedTotalDeg
ree` of `p`
  where all of the weights are `1`.
-/
theorem weightedTotalDegree_one (φ : MvPolynomial σ R) :
    weightedTotalDegree (1 : σ → ℕ) φ = φ.totalDegree := by
  simp only [totalDegree, weightedTotalDegree, weight, LinearMap.toAddMonoidHom_coe,
    linearCombination, Pi.one_apply, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
    id, smul_eq_mul, mul_one]

/-- The `degreeOf` a variable `i` for a polynomial `p` is a special case of the
  `weightedTotalDegree` of `p` where `i` has the only nonzero weight and that weight is `1`. -/
@[simp]
/-
**MvPolynomial.weightedTotalDegree_piSingle** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynom
ial`。
形式化陈述：weightedTotalDegree_piSingle [DecidableEq σ] (i : σ) (p : MvPolynomial σ R
) : weightedTotalDegree (Pi.single i 1) p = degreeOf i p
参数：i : σ；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.smulRight.congr_simp`：∀ {R : Type u_1} {S : Type u_3} {M : Typ
e u_4} {M₁ : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid M₁] …
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `Multiset.count_finset_sup`：count_finset_sup [DecidableEq β] (s : Finset 
α) (f : α -> Multiset β) (b : β) : count b (s.sup f) = s.sup fun a => count b (f
 a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finsupp.sum_ite_eq'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : DecidableEq α]   (f : α →₀ M) 
(a : α) (…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `Finsupp.count_toMultiset`：count_toMultiset [DecidableEq α] (f : α ->₀ Na
t) (a : α) : (toMultiset f).count a = f a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The `degreeOf` a variable `i` for a polynomial `p` is a special case of the
  `weightedTotalDegree` of `p` where `i` has the only nonzero weight and that we
ight is `1`.
-/
theorem weightedTotalDegree_piSingle [DecidableEq σ] (i : σ) (p : MvPolynomial σ R) :
    weightedTotalDegree (Pi.single i 1) p = degreeOf i p := by
  simp only [weightedTotalDegree, weight, linearCombination, Pi.single_apply, degreeOf, degrees,
    Multiset.count_finset_sup]
  congr; ext d
  simp +contextual
/-
**MvPolynomial.weightedTotalDegree_rename_of_injective** 是 Mathlib 中的一个定理，位于命名空间
 `MvPolynomial`。
形式化陈述：weightedTotalDegree_rename_of_injective {σ τ : Type*} {e : σ -> τ} {w : τ 
-> Nat} {P : MvPolynomial σ R} (he : Function.Injective e) : weightedTotalDegree
 w (rename e P) = weightedTotalDegree (w ∘ e) P
参数：he : Function.Injective e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.support_rename_of_injective`：support_rename_of_injective {p
 : MvPolynomial σ R} {f : σ -> τ} [DecidableEq τ] (h : Function.Injective f) : (
rename f p).support = Finset.i…
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.linearCombination_mapDomain`：linearCombination_mapDomain (f : α 
-> α') (l : α ->₀ R) : (linearCombination R v') (mapDomain f l) = (linearCombina
tion R (v' ∘ f)) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem weightedTotalDegree_rename_of_injective {σ τ : Type*} {e : σ → τ}
    {w : τ → ℕ} {P : MvPolynomial σ R} (he : Function.Injective e) :
    weightedTotalDegree w (rename e P) = weightedTotalDegree (w ∘ e) P := by
  classical
  unfold weightedTotalDegree
  rw [support_rename_of_injective he, Finset.sup_image]
  congr; ext; unfold weight; simp

variable (σ R)

/-- The submodule of homogeneous `MvPolynomial`s of degree `n`. -/
/-
**MvPolynomial.homogeneousSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：homogeneousSubmodule (n : Nat) : Submodule R (MvPolynomial σ R) where carr
ier
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of homogeneous `MvPolynomial`s of degree `n`.
-/
def homogeneousSubmodule (n : ℕ) : Submodule R (MvPolynomial σ R) where
  carrier := { x | x.IsHomogeneous n }
  __ := weightedHomogeneousSubmodule R 1 n

@[simp]
/-
**MvPolynomial.weightedHomogeneousSubmodule_one** 是 Mathlib 中的一个引理，位于命名空间 `MvPol
ynomial`。
形式化陈述：weightedHomogeneousSubmodule_one (n : Nat) : weightedHomogeneousSubmodule 
R 1 n = homogeneousSubmodule σ R n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weightedHomogeneousSubmodule_one (n : ℕ) :
    weightedHomogeneousSubmodule R 1 n = homogeneousSubmodule σ R n := rfl

variable {σ R}

@[simp]
/-
**MvPolynomial.mem_homogeneousSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：mem_homogeneousSubmodule (n : Nat) (p : MvPolynomial σ R) : p in homogeneo
usSubmodule σ R n ↔ p.IsHomogeneous n
参数：n : Nat；p : MvPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_homogeneousSubmodule (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ homogeneousSubmodule σ R n ↔ p.IsHomogeneous n := Iff.rfl

variable (σ R)

/-- While equal, the former has a convenient definitional reduction. -/
/-
**MvPolynomial.homogeneousSubmodule_eq_finsupp_supported** 是 Mathlib 中的一个定理，位于命名
空间 `MvPolynomial`。
形式化陈述：homogeneousSubmodule_eq_finsupp_supported (n : Nat) : homogeneousSubmodule
 σ R n = AddMonoidAlgebra.supported _ R {d | d.degree = n}
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported`：weighted
HomogeneousSubmodule_eq_finsupp_supported (w : σ -> M) (m : M) : weightedHomogen
eousSubmodule R w m = AddMonoidAlgebra.supported R R…

--- 原说明 ---
While equal, the former has a convenient definitional reduction.
-/
theorem homogeneousSubmodule_eq_finsupp_supported (n : ℕ) :
    homogeneousSubmodule σ R n = AddMonoidAlgebra.supported _ R {d | d.degree = n} := by
  simp_rw [degree_eq_weight_one]
  exact weightedHomogeneousSubmodule_eq_finsupp_supported R 1 n
/-
**MvPolynomial.homogeneousSubmodule_fg** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：homogeneousSubmodule_fg [Finite σ] (n : Nat) : (homogeneousSubmodule σ R n
).FG
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.weightedHomogeneousSubmodule_fg`：weightedHomogeneousSubmodu
le_fg [Finite σ] (w : σ -> Nat) (hw : forall (x : σ), w x != 0) (n : Nat) : (wei
ghtedHomogeneousSubmodule R w n).F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma homogeneousSubmodule_fg [Finite σ] (n : ℕ) :
    (homogeneousSubmodule σ R n).FG :=
  weightedHomogeneousSubmodule_fg R (1 : σ → ℕ) (by simp) n

variable {σ R}

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.homogeneousSubmodule_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：homogeneousSubmodule_mul (m n : Nat) : homogeneousSubmodule σ R m * homoge
neousSubmodule σ R n <= homogeneousSubmodule σ R (m + n)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.weightedHomogeneousSubmodule_mul`：weightedHomogeneousSubmod
ule_mul (w : σ -> M) (m n : M) : weightedHomogeneousSubmodule R w m * weightedHo
mogeneousSubmodule R w n <= weighte…
-/
theorem homogeneousSubmodule_mul (m n : ℕ) :
    homogeneousSubmodule σ R m * homogeneousSubmodule σ R n ≤ homogeneousSubmodule σ R (m + n) :=
  weightedHomogeneousSubmodule_mul 1 m n

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.homogeneousSubmodule_one_eq_span_X** 是 Mathlib 中的一个引理，位于命名空间 `MvP
olynomial`。
形式化陈述：homogeneousSubmodule_one_eq_span_X : MvPolynomial.homogeneousSubmodule σ R
 1 = .span R (.range X)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.homogeneousSubmodule_eq_finsupp_supported`：homogeneousSubmo
dule_eq_finsupp_supported (n : Nat) : homogeneousSubmodule σ R n = AddMonoidAlge
bra.supported _ R {d | d.degree = n}
· 使用定理 `AddMonoidAlgebra.supported_eq_span_single`：∀ (R : Type u_1) {M : Type u_
3} [inst : Semiring R] (s : Set M),   AddMonoidAlgebra.supported R R s = Submodu
le.span R ((fun m => AddMonoidA…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homogeneousSubmodule_one_eq_span_X :
    MvPolynomial.homogeneousSubmodule σ R 1 = .span R (.range X) := by
  simp [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single, MvPolynomial.single_eq_monomial,
    ← Finsupp.range_single_one, ← Set.range_comp, Function.comp_def, ← X_pow_eq_monomial]

section

/-
**MvPolynomial.isHomogeneous_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：isHomogeneous_monomial {d : σ ->₀ Nat} (r : R) {n : Nat} (hn : d.degree = 
n) : IsHomogeneous (monomial d r) n
参数：r : R；hn : d.degree = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.isWeightedHomogeneous_monomial`：isWeightedHomogeneous_monom
ial (w : σ -> M) (d : σ ->₀ Nat) (r : R) {m : M} (hm : weight w d = m) : IsWeigh
tedHomogeneous w (monomial d r) m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
-/
theorem isHomogeneous_monomial {d : σ →₀ ℕ} (r : R) {n : ℕ} (hn : d.degree = n) :
    IsHomogeneous (monomial d r) n := by
  rw [degree_eq_weight_one] at hn
  exact isWeightedHomogeneous_monomial 1 d r hn

variable (σ)
/-
**MvPolynomial.totalDegree_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：totalDegree_eq_zero_iff (p : MvPolynomial σ R) : p.totalDegree = 0 ↔ foral
l (m : σ ->₀ Nat) (_ : m in p.support) (x : σ), m x = 0
参数：p : MvPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.weightedTotalDegree_one`：weightedTotalDegree_one (φ : MvPol
ynomial σ R) : weightedTotalDegree (1 : σ -> Nat) φ = φ.totalDegree
· 使用定理 `MvPolynomial.weightedTotalDegree_eq_zero_iff`：weightedTotalDegree_eq_zer
o_iff (hw : NonTorsionWeight w) (p : MvPolynomial σ R) : p.weightedTotalDegree w
 = 0 ↔ forall (m : σ ->₀ Nat) (_ :…
· 使用定理 `MvPolynomial.nonTorsionWeight_of`：nonTorsionWeight_of [IsAddTorsionFree 
M] (hw : forall i : σ, w i != 0) : NonTorsionWeight w
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem totalDegree_eq_zero_iff (p : MvPolynomial σ R) :
    p.totalDegree = 0 ↔ ∀ (m : σ →₀ ℕ) (_ : m ∈ p.support) (x : σ), m x = 0 := by
  rw [← weightedTotalDegree_one, weightedTotalDegree_eq_zero_iff _ p]
  exact nonTorsionWeight_of (Function.const σ one_ne_zero)
/-
**MvPolynomial.totalDegree_zero_iff_isHomogeneous** 是 Mathlib 中的一个定理，位于命名空间 `MvP
olynomial`。
形式化陈述：totalDegree_zero_iff_isHomogeneous {p : MvPolynomial σ R} : p.totalDegree 
= 0 ↔ IsHomogeneous p 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.weightedTotalDegree_one`：weightedTotalDegree_one (φ : MvPol
ynomial σ R) : weightedTotalDegree (1 : σ -> Nat) φ = φ.totalDegree
· 使用定理 `MvPolynomial.isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero`
：isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero {p : MvPolynomial σ 
R} : IsWeightedHomogeneous w p 0 ↔ p.weightedTotalDegree w = …
· 使用定理 `MvPolynomial.IsHomogeneous.eq_1`：∀ {σ : Type u_1} {R : Type u_3} [inst :
 CommSemiring R] (φ : MvPolynomial σ R) (n : ℕ),   φ.IsHomogeneous n = MvPolynom
ial.IsWeightedHomogen…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem totalDegree_zero_iff_isHomogeneous {p : MvPolynomial σ R} :
    p.totalDegree = 0 ↔ IsHomogeneous p 0 := by
  rw [← weightedTotalDegree_one,
    ← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero, IsHomogeneous]

alias ⟨isHomogeneous_of_totalDegree_zero, _⟩ := totalDegree_zero_iff_isHomogeneous

@[simp]
/-
**MvPolynomial.homogeneousSubmodule_zero** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial
`。
形式化陈述：homogeneousSubmodule_zero : MvPolynomial.homogeneousSubmodule σ R 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.mem_homogeneousSubmodule`：mem_homogeneousSubmodule (n : Nat
) (p : MvPolynomial σ R) : p in homogeneousSubmodule σ R n ↔ p.IsHomogeneous n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.totalDegree_zero_iff_isHomogeneous`：totalDegree_zero_iff_is
Homogeneous {p : MvPolynomial σ R} : p.totalDegree = 0 ↔ IsHomogeneous p 0
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
· 使用定理 `MvPolynomial.algebraMap_eq`：algebraMap_eq : algebraMap R (MvPolynomial σ
 R) = C
· 使用定理 `MvPolynomial.totalDegree_eq_zero_iff_eq_C`：totalDegree_eq_zero_iff_eq_C 
{p : MvPolynomial σ R} : p.totalDegree = 0 ↔ p = C (p.coeff 0)
-/
lemma homogeneousSubmodule_zero :
    MvPolynomial.homogeneousSubmodule σ R 0 = 1 := by
  ext
  rw [MvPolynomial.mem_homogeneousSubmodule,
    ← MvPolynomial.totalDegree_zero_iff_isHomogeneous, Submodule.mem_one,
    MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_eq_zero_iff_eq_C]
  grind [coeff_zero_C]
/-
**MvPolynomial.isHomogeneous_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：isHomogeneous_C (r : R) : IsHomogeneous (C r : MvPolynomial σ R) 0
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.isHomogeneous_monomial`：isHomogeneous_monomial {d : σ ->₀ N
at} (r : R) {n : Nat} (hn : d.degree = n) : IsHomogeneous (monomial d r) n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.zero_apply`：zero_apply {a : α} : (0 : α ->₀ M) a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isHomogeneous_C (r : R) : IsHomogeneous (C r : MvPolynomial σ R) 0 := by
  apply isHomogeneous_monomial
  simp only [degree_apply, Finsupp.support_zero, zero_apply, Finset.sum_const_zero]

variable (R)
/-
**MvPolynomial.isHomogeneous_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：isHomogeneous_zero (n : Nat) : IsHomogeneous (0 : MvPolynomial σ R) n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
-/
theorem isHomogeneous_zero (n : ℕ) : IsHomogeneous (0 : MvPolynomial σ R) n :=
  (homogeneousSubmodule σ R n).zero_mem
/-
**MvPolynomial.isHomogeneous_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：isHomogeneous_one : IsHomogeneous (1 : MvPolynomial σ R) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.isHomogeneous_C`：isHomogeneous_C (r : R) : IsHomogeneous (C
 r : MvPolynomial σ R) 0
-/
theorem isHomogeneous_one : IsHomogeneous (1 : MvPolynomial σ R) 0 :=
  isHomogeneous_C _ _
/-
**MvPolynomial.isHomogeneous_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`
。
形式化陈述：isHomogeneous_of_isEmpty [IsEmpty σ] (f : MvPolynomial σ R) : f.IsHomogene
ous 0
参数：f : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.eq_C_of_isEmpty`：eq_C_of_isEmpty [IsEmpty σ] (p : MvPolynom
ial σ R) : p = C (p.coeff 0)
· 使用定理 `MvPolynomial.isHomogeneous_C`：isHomogeneous_C (r : R) : IsHomogeneous (C
 r : MvPolynomial σ R) 0
-/
lemma isHomogeneous_of_isEmpty [IsEmpty σ] (f : MvPolynomial σ R) : f.IsHomogeneous 0 := by
  rw [eq_C_of_isEmpty f]
  exact isHomogeneous_C _ _

variable {σ}
/-
**MvPolynomial.isHomogeneous_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：isHomogeneous_X (i : σ) : IsHomogeneous (X i : MvPolynomial σ R) 1
参数：i : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.isHomogeneous_monomial`：isHomogeneous_monomial {d : σ ->₀ N
at} (r : R) {n : Nat} (hn : d.degree = n) : IsHomogeneous (monomial d r) n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isHomogeneous_X (i : σ) : IsHomogeneous (X i : MvPolynomial σ R) 1 := by
  apply isHomogeneous_monomial
  simp only [degree_apply, Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
    single_eq_same]

variable {R} in
/-
**MvPolynomial.monomial_mem_homogeneousSubmodule_pow_degree** 是 Mathlib 中的一个引理，位
于命名空间 `MvPolynomial`。
形式化陈述：monomial_mem_homogeneousSubmodule_pow_degree (r : R) (s : σ ->₀ Nat) : mon
omial s r in (homogeneousSubmodule σ R 1) ^ s.degree
参数：r : R；s : σ ->₀ Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.induction`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass 
M] {motive : (ι →₀ M) → Prop} (f : ι →₀ M),   motive 0 →     (∀ (a : ι) (b : M) 
(f : ι …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `Finsupp.degree_single`：degree_single (a : σ) (r : R) : (Finsupp.single a
 r).degree = r
· 使用定理 `MvPolynomial.monomial_single_add`：monomial_single_add : monomial (Finsup
p.single n e + s) a = X n ^ e * monomial s a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `Submodule.pow_mem_pow`：pow_mem_pow {x : A} (hx : x in M) (n : Nat) : x ^
 n in M ^ n
· 使用定理 `MvPolynomial.isHomogeneous_X`：isHomogeneous_X (i : σ) : IsHomogeneous (X
 i : MvPolynomial σ R) 1
-/
lemma monomial_mem_homogeneousSubmodule_pow_degree
    (r : R) (s : σ →₀ ℕ) :
    monomial s r ∈ (homogeneousSubmodule σ R 1) ^ s.degree := by
  induction s using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ h =>
    rw [map_add, Finsupp.degree_single, monomial_single_add, pow_add]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (isHomogeneous_X R a) _) h

@[simp]
/-
**MvPolynomial.homogeneousSubmodule_one_pow** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynom
ial`。
形式化陈述：homogeneousSubmodule_one_pow (n : Nat) : (homogeneousSubmodule σ R 1) ^ n 
= homogeneousSubmodule σ R n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `MvPolynomial.homogeneousSubmodule_zero`：homogeneousSubmodule_zero : MvPo
lynomial.homogeneousSubmodule σ R 0 = 1
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Submodule.instMulLeftMono`：∀ {R : Type u} [inst : Semiring R] {A : Type 
v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower 
R A A], MulLeft…
· 使用定理 `Submodule.instMulRightMono`：∀ {R : Type u} [inst : Semiring R] {A : Type
 v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower
 R A A], MulRigh…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MvPolynomial.homogeneousSubmodule_mul`：homogeneousSubmodule_mul (m n : N
at) : homogeneousSubmodule σ R m * homogeneousSubmodule σ R n <= homogeneousSubm
odule σ R (m + n)
· 使用引理 `MvPolynomial.IsWeightedHomogeneous.induction_on`：induction_on {w : σ -> 
M} {m : M} {motive : (p : MvPolynomial σ R) -> p.IsWeightedHomogeneous w m -> Pr
op} (zero : motive 0 (isWeightedHomog…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用引理 `Pi.one_def`：one_def : (1 : forall i, M i) = fun _ => 1
· 使用引理 `MvPolynomial.monomial_mem_homogeneousSubmodule_pow_degree`：monomial_mem_
homogeneousSubmodule_pow_degree (r : R) (s : σ ->₀ Nat) : monomial s r in (homog
eneousSubmodule σ R 1) ^ s.degree
-/
lemma homogeneousSubmodule_one_pow (n : ℕ) :
    (homogeneousSubmodule σ R 1) ^ n = homogeneousSubmodule σ R n := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · induction n with
    | zero => simp [homogeneousSubmodule_zero]
    | succ n ih =>
      grw [pow_add, pow_one, ih]
      apply homogeneousSubmodule_mul
  · simp only [mem_homogeneousSubmodule] at hx
    induction hx using IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add p q _ _ hp hq => exact Submodule.add_mem _ hp hq
    | monomial d r hr =>
      convert! monomial_mem_homogeneousSubmodule_pow_degree _ _
      rw [Finsupp.degree_eq_weight_one, ← Pi.one_def, ← hr]

end

namespace IsHomogeneous

variable [CommSemiring S] {φ ψ : MvPolynomial σ R} {m n : ℕ}

/-
**MvPolynomial.IsHomogeneous.coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al.IsHomogeneous`。
形式化陈述：coeff_eq_zero (hφ : IsHomogeneous φ n) {d : σ ->₀ Nat} (hd : d.degree != n
) : coeff d φ = 0
参数：hφ : IsHomogeneous φ n；hd : d.degree != n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero`：coeff_eq_zero {w : σ -
> M} (hφ : IsWeightedHomogeneous w φ n) (d : σ ->₀ Nat) (hd : weight w d != n) :
 coeff d φ = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
-/
theorem coeff_eq_zero (hφ : IsHomogeneous φ n) {d : σ →₀ ℕ} (hd : d.degree ≠ n) :
    coeff d φ = 0 := by
  rw [degree_eq_weight_one] at hd
  exact IsWeightedHomogeneous.coeff_eq_zero hφ d hd
/-
**MvPolynomial.IsHomogeneous.inj_right** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.I
sHomogeneous`。
形式化陈述：inj_right (hm : IsHomogeneous φ m) (hn : IsHomogeneous φ n) (hφ : φ != 0) 
: m = n
参数：hm : IsHomogeneous φ m；hn : IsHomogeneous φ n；hφ : φ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.exists_coeff_ne_zero`：exists_coeff_ne_zero {p : MvPolynomia
l σ R} (h : p != 0) : exists d, coeff d p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inj_right (hm : IsHomogeneous φ m) (hn : IsHomogeneous φ n) (hφ : φ ≠ 0) : m = n := by
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ
  rw [← hm hd, ← hn hd]
/-
**MvPolynomial.IsHomogeneous.add** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsHomog
eneous`。
形式化陈述：add (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ +
 ψ) n
参数：hφ : IsHomogeneous φ n；hψ : IsHomogeneous ψ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
-/
theorem add (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ + ψ) n :=
  (homogeneousSubmodule σ R n).add_mem hφ hψ
/-
**MvPolynomial.IsHomogeneous.sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsHomog
eneous`。
形式化陈述：sum {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) (n : Nat) (h : 
forall i in s, IsHomogeneous (φ i) n) : IsHomogeneous (∑ i in s, φ i) n
参数：s : Finset ι；φ : ι -> MvPolynomial σ R；n : Nat；h : forall i in s, IsHomogeneo
us (φ i) n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
-/
theorem sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ℕ)
    (h : ∀ i ∈ s, IsHomogeneous (φ i) n) : IsHomogeneous (∑ i ∈ s, φ i) n :=
  (homogeneousSubmodule σ R n).sum_mem h

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.IsHomogeneous.mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsHomog
eneous`。
形式化陈述：mul (hφ : IsHomogeneous φ m) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ *
 ψ) (m + n)
参数：hφ : IsHomogeneous φ m；hψ : IsHomogeneous ψ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.homogeneousSubmodule_mul`：homogeneousSubmodule_mul (m n : N
at) : homogeneousSubmodule σ R m * homogeneousSubmodule σ R n <= homogeneousSubm
odule σ R (m + n)
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem mul (hφ : IsHomogeneous φ m) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ * ψ) (m + n) :=
  homogeneousSubmodule_mul m n <| Submodule.mul_mem_mul hφ hψ
/-
**MvPolynomial.IsHomogeneous.prod** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsHomo
geneous`。
形式化陈述：prod {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) (n : ι -> Nat)
 (h : forall i in s, IsHomogeneous (φ i) (n i)) : IsHomogeneous (∏ i in s, φ i) 
(∑ i in s, n i)
参数：s : Finset ι；φ : ι -> MvPolynomial σ R；n : ι -> Nat；h : forall i in s, IsHomo
geneous (φ i) (n i)。
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
· 使用定理 `MvPolynomial.IsHomogeneous.mul`：mul (hφ : IsHomogeneous φ m) (hψ : IsHom
ogeneous ψ n) : IsHomogeneous (φ * ψ) (m + n)
-/
theorem prod {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ι → ℕ)
    (h : ∀ i ∈ s, IsHomogeneous (φ i) (n i)) : IsHomogeneous (∏ i ∈ s, φ i) (∑ i ∈ s, n i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro
    simp only [isHomogeneous_one, Finset.sum_empty, Finset.prod_empty]
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (by grind)).mul (IH _)
    grind
/-
**MvPolynomial.IsHomogeneous.C_mul** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial.IsHom
ogeneous`。
形式化陈述：C_mul (hφ : φ.IsHomogeneous m) (r : R) : (C r * φ).IsHomogeneous m
参数：hφ : φ.IsHomogeneous m；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MvPolynomial.IsHomogeneous.mul`：mul (hφ : IsHomogeneous φ m) (hψ : IsHom
ogeneous ψ n) : IsHomogeneous (φ * ψ) (m + n)
· 使用定理 `MvPolynomial.isHomogeneous_C`：isHomogeneous_C (r : R) : IsHomogeneous (C
 r : MvPolynomial σ R) 0
-/
lemma C_mul (hφ : φ.IsHomogeneous m) (r : R) :
    (C r * φ).IsHomogeneous m := by
  simpa only [zero_add] using (isHomogeneous_C _ _).mul hφ
/-
**MvPolynomial.IsHomogeneous._root_.MvPolynomial.isHomogeneous_C_mul_X** 是 Mathl
ib 中的一个引理，位于命名空间 `MvPolynomial.IsHomogeneous`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MvPolynomial.isHomogeneous_C_mul_X (r : R) (i : σ) :
    (C r * X i).IsHomogeneous 1 :=
  (isHomogeneous_X _ _).C_mul _
/-
**MvPolynomial.IsHomogeneous.pow** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial.IsHomog
eneous`。
形式化陈述：pow (hφ : φ.IsHomogeneous m) (n : Nat) : (φ ^ n).IsHomogeneous (m * n)
参数：hφ : φ.IsHomogeneous m；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MvPolynomial.IsHomogeneous.prod`：prod {ι : Type*} (s : Finset ι) (φ : ι 
-> MvPolynomial σ R) (n : ι -> Nat) (h : forall i in s, IsHomogeneous (φ i) (n i
)) : IsHomogeneous (∏…
-/
lemma pow (hφ : φ.IsHomogeneous m) (n : ℕ) : (φ ^ n).IsHomogeneous (m * n) := by
  rw [show φ ^ n = ∏ _i ∈ Finset.range n, φ by simp]
  rw [show m * n = ∑ _i ∈ Finset.range n, m by simp [mul_comm]]
  apply IsHomogeneous.prod _ _ _ (fun _ _ ↦ hφ)
/-
**MvPolynomial.IsHomogeneous._root_.MvPolynomial.isHomogeneous_X_pow** 是 Mathlib
 中的一个引理，位于命名空间 `MvPolynomial.IsHomogeneous`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MvPolynomial.isHomogeneous_X_pow (i : σ) (n : ℕ) :
    (X (R := R) i ^ n).IsHomogeneous n := by
  simpa only [one_mul] using (isHomogeneous_X _ _).pow n
/-
**MvPolynomial.IsHomogeneous._root_.MvPolynomial.isHomogeneous_C_mul_X_pow** 是 M
athlib 中的一个引理，位于命名空间 `MvPolynomial.IsHomogeneous`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MvPolynomial.isHomogeneous_C_mul_X_pow (r : R) (i : σ) (n : ℕ) :
    (C r * X i ^ n).IsHomogeneous n :=
  (isHomogeneous_X_pow _ _).C_mul _
/-
**MvPolynomial.IsHomogeneous.eval** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial.IsHomo
geneous`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eval₂ (hφ : φ.IsHomogeneous m) (f : R →+* MvPolynomial τ S) (g : σ → MvPolynomial τ S)
    (hf : ∀ r, (f r).IsHomogeneous 0) (hg : ∀ i, (g i).IsHomogeneous n) :
    (eval₂ f g φ).IsHomogeneous (n * m) := by
  apply IsHomogeneous.sum
  intro i hi
  rw [← zero_add (n * m)]
  apply IsHomogeneous.mul (hf _) _
  convert! IsHomogeneous.prod _ _ (fun k ↦ n * i k) _
  · rw [Finsupp.mem_support_iff] at hi
    rw [← Finset.mul_sum, ← hφ hi, weight_apply]
    simp_rw [smul_eq_mul, Finsupp.sum, Pi.one_apply, mul_one]
  · rintro k -
    apply (hg k).pow
/-
**MvPolynomial.IsHomogeneous.map** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsHomog
eneous`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} {S : Type u_4} [inst : CommSemiring R] [in
st_1 : CommSemiring S] {φ : MvPolynomial σ R}   {n : ℕ}, φ.IsHomogeneous n → ∀ (
f : R →+* S), ((MvPolynomial.map f) φ).IsHomogeneous n
参数：f : R →+* S；(MvPolynomial.map f) φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.map_eq_eval₂Hom_C_comp`：map_eq_eval₂Hom_C_comp : map (σ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `MvPolynomial.IsHomogeneous.eval₂`：eval₂ (hφ : φ.IsHomogeneous m) (f : R 
->+* MvPolynomial τ S) (g : σ -> MvPolynomial τ S) (hf : forall r, (f r).IsHomog
eneous 0) (hg : forall…
· 使用定理 `MvPolynomial.isHomogeneous_C`：isHomogeneous_C (r : R) : IsHomogeneous (C
 r : MvPolynomial σ R) 0
· 使用定理 `MvPolynomial.isHomogeneous_X`：isHomogeneous_X (i : σ) : IsHomogeneous (X
 i : MvPolynomial σ R) 1
-/
protected lemma map (hφ : φ.IsHomogeneous n) (f : R →+* S) : (map f φ).IsHomogeneous n := by
  rw [map_eq_eval₂Hom_C_comp]
  simpa [one_mul] using hφ.eval₂ _ _ (fun r ↦ isHomogeneous_C _ (f r)) (isHomogeneous_X _)
/-
**MvPolynomial.IsHomogeneous.of_map** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial.IsHo
mogeneous`。
形式化陈述：of_map {f : R ->+* S} (hf : Function.Injective f) (h : (MvPolynomial.map f
 φ).IsHomogeneous n) : φ.IsHomogeneous n
参数：hf : Function.Injective f；h : (MvPolynomial.map f φ).IsHomogeneous n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.coeff_map`：coeff_map (p : MvPolynomial σ R) : forall m : σ 
->₀ Nat, coeff m (map f p) = f (coeff m p)
-/
lemma of_map {f : R →+* S} (hf : Function.Injective f)
    (h : (MvPolynomial.map f φ).IsHomogeneous n) : φ.IsHomogeneous n :=
  fun u hu ↦ h (coeff_map f φ u ▸ map_zero f ▸ hf.ne hu)
/-
**MvPolynomial.IsHomogeneous.aeval** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial.IsHom
ogeneous`。
形式化陈述：aeval [Algebra R S] (hφ : φ.IsHomogeneous m) (g : σ -> MvPolynomial τ S) (
hg : forall i, (g i).IsHomogeneous n) : (aeval g φ).IsHomogeneous (n * m)
参数：hφ : φ.IsHomogeneous m；g : σ -> MvPolynomial τ S；hg : forall i, (g i).IsHomog
eneous n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.IsHomogeneous.eval₂`：eval₂ (hφ : φ.IsHomogeneous m) (f : R 
->+* MvPolynomial τ S) (g : σ -> MvPolynomial τ S) (hf : forall r, (f r).IsHomog
eneous 0) (hg : forall…
· 使用定理 `MvPolynomial.isHomogeneous_C`：isHomogeneous_C (r : R) : IsHomogeneous (C
 r : MvPolynomial σ R) 0
-/
lemma aeval [Algebra R S] (hφ : φ.IsHomogeneous m)
    (g : σ → MvPolynomial τ S) (hg : ∀ i, (g i).IsHomogeneous n) :
    (aeval g φ).IsHomogeneous (n * m) :=
  hφ.eval₂ _ _ (fun _ ↦ isHomogeneous_C _ _) hg

section CommRing

-- In this section we shadow the semiring `R` with a ring `R`.
variable {R σ : Type*} [CommRing R] {φ ψ : MvPolynomial σ R} {n : ℕ}

/-
**MvPolynomial.IsHomogeneous.neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsHomog
eneous`。
形式化陈述：neg (hφ : IsHomogeneous φ n) : IsHomogeneous (-φ) n
参数：hφ : IsHomogeneous φ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
-/
theorem neg (hφ : IsHomogeneous φ n) : IsHomogeneous (-φ) n :=
  (homogeneousSubmodule σ R n).neg_mem hφ
/-
**MvPolynomial.IsHomogeneous.sub** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsHomog
eneous`。
形式化陈述：sub (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ -
 ψ) n
参数：hφ : IsHomogeneous φ n；hψ : IsHomogeneous ψ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
-/
theorem sub (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ - ψ) n :=
  (homogeneousSubmodule σ R n).sub_mem hφ hψ

end CommRing

/-- The homogeneous degree bounds the total degree.

See also `MvPolynomial.IsHomogeneous.totalDegree` when `φ` is non-zero. -/
/-
**MvPolynomial.IsHomogeneous.totalDegree_le** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynom
ial.IsHomogeneous`。
形式化陈述：totalDegree_le (hφ : IsHomogeneous φ n) : φ.totalDegree <= n
参数：hφ : IsHomogeneous φ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
The homogeneous degree bounds the total degree.

See also `MvPolynomial.IsHomogeneous.totalDegree` when `φ` is non-zero.
-/
lemma totalDegree_le (hφ : IsHomogeneous φ n) : φ.totalDegree ≤ n := by
  apply Finset.sup_le
  intro d hd
  rw [mem_support_iff] at hd
  simp_rw [Finsupp.sum, ← hφ hd, weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum,
    le_rfl]
/-
**MvPolynomial.IsHomogeneous.totalDegree** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
.IsHomogeneous`。
形式化陈述：totalDegree (hφ : IsHomogeneous φ n) (h : φ != 0) : totalDegree φ = n
参数：hφ : IsHomogeneous φ n；h : φ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `MvPolynomial.IsHomogeneous.totalDegree_le`：totalDegree_le (hφ : IsHomoge
neous φ n) : φ.totalDegree <= n
· 使用定理 `MvPolynomial.exists_coeff_ne_zero`：exists_coeff_ne_zero {p : MvPolynomia
l σ R} (h : p != 0) : exists d, coeff d p != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem totalDegree (hφ : IsHomogeneous φ n) (h : φ ≠ 0) : totalDegree φ = n := by
  apply le_antisymm hφ.totalDegree_le
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h
  simp only [← hφ hd, MvPolynomial.totalDegree, Finsupp.sum]
  replace hd := Finsupp.mem_support_iff.mpr hd
  simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
  -- Porting note: Original proof did not define `f`
  exact Finset.le_sup (f := fun s ↦ ∑ x ∈ s.support, s x) hd
/-
**MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support** 是 Mathlib 中的一个引理，位于命名空间
 `MvPolynomial.IsHomogeneous`。
形式化陈述：degree_eq_sum_deg_support (hφ : φ.IsHomogeneous n) {s : σ ->₀ Nat} (hs : s
 in φ.support) : n = ∑ i in s.support, s i
参数：hφ : φ.IsHomogeneous n；hs : s in φ.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma degree_eq_sum_deg_support (hφ : φ.IsHomogeneous n) {s : σ →₀ ℕ} (hs : s ∈ φ.support) :
    n = ∑ i ∈ s.support, s i := by
  simp [← hφ <| mem_support_iff.mp hs, ← degree_apply, degree_eq_weight_one, Pi.one_def]
/-
**MvPolynomial.IsHomogeneous.rename_isHomogeneous** 是 Mathlib 中的一个定理，位于命名空间 `MvP
olynomial.IsHomogeneous`。
形式化陈述：rename_isHomogeneous {f : σ -> τ} (h : φ.IsHomogeneous n) : (rename f φ).I
sHomogeneous n
参数：h : φ.IsHomogeneous n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.support_sum_monomial_coeff`：support_sum_monomial_coeff (p :
 MvPolynomial σ R) : ∑ v in p.support, monomial v (coeff v p) = p
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.rename_monomial`：rename_monomial (f : σ -> τ) (d : σ ->₀ Na
t) (r : R) : rename f (monomial d r) = monomial (d.mapDomain f) r
· 使用定理 `MvPolynomial.IsHomogeneous.sum`：sum {ι : Type*} (s : Finset ι) (φ : ι ->
 MvPolynomial σ R) (n : Nat) (h : forall i in s, IsHomogeneous (φ i) n) : IsHomo
geneous (∑ i in s, φ…
· 使用定理 `MvPolynomial.isHomogeneous_monomial`：isHomogeneous_monomial {d : σ ->₀ N
at} (r : R) {n : Nat} (hn : d.degree = n) : IsHomogeneous (monomial d r) n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.sum_mapDomain_index_addMonoidHom`：sum_mapDomain_index_addMonoidH
om [AddCommMonoid N] {f : α -> β} {s : α ->₀ M} (h : β -> M ->+ N) : ((mapDomain
 f s).sum fun b m => h b m) = …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddMonoidHom.id_apply`：∀ (M : Type u_10) [inst : AddZero M] (x : M), (Ad
dMonoidHom.id M) x = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
-/
theorem rename_isHomogeneous {f : σ → τ} (h : φ.IsHomogeneous n) :
    (rename f φ).IsHomogeneous n := by
  rw [← φ.support_sum_monomial_coeff, map_sum]; simp_rw [rename_monomial]
  apply IsHomogeneous.sum _ _ _ fun d hd ↦ isHomogeneous_monomial _ _
  intro d hd
  apply (Finsupp.sum_mapDomain_index_addMonoidHom fun _ ↦ .id ℕ).trans
  convert! h (mem_support_iff.mp hd)
  simp only [weight_apply, AddMonoidHom.id_apply, Pi.one_apply, smul_eq_mul, mul_one]
/-
**MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff** 是 Mathlib 中的一个定理，位于命名空间 
`MvPolynomial.IsHomogeneous`。
形式化陈述：rename_isHomogeneous_iff {f : σ -> τ} (hf : f.Injective) : (rename f φ).Is
Homogeneous n ↔ φ.IsHomogeneous n
参数：hf : f.Injective。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.sum_mapDomain_index_inj`：∀ {α : Type u_1} {β : Type u_2} {M : Ty
pe u_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f 
: α → β} {s : α →₀ M}…
· 使用定理 `MvPolynomial.coeff_rename_mapDomain`：coeff_rename_mapDomain (f : σ -> τ)
 (hf : Injective f) (φ : MvPolynomial σ R) (d : σ ->₀ Nat) : (rename f φ).coeff 
(d.mapDomain f) = φ.coeff…
· 使用定理 `MvPolynomial.IsHomogeneous.rename_isHomogeneous`：rename_isHomogeneous {f
 : σ -> τ} (h : φ.IsHomogeneous n) : (rename f φ).IsHomogeneous n
-/
theorem rename_isHomogeneous_iff {f : σ → τ} (hf : f.Injective) :
    (rename f φ).IsHomogeneous n ↔ φ.IsHomogeneous n := by
  refine ⟨fun h d hd ↦ ?_, rename_isHomogeneous⟩
  convert! ← @h (d.mapDomain f) _
  · simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact Finsupp.sum_mapDomain_index_inj (h := fun _ ↦ id) hf
  · rwa [coeff_rename_mapDomain f hf]
/-
**MvPolynomial.IsHomogeneous.finSuccEquiv_coeff_isHomogeneous** 是 Mathlib 中的一个引理
，位于命名空间 `MvPolynomial.IsHomogeneous`。
形式化陈述：finSuccEquiv_coeff_isHomogeneous {N : Nat} {φ : MvPolynomial (Fin (N + 1))
 R} {n : Nat} (hφ : φ.IsHomogeneous n) (i j : Nat) (h : i + j = n) : ((finSuccEq
uiv _ _ φ).coeff i).IsHomogeneous j
参数：Fin (N + 1)；hφ : φ.IsHomogeneous n；i j : Nat；h : i + j = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.finSuccEquiv_coeff_coeff`：finSuccEquiv_coeff_coeff (m : Fin
 n ->₀ Nat) (f : MvPolynomial (Fin (n + 1)) R) (i : Nat) : coeff m (Polynomial.c
oeff (finSuccEquiv R n f) i…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finsupp.sum_cons`：sum_cons [AddCommMonoid M] (n : Nat) (σ : Fin n ->₀ M)
 (i : M) : (sum (cons i σ) fun _ e => e) = i + sum σ (fun _ e => e)
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
lemma finSuccEquiv_coeff_isHomogeneous {N : ℕ} {φ : MvPolynomial (Fin (N + 1)) R} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (i j : ℕ) (h : i + j = n) :
    ((finSuccEquiv _ _ φ).coeff i).IsHomogeneous j := by
  intro d hd
  rw [finSuccEquiv_coeff_coeff] at hd
  have h' : (weight 1) (Finsupp.cons i d) = i + j := by
    simpa [Finset.sum_subset_zero_on_sdiff (g := d.cons i)
     (d.cons_support (y := i)) (by simp) (fun _ _ ↦ rfl), ← h] using hφ hd
  simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum_cons,
    add_right_inj] at h' ⊢
  exact h'

set_option backward.defeqAttrib.useBackward true in
-- TODO: develop API for `optionEquivLeft` and get rid of the `[Fintype σ]` assumption
/-
**MvPolynomial.IsHomogeneous.coeff_isHomogeneous_of_optionEquivLeft_symm** 是 Mat
hlib 中的一个引理，位于命名空间 `MvPolynomial.IsHomogeneous`。
形式化陈述：coeff_isHomogeneous_of_optionEquivLeft_symm [hσ : Finite σ] {p : Polynomia
l (MvPolynomial σ R)} (hp : ((optionEquivLeft R σ).symm p).IsHomogeneous n) (i j
 : Nat) (h : i + j = n) : (p.coeff i).IsHomogeneous j
参数：MvPolynomial σ R；hp : ((optionEquivLeft R σ).symm p).IsHomogeneous n；i j : Na
t；h : i + j = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MvPolynomial.IsHomogeneous.rename_isHomogeneous`：rename_isHomogeneous {f
 : σ -> τ} (h : φ.IsHomogeneous n) : (rename f φ).IsHomogeneous n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.finSuccEquiv_rename_finSuccEquiv`：finSuccEquiv_rename_finSu
ccEquiv (e : σ ≃ Fin n) (φ : MvPolynomial (Option σ) R) : ((finSuccEquiv R n) ((
rename ((Equiv.optionCongr e).trans…
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MvPolynomial.IsHomogeneous.finSuccEquiv_coeff_isHomogeneous`：finSuccEqui
v_coeff_isHomogeneous {N : Nat} {φ : MvPolynomial (Fin (N + 1)) R} {n : Nat} (hφ
 : φ.IsHomogeneous n) (i j : Nat) (h : i + j = n)…
· 使用定理 `MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff`：rename_isHomogeneou
s_iff {f : σ -> τ} (hf : f.Injective) : (rename f φ).IsHomogeneous n ↔ φ.IsHomog
eneous n
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma coeff_isHomogeneous_of_optionEquivLeft_symm
    [hσ : Finite σ] {p : Polynomial (MvPolynomial σ R)}
    (hp : ((optionEquivLeft R σ).symm p).IsHomogeneous n) (i j : ℕ) (h : i + j = n) :
    (p.coeff i).IsHomogeneous j := by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let e' := e.optionCongr.trans (_root_.finSuccEquiv _).symm
  let F := renameEquiv R e
  let F' := renameEquiv R e'
  let φ := F' ((optionEquivLeft R σ).symm p)
  have hφ : φ.IsHomogeneous n := hp.rename_isHomogeneous
  suffices IsHomogeneous (F (p.coeff i)) j by
    rwa [← (IsHomogeneous.rename_isHomogeneous_iff e.injective)]
  convert! hφ.finSuccEquiv_coeff_isHomogeneous i j h using 1
  dsimp only [φ, F', F, renameEquiv_apply]
  rw [finSuccEquiv_rename_finSuccEquiv, AlgEquiv.apply_symm_apply]
  simp

open Polynomial in
private
/-
**MvPolynomial.IsHomogeneous.exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_a
ux** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial.IsHomogeneous`。
形式化陈述：exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux {N : Nat} {F : MvPol
ynomial (Fin (Nat.succ N)) R} {n : Nat} (hF : IsHomogeneous F n) (hFn : ((finSuc
cEquiv R N) F).coeff n != 0) : exists r, eval r F != 0
参数：Fin (Nat.succ N)；hF : IsHomogeneous F n；hFn : ((finSuccEquiv R N) F).coeff n 
!= 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux
    {N : ℕ} {F : MvPolynomial (Fin (Nat.succ N)) R} {n : ℕ} (hF : IsHomogeneous F n)
    (hFn : ((finSuccEquiv R N) F).coeff n ≠ 0) :
    ∃ r, eval r F ≠ 0 := by
  have hF₀ : F ≠ 0 := by contrapose hFn; simp [hFn]
  have hdeg : natDegree (finSuccEquiv R N F) < n + 1 := by
    linarith [natDegree_finSuccEquiv F, degreeOf_le_totalDegree F 0, hF.totalDegree hF₀]
  use Fin.cons 1 0
  have aux : ∀ i ∈ Finset.range n, constantCoeff ((finSuccEquiv R N F).coeff i) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply (hF.finSuccEquiv_coeff_isHomogeneous i (n - i) (by lia)).coeff_eq_zero
    simp only [map_zero]
    rw [← Nat.sub_ne_zero_iff_lt] at hi
    exact hi.symm
  simp_rw [eval_eq_eval_mv_eval', eval_one_map, Polynomial.eval_eq_sum_range' hdeg,
    eval_zero, one_pow, mul_one, map_sum, Finset.sum_range_succ, Finset.sum_eq_zero aux, zero_add]
  contrapose hFn
  ext d
  rw [coeff_zero]
  obtain rfl | hd := eq_or_ne d 0
  · apply hFn
  · contrapose! hd
    ext i
    rw [Finsupp.coe_zero, Pi.zero_apply]
    by_cases hi : i ∈ d.support
    · have := hF.finSuccEquiv_coeff_isHomogeneous n 0 (add_zero _) hd
      simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum] at this
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ zero_le)] at this
      exact this i hi
    · simpa using hi

section IsDomain

-- In this section we shadow the semiring `R` with a domain `R`.
variable {R σ : Type*} [CommRing R] [IsDomain R] {F G : MvPolynomial σ R} {n : ℕ}

open Cardinal Polynomial

private
/-
**MvPolynomial.IsHomogeneous.exists_eval_ne_zero_of_totalDegree_le_card_aux** 是 
Mathlib 中的一个引理，位于命名空间 `MvPolynomial.IsHomogeneous`。
形式化陈述：exists_eval_ne_zero_of_totalDegree_le_card_aux {N : Nat} {F : MvPolynomial
 (Fin N) R} {n : Nat} (hF : F.IsHomogeneous n) (hF₀ : F != 0) (hnR : n <= #R) : 
exists r, eval r F != 0
参数：Fin N；hF : F.IsHomogeneous n；hF₀ : F != 0；hnR : n <= #R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_eval_ne_zero_of_totalDegree_le_card_aux {N : ℕ} {F : MvPolynomial (Fin N) R} {n : ℕ}
    (hF : F.IsHomogeneous n) (hF₀ : F ≠ 0) (hnR : n ≤ #R) :
    ∃ r, eval r F ≠ 0 := by
  induction N generalizing n with
  | zero =>
    use 0
    contrapose hF₀
    ext d
    simpa only [Subsingleton.elim d 0, eval_zero, coeff_zero] using! hF₀
  | succ N IH =>
    have hdeg : natDegree (finSuccEquiv R N F) < n + 1 := by
      linarith [natDegree_finSuccEquiv F, degreeOf_le_totalDegree F 0, hF.totalDegree hF₀]
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (finSuccEquiv R N F).coeff i ≠ 0 := by
      contrapose! hF₀
      exact (finSuccEquiv _ _).injective <| Polynomial.ext <| by simpa using! hF₀
    have hin : i ≤ n := by
      contrapose! hi
      exact coeff_eq_zero_of_natDegree_lt <| (Nat.le_of_lt_succ hdeg).trans_lt hi
    obtain hFn | hFn := ne_or_eq ((finSuccEquiv R N F).coeff n) 0
    · exact hF.exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux hFn
    have hin : i < n := hin.lt_or_eq.elim id <| by aesop
    obtain ⟨j, hj⟩ : ∃ j, i + (j + 1) = n := (Nat.exists_eq_add_of_lt hin).imp <| by lia
    obtain ⟨r, hr⟩ : ∃ r, (eval r) (Polynomial.coeff ((finSuccEquiv R N) F) i) ≠ 0 :=
      IH (hF.finSuccEquiv_coeff_isHomogeneous _ _ hj) hi (.trans (by norm_cast; lia) hnR)
    set φ : R[X] := Polynomial.map (eval r) (finSuccEquiv _ _ F) with hφ
    have hφ₀ : φ ≠ 0 := fun hφ₀ ↦ hr <| by
      rw [← coeff_eval_eq_eval_coeff, ← hφ, hφ₀, Polynomial.coeff_zero]
    have hφR : φ.natDegree < #R := by
      refine lt_of_lt_of_le ?_ hnR
      norm_cast
      refine lt_of_le_of_lt natDegree_map_le ?_
      suffices (finSuccEquiv _ _ F).natDegree ≠ n by lia
      rintro rfl
      refine leadingCoeff_ne_zero.mpr ?_ hFn
      simpa using! (finSuccEquiv R N).injective.ne hF₀
    obtain ⟨r₀, hr₀⟩ : ∃ r₀, Polynomial.eval r₀ φ ≠ 0 :=
      φ.exists_eval_ne_zero_of_natDegree_lt_card hφ₀ hφR
    use Fin.cons r₀ r
    rwa [eval_eq_eval_mv_eval']

/-- See `MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero`
for a version that assumes `Infinite R`. -/
/-
**MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_le_card** 是 Mathl
ib 中的一个引理，位于命名空间 `MvPolynomial.IsHomogeneous`。
形式化陈述：eq_zero_of_forall_eval_eq_zero_of_le_card (hF : F.IsHomogeneous n) (h : fo
rall r : σ -> R, eval r F = 0) (hnR : n <= #R) : F = 0
参数：hF : F.IsHomogeneous n；h : forall r : σ -> R, eval r F = 0；hnR : n <= #R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `MvPolynomial.exists_fin_rename`：exists_fin_rename (p : MvPolynomial σ R)
 : exists (n : Nat) (f : Fin n -> σ) (_hf : Injective f) (q : MvPolynomial (Fin 
n) R), p = rename f …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff`：rename_isHomogeneou
s_iff {f : σ -> τ} (hf : f.Injective) : (rename f φ).IsHomogeneous n ↔ φ.IsHomog
eneous n
· 使用定理 `_private.Mathlib.RingTheory.MvPolynomial.Homogeneous.0.MvPolynomial.IsHo
mogeneous.exists_eval_ne_zero_of_totalDegree_le_card_aux`：∀ {R : Type u_5} [inst
 : CommRing R] [IsDomain R] {N : ℕ} {F : MvPolynomial (Fin N) R} {n : ℕ},   F.Is
Homogeneous n → F ≠ 0 → ↑n ≤ Cardinal.…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Function.factorsThrough_iff`：factorsThrough_iff (g : α -> γ) [Nonempty γ
] : g.FactorsThrough f ↔ exists (e : β -> γ), g = e ∘ f
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Function.Injective.factorsThrough`：∀ {α : Sort u_1} {β : Sort u_2} {γ : 
Sort u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ), Function.FactorsT
hrough g f
· 使用定理 `MvPolynomial.eval_rename`：eval_rename (g : τ -> R) (p : MvPolynomial σ R
) : eval g (rename k p) = eval (g ∘ k) p

--- 原说明 ---
See `MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero`
for a version that assumes `Infinite R`.
-/
lemma eq_zero_of_forall_eval_eq_zero_of_le_card
    (hF : F.IsHomogeneous n) (h : ∀ r : σ → R, eval r F = 0) (hnR : n ≤ #R) :
    F = 0 := by
  contrapose! h
  -- reduce to the case where σ is finite
  obtain ⟨k, f, hf, F, rfl⟩ := exists_fin_rename F
  have hF₀ : F ≠ 0 := by rintro rfl; simp at h
  have hF : F.IsHomogeneous n := by rwa [rename_isHomogeneous_iff hf] at hF
  obtain ⟨r, hr⟩ := exists_eval_ne_zero_of_totalDegree_le_card_aux hF hF₀ hnR
  obtain ⟨r, rfl⟩ := (Function.factorsThrough_iff _).mp <| (hf.factorsThrough r)
  use r
  rwa [eval_rename]

/-- See `MvPolynomial.IsHomogeneous.funext`
for a version that assumes `Infinite R`. -/
/-
**MvPolynomial.IsHomogeneous.funext_of_le_card** 是 Mathlib 中的一个引理，位于命名空间 `MvPoly
nomial.IsHomogeneous`。
形式化陈述：funext_of_le_card (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n) (h : f
orall r : σ -> R, eval r F = eval r G) (hnR : n <= #R) : F = G
参数：hF : F.IsHomogeneous n；hG : G.IsHomogeneous n；h : forall r : σ -> R, eval r F
 = eval r G；hnR : n <= #R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_le_card`：eq
_zero_of_forall_eval_eq_zero_of_le_card (hF : F.IsHomogeneous n) (h : forall r :
 σ -> R, eval r F = 0) (hnR : n <= #R) : F = 0
· 使用定理 `MvPolynomial.IsHomogeneous.sub`：sub (hφ : IsHomogeneous φ n) (hψ : IsHom
ogeneous ψ n) : IsHomogeneous (φ - ψ) n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…

--- 原说明 ---
See `MvPolynomial.IsHomogeneous.funext`
for a version that assumes `Infinite R`.
-/
lemma funext_of_le_card (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n)
    (h : ∀ r : σ → R, eval r F = eval r G) (hnR : n ≤ #R) :
    F = G := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_eval_eq_zero_of_le_card (hF.sub hG) _ hnR
  simpa [sub_eq_zero] using h

/-- See `MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_le_card`
for a version that assumes `n ≤ #R`. -/
/-
**MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero** 是 Mathlib 中的一个引理，位
于命名空间 `MvPolynomial.IsHomogeneous`。
形式化陈述：eq_zero_of_forall_eval_eq_zero [Infinite R] {F : MvPolynomial σ R} {n : Na
t} (hF : F.IsHomogeneous n) (h : forall r : σ -> R, eval r F = 0) : F = 0
参数：hF : F.IsHomogeneous n；h : forall r : σ -> R, eval r F = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_le_card`：eq
_zero_of_forall_eval_eq_zero_of_le_card (hF : F.IsHomogeneous n) (h : forall r :
 σ -> R, eval r F = 0) (hnR : n <= #R) : F = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.infinite_iff`：infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ <= #α

--- 原说明 ---
See `MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_le_card`
for a version that assumes `n ≤ #R`.
-/
lemma eq_zero_of_forall_eval_eq_zero [Infinite R] {F : MvPolynomial σ R} {n : ℕ}
    (hF : F.IsHomogeneous n) (h : ∀ r : σ → R, eval r F = 0) : F = 0 := by
  apply eq_zero_of_forall_eval_eq_zero_of_le_card hF h
  exact Cardinal.natCast_le_aleph0.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

/-- See `MvPolynomial.IsHomogeneous.funext_of_le_card`
for a version that assumes `n ≤ #R`. -/
/-
**MvPolynomial.IsHomogeneous.funext** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial.IsHo
mogeneous`。
形式化陈述：funext [Infinite R] {F G : MvPolynomial σ R} {n : Nat} (hF : F.IsHomogeneo
us n) (hG : G.IsHomogeneous n) (h : forall r : σ -> R, eval r F = eval r G) : F 
= G
参数：hF : F.IsHomogeneous n；hG : G.IsHomogeneous n；h : forall r : σ -> R, eval r F
 = eval r G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.IsHomogeneous.funext_of_le_card`：funext_of_le_card (hF : F.
IsHomogeneous n) (hG : G.IsHomogeneous n) (h : forall r : σ -> R, eval r F = eva
l r G) (hnR : n <= #R) : F = G
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.infinite_iff`：infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ <= #α

--- 原说明 ---
See `MvPolynomial.IsHomogeneous.funext_of_le_card`
for a version that assumes `n ≤ #R`.
-/
lemma funext [Infinite R] {F G : MvPolynomial σ R} {n : ℕ}
    (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n)
    (h : ∀ r : σ → R, eval r F = eval r G) : F = G := by
  apply funext_of_le_card hF hG h
  exact Cardinal.natCast_le_aleph0.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end IsDomain

/-- The homogeneous submodules form a graded ring. This instance is used by `DirectSum.commSemiring`
and `DirectSum.algebra`. -/
/-
**MvPolynomial.IsHomogeneous.HomogeneousSubmodule.gcommSemiring** 是 Mathlib 中的一个
定理，位于命名空间 `MvPolynomial.IsHomogeneous.HomogeneousSubmodule`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} [inst : CommSemiring R], SetLike.GradedMon
oid (MvPolynomial.homogeneousSubmodule σ R)
参数：MvPolynomial.homogeneousSubmodule σ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.isHomogeneous_one`：isHomogeneous_one : IsHomogeneous (1 : M
vPolynomial σ R) 0
· 使用定理 `MvPolynomial.IsHomogeneous.mul`：mul (hφ : IsHomogeneous φ m) (hψ : IsHom
ogeneous ψ n) : IsHomogeneous (φ * ψ) (m + n)

--- 原说明 ---
The homogeneous submodules form a graded ring. This instance is used by `DirectS
um.commSemiring`
and `DirectSum.algebra`.
-/
instance HomogeneousSubmodule.gcommSemiring : SetLike.GradedMonoid (homogeneousSubmodule σ R) where
  one_mem := isHomogeneous_one σ R
  mul_mem _ _ _ _ := IsHomogeneous.mul

end IsHomogeneous

noncomputable section

open Finset

/-- `homogeneousComponent n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneousComponent` for the statement that `φ` is equal to the sum
of all its homogeneous components. -/
/-
**MvPolynomial.homogeneousComponent** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：homogeneousComponent (n : Nat) : MvPolynomial σ R ->ₗ[R] MvPolynomial σ R
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`homogeneousComponent n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneousComponent` for the statement that `φ` is equal to the sum
of all its homogeneous components.
-/
def homogeneousComponent (n : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  weightedHomogeneousComponent 1 n

section HomogeneousComponent

open Finset Finsupp

variable (n : ℕ) (φ ψ : MvPolynomial σ R)

/-
**MvPolynomial.homogeneousComponent_mem** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：homogeneousComponent_mem : homogeneousComponent n φ in homogeneousSubmodul
e σ R n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_mem`：weightedHomogeneousCompon
ent_mem (w : σ -> M) (φ : MvPolynomial σ R) (m : M) : weightedHomogeneousCompone
nt w m φ in weightedHomogeneousSubm…
-/
theorem homogeneousComponent_mem :
    homogeneousComponent n φ ∈ homogeneousSubmodule σ R n :=
  weightedHomogeneousComponent_mem _ φ n
/-
**MvPolynomial.coeff_homogeneousComponent** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：coeff_homogeneousComponent (d : σ ->₀ Nat) : coeff d (homogeneousComponent
 n φ) = if d.degree = n then coeff d φ else 0
参数：d : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `MvPolynomial.coeff_weightedHomogeneousComponent`：coeff_weightedHomogeneo
usComponent [DecidableEq M] (d : σ ->₀ Nat) : coeff d (weightedHomogeneousCompon
ent w n φ) = if weight w d = n then c…
-/
theorem coeff_homogeneousComponent (d : σ →₀ ℕ) :
    coeff d (homogeneousComponent n φ) = if d.degree = n then coeff d φ else 0 := by
  rw [degree_eq_weight_one]
  convert! coeff_weightedHomogeneousComponent n φ d
/-
**MvPolynomial.homogeneousComponent_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：homogeneousComponent_apply : homogeneousComponent n φ = ∑ d in φ.support w
ith d.degree = n, monomial d (coeff d φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_apply`：weightedHomogeneousComp
onent_apply [DecidableEq M] : weightedHomogeneousComponent w n φ = ∑ d in φ.supp
ort with weight w d = n, monomial d (…
-/
theorem homogeneousComponent_apply :
    homogeneousComponent n φ = ∑ d ∈ φ.support with d.degree = n, monomial d (coeff d φ) := by
  simp_rw [degree_eq_weight_one]
  convert! weightedHomogeneousComponent_apply n φ
/-
**MvPolynomial.homogeneousComponent_isHomogeneous** 是 Mathlib 中的一个定理，位于命名空间 `MvP
olynomial`。
形式化陈述：homogeneousComponent_isHomogeneous : (homogeneousComponent n φ).IsHomogene
ous n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous`：weighte
dHomogeneousComponent_isWeightedHomogeneous : (weightedHomogeneousComponent w n 
φ).IsWeightedHomogeneous w n
-/
theorem homogeneousComponent_isHomogeneous : (homogeneousComponent n φ).IsHomogeneous n :=
  weightedHomogeneousComponent_isWeightedHomogeneous n φ

@[simp]
/-
**MvPolynomial.homogeneousComponent_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：homogeneousComponent_zero : homogeneousComponent 0 φ = C (coeff 0 φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_zero`：weightedHomogeneousCompo
nent_zero [CanonicallyOrderedAdd M] [IsAddTorsionFree M] (hw : forall i : σ, w i
 != 0) : weightedHomogeneousComponen…
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
theorem homogeneousComponent_zero : homogeneousComponent 0 φ = C (coeff 0 φ) :=
  weightedHomogeneousComponent_zero φ (fun _ => Nat.succ_ne_zero Nat.zero)

@[simp]
/-
**MvPolynomial.homogeneousComponent_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：homogeneousComponent_C_mul (n : Nat) (r : R) : homogeneousComponent n (C r
 * φ) = C r * homogeneousComponent n φ
参数：n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_C_mul`：weightedHomogeneousComp
onent_C_mul (n : M) (r : R) : weightedHomogeneousComponent w n (C r * φ) = C r *
 weightedHomogeneousComponent w n φ
-/
theorem homogeneousComponent_C_mul (n : ℕ) (r : R) :
    homogeneousComponent n (C r * φ) = C r * homogeneousComponent n φ :=
  weightedHomogeneousComponent_C_mul φ n r
/-
**MvPolynomial.homogeneousComponent_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyno
mial`。
形式化陈述：homogeneousComponent_eq_zero' (h : forall d : σ ->₀ Nat, d in φ.support ->
 d.degree != n) : homogeneousComponent n φ = 0
参数：h : forall d : σ ->₀ Nat, d in φ.support -> d.degree != n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_eq_zero'`：weightedHomogeneousC
omponent_eq_zero' (h : forall d : σ ->₀ Nat, d in φ.support -> weight w d != n) 
: weightedHomogeneousComponent w n φ = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
-/
theorem homogeneousComponent_eq_zero'
    (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → d.degree ≠ n) :
    homogeneousComponent n φ = 0 := by
  simp_rw [degree_eq_weight_one] at h
  exact weightedHomogeneousComponent_eq_zero' n φ h
/-
**MvPolynomial.homogeneousComponent_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynom
ial`。
形式化陈述：homogeneousComponent_eq_zero (h : φ.totalDegree < n) : homogeneousComponen
t n φ = 0
参数：h : φ.totalDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.homogeneousComponent_eq_zero'`：homogeneousComponent_eq_zero
' (h : forall d : σ ->₀ Nat, d in φ.support -> d.degree != n) : homogeneousCompo
nent n φ = 0
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `MvPolynomial.totalDegree.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : Com
mSemiring R] (p : MvPolynomial σ R),   p.totalDegree = p.support.sup fun s => s.
sum fun x e => e
-/
theorem homogeneousComponent_eq_zero (h : φ.totalDegree < n) : homogeneousComponent n φ = 0 := by
  apply homogeneousComponent_eq_zero'
  rw [totalDegree, Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le _) h)] at h
  intro d hd; exact ne_of_lt (h d hd)
/-
**MvPolynomial.sum_homogeneousComponent** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：sum_homogeneousComponent : (∑ i in range (φ.totalDegree + 1), homogeneousC
omponent i φ) = φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.coeff_eq_zero_of_totalDegree_lt`：coeff_eq_zero_of_totalDegr
ee_lt {f : MvPolynomial σ R} {d : σ ->₀ Nat} (h : f.totalDegree < ∑ i in d.suppo
rt, d i) : coeff d f = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_sum`：coeff_sum {X : Type*} (s : Finset X) (f : X -> M
vPolynomial σ R) (m : σ ->₀ Nat) : coeff m (∑ x in s, f x) = ∑ x in s, coeff m (
f x)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.coeff_homogeneousComponent`：coeff_homogeneousComponent (d :
 σ ->₀ Nat) : coeff d (homogeneousComponent n φ) = if d.degree = n then coeff d 
φ else 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem sum_homogeneousComponent :
    (∑ i ∈ range (φ.totalDegree + 1), homogeneousComponent i φ) = φ := by
  ext1 d
  suffices φ.totalDegree < d.support.sum d → 0 = coeff d φ by
    simpa [coeff_sum, coeff_homogeneousComponent]
  exact fun h => (coeff_eq_zero_of_totalDegree_lt h).symm
/-
**MvPolynomial.homogeneousComponent_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：homogeneousComponent_of_mem {m n : Nat} {p : MvPolynomial σ R} (h : p in h
omogeneousSubmodule σ R n) : homogeneousComponent m p = if m = n then p else 0
参数：h : p in homogeneousSubmodule σ R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.weightedHomogeneousComponent_of_mem`：weightedHomogeneousCom
ponent_of_mem [DecidableEq M] {m n : M} {p : MvPolynomial σ R} (h : p in weighte
dHomogeneousSubmodule R w n) : weighte…
-/
theorem homogeneousComponent_of_mem {m n : ℕ} {p : MvPolynomial σ R}
    (h : p ∈ homogeneousSubmodule σ R n) :
    homogeneousComponent m p = if m = n then p else 0 :=
  weightedHomogeneousComponent_of_mem h
/-
**MvPolynomial.homogeneousComponent_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynom
ial`。
形式化陈述：homogeneousComponent_eq_self {n : Nat} {p : MvPolynomial σ R} (hp : p.IsHo
mogeneous n) : homogeneousComponent n p = p
参数：hp : p.IsHomogeneous n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.homogeneousComponent_of_mem`：homogeneousComponent_of_mem {m
 n : Nat} {p : MvPolynomial σ R} (h : p in homogeneousSubmodule σ R n) : homogen
eousComponent m p = if m = n t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homogeneousComponent_eq_self {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) : homogeneousComponent n p = p := by
  simp [homogeneousComponent_of_mem hp]
/-
**MvPolynomial.support_homogeneousComponent** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynom
ial`。
形式化陈述：support_homogeneousComponent (n : Nat) (p : MvPolynomial σ R) : (homogeneo
usComponent n p).support = {c in p.support | c.degree = n}
参数：n : Nat；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用引理 `MvPolynomial.support_weightedHomogeneousComponent`：support_weightedHomog
eneousComponent [DecidableEq M] (n : M) (p : MvPolynomial σ R) : (weightedHomoge
neousComponent w n p).support = {c in p…
-/
lemma support_homogeneousComponent (n : ℕ) (p : MvPolynomial σ R) :
    (homogeneousComponent n p).support = {c ∈ p.support | c.degree = n} := by
  rw [degree_eq_weight_one]
  exact support_weightedHomogeneousComponent n p
/-
**MvPolynomial.rename_homogeneousComponent** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomi
al`。
形式化陈述：rename_homogeneousComponent {τ : Type*} {φ : σ -> τ} (n : Nat) (p : MvPoly
nomial σ R) : rename φ (homogeneousComponent n p) = homogeneousComponent n (rena
me φ p)
参数：n : Nat；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on'`：induction_on' {P : MvPolynomial σ R -> Prop}
 (p : MvPolynomial σ R) (monomial : forall (u : σ ->₀ Nat) (a : R), P (monomial 
u a)) (add : for…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_monomial`：rename_monomial (f : σ -> τ) (d : σ ->₀ Na
t) (r : R) : rename f (monomial d r) = monomial (d.mapDomain f) r
· 使用定理 `MvPolynomial.homogeneousComponent_of_mem`：homogeneousComponent_of_mem {m
 n : Nat} {p : MvPolynomial σ R} (h : p in homogeneousSubmodule σ R n) : homogen
eousComponent m p = if m = n t…
· 使用定理 `MvPolynomial.isHomogeneous_monomial`：isHomogeneous_monomial {d : σ ->₀ N
at} (r : R) {n : Nat} (hn : d.degree = n) : IsHomogeneous (monomial d r) n
· 使用定理 `Finsupp.degree_mapDomain`：degree_mapDomain {τ : Type*} (f : σ -> τ) [Add
CommMonoid M] (x : σ ->₀ M) : degree (x.mapDomain f) = degree x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
lemma rename_homogeneousComponent {τ : Type*} {φ : σ → τ} (n : ℕ) (p : MvPolynomial σ R) :
    rename φ (homogeneousComponent n p) = homogeneousComponent n (rename φ p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [rename_monomial,
      homogeneousComponent_of_mem (isHomogeneous_monomial c rfl),
      homogeneousComponent_of_mem (isHomogeneous_monomial c (Finsupp.degree_mapDomain φ d))]
    split_ifs <;> simp [rename_monomial]
  | add p q hp hq => simp [map_add, hp, hq]


end HomogeneousComponent

end

noncomputable section GradedAlgebra

/-- The homogeneous submodules form a graded ring.
This instance is used by `DirectSum.commSemiring` and `DirectSum.algebra`. -/
/-
**MvPolynomial.HomogeneousSubmodule.gradedMonoid** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
lynomial.HomogeneousSubmodule`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} [inst : CommSemiring R], SetLike.GradedMon
oid (MvPolynomial.homogeneousSubmodule σ R)
参数：MvPolynomial.homogeneousSubmodule σ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid`：∀ {R : Type u_1}
 {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} [inst_1 : AddCommMonoid M
] {w : σ → M},   SetLike.GradedMonoid (MvPol…

--- 原说明 ---
The homogeneous submodules form a graded ring.
This instance is used by `DirectSum.commSemiring` and `DirectSum.algebra`.
-/
lemma HomogeneousSubmodule.gradedMonoid :
    SetLike.GradedMonoid (homogeneousSubmodule σ R) :=
  WeightedHomogeneousSubmodule.gradedMonoid

/-- The decomposition of `MvPolynomial σ R` into homogeneous submodules. -/
/-
**MvPolynomial.decomposition** 是 Mathlib 中的一个缩写定义，位于命名空间 `MvPolynomial`。
形式化陈述：decomposition : DirectSum.Decomposition (homogeneousSubmodule σ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The decomposition of `MvPolynomial σ R` into homogeneous submodules.
-/
abbrev decomposition :
    DirectSum.Decomposition (homogeneousSubmodule σ R) :=
  fast_instance% weightedDecomposition R (1 : σ → ℕ)

/-- `MvPolynomial σ R` as a graded algebra, graded by the degree.
We do not make this a global instance because one may want to consider a different
graded algebra structure on `MvPolynomial σ R`, induced by another weight function.
To make it a local instance, you may use
`attribute [local instance] MvPolynomial.gradedAlgebra`.
-/
/-
**MvPolynomial.gradedAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 `MvPolynomial`。
形式化陈述：gradedAlgebra : GradedAlgebra (homogeneousSubmodule σ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MvPolynomial σ R` as a graded algebra, graded by the degree.
We do not make this a global instance because one may want to consider a differe
nt
graded algebra structure on `MvPolynomial σ R`, induced by another weight functi
on.
To make it a local instance, you may use
`attribute [local instance] MvPolynomial.gradedAlgebra`.
-/
abbrev gradedAlgebra : GradedAlgebra (homogeneousSubmodule σ R) :=
  fast_instance% weightedGradedAlgebra R (1 : σ → ℕ)
/-
**MvPolynomial.decomposition.decompose'_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyn
omial.decomposition`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} [inst : CommSemiring R] (φ : MvPolynomial 
σ R) (i : ℕ),   ↑((DirectSum.Decomposition.decompose' φ) i) = (MvPolynomial.homo
geneousComponent i) φ
参数：φ : MvPolynomial σ R；i : ℕ；(DirectSum.Decomposition.decompose' φ) i；MvPolynom
ial.homogeneousComponent i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.weightedDecomposition.decompose'_apply`：∀ (R : Type u_1) {M
 : Type u_2} [inst : CommSemiring R] {σ : Type u_3} (w : σ → M) [inst_1 : AddCom
mMonoid M]   [inst_2 : DecidableEq M] (φ …
-/
theorem decomposition.decompose'_apply (φ : MvPolynomial σ R) (i : ℕ) :
    (decomposition.decompose' φ i : MvPolynomial σ R) = homogeneousComponent i φ :=
  weightedDecomposition.decompose'_apply R _ φ i
/-
**MvPolynomial.decomposition.decompose'_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al.decomposition`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} [inst : CommSemiring R],   DirectSum.Decom
position.decompose' = fun φ =>     (DirectSum.mk (fun i => ↥(MvPolynomial.homoge
neousSubmodule σ R i)) (Finset.image (⇑Finsupp.degree) φ.support))       fun m =
> ⟨(MvPolynomial.homogeneousComponent ↑m) φ, ⋯⟩
参数：DirectSum.mk (fun i => ↥(MvPolynomial.homogeneousSubmodule σ R i)) (Finset.im
age (⇑Finsupp.degree) φ.support)；MvPolynomial.homogeneousComponent ↑m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.homogeneousComponent_mem`：homogeneousComponent_mem : homoge
neousComponent n φ in homogeneousSubmodule σ R n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
-/
theorem decomposition.decompose'_eq :
    decomposition.decompose' = fun φ : MvPolynomial σ R =>
      DirectSum.mk (fun i : ℕ => ↥(homogeneousSubmodule σ R i)) (φ.support.image Finsupp.degree)
        fun m => ⟨homogeneousComponent m φ, homogeneousComponent_mem m φ⟩ := by
  rw [degree_eq_weight_one]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra
/-
**MvPolynomial.mem_iff_homogeneousComponent_mem** 是 Mathlib 中的一个引理，位于命名空间 `MvPol
ynomial`。
形式化陈述：mem_iff_homogeneousComponent_mem {I : Ideal (MvPolynomial σ R)} (h : I.IsH
omogeneous (homogeneousSubmodule σ R)) (p : MvPolynomial σ R) : p in I ↔ forall 
n, (homogeneousComponent n p) in I
参数：MvPolynomial σ R；h : I.IsHomogeneous (homogeneousSubmodule σ R)；p : MvPolynom
ial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.mem_iff_weightedHomogeneousComponent_mem`：mem_iff_weightedH
omogeneousComponent_mem [DecidableEq M] {I : Ideal (MvPolynomial σ R)} (h : I.Is
Homogeneous (weightedHomogeneousSubmodule R…
-/
lemma mem_iff_homogeneousComponent_mem {I : Ideal (MvPolynomial σ R)}
    (h : I.IsHomogeneous (homogeneousSubmodule σ R)) (p : MvPolynomial σ R) :
    p ∈ I ↔ ∀ n, (homogeneousComponent n p) ∈ I :=
  mem_iff_weightedHomogeneousComponent_mem R (1 : σ → ℕ) h p
/-
**MvPolynomial.homogeneousComponent_mem_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `MvPoly
nomial`。
形式化陈述：homogeneousComponent_mem_of_mem {I : Ideal (MvPolynomial σ R)} (h : I.IsHo
mogeneous (homogeneousSubmodule σ R)) {p : MvPolynomial σ R} (hp : p in I) (n : 
Nat) : (homogeneousComponent n p) in I
参数：MvPolynomial σ R；h : I.IsHomogeneous (homogeneousSubmodule σ R)；hp : p in I；n
 : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.weightedHomogeneousComponent_mem_of_mem`：weightedHomogeneou
sComponent_mem_of_mem [DecidableEq M] {I : Ideal (MvPolynomial σ R)} (h : I.IsHo
mogeneous (weightedHomogeneousSubmodule R …
-/
lemma homogeneousComponent_mem_of_mem {I : Ideal (MvPolynomial σ R)}
    (h : I.IsHomogeneous (homogeneousSubmodule σ R)) {p : MvPolynomial σ R} (hp : p ∈ I) (n : ℕ) :
    (homogeneousComponent n p) ∈ I :=
  weightedHomogeneousComponent_mem_of_mem R (1 : σ → ℕ) h hp n

end GradedAlgebra

end MvPolynomial

/-- Try to use the universal property of the span (e.g., `Submodule.span_induction`) instead of
this. -/
/-
**Ideal.span_eq_map_homogeneousSubmodule** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.span_eq_map_homogeneousSubmodule {ι R : Type*} [CommSemiring R] (x :
 ι -> R) : Ideal.span (Set.range x) = Submodule.map (MvPolynomial.aeval x).toLin
earMap (MvPolynomial.homogeneousSubmodule ι R 1)
参数：x : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用引理 `MvPolynomial.homogeneousSubmodule_one_eq_span_X`：homogeneousSubmodule_on
e_eq_span_X : MvPolynomial.homogeneousSubmodule σ R 1 = .span R (.range X)
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Try to use the universal property of the span (e.g., `Submodule.span_induction`)
 instead of
this.
-/
lemma Ideal.span_eq_map_homogeneousSubmodule {ι R : Type*} [CommSemiring R]
    (x : ι → R) :
    Ideal.span (Set.range x) =
      Submodule.map (MvPolynomial.aeval x).toLinearMap
        (MvPolynomial.homogeneousSubmodule ι R 1) := by
  simp [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp,
    Function.comp_def]

/-- Try to use the universal property of the span (e.g., `Submodule.span_induction`) instead of
this. -/
/-
**Ideal.span_pow_eq_map_homogeneousSubmodule** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.span_pow_eq_map_homogeneousSubmodule {ι R : Type*} [CommSemiring R] 
(x : ι -> R) (n : Nat) : Ideal.span (Set.range x) ^ n = Submodule.map (MvPolynom
ial.aeval x).toLinearMap (MvPolynomial.homogeneousSubmodule ι R n)
参数：x : ι -> R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MvPolynomial.homogeneousSubmodule_one_pow`：homogeneousSubmodule_one_pow 
(n : Nat) : (homogeneousSubmodule σ R 1) ^ n = homogeneousSubmodule σ R n
· 使用定理 `Submodule.map_pow`：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [
inst_1 : Semiring A] [inst_2 : Algebra R A] (M : Submodule R A)   {A' : Type u_1
} [inst…
· 使用引理 `Ideal.span_eq_map_homogeneousSubmodule`：Ideal.span_eq_map_homogeneousSub
module {ι R : Type*} [CommSemiring R] (x : ι -> R) : Ideal.span (Set.range x) = 
Submodule.map (MvPolynomial.…

--- 原说明 ---
Try to use the universal property of the span (e.g., `Submodule.span_induction`)
 instead of
this.
-/
lemma Ideal.span_pow_eq_map_homogeneousSubmodule {ι R : Type*} [CommSemiring R]
    (x : ι → R) (n : ℕ) :
    Ideal.span (Set.range x) ^ n =
      Submodule.map (MvPolynomial.aeval x).toLinearMap
        (MvPolynomial.homogeneousSubmodule ι R n) := by
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow,
    Ideal.span_eq_map_homogeneousSubmodule]

/-- Try to use the universal property of the span (e.g., `Submodule.span_induction`) instead of
this. -/
/-
**Ideal.mem_span_pow_iff_exists_isHomogeneous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.mem_span_pow_iff_exists_isHomogeneous {ι R : Type*} [CommSemiring R]
 {n : Nat} (x : ι -> R) (y : R) : y in (Ideal.span <| Set.range x) ^ n ↔ exists 
(p : MvPolynomial ι R), p.IsHomogeneous n ∧ p.eval x = y
参数：x : ι -> R；y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.span_pow_eq_map_homogeneousSubmodule`：Ideal.span_pow_eq_map_homoge
neousSubmodule {ι R : Type*} [CommSemiring R] (x : ι -> R) (n : Nat) : Ideal.spa
n (Set.range x) ^ n = Submodule.…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Try to use the universal property of the span (e.g., `Submodule.span_induction`)
 instead of
this.
-/
lemma Ideal.mem_span_pow_iff_exists_isHomogeneous {ι R : Type*} [CommSemiring R] {n : ℕ} (x : ι → R)
    (y : R) :
    y ∈ (Ideal.span <| Set.range x) ^ n ↔
      ∃ (p : MvPolynomial ι R), p.IsHomogeneous n ∧ p.eval x = y := by
  simp [Ideal.span_pow_eq_map_homogeneousSubmodule]

/-- Try to use the universal property of the span (e.g., `Submodule.span_induction`) instead of
this. -/
/-
**Ideal.mem_span_iff_exists_isHomogeneous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.mem_span_iff_exists_isHomogeneous {ι R : Type*} [CommSemiring R] (x 
: ι -> R) (y : R) : y in Ideal.span (.range x) ↔ exists (p : MvPolynomial ι R), 
p.IsHomogeneous 1 ∧ p.eval x = y
参数：x : ι -> R；y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.span_eq_map_homogeneousSubmodule`：Ideal.span_eq_map_homogeneousSub
module {ι R : Type*} [CommSemiring R] (x : ι -> R) : Ideal.span (Set.range x) = 
Submodule.map (MvPolynomial.…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Try to use the universal property of the span (e.g., `Submodule.span_induction`)
 instead of
this.
-/
lemma Ideal.mem_span_iff_exists_isHomogeneous {ι R : Type*} [CommSemiring R] (x : ι → R) (y : R) :
    y ∈ Ideal.span (.range x) ↔
      ∃ (p : MvPolynomial ι R), p.IsHomogeneous 1 ∧ p.eval x = y := by
  simp [Ideal.span_eq_map_homogeneousSubmodule]
