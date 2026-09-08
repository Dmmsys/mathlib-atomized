/-
Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Unbundled.InvariantExtension
public import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
public import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The spectral norm and the norm extension theorem

This file shows that if `K` is a nonarchimedean normed field and `L/K` is an algebraic extension,
then there is a natural extension of the norm on `K` to a `K`-algebra norm on `L`, the so-called
*spectral norm*. The spectral norm of an element of `L` only depends on its minimal polynomial
over `K`, so for `K ⊆ L ⊆ M` two extensions of `K`, the spectral norm on `M` restricts to the
spectral norm on `L`. This work can be used to uniquely extend the `p`-adic norm on `ℚ_[p]` to an
algebraic closure of `ℚ_[p]`, for example.

## Details

We define the spectral value and the spectral norm. We prove the norm extension theorem
[S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis* (Theorem 3.2.1/2)]
[bosch-guntzer-remmert] : given a nonarchimedean normed field `K` and an algebraic
extension `L/K`, the spectral norm is a power-multiplicative `K`-algebra norm on `L` extending
the norm on `K`. All `K`-algebra automorphisms of `L` are isometries with respect to this norm.
If `L/K` is finite, we get a formula relating the spectral norm on `L` with any other
power-multiplicative norm on `L` extending the norm on `K`.

Moreover, we also prove the unique norm extension theorem: if `K` is a field complete with respect
to a nontrivial nonarchimedean multiplicative norm and `L/K` is an algebraic extension, then the
spectral norm on `L` is a nonarchimedean multiplicative norm, and any power-multiplicative
`K`-algebra norm on `L` coincides with the spectral norm. More over, if `L/K` is finite, then `L`
is a complete space. This result is [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*
(Theorem 3.2.4/2)][bosch-guntzer-remmert].

As a prerequisite, we formalize the proof of [S. Bosch, U. Güntzer, R. Remmert,
*Non-Archimedean Analysis* (Proposition 3.1.2/1)][bosch-guntzer-remmert].

## Main Definitions

* `spectralValue` : the spectral value of a polynomial in `R[X]`.
* `spectralNorm` : the spectral norm `|y|_sp` is the spectral value of the minimal polynomial
  of `y : L` over `K`.
* `spectralAlgNorm` : the spectral norm is a `K`-algebra norm on `L`.
* `spectralMulAlgNorm` : the spectral norm is a multiplicative `K`-algebra norm on `L`.

## Main Results

* `norm_le_spectralNorm` : if `f` is a power-multiplicative `K`-algebra norm on `L`, then `f` is
  bounded above by `spectralNorm K L`.
* `spectralNorm_eq_of_equiv` : the `K`-algebra automorphisms of `L` are isometries with respect to
  the spectral norm.
* `spectralNorm_eq_iSup_of_finiteDimensional_normal` : if `L/K` is finite and normal, then
  `spectralNorm K L x = iSup (fun (σ : Gal(L/K)) ↦ f (σ x))`.
* `isPowMul_spectralNorm` : the spectral norm is power-multiplicative.
* `isNonarchimedean_spectralNorm` : the spectral norm is nonarchimedean.
* `spectralNorm_extends` : the spectral norm extends the norm on `K`.
* `spectralNorm_unique` : any power-multiplicative `K`-algebra norm on `L` coincides with the
  spectral norm.
* `spectralAlgNorm_mul` : the spectral norm on `L` is multiplicative.
* `spectralNorm.completeSpace` : if `L/K` is finite dimensional, then `L` is a complete space
  with respect to topology induced by the spectral norm.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

spectral, spectral norm, spectral value, seminorm, norm, nonarchimedean
-/

@[expose] public section

open Polynomial

open scoped Polynomial


noncomputable section

variable {R : Type*}

section spectralValue

open Nat Real

section Seminormed

variable [SeminormedRing R]

/-- The function `ℕ → ℝ` sending `n` to `‖ p.coeff n ‖^(1/(p.natDegree - n : ℝ))`, if
  `n < p.natDegree`, or to `0` otherwise. -/
/-
**spectralValueTerms** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：spectralValueTerms (p : R[X]) : Nat -> Real
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `ℕ → ℝ` sending `n` to `‖ p.coeff n ‖^(1/(p.natDegree - n : ℝ))`, i
f
  `n < p.natDegree`, or to `0` otherwise.
-/
def spectralValueTerms (p : R[X]) : ℕ → ℝ := fun n : ℕ ↦
  if n < p.natDegree then ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) else 0
/-
**spectralValueTerms_of_lt_natDegree** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralValueTerms_of_lt_natDegree (p : R[X]) {n : Nat} (hn : n < p.natDeg
ree) : spectralValueTerms p n = ‖p.coeff n‖ ^ (1 / (p.natDegree - n : Real))
参数：p : R[X]；hn : n < p.natDegree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem spectralValueTerms_of_lt_natDegree (p : R[X]) {n : ℕ} (hn : n < p.natDegree) :
    spectralValueTerms p n = ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) := by
  simp [spectralValueTerms, if_pos hn]
/-
**spectralValueTerms_of_natDegree_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralValueTerms_of_natDegree_le (p : R[X]) {n : Nat} (hn : p.natDegree 
<= n) : spectralValueTerms p n = 0
参数：p : R[X]；hn : p.natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem spectralValueTerms_of_natDegree_le (p : R[X]) {n : ℕ} (hn : p.natDegree ≤ n) :
    spectralValueTerms p n = 0 := by simp only [spectralValueTerms, if_neg (not_lt.mpr hn)]

/-- The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. One motivation
  for the spectral value: if the norm on `R` is nonarchimedean, and if a monic polynomial
  splits into linear factors, then its spectral value is the norm of its largest root.
  See `max_norm_root_eq_spectralValue`. -/
/-
**spectralValue** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：spectralValue (p : R[X]) : Real
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. On
e motivation
  for the spectral value: if the norm on `R` is nonarchimedean, and if a monic p
olynomial
  splits into linear factors, then its spectral value is the norm of its largest
 root.
  See `max_norm_root_eq_spectralValue`.
-/
def spectralValue (p : R[X]) : ℝ := iSup (spectralValueTerms p)

/-- The range of `spectralValue_terms p` is a finite set. -/
/-
**spectralValueTerms_finite_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralValueTerms_finite_range (p : R[X]) : (Set.range (spectralValueTerm
s p)).Finite
参数：p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.finite_Iio`：∀ {α : Type u_1} [inst : Preorder α] [LocallyFiniteOrder
Bot α] (a : α), (Set.Iio a).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
The range of `spectralValue_terms p` is a finite set.
-/
theorem spectralValueTerms_finite_range (p : R[X]) : (Set.range (spectralValueTerms p)).Finite :=
  Set.Finite.subset (Set.Finite.union (Set.finite_singleton 0) <|
    (Set.finite_Iio p.natDegree).image (fun n ↦ ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)))) <| by
      aesop (add simp [Set.range_subset_iff, spectralValueTerms])

open List in
/-- The sequence `spectralValue_terms p` is bounded above. -/
/-
**spectralValueTerms_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralValueTerms_bddAbove (p : R[X]) : BddAbove (Set.range (spectralValu
eTerms p))
参数：p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `spectralValueTerms_finite_range`：spectralValueTerms_finite_range (p : R[
X]) : (Set.range (spectralValueTerms p)).Finite

--- 原说明 ---
The sequence `spectralValue_terms p` is bounded above.
-/
theorem spectralValueTerms_bddAbove (p : R[X]) : BddAbove (Set.range (spectralValueTerms p)) :=
  (spectralValueTerms_finite_range p).bddAbove

/-- The sequence `spectralValue_terms p` is nonnegative. -/
/-
**spectralValueTerms_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralValueTerms_nonneg (p : R[X]) (n : Nat) : 0 <= spectralValueTerms p
 n
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The sequence `spectralValue_terms p` is nonnegative.
-/
theorem spectralValueTerms_nonneg (p : R[X]) (n : ℕ) : 0 ≤ spectralValueTerms p n := by
  simp only [spectralValueTerms]
  split_ifs with h
  · positivity
  · exact le_refl _

/-- The spectral value of a polynomial is nonnegative. -/
/-
**spectralValue_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralValue_nonneg (p : R[X]) : 0 <= spectralValue p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.iSup_nonneg`：iSup_nonneg (hf : forall i, 0 <= f i) : 0 <= ⨆ i, f i
· 使用定理 `spectralValueTerms_nonneg`：spectralValueTerms_nonneg (p : R[X]) (n : Nat
) : 0 <= spectralValueTerms p n

--- 原说明 ---
The spectral value of a polynomial is nonnegative.
-/
theorem spectralValue_nonneg (p : R[X]) : 0 ≤ spectralValue p :=
  iSup_nonneg (spectralValueTerms_nonneg p)

variable [Nontrivial R]

/-- The polynomial `X - r` has spectral value `‖ r ‖`. -/
/-
**spectralValue_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralValue_X_sub_C (r : R) : spectralValue (X - C r) = ‖r‖
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectralValue.eq_1`：∀ {R : Type u_1} [inst : SeminormedRing R] (p : Poly
nomial R), spectralValue p = iSup (spectralValueTerms p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ciSup_eq_of_forall_le_of_forall_lt_exists_gt`：ciSup_eq_of_forall_le_of_f
orall_lt_exists_gt [Nonempty ι] {f : ι -> α} (h₁ : forall i, f i <= b) (h₂ : for
all w, w < b -> exists i, w < f i)…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The polynomial `X - r` has spectral value `‖ r ‖`.
-/
theorem spectralValue_X_sub_C (r : R) : spectralValue (X - C r) = ‖r‖ := by
  rw [spectralValue]
  unfold spectralValueTerms
  simp only [natDegree_X_sub_C, lt_one_iff, coeff_sub, cast_one, one_div]
  suffices (⨆ n : ℕ, ite (n = 0) ‖r‖ 0) = ‖r‖ by
    rw [← this]
    apply congr_arg
    ext n
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn, hn, cast_zero, sub_zero, coeff_X_zero, coeff_C_zero, zero_sub,
        norm_neg, inv_one, rpow_one]
    · rw [if_neg hn, if_neg hn]
  · apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun n ↦ ?_)
      (fun _ hx ↦ ⟨0, by simp only [if_true, hx]⟩)
    split_ifs
    · exact le_refl _
    · exact norm_nonneg _

/-- The polynomial `X ^ n` has spectral value `0`. -/
/-
**spectralValue_X_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralValue_X_pow (n : Nat) : spectralValue (X ^ n : R[X]) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectralValue.eq_1`：∀ {R : Type u_1} [inst : SeminormedRing R] (p : Poly
nomial R), spectralValue p = iSup (spectralValueTerms p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `Polynomial.natDegree_X_pow`：natDegree_X_pow : natDegree ((X : R[X]) ^ n)
 = n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Real.rpow_eq_zero_iff_of_nonneg`：rpow_eq_zero_iff_of_nonneg (hx : 0 <= x
) : x ^ y = 0 ↔ x = 0 ∧ y != 0
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `inv_eq_zero`：inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.sub_eq_zero_iff_le`：∀ {n m : ℕ}, n - m = 0 ↔ n ≤ m
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
The polynomial `X ^ n` has spectral value `0`.
-/
theorem spectralValue_X_pow (n : ℕ) : spectralValue (X ^ n : R[X]) = 0 := by
  rw [spectralValue]
  unfold spectralValueTerms
  simp_rw [coeff_X_pow n, natDegree_X_pow]
  convert! ciSup_const using 2
  · ext m
    by_cases hmn : m < n
    · rw [if_pos hmn, rpow_eq_zero_iff_of_nonneg (norm_nonneg _), if_neg (_root_.ne_of_lt hmn),
        norm_zero, one_div, ne_eq, inv_eq_zero, ← cast_sub (le_of_lt hmn), cast_eq_zero,
        Nat.sub_eq_zero_iff_le]
      exact ⟨Eq.refl _, not_le_of_gt hmn⟩
    · rw [if_neg hmn]
  · infer_instance

end Seminormed

section Normed

variable [NormedRing R]

/-- The spectral value of `p` equals zero if and only if `p` is of the form `X ^ n`. -/
/-
**spectralValue_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralValue_eq_zero_iff [Nontrivial R] {p : R[X]} (hp : p.Monic) : spect
ralValue p = 0 ↔ p = X ^ p.natDegree
参数：hp : p.Monic。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Polynomial.Monic.eq_X_pow_iff_natDegree_le_natTrailingDegree`：eq_X_pow_i
ff_natDegree_le_natTrailingDegree (h₁ : p.Monic) : p = X ^ p.natDegree ↔ p.natDe
gree <= p.natTrailingDegree
· 使用定理 `Polynomial.le_natTrailingDegree`：le_natTrailingDegree (hp : p != 0) (hn 
: forall m < n, p.coeff m = 0) : n <= p.natTrailingDegree
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `spectralValueTerms_bddAbove`：spectralValueTerms_bddAbove (p : R[X]) : Bd
dAbove (Set.range (spectralValueTerms p))
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `spectralValueTerms_nonneg`：spectralValueTerms_nonneg (p : R[X]) (n : Nat
) : 0 <= spectralValueTerms p n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_eq_zero_iff_of_nonneg`：rpow_eq_zero_iff_of_nonneg (hx : 0 <= x
) : x ^ y = 0 ↔ x = 0 ∧ y != 0
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `spectralValueTerms_of_lt_natDegree`：spectralValueTerms_of_lt_natDegree (
p : R[X]) {n : Nat} (hn : n < p.natDegree) : spectralValueTerms p n = ‖p.coeff n
‖ ^ (1 / (p.natDegree - …
· 使用定理 `spectralValue_X_pow`：spectralValue_X_pow (n : Nat) : spectralValue (X ^ 
n : R[X]) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The spectral value of `p` equals zero if and only if `p` is of the form `X ^ n`.
-/
theorem spectralValue_eq_zero_iff [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    spectralValue p = 0 ↔ p = X ^ p.natDegree := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ spectralValue_X_pow p.natDegree⟩
  refine hp.eq_X_pow_iff_natDegree_le_natTrailingDegree.mpr <|
    le_natTrailingDegree hp.ne_zero fun n hn ↦ ?_
  have h0 : spectralValueTerms p n = 0 := by
    apply le_antisymm ((le_ciSup (spectralValueTerms_bddAbove p) n).trans h.le)
    exact spectralValueTerms_nonneg _ _
  rw [spectralValueTerms_of_lt_natDegree _ hn,
    Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _)] at h0
  exact norm_eq_zero.mp h0.1

end Normed

section NormedDivisionRing

variable [NormedDivisionRing R]

/-- The spectral value of a monic polynomial `P` is less than or equal to one if and only
if all of its coefficients have norm less than or equal to 1. -/
/-
**spectralValue_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralValue_le_one_iff {P : R[X]} (hP : Monic P) : spectralValue P <= 1 
↔ forall n : Nat, ‖P.coeff n‖ <= 1
参数：hP : Monic P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectralValue.eq_1`：∀ {R : Type u_1} [inst : SeminormedRing R] (p : Poly
nomial R), spectralValue p = iSup (spectralValueTerms p)
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.coeff_natDegree`：∀ {R : Type u} [inst : Semiring R] {p 
: Polynomial R}, p.Monic → p.coeff p.natDegree = 1
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `spectralValueTerms_bddAbove`：spectralValueTerms_bddAbove (p : R[X]) : Bd
dAbove (Set.range (spectralValueTerms p))
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `spectralValueTerms_of_lt_natDegree`：spectralValueTerms_of_lt_natDegree (
p : R[X]) {n : Nat} (hn : n < p.natDegree) : spectralValueTerms p n = ‖p.coeff n
‖ ^ (1 / (p.natDegree - …
· 使用定理 `Real.one_lt_rpow`：one_lt_rpow {x z : Real} (hx : 1 < x) (hz : 0 < z) : 1
 < x ^ z
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
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
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
The spectral value of a monic polynomial `P` is less than or equal to one if and
 only
if all of its coefficients have norm less than or equal to 1.
-/
theorem spectralValue_le_one_iff {P : R[X]} (hP : Monic P) :
    spectralValue P ≤ 1 ↔ ∀ n : ℕ, ‖P.coeff n‖ ≤ 1 := by
  rw [spectralValue]
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · obtain hPn | hPn | hPn := lt_trichotomy P.natDegree n
    · simp [coeff_eq_zero_of_natDegree_lt hPn]
    · rw [← hPn, hP.coeff_natDegree, norm_one]
    · have : spectralValueTerms P n ≤ 1 := le_ciSup (spectralValueTerms_bddAbove P) n |>.trans h
      contrapose! this
      simp only [spectralValueTerms_of_lt_natDegree _ hPn]
      exact Real.one_lt_rpow this (by simp [hPn])
  · apply ciSup_le (fun n ↦ ?_)
    rw [spectralValueTerms]
    split_ifs with hn
    · apply Real.rpow_le_one (norm_nonneg _) (h n)
      rw [one_div_nonneg, sub_nonneg, Nat.cast_le]
      exact le_of_lt hn
    · exact zero_le_one

end NormedDivisionRing

end spectralValue

/- In this section we prove [S. Bosch, U. Güntzer, R. Remmert,
*Non-Archimedean Analysis* (Proposition 3.1.2/1)][bosch-guntzer-remmert]. -/
section BddBySpectralValue

open Real

variable {K : Type*} [NormedField K] {L : Type*} [Field L] [Algebra K L]

open Nat in
/-- The norm of any root of `p` is bounded by the spectral value of `p`. See
[S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis* (Proposition 3.1.2/1(1))]
[bosch-guntzer-remmert]. -/
/-
**norm_root_le_spectralValue** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_root_le_spectralValue {f : AlgebraNorm K L} (hf_pm : IsPowMul f) (hf_
na : IsNonarchimedean f) {p : K[X]} (hp : p.Monic) {x : L} (hx : aeval x p = 0) 
: f x <= spectralValue p
参数：hf_pm : IsPowMul f；hf_na : IsNonarchimedean f；hp : p.Monic；hx : aeval x p = 0
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectralValue_nonneg`：spectralValue_nonneg (p : R[X]) : 0 <= spectralVal
ue p
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.pow_rpow_inv_natCast`：pow_rpow_inv_natCast (hx : 0 <= x) (hn : n !=
 0) : (x ^ n) ^ (n⁻¹ : Real) = x
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Finite.csSup_lt_iff`：Set.Finite.csSup_lt_iff (hs : s.Finite) (h : s.
Nonempty) : sSup s < a ↔ forall x in s, x < a
· 使用定理 `spectralValueTerms_finite_range`：spectralValueTerms_finite_range (p : R[
X]) : (Set.range (spectralValueTerms p)).Finite
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `spectralValue.eq_1`：∀ {R : Type u_1} [inst : SeminormedRing R] (p : Poly
nomial R), spectralValue p = iSup (spectralValueTerms p)
· 使用定理 `Real.rpow_lt_rpow`：rpow_lt_rpow (hx : 0 <= x) (hxy : x < y) (hz : 0 < z)
 : x ^ z < y ^ z
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
The norm of any root of `p` is bounded by the spectral value of `p`. See
[S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis* (Proposition 3.1.2
/1(1))]
[bosch-guntzer-remmert].
-/
theorem norm_root_le_spectralValue {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) {p : K[X]} (hp : p.Monic) {x : L} (hx : aeval x p = 0) :
    f x ≤ spectralValue p := by
  by_cases hx0 : f x = 0
  · rw [hx0]; exact spectralValue_nonneg p
  · by_contra h_ge
    have hn_lt (n : ℕ) (hn : n < p.natDegree) : ‖p.coeff n‖ < f x ^ (p.natDegree - n) := by
      have hexp : (‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ))) ^ (p.natDegree - n) =
          ‖p.coeff n‖ := by
        rw [← rpow_natCast, ← rpow_mul (norm_nonneg _), mul_comm, rpow_mul (norm_nonneg _),
          rpow_natCast, ← cast_sub (le_of_lt hn), one_div,
          pow_rpow_inv_natCast (norm_nonneg _) (_root_.ne_of_gt (tsub_pos_of_lt hn))]
      have h_base : ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) < f x := by
        rw [spectralValue, iSup, not_le, Set.Finite.csSup_lt_iff (spectralValueTerms_finite_range p)
          (Set.range_nonempty (spectralValueTerms p))] at h_ge
        have h_rg : ‖p.coeff n‖ ^ (1 / (p.natDegree - n : ℝ)) ∈
          Set.range (spectralValueTerms p) := by use n; simp only [spectralValueTerms, if_pos hn]
        exact h_ge (‖p.coeff n‖₊ ^ (1 / (p.natDegree - n : ℝ))) h_rg
      rw [← hexp, ← rpow_natCast, ← rpow_natCast]
      gcongr
      exact cast_pos.mpr (tsub_pos_of_lt hn)
    have h_deg : 0 < p.natDegree := natDegree_pos_of_monic_of_aeval_eq_zero hp hx
    have h_lt : f ((Finset.range p.natDegree).sum fun i : ℕ ↦ p.coeff i • x ^ i) <
        f (x ^ p.natDegree) := by
      have hn' (n : ℕ) (hn : n < p.natDegree) : f (p.coeff n • x ^ n) < f (x ^ p.natDegree) := by
        by_cases hn0 : n = 0
        · rw [hn0, pow_zero, map_smul_eq_mul, hf_pm _ (succ_le_iff.mpr h_deg),
            ← Nat.sub_zero p.natDegree, ← hn0]
          exact (mul_le_of_le_one_right (norm_nonneg _) hf_pm.map_one_le_one).trans_lt (hn_lt n hn)
        · have : p.natDegree = p.natDegree - n + n := by rw [Nat.sub_add_cancel (le_of_lt hn)]
          rw [map_smul_eq_mul, hf_pm _ (succ_le_iff.mp (pos_iff_ne_zero.mpr hn0)),
            hf_pm _ (succ_le_iff.mpr h_deg), this, pow_add]
          gcongr
          exact hn_lt n hn
      set g := fun i : ℕ ↦ p.coeff i • x ^ i
      obtain ⟨m, hm_in, hm⟩ : ∃ (m : ℕ) (_ : 0 < p.natDegree → m < p.natDegree),
          f ((Finset.range p.natDegree).sum g) ≤ f (g m) := by
        obtain ⟨m, hm, h⟩ := IsNonarchimedean.finset_image_add (map_zero _) (apply_nonneg _) hf_na g
          (Finset.range p.natDegree)
        rw [Finset.nonempty_range_iff, ← zero_lt_iff, Finset.mem_range] at hm
        exact ⟨m, hm, h⟩
      exact lt_of_le_of_lt hm (hn' m (hm_in h_deg))
    have h0 : f 0 ≠ 0 := by
      have h_eq : f 0 = f (x ^ p.natDegree) := by
        rw [← hx, aeval_eq_sum_range, Finset.sum_range_succ, add_comm, hp.coeff_natDegree,
          one_smul, ← max_eq_left_of_lt h_lt]
        exact IsNonarchimedean.add_eq_max_of_ne hf_na (ne_of_gt h_lt)
      exact h_eq ▸ ne_of_gt (lt_of_le_of_lt (apply_nonneg _ _) h_lt)
    exact h0 (map_zero _)

open Multiset

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f` is a nonarchimedean, power-multiplicative `K`-algebra norm on `L`, then the spectral
value of a polynomial `p : K[X]` that decomposes into linear factors in `L` is equal to the
maximum of the norms of the roots. See [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*
(Proposition 3.1.2/1(2))][bosch-guntzer-remmert]. -/
/-
**max_norm_root_eq_spectralValue** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_norm_root_eq_spectralValue [DecidableEq L] {f : AlgebraNorm K L} (hf_p
m : IsPowMul f) (hf_na : IsNonarchimedean f) (hf1 : f 1 = 1) (p : K[X]) (s : Mul
tiset L) (hp : mapAlg K L p = (map (fun a : L => X - C a) s).prod) : (⨆ x : L, i
f x in s then f x else 0) = spectralValue p
参数：hf_pm : IsPowMul f；hf_na : IsNonarchimedean f；hf1 : f 1 = 1；p : K[X]；s : Mult
iset L；hp : mapAlg K L p = (map (fun a : L => X - C a) s).prod。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.iSup_nonneg`：iSup_nonneg (hf : forall i, 0 <= f i) : 0 <= ⨆ i, f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `RingNormClass.toRingSeminormClass`：∀ {F : Type u_7} {α : outParam (Type 
u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {inst_1 : Sem
iring β} {inst_2 : Part…
· 使用定理 `AlgebraNormClass.toRingNormClass`：∀ {F : Type u_1} {R : outParam (Type u
_2)} {inst : SeminormedCommRing R} {S : outParam (Type u_3)} {inst_1 : Ring S}  
 {inst_2 : Algebra R S…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C`：aeval_root_of_
mapAlg_eq_multiset_prod_X_sub_C (s : Multiset A) {x : A} (hx : x in s) {p : R[X]
} (hp : p.mapAlg R A = (s.map (X - C ·)).prod)…
· 使用定理 `norm_root_le_spectralValue`：norm_root_le_spectralValue {f : AlgebraNorm 
K L} (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f) {p : K[X]} (hp : p.Monic)
 {x : L} (hx : a…
· 使用定理 `Polynomial.monic_of_monic_mapAlg`：monic_of_monic_mapAlg [FaithfulSMul R 
S] {p : Polynomial R} (hp : (mapAlg R S p).Monic) : p.Monic
· 使用定理 `instFaithfulSMul_1`：∀ (R : Type u_1) (A : Type u_2) [inst : CommRing R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] [IsSimpleRing R]   [Nontrivial A], 
Faithful…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Polynomial.monic_multisetProd_X_sub_C`：monic_multisetProd_X_sub_C (s : M
ultiset R) : Monic (s.map fun a => X - C a).prod
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `spectralValue_nonneg`：spectralValue_nonneg (p : R[X]) : 0 <= spectralVal
ue p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `spectralValueTerms_of_lt_natDegree`：spectralValueTerms_of_lt_natDegree (
p : R[X]) {n : Nat} (hn : n < p.natDegree) : spectralValueTerms p n = ‖p.coeff n
‖ ^ (1 / (p.natDegree - …
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
（共 87 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a nonarchimedean, power-multiplicative `K`-algebra norm on `L`, then t
he spectral
value of a polynomial `p : K[X]` that decomposes into linear factors in `L` is e
qual to the
maximum of the norms of the roots. See [S. Bosch, U. Güntzer, R. Remmert, *Non-A
rchimedean Analysis*
(Proposition 3.1.2/1(2))][bosch-guntzer-remmert].
-/
theorem max_norm_root_eq_spectralValue [DecidableEq L] {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hf1 : f 1 = 1) (p : K[X]) (s : Multiset L)
    (hp : mapAlg K L p = (map (fun a : L ↦ X - C a) s).prod) :
    (⨆ x : L, if x ∈ s then f x else 0) = spectralValue p := by
  have h_le : 0 ≤ ⨆ x : L, ite (x ∈ s) (f x) 0 := by
    apply iSup_nonneg (fun _ ↦ ?_)
    split_ifs
    exacts [apply_nonneg _ _, le_refl _]
  apply le_antisymm
  · apply ciSup_le (fun x ↦ ?_)
    by_cases hx : x ∈ s
    · have hx0 : aeval x p = 0 := aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C s hx hp
      rw [if_pos hx]
      exact norm_root_le_spectralValue hf_pm hf_na
        (monic_of_monic_mapAlg (hp ▸ monic_multisetProd_X_sub_C s)) hx0
    · simp only [if_neg hx, spectralValue_nonneg _]
  · apply ciSup_le (fun m ↦ ?_)
    by_cases hm : m < p.natDegree
    · rw [spectralValueTerms_of_lt_natDegree _ hm]
      have h : 0 < (p.natDegree - m : ℝ) := by rw [sub_pos, Nat.cast_lt]; exact hm
      rw [← rpow_le_rpow_iff (rpow_nonneg (norm_nonneg _) _) h_le h, ← rpow_mul (norm_nonneg _),
        one_div_mul_cancel (ne_of_gt h), rpow_one, ← Nat.cast_sub (le_of_lt hm), rpow_natCast]
      have hps : card s = p.natDegree := by
        rw [← natDegree_map (algebraMap K L), ← mapAlg_eq_map, hp,
          natDegree_multiset_prod_X_sub_C_eq_card]
      have hc : ‖p.coeff m‖ = f (((mapAlg K L) p).coeff m) := by
        rw [← AlgebraNorm.extends_norm hf1, mapAlg_eq_map, coeff_map]
      rw [hc, hp, prod_X_sub_C_coeff s (hps ▸ le_of_lt hm)]
      have h : f ((-1) ^ (card s - m) * s.esymm (card s - m)) = f (s.esymm (card s - m)) := by
        rcases neg_one_pow_eq_or L (card s - m) with h1 | hn1
        · rw [h1, one_mul]
        · rw [hn1, neg_mul, one_mul, map_neg_eq_map]
      rw [h, esymm]
      obtain ⟨t, ht_card, hts, ht_ge⟩ : ∃ t : Multiset L, card t = card s - m ∧
          (∀ x : L, x ∈ t → x ∈ s) ∧ f (map prod (powersetCard (card s - m) s)).sum ≤ f t.prod :=
        hf_na.multiset_powerset_image_add s m
      apply le_trans ht_ge
      have h_pr : f t.prod ≤ (t.map f).prod := le_prod_of_submultiplicative_of_nonneg f
        (apply_nonneg _) (le_of_eq hf1) (map_mul_le_mul _) t
      apply le_trans h_pr
      have hs_ne : s ≠ 0 :=
        have hpos : 0 < s.toFinset.card := by
          have hs0 : 0 < s.card := hps ▸ hm.pos
          obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp hs0
          exact Finset.card_pos.mpr ⟨x, mem_toFinset.mpr hx⟩
        toFinset_nonempty.mp (Finset.card_pos.mp hpos)
      obtain ⟨y, hyx, hy_max⟩ : ∃ y : L, y ∈ s ∧ ∀ z : L, z ∈ s → f z ≤ f y :=
        exists_max_image f hs_ne
      have : (map f t).prod ≤ f y ^ (p.natDegree - m) := by
        set g : L → NNReal := fun x ↦ ⟨f x, apply_nonneg f x⟩
        have h_card : p.natDegree - m = card (t.map g) := by rw [card_map, ht_card, ← hps]
        have hx_le : ∀ x : NNReal, x ∈ map g t → x ≤ g y := by
          intro r hr
          obtain ⟨_, hzt, hzr⟩ := mem_map.mp hr
          exact hzr ▸ hy_max _ (hts _ hzt)
        have : (map g t).prod ≤ g y ^ (p.natDegree - m) := h_card ▸ prod_le_pow_card _ _ hx_le
        simpa [g, ← NNReal.coe_le_coe, NNReal.coe_pow, NNReal.coe_mk, NNReal.coe_multiset_prod,
          map_map, Function.comp_apply, NNReal.coe_mk] using! this
      have h_bdd : BddAbove (Set.range fun x : L ↦ ite (x ∈ s) (f x) 0) := by
        use f y
        intro r hr
        obtain ⟨z, hz⟩ := Set.mem_range.mpr hr
        simp only at hz
        rw [← hz]
        split_ifs with h
        · exact hy_max _ h
        · exact apply_nonneg _ _
      exact le_trans this (pow_le_pow_left₀ (apply_nonneg _ _)
        (le_trans (by rw [if_pos hyx]) (le_ciSup h_bdd y)) _)
    · simp only [spectralValueTerms, if_neg hm, h_le]

end BddBySpectralValue


section spectralNorm

section NormedField
/- In this section we prove [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*
(Theorem 3.2.1/2)][bosch-guntzer-remmert]. -/

open IntermediateField

variable (K : Type*) [NormedField K] (L : Type*) [Field L] [Algebra K L]

/-- If `L` is an algebraic extension of a normed field `K` and `y : L` then the spectral norm
  `spectralNorm K y : ℝ` of `y` (written `|y|_sp` in the textbooks) is the spectral value of the
  minimal polynomial of `y` over `K`. -/
/-
**spectralNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：spectralNorm (y : L) : Real
参数：y : L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L` is an algebraic extension of a normed field `K` and `y : L` then the spec
tral norm
  `spectralNorm K y : ℝ` of `y` (written `|y|_sp` in the textbooks) is the spect
ral value of the
  minimal polynomial of `y` over `K`.
-/
def spectralNorm (y : L) : ℝ := spectralValue (minpoly K y)

variable {K L}

/-- If `L/E/K` is a tower of fields, then the spectral norm of `x : E` equals its spectral norm
  when regarding `x` as an element of `L`. -/
/-
**spectralNorm.eq_of_tower** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm.eq_of_tower {E : Type*} [Field E] [Algebra K E] [Algebra E L]
 [IsScalarTower K E L] (x : E) : spectralNorm K E x = spectralNorm K L (algebraM
ap E L x)
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.algebraMap_eq`：algebraMap_eq {B} [CommRing B] [Algebra A B] [Alg
ebra B B'] [IsScalarTower A B B'] (h : Function.Injective (algebraMap B B')) (x 
: B) : minp…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `L/E/K` is a tower of fields, then the spectral norm of `x : E` equals its sp
ectral norm
  when regarding `x` as an element of `L`.
-/
theorem spectralNorm.eq_of_tower {E : Type*} [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L] (x : E) :
    spectralNorm K E x = spectralNorm K L (algebraMap E L x) := by
  have hx : minpoly K (algebraMap E L x) = minpoly K x :=
    minpoly.algebraMap_eq (algebraMap E L).injective x
  simp only [spectralNorm, hx]

variable (E : IntermediateField K L)

/-- If `L/E/K` is a tower of fields, then the spectral norm of `x : E` when regarded as an element
  of the normal closure of `E` equals its spectral norm when regarding `x` as an element of `L`. -/
/-
**spectralNorm.eq_of_normalClosure'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm.eq_of_normalClosure' (x : E) : spectralNorm K (normalClosure 
K E (AlgebraicClosure E)) (algebraMap E (normalClosure K E (AlgebraicClosure E))
 x) = spectralNorm K L (algebraMap E L x)
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `normalClosure.instIsScalarTowerSubtypeMemIntermediateFieldNormalClosure`
：∀ (F : Type u_1) (K : Type u_2) (L : Type u_3) [inst : Field F] [inst_1 : Field
 K] [inst_2 : Field L]   [inst_3 : Algebra F K] [inst_4 : Alg…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `L/E/K` is a tower of fields, then the spectral norm of `x : E` when regarded
 as an element
  of the normal closure of `E` equals its spectral norm when regarding `x` as an
 element of `L`.
-/
theorem spectralNorm.eq_of_normalClosure' (x : E) :
    spectralNorm K (normalClosure K E (AlgebraicClosure E))
      (algebraMap E (normalClosure K E (AlgebraicClosure E)) x) =
    spectralNorm K L (algebraMap E L x) := by
  simp_rw [← spectralNorm.eq_of_tower]

/-- If `L/E/K` is a tower of fields and `x = algebraMap E L g`, then the spectral norm
  of `g : E` when regarded as an element of the normal closure of `E` equals the spectral norm
  of `x : L`. -/
/-
**spectralNorm.eq_of_normalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm.eq_of_normalClosure {E : IntermediateField K L} {x : L} (g : 
E) (h_map : algebraMap E L g = x) : spectralNorm K (normalClosure K E (Algebraic
Closure E)) (algebraMap E (normalClosure K E (AlgebraicClosure E)) g) = spectral
Norm K L x
参数：g : E；h_map : algebraMap E L g = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `spectralNorm.eq_of_normalClosure'`：spectralNorm.eq_of_normalClosure' (x 
: E) : spectralNorm K (normalClosure K E (AlgebraicClosure E)) (algebraMap E (no
rmalClosure K E (Algebr…

--- 原说明 ---
If `L/E/K` is a tower of fields and `x = algebraMap E L g`, then the spectral no
rm
  of `g : E` when regarded as an element of the normal closure of `E` equals the
 spectral norm
  of `x : L`.
-/
theorem spectralNorm.eq_of_normalClosure {E : IntermediateField K L} {x : L} (g : E)
    (h_map : algebraMap E L g = x) :
    spectralNorm K (normalClosure K E (AlgebraicClosure E))
        (algebraMap E (normalClosure K E (AlgebraicClosure E)) g) =
      spectralNorm K L x :=
  h_map ▸ spectralNorm.eq_of_normalClosure' E g

variable (y : L)

open Real

/-- `spectralNorm K L (0 : L) = 0`. -/
/-
**spectralNorm_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_zero : spectralNorm K L (0 : L) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.zero`：zero : minpoly A (0 : B) = X
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `spectralValue_X_pow`：spectralValue_X_pow (n : Nat) : spectralValue (X ^ 
n : R[X]) = 0

--- 原说明 ---
`spectralNorm K L (0 : L) = 0`.
-/
theorem spectralNorm_zero : spectralNorm K L (0 : L) = 0 := by
  unfold spectralNorm
  rw [minpoly.zero, ← pow_one X, spectralValue_X_pow 1]

/-- `spectralNorm K L y` is nonnegative. -/
/-
**spectralNorm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_nonneg (y : L) : 0 <= spectralNorm K L y
参数：y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `spectralValueTerms_bddAbove`：spectralValueTerms_bddAbove (p : R[X]) : Bd
dAbove (Set.range (spectralValueTerms p))
· 使用定理 `spectralValueTerms_nonneg`：spectralValueTerms_nonneg (p : R[X]) (n : Nat
) : 0 <= spectralValueTerms p n

--- 原说明 ---
`spectralNorm K L y` is nonnegative.
-/
theorem spectralNorm_nonneg (y : L) : 0 ≤ spectralNorm K L y :=
  le_ciSup_of_le (spectralValueTerms_bddAbove (minpoly K y)) 0 (spectralValueTerms_nonneg _ 0)

/-- `spectralNorm K L y` is positive if `y ≠ 0`. -/
/-
**spectralNorm_zero_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_zero_lt {y : L} (hy : y != 0) (hy_alg : IsAlgebraic K y) : 0 
< spectralNorm K L y
参数：hy : y != 0；hy_alg : IsAlgebraic K y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `spectralNorm_nonneg`：spectralNorm_nonneg (y : L) : 0 <= spectralNorm K L
 y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectralNorm.eq_1`：∀ (K : Type u_2) [inst : NormedField K] (L : Type u_3
) [inst_1 : Field L] [inst_2 : Algebra K L] (y : L),   spectralNorm K L y = spec
tralVal…
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `spectralValue_eq_zero_iff`：spectralValue_eq_zero_iff [Nontrivial R] {p :
 R[X]} (hp : p.Monic) : spectralValue p = 0 ↔ p = X ^ p.natDegree
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `minpoly.coeff_zero_ne_zero`：coeff_zero_ne_zero (hx : IsIntegral A x) (h 
: x != 0) : coeff (minpoly A x) 0 != 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `minpoly.natDegree_pos`：natDegree_pos [Nontrivial B] (hx : IsIntegral A x
) : 0 < natDegree (minpoly A x)

--- 原说明 ---
`spectralNorm K L y` is positive if `y ≠ 0`.
-/
theorem spectralNorm_zero_lt {y : L} (hy : y ≠ 0) (hy_alg : IsAlgebraic K y) :
    0 < spectralNorm K L y := by
  apply lt_of_le_of_ne (spectralNorm_nonneg _)
  rw [spectralNorm, ne_eq, eq_comm, spectralValue_eq_zero_iff (minpoly.monic hy_alg.isIntegral)]
  intro h
  apply minpoly.coeff_zero_ne_zero hy_alg.isIntegral hy
  rw [h, coeff_X_pow, if_neg (ne_of_lt (minpoly.natDegree_pos hy_alg.isIntegral))]

/-- If `spectralNorm K L x = 0`, then `x = 0`. -/
/-
**eq_zero_of_map_spectralNorm_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_of_map_spectralNorm_eq_zero {x : L} (hx : spectralNorm K L x = 0) 
(hx_alg : IsAlgebraic K x) : x = 0
参数：hx : spectralNorm K L x = 0；hx_alg : IsAlgebraic K x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `spectralNorm_zero_lt`：spectralNorm_zero_lt {y : L} (hy : y != 0) (hy_alg
 : IsAlgebraic K y) : 0 < spectralNorm K L y

--- 原说明 ---
If `spectralNorm K L x = 0`, then `x = 0`.
-/
theorem eq_zero_of_map_spectralNorm_eq_zero {x : L} (hx : spectralNorm K L x = 0)
    (hx_alg : IsAlgebraic K x) : x = 0 := by
  by_contra h0
  exact (ne_of_gt (spectralNorm_zero_lt h0 hx_alg)) hx

/-- If `f` is a power-multiplicative `K`-algebra norm on `L`, then `f`
  is bounded above by `spectralNorm K L`. -/
/-
**norm_le_spectralNorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_le_spectralNorm {f : AlgebraNorm K L} (hf_pm : IsPowMul f) (hf_na : I
sNonarchimedean f) {x : L} (hx_alg : IsAlgebraic K x) : f x <= spectralNorm K L 
x
参数：hf_pm : IsPowMul f；hf_na : IsNonarchimedean f；hx_alg : IsAlgebraic K x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_root_le_spectralValue`：norm_root_le_spectralValue {f : AlgebraNorm 
K L} (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f) {p : K[X]} (hp : p.Monic)
 {x : L} (hx : a…
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0

--- 原说明 ---
If `f` is a power-multiplicative `K`-algebra norm on `L`, then `f`
  is bounded above by `spectralNorm K L`.
-/
theorem norm_le_spectralNorm {f : AlgebraNorm K L} (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) {x : L} (hx_alg : IsAlgebraic K x) :
    f x ≤ spectralNorm K L x :=
  norm_root_le_spectralValue hf_pm hf_na (minpoly.monic hx_alg.isIntegral)
    (by rw [minpoly.aeval])

/-- The `K`-algebra automorphisms of `L` are isometries with respect to the spectral norm. -/
/-
**spectralNorm_eq_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_eq_of_equiv (σ : Gal(L/K)) (x : L) : spectralNorm K L x = spe
ctralNorm K L (σ x)
参数：σ : Gal(L/K)；x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.algEquiv_eq`：algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f
 x) = minpoly A x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `K`-algebra automorphisms of `L` are isometries with respect to the spectral
 norm.
-/
theorem spectralNorm_eq_of_equiv (σ : Gal(L/K)) (x : L) :
    spectralNorm K L x = spectralNorm K L (σ x) := by
  simp only [spectralNorm, minpoly.algEquiv_eq]

-- We first assume that the extension is finite and normal

section FiniteNormal

variable (K L) [h_fin : FiniteDimensional K L] [hn : Normal K L]

/--
If `L/K` is finite and normal, then `spectralNorm K L x = supr (λ (σ : Gal(L/K)), f (σ x))`. -/
/-
**spectralNorm_eq_iSup_of_finiteDimensional_normal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_eq_iSup_of_finiteDimensional_normal {f : AlgebraNorm K L} (hf
_pm : IsPowMul f) (hf_na : IsNonarchimedean f) (hf_ext : forall (x : K), f (alge
braMap K L x) = ‖x‖) (x : L) : spectralNorm K L x = ⨆ σ : Gal(L/K), f (σ x)
参数：hf_pm : IsPowMul f；hf_na : IsNonarchimedean f；hf_ext : forall (x : K), f (alg
ebraMap K L x) = ‖x‖；x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Normal.splits`：Normal.splits (_ : Normal F K) (x : K) : Splits ((minpoly
 F x).map (algebraMap F K))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.splits_iff_exists_multiset`：splits_iff_exists_multiset : Spli
ts f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Normal.isIntegral`：Normal.isIntegral (_ : Normal F K) (x : K) : IsIntegr
al F x
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `max_norm_root_eq_spectralValue`：max_norm_root_eq_spectralValue [Decidabl
eEq L] {f : AlgebraNorm K L} (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f) (
hf1 : f 1 = 1) (p : …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.leadingCoeff_map`：leadingCoeff_map (f : R ->+* S) : (p.map f)
.leadingCoeff = f p.leadingCoeff
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `minpoly.exists_algEquiv_of_root'`：exists_algEquiv_of_root' [Normal K L] 
{x y : L} (hy : IsAlgebraic K y) (h_ev : (Polynomial.aeval x) (minpoly K y) = 0)
 : exists σ : Gal(L/K)…
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
If `L/K` is finite and normal, then `spectralNorm K L x = supr (λ (σ : Gal(L/K))
, f (σ x))`.
-/
theorem spectralNorm_eq_iSup_of_finiteDimensional_normal
    {f : AlgebraNorm K L} (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f)
    (hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖) (x : L) :
    spectralNorm K L x = ⨆ σ : Gal(L/K), f (σ x) := by
  classical
  have hf1 : f 1 = 1 := by
    rw [← (algebraMap K L).map_one, hf_ext]
    simp
  refine le_antisymm ?_ (ciSup_le fun σ ↦
    norm_root_le_spectralValue hf_pm hf_na
      (minpoly.monic (hn.isIntegral x)) (minpoly.aeval_algHom _ σ.toAlgHom _))
  · set p := minpoly K x
    have hp_sp : Splits ((minpoly K x).map (algebraMap K L)) := hn.splits x
    obtain ⟨s, hs⟩ := splits_iff_exists_multiset.mp hp_sp
    have h_lc : (algebraMap K L) (minpoly K x).leadingCoeff = 1 := by
      rw [minpoly.monic (hn.isIntegral x), map_one]
    rw [leadingCoeff_map, h_lc, map_one, one_mul] at hs
    simp only [spectralNorm]
    rw [← max_norm_root_eq_spectralValue hf_pm hf_na hf1 _ _ hs]
    apply ciSup_le
    intro y
    split_ifs with h
    · obtain ⟨σ, hσ⟩ : ∃ σ : Gal(L/K), σ x = y := minpoly.exists_algEquiv_of_root'
        (Algebra.IsAlgebraic.isAlgebraic x) (aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C s h hs)
      rw [← hσ]
      apply Finite.le_ciSup _ σ
    · exact iSup_nonneg fun σ ↦ apply_nonneg _ _

open IsUltrametricDist

/-- If `L/K` is finite and normal, then `spectralNorm K L = invariantExtension K L`. -/
/-
**spectralNorm_eq_invariantExtension** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_eq_invariantExtension [hu : IsUltrametricDist K] : spectralNo
rm K L = invariantExtension K L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `IsUltrametricDist.isNonarchimedean_norm`：isNonarchimedean_norm {R} [Semi
normedAddCommGroup R] [IsUltrametricDist R] : IsNonarchimedean (‖·‖ : R -> Real)
· 使用定理 `exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional`：exists_nona
rchimedean_pow_mul_seminorm_of_finiteDimensional (hfd : FiniteDimensional K L) (
hna : IsNonarchimedean (norm : K -> Real)) : exis…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectralNorm_eq_iSup_of_finiteDimensional_normal`：spectralNorm_eq_iSup_o
f_finiteDimensional_normal {f : AlgebraNorm K L} (hf_pm : IsPowMul f) (hf_na : I
sNonarchimedean f) (hf_ext : forall (x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `L/K` is finite and normal, then `spectralNorm K L = invariantExtension K L`.
-/
theorem spectralNorm_eq_invariantExtension [hu : IsUltrametricDist K] :
    spectralNorm K L = invariantExtension K L := by
  ext x
  have hna := hu.isNonarchimedean_norm
  set f := Classical.choose (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)
    with hf
  have hf_pow : IsPowMul f := (Classical.choose_spec
    (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).1
  have hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖ := (Classical.choose_spec
    (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).2.1
  have hf_na : IsNonarchimedean f := (Classical.choose_spec
    (exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional h_fin hna)).2.2
  rw [spectralNorm_eq_iSup_of_finiteDimensional_normal K L hf_pow hf_na hf_ext]
  simp only [invariantExtension_apply, algNormOfAlgEquiv_apply, hf]

/- Note that the main results below are reproved without the finite dimensionality and normality
  assumptions later on in this file. -/

/-- If `L/K` is finite and normal, then `spectralNorm K L` is power-multiplicative.
  See also the more general result `isPowMul_spectralNorm`. -/
/-
**isPowMul_spectralNorm_of_finiteDimensional_normal** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：isPowMul_spectralNorm_of_finiteDimensional_normal [IsUltrametricDist K] : 
IsPowMul (spectralNorm K L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectralNorm_eq_invariantExtension`：spectralNorm_eq_invariantExtension [
hu : IsUltrametricDist K] : spectralNorm K L = invariantExtension K L
· 使用定理 `IsUltrametricDist.isPowMul_invariantExtension`：isPowMul_invariantExtensi
on : IsPowMul (invariantExtension K L)

--- 原说明 ---
If `L/K` is finite and normal, then `spectralNorm K L` is power-multiplicative.
  See also the more general result `isPowMul_spectralNorm`.
-/
theorem isPowMul_spectralNorm_of_finiteDimensional_normal [IsUltrametricDist K] :
    IsPowMul (spectralNorm K L) := by
  rw [spectralNorm_eq_invariantExtension K L]
  exact isPowMul_invariantExtension K L

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The spectral norm is a `K`-algebra norm on `L` when `L/K` is finite and normal.
  See also `spectralAlgNorm` for a more general construction. -/
/-
**spectralAlgNorm_of_finiteDimensional_normal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：spectralAlgNorm_of_finiteDimensional_normal [IsUltrametricDist K] : Algebr
aNorm K L where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The spectral norm is a `K`-algebra norm on `L` when `L/K` is finite and normal.
  See also `spectralAlgNorm` for a more general construction.
-/
def spectralAlgNorm_of_finiteDimensional_normal [IsUltrametricDist K] : AlgebraNorm K L where
  toFun     := spectralNorm K L
  map_zero' := by rw [spectralNorm_eq_invariantExtension K L, map_zero]
  add_le'   := by rw [spectralNorm_eq_invariantExtension]; exact map_add_le_add _
  neg'      := by rw [spectralNorm_eq_invariantExtension]; exact map_neg_eq_map _
  mul_le'   := by
    simp only [spectralNorm_eq_invariantExtension]
    exact map_mul_le_mul (invariantExtension K L)
  smul'     := by
    simp [spectralNorm_eq_invariantExtension, AlgebraNormClass.map_smul_eq_mul _]
  eq_zero_of_map_eq_zero' x := by
    simp only [spectralNorm_eq_invariantExtension]
    exact eq_zero_of_map_eq_zero _
/-
**spectralAlgNorm_of_finiteDimensional_normal_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralAlgNorm_of_finiteDimensional_normal_def [IsUltrametricDist K] (x :
 L) : spectralAlgNorm_of_finiteDimensional_normal K L x = spectralNorm K L x
参数：x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spectralAlgNorm_of_finiteDimensional_normal_def [IsUltrametricDist K] (x : L) :
    spectralAlgNorm_of_finiteDimensional_normal K L x = spectralNorm K L x := rfl

/-- The spectral norm is nonarchimedean when `L/K` is finite and normal.
  See also `isNonarchimedean_spectralNorm` for a more general result. -/
/-
**isNonarchimedean_spectralNorm_of_finiteDimensional_normal** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：isNonarchimedean_spectralNorm_of_finiteDimensional_normal [IsUltrametricDi
st K] : IsNonarchimedean (spectralNorm K L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectralNorm_eq_invariantExtension`：spectralNorm_eq_invariantExtension [
hu : IsUltrametricDist K] : spectralNorm K L = invariantExtension K L
· 使用定理 `IsUltrametricDist.isNonarchimedean_invariantExtension`：isNonarchimedean_
invariantExtension : IsNonarchimedean (invariantExtension K L)

--- 原说明 ---
The spectral norm is nonarchimedean when `L/K` is finite and normal.
  See also `isNonarchimedean_spectralNorm` for a more general result.
-/
theorem isNonarchimedean_spectralNorm_of_finiteDimensional_normal
    [IsUltrametricDist K] : IsNonarchimedean (spectralNorm K L) := by
  rw [spectralNorm_eq_invariantExtension]
  exact isNonarchimedean_invariantExtension K L

/-- The spectral norm extends the norm on `K` when `L/K` is finite and normal.
  See also `spectralNorm_extends` for a more general result. -/
/-
**spectralNorm_extends_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_extends_of_finiteDimensional [IsUltrametricDist K] (x : K) : 
spectralNorm K L (algebraMap K L x) = ‖x‖
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectralNorm_eq_invariantExtension`：spectralNorm_eq_invariantExtension [
hu : IsUltrametricDist K] : spectralNorm K L = invariantExtension K L
· 使用定理 `IsUltrametricDist.invariantExtension_extends`：invariantExtension_extends
 (x : K) : (invariantExtension K L) (algebraMap K L x) = ‖x‖

--- 原说明 ---
The spectral norm extends the norm on `K` when `L/K` is finite and normal.
  See also `spectralNorm_extends` for a more general result.
-/
theorem spectralNorm_extends_of_finiteDimensional [IsUltrametricDist K] (x : K) :
    spectralNorm K L (algebraMap K L x) = ‖x‖ := by
  rw [spectralNorm_eq_invariantExtension, invariantExtension_extends K L x]

/-- If `L/K` is finite and normal, and `f` is a power-multiplicative `K`-algebra norm on `L`
  extending the norm on `K`, then `f = spectralNorm K L`. -/
/-
**spectralNorm_unique_of_finiteDimensional_normal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_unique_of_finiteDimensional_normal {f : AlgebraNorm K L} (hf_
pm : IsPowMul f) (hf_na : IsNonarchimedean f) (hf_ext : forall (x : K), f (algeb
raMap K L x) = ‖x‖₊) (hf_iso : forall (σ : Gal(L/K)) (x : L), f x = f (σ x)) (x 
: L) : f x = spectralNorm K L x
参数：hf_pm : IsPowMul f；hf_na : IsNonarchimedean f；hf_ext : forall (x : K), f (alg
ebraMap K L x) = ‖x‖₊；hf_iso : forall (σ : Gal(L/K)) (x : L), f x = f (σ x)；x : 
L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iSup_congr`：iSup_congr (h : forall i, f i = g i) : ⨆ i, f i = ⨆ i, g i
· 使用定理 `spectralNorm_eq_iSup_of_finiteDimensional_normal`：spectralNorm_eq_iSup_o
f_finiteDimensional_normal {f : AlgebraNorm K L} (hf_pm : IsPowMul f) (hf_na : I
sNonarchimedean f) (hf_ext : forall (x…

--- 原说明 ---
If `L/K` is finite and normal, and `f` is a power-multiplicative `K`-algebra nor
m on `L`
  extending the norm on `K`, then `f = spectralNorm K L`.
-/
theorem spectralNorm_unique_of_finiteDimensional_normal {f : AlgebraNorm K L}
    (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f)
    (hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖₊)
    (hf_iso : ∀ (σ : Gal(L/K)) (x : L), f x = f (σ x)) (x : L) : f x = spectralNorm K L x := by
  have h_sup : (⨆ σ : Gal(L/K), f (σ x)) = f x := by
    rw [← @ciSup_const _ Gal(L/K) _ _ (f x)]
    exact iSup_congr fun σ ↦ by rw [hf_iso σ x]
  rw [spectralNorm_eq_iSup_of_finiteDimensional_normal K L hf_pm hf_na hf_ext, h_sup]

end FiniteNormal

-- Now we let `L/K` be any algebraic extension.

open scoped IntermediateField

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SeminormClass (AlgebraNorm K ↥(normalClosure K (↥E) (AlgebraicClosure ↥E))) K
    ↥(normalClosure K (↥E) (AlgebraicClosure ↥E)) := AlgebraNormClass.toSeminormClass

/-- The spectral norm extends the norm on `K`. -/
/-
**spectralNorm_extends** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_extends (k : K) : spectralNorm K L (algebraMap K L k) = ‖k‖
参数：k : K。
该定理/引理给出了一组等式。
继承自：(k : K) : spectralNorm K L (algebraMap K L k) = ‖k‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.eq_X_sub_C_of_algebraMap_inj`：eq_X_sub_C_of_algebraMap_inj (a : 
A) (hf : Function.Injective (algebraMap A B)) : minpoly A (algebraMap A B a) = X
 - C a
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `spectralValue_X_sub_C`：spectralValue_X_sub_C (r : R) : spectralValue (X 
- C r) = ‖r‖

--- 原说明 ---
The spectral norm extends the norm on `K`.
-/
theorem spectralNorm_extends (k : K) : spectralNorm K L (algebraMap K L k) = ‖k‖ := by
  simp_rw [spectralNorm, minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap K L).injective]
  exact spectralValue_X_sub_C k
/-
**spectralNorm_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_one : spectralNorm K L 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `spectralNorm_extends`：spectralNorm_extends (k : K) : spectralNorm K L (a
lgebraMap K L k) = ‖k‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
-/
theorem spectralNorm_one : spectralNorm K L 1 = 1 := by
  have h1 : (1 : L) = algebraMap K L 1 := by rw [map_one]
  rw [h1, spectralNorm_extends, norm_one]

variable [IsUltrametricDist K]

/-- `spectralNorm K L (-y) = spectralNorm K L y` . -/
/-
**spectralNorm_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_neg {y : L} (hy : IsAlgebraic K y) : spectralNorm K L (-y) = 
spectralNorm K L y
参数：hy : IsAlgebraic K y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `spectralNorm.eq_of_normalClosure`：spectralNorm.eq_of_normalClosure {E : 
IntermediateField K L} {x : L} (g : E) (h_map : algebraMap E L g = x) : spectral
Norm K (normalClosure …
· 使用定理 `IntermediateField.AdjoinSimple.algebraMap_gen`：∀ (F : Type u_1) [inst : 
Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (α : E),   (al
gebraMap (↥F⟮α⟯) E) (IntermediateFi…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `IsAlgClosure.normal`：∀ (R : Type u_1) (K : Type u_2) [inst : Field R] [i
nst_1 : Field K] [inst_2 : Algebra R K] [IsAlgClosure R K],   Normal R K
· 使用定理 `IntermediateField.instIsAlgClosureAlgebraicClosureSubtypeMemOfIsAlgebrai
c`：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 :
 Algebra K L] (E : IntermediateField K L)   [Algebra.IsAlgebrai…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `spectralAlgNorm_of_finiteDimensional_normal_def`：spectralAlgNorm_of_fini
teDimensional_normal_def [IsUltrametricDist K] (x : L) : spectralAlgNorm_of_fini
teDimensional_normal K L x = spectral…
· 使用定理 `AddGroupSeminormClass.map_neg_eq_map`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommMonoid β
}   {inst_2 : PartialOrder…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `instSeminormClassAlgebraNormSubtypeAlgebraicClosureMemIntermediateFieldN
ormalClosure`：∀ {K : Type u_2} [inst : NormedField K] {L : Type u_3} [inst_1 : F
ield L] [inst_2 : Algebra K L]   (E : IntermediateField K L),   SeminormCl…

--- 原说明 ---
`spectralNorm K L (-y) = spectralNorm K L y` .
-/
theorem spectralNorm_neg {y : L} (hy : IsAlgebraic K y) :
    spectralNorm K L (-y) = spectralNorm K L y := by
  set E := K⟮y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  set g := IntermediateField.AdjoinSimple.gen K y
  have hy : -y = (algebraMap K⟮y⟯ L) (-g) := rfl
  rw [← spectralNorm.eq_of_normalClosure g (IntermediateField.AdjoinSimple.algebraMap_gen K y), hy,
    ← spectralNorm.eq_of_normalClosure (-g) hy, map_neg,
    ← spectralAlgNorm_of_finiteDimensional_normal_def]
  exact map_neg_eq_map _ _

/-- The spectral norm is compatible with the action of `K`. -/
/-
**spectralNorm_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_smul (k : K) {y : L} (hy : IsAlgebraic K y) : spectralNorm K 
L (k • y) = ‖k‖₊ * spectralNorm K L y
参数：k : K；hy : IsAlgebraic K y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `normalClosure.instIsScalarTowerSubtypeMemIntermediateFieldNormalClosure`
：∀ (F : Type u_1) (K : Type u_2) (L : Type u_3) [inst : Field F] [inst_1 : Field
 K] [inst_2 : Field L]   [inst_3 : Algebra F K] [inst_4 : Alg…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `spectralNorm.eq_of_normalClosure`：spectralNorm.eq_of_normalClosure {E : 
IntermediateField K L} {x : L} (g : E) (h_map : algebraMap E L g = x) : spectral
Norm K (normalClosure …
· 使用定理 `IntermediateField.AdjoinSimple.algebraMap_gen`：∀ (F : Type u_1) [inst : 
Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (α : E),   (al
gebraMap (↥F⟮α⟯) E) (IntermediateFi…
· 使用定理 `IsAlgClosure.normal`：∀ (R : Type u_1) (K : Type u_2) [inst : Field R] [i
nst_1 : Field K] [inst_2 : Algebra R K] [IsAlgClosure R K],   Normal R K
· 使用定理 `IntermediateField.instIsAlgClosureAlgebraicClosureSubtypeMemOfIsAlgebrai
c`：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 :
 Algebra K L] (E : IntermediateField K L)   [Algebra.IsAlgebrai…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `spectralAlgNorm_of_finiteDimensional_normal_def`：spectralAlgNorm_of_fini
teDimensional_normal_def [IsUltrametricDist K] (x : L) : spectralAlgNorm_of_fini
teDimensional_normal K L x = spectral…
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `instSeminormClassAlgebraNormSubtypeAlgebraicClosureMemIntermediateFieldN
ormalClosure`：∀ {K : Type u_2} [inst : NormedField K] {L : Type u_3} [inst_1 : F
ield L] [inst_2 : Algebra K L]   (E : IntermediateField K L),   SeminormCl…

--- 原说明 ---
The spectral norm is compatible with the action of `K`.
-/
theorem spectralNorm_smul (k : K) {y : L} (hy : IsAlgebraic K y) :
    spectralNorm K L (k • y) = ‖k‖₊ * spectralNorm K L y := by
  set E := K⟮y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  set g := IntermediateField.AdjoinSimple.gen K y
  have hgy : k • y = (algebraMap (↥K⟮y⟯) L) (k • g) := rfl
  have h : algebraMap K⟮y⟯ (normalClosure K K⟮y⟯ (AlgebraicClosure K⟮y⟯)) (k • g) =
      k • algebraMap K⟮y⟯ (normalClosure K K⟮y⟯ (AlgebraicClosure K⟮y⟯)) g := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_assoc]
  rw [← spectralNorm.eq_of_normalClosure g (IntermediateField.AdjoinSimple.algebraMap_gen K y), hgy,
    ← spectralNorm.eq_of_normalClosure (k • g) rfl, h]
  rw [← spectralAlgNorm_of_finiteDimensional_normal_def]
  apply map_smul_eq_mul

/-- The spectral norm is submultiplicative. -/
/-
**spectralNorm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_mul {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
 spectralNorm K L (x * y) <= spectralNorm K L x * spectralNorm K L y
参数：hx : IsAlgebraic K x；hy : IsAlgebraic K y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.finiteDimensional_adjoin_pair`：finiteDimensional_adjoi
n_pair (hx : IsIntegral K x) (hy : IsIntegral K y) : FiniteDimensional K K⟮x, y⟯
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `spectralNorm.eq_of_normalClosure`：spectralNorm.eq_of_normalClosure {E : 
IntermediateField K L} {x : L} (g : E) (h_map : algebraMap E L g = x) : spectral
Norm K (normalClosure …
· 使用定理 `IntermediateField.AdjoinPair.algebraMap_gen₁`：∀ (K : Type u_1) {L : Type
 u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (x y : L),   (a
lgebraMap (↥K⟮x, y⟯) L) (Intermedi…
· 使用定理 `IntermediateField.AdjoinPair.algebraMap_gen₂`：∀ (K : Type u_1) {L : Type
 u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (x y : L),   (a
lgebraMap (↥K⟮x, y⟯) L) (Intermedi…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsAlgClosure.normal`：∀ (R : Type u_1) (K : Type u_2) [inst : Field R] [i
nst_1 : Field K] [inst_2 : Algebra R K] [IsAlgClosure R K],   Normal R K
· 使用定理 `IntermediateField.instIsAlgClosureAlgebraicClosureSubtypeMemOfIsAlgebrai
c`：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 :
 Algebra K L] (E : IntermediateField K L)   [Algebra.IsAlgebrai…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `spectralAlgNorm_of_finiteDimensional_normal_def`：spectralAlgNorm_of_fini
teDimensional_normal_def [IsUltrametricDist K] (x : L) : spectralAlgNorm_of_fini
teDimensional_normal K L x = spectral…
· 使用定理 `SubmultiplicativeHomClass.map_mul_le_mul`：∀ {F : Type u_7} {α : outParam
 (Type u_8)} {β : outParam (Type u_9)} {inst : Mul α} {inst_1 : Mul β} {inst_2 :
 LE β}   {inst_3 : FunLike F α…
· 使用定理 `RingSeminormClass.toSubmultiplicativeHomClass`：∀ {F : Type u_7} {α : out
Param (Type u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {
inst_1 : Semiring β} {inst_2 : Part…
· 使用定理 `RingNormClass.toRingSeminormClass`：∀ {F : Type u_7} {α : outParam (Type 
u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {inst_1 : Sem
iring β} {inst_2 : Part…
· 使用定理 `AlgebraNormClass.toRingNormClass`：∀ {F : Type u_1} {R : outParam (Type u
_2)} {inst : SeminormedCommRing R} {S : outParam (Type u_3)} {inst_1 : Ring S}  
 {inst_2 : Algebra R S…

--- 原说明 ---
The spectral norm is submultiplicative.
-/
theorem spectralNorm_mul {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    spectralNorm K L (x * y) ≤ spectralNorm K L x * spectralNorm K L y := by
  set E := K⟮x, y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  set gx := IntermediateField.AdjoinPair.gen₁ K x y
  set gy := IntermediateField.AdjoinPair.gen₂ K x y
  have hxy : x * y = (algebraMap K⟮x, y⟯ L) (gx * gy) := rfl
  rw [hxy, ← spectralNorm.eq_of_normalClosure (gx * gy) hxy,
    ← spectralNorm.eq_of_normalClosure gx (IntermediateField.AdjoinPair.algebraMap_gen₁ K x y),
    ← spectralNorm.eq_of_normalClosure gy (IntermediateField.AdjoinPair.algebraMap_gen₂ K x y),
    map_mul, ← spectralAlgNorm_of_finiteDimensional_normal_def]
  exact map_mul_le_mul _ _ _

section IsAlgebraic

variable [h_alg : Algebra.IsAlgebraic K L]

/-- The spectral norm is power-multiplicative. -/
/-
**isPowMul_spectralNorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPowMul_spectralNorm : IsPowMul (spectralNorm K L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `spectralNorm.eq_of_normalClosure`：spectralNorm.eq_of_normalClosure {E : 
IntermediateField K L} {x : L} (g : E) (h_map : algebraMap E L g = x) : spectral
Norm K (normalClosure …
· 使用定理 `IntermediateField.AdjoinSimple.algebraMap_gen`：∀ (F : Type u_1) [inst : 
Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (α : E),   (al
gebraMap (↥F⟮α⟯) E) (IntermediateFi…
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `isPowMul_spectralNorm_of_finiteDimensional_normal`：isPowMul_spectralNorm
_of_finiteDimensional_normal [IsUltrametricDist K] : IsPowMul (spectralNorm K L)
· 使用定理 `IsAlgClosure.normal`：∀ (R : Type u_1) (K : Type u_2) [inst : Field R] [i
nst_1 : Field K] [inst_2 : Algebra R K] [IsAlgClosure R K],   Normal R K
· 使用定理 `IntermediateField.instIsAlgClosureAlgebraicClosureSubtypeMemOfIsAlgebrai
c`：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 :
 Algebra K L] (E : IntermediateField K L)   [Algebra.IsAlgebrai…

--- 原说明 ---
The spectral norm is power-multiplicative.
-/
theorem isPowMul_spectralNorm : IsPowMul (spectralNorm K L) := by
  intro x n hn
  set E := K⟮x⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (h_alg.isAlgebraic x).isIntegral
  set g := IntermediateField.AdjoinSimple.gen K x with hg
  have h_map : algebraMap E L g ^ n = x ^ n := rfl
  rw [← spectralNorm.eq_of_normalClosure _ (IntermediateField.AdjoinSimple.algebraMap_gen K x),
    ← spectralNorm.eq_of_normalClosure (g ^ n) h_map, map_pow, ← hg]
  exact isPowMul_spectralNorm_of_finiteDimensional_normal _ _
    ((algebraMap ↥K⟮x⟯ ↥(normalClosure K (↥K⟮x⟯) (AlgebraicClosure ↥K⟮x⟯))) g) hn

/-- The spectral norm is nonarchimedean. -/
/-
**isNonarchimedean_spectralNorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNonarchimedean_spectralNorm : IsNonarchimedean (spectralNorm K L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.finiteDimensional_adjoin_pair`：finiteDimensional_adjoi
n_pair (hx : IsIntegral K x) (hy : IsIntegral K y) : FiniteDimensional K K⟮x, y⟯
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `spectralNorm.eq_of_normalClosure`：spectralNorm.eq_of_normalClosure {E : 
IntermediateField K L} {x : L} (g : E) (h_map : algebraMap E L g = x) : spectral
Norm K (normalClosure …
· 使用定理 `IntermediateField.AdjoinPair.algebraMap_gen₁`：∀ (K : Type u_1) {L : Type
 u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (x y : L),   (a
lgebraMap (↥K⟮x, y⟯) L) (Intermedi…
· 使用定理 `IntermediateField.AdjoinPair.algebraMap_gen₂`：∀ (K : Type u_1) {L : Type
 u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (x y : L),   (a
lgebraMap (↥K⟮x, y⟯) L) (Intermedi…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `isNonarchimedean_spectralNorm_of_finiteDimensional_normal`：isNonarchimed
ean_spectralNorm_of_finiteDimensional_normal [IsUltrametricDist K] : IsNonarchim
edean (spectralNorm K L)
· 使用定理 `IsAlgClosure.normal`：∀ (R : Type u_1) (K : Type u_2) [inst : Field R] [i
nst_1 : Field K] [inst_2 : Algebra R K] [IsAlgClosure R K],   Normal R K
· 使用定理 `IntermediateField.instIsAlgClosureAlgebraicClosureSubtypeMemOfIsAlgebrai
c`：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 :
 Algebra K L] (E : IntermediateField K L)   [Algebra.IsAlgebrai…

--- 原说明 ---
The spectral norm is nonarchimedean.
-/
theorem isNonarchimedean_spectralNorm : IsNonarchimedean (spectralNorm K L) := by
  intro x y
  set E := K⟮x, y⟯
  have h_finiteDimensional_E : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin_pair (h_alg.isAlgebraic x).isIntegral
       (h_alg.isAlgebraic y).isIntegral
  set gx := IntermediateField.AdjoinPair.gen₁ K x y
  set gy := IntermediateField.AdjoinPair.gen₂ K x y
  have hxy : x + y = (algebraMap K⟮x, y⟯ L) (gx + gy) := rfl
  rw [hxy, ← spectralNorm.eq_of_normalClosure (gx + gy) hxy,
    ← spectralNorm.eq_of_normalClosure gx (IntermediateField.AdjoinPair.algebraMap_gen₁ K x y),
    ← spectralNorm.eq_of_normalClosure gy (IntermediateField.AdjoinPair.algebraMap_gen₂ K x y),
    _root_.map_add]
  apply isNonarchimedean_spectralNorm_of_finiteDimensional_normal

set_option linter.style.whitespace false in -- manual alignment is not recognised
variable (K L) in
/-- The spectral norm is a `K`-algebra norm on `L`. -/
/-
**spectralAlgNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：spectralAlgNorm : AlgebraNorm K L where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `spectralNorm_zero`：spectralNorm_zero : spectralNorm K L (0 : L) = 0

--- 原说明 ---
The spectral norm is a `K`-algebra norm on `L`.
-/
def spectralAlgNorm : AlgebraNorm K L where
  toFun       := spectralNorm K L
  map_zero'   := spectralNorm_zero
  add_le' _ _ := IsNonarchimedean.add_le spectralNorm_nonneg isNonarchimedean_spectralNorm
  mul_le' x y := spectralNorm_mul (h_alg.isAlgebraic x) (h_alg.isAlgebraic y)
  smul' k x   := spectralNorm_smul k (h_alg.isAlgebraic x)
  neg' x      := spectralNorm_neg (h_alg.isAlgebraic x)
  eq_zero_of_map_eq_zero' x hx := eq_zero_of_map_spectralNorm_eq_zero hx (h_alg.isAlgebraic x)
/-
**spectralAlgNorm_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralAlgNorm_def (x : L) : spectralAlgNorm K L x = spectralNorm K L x
参数：x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spectralAlgNorm_def (x : L) : spectralAlgNorm K L x = spectralNorm K L x := rfl
/-
**spectralAlgNorm_extends** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralAlgNorm_extends (k : K) : spectralAlgNorm K L (algebraMap K L k) =
 ‖k‖
参数：k : K。
该定理/引理给出了一组等式。
继承自：(k : K) : spectralAlgNorm K L (algebraMap K L k) = ‖k‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectralNorm_extends`：spectralNorm_extends (k : K) : spectralNorm K L (a
lgebraMap K L k) = ‖k‖
-/
theorem spectralAlgNorm_extends (k : K) : spectralAlgNorm K L (algebraMap K L k) = ‖k‖ :=
  spectralNorm_extends k
/-
**spectralAlgNorm_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralAlgNorm_one : spectralAlgNorm K L (1 : L) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectralNorm_one`：spectralNorm_one : spectralNorm K L 1 = 1
-/
theorem spectralAlgNorm_one : spectralAlgNorm K L (1 : L) = 1 := spectralNorm_one
/-
**spectralAlgNorm_isPowMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralAlgNorm_isPowMul : IsPowMul (spectralAlgNorm K L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isPowMul_spectralNorm`：isPowMul_spectralNorm : IsPowMul (spectralNorm K 
L)
-/
theorem spectralAlgNorm_isPowMul : IsPowMul (spectralAlgNorm K L) := isPowMul_spectralNorm

end IsAlgebraic

end NormedField

section NontriviallyNormedField

open IntermediateField

universe u v

variable {K : Type u} [NontriviallyNormedField K] {L : Type v} [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [hu : IsUltrametricDist K]

set_option allowUnsafeReducibility true

/-- If `K` is a field complete with respect to a nontrivial nonarchimedean multiplicative norm and
  `L/K` is an algebraic extension, then any power-multiplicative `K`-algebra norm on `L` coincides
  with the spectral norm. -/
/-
**spectralNorm_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_unique [CompleteSpace K] {f : AlgebraNorm K L} (hf_pm : IsPow
Mul f) : f = spectralAlgNorm K L
参数：hf_pm : IsPowMul f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_powMul_faithful`：eq_of_powMul_faithful (f₁ : AlgebraNorm R S) (hf₁
_pm : IsPowMul f₁) (f₂ : AlgebraNorm R S) (hf₂_pm : IsPowMul f₂) (h_eq : forall 
y : S, exis…
· 使用定理 `spectralAlgNorm_isPowMul`：spectralAlgNorm_isPowMul : IsPowMul (spectralA
lgNorm K L)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
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
· 使用定理 `spectralNorm_zero`：spectralNorm_zero : spectralNorm K L (0 : L) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SubadditiveHomClass.map_add_le_add`：∀ {F : Type u_7} {α : outParam (Type
 u_8)} {β : outParam (Type u_9)} {inst : Add α} {inst_1 : Add β} {inst_2 : LE β}
   {inst_3 : FunLike F α…
· 使用定理 `AddGroupSeminormClass.toSubadditiveHomClass`：∀ {F : Type u_7} {α : outPa
ram (Type u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommM
onoid β}   {inst_2 : PartialOrder…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `AlgebraNormClass.toSeminormClass`：∀ {F : Type u_1} {R : outParam (Type u
_2)} [inst : SeminormedCommRing R] {S : outParam (Type u_3)} [inst_1 : Ring S]  
 [inst_2 : Algebra R S…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddGroupSeminormClass.map_neg_eq_map`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommMonoid β
}   {inst_2 : PartialOrder…
· 使用定理 `SubmultiplicativeHomClass.map_mul_le_mul`：∀ {F : Type u_7} {α : outParam
 (Type u_8)} {β : outParam (Type u_9)} {inst : Mul α} {inst_1 : Mul β} {inst_2 :
 LE β}   {inst_3 : FunLike F α…
· 使用定理 `RingSeminormClass.toSubmultiplicativeHomClass`：∀ {F : Type u_7} {α : out
Param (Type u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {
inst_1 : Semiring β} {inst_2 : Part…
· 使用定理 `RingNormClass.toRingSeminormClass`：∀ {F : Type u_7} {α : outParam (Type 
u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {inst_1 : Sem
iring β} {inst_2 : Part…
· 使用定理 `AlgebraNormClass.toRingNormClass`：∀ {F : Type u_1} {R : outParam (Type u
_2)} {inst : SeminormedCommRing R} {S : outParam (Type u_3)} {inst_1 : Ring S}  
 {inst_2 : Algebra R S…
· 使用定理 `RingNormClass.toAddGroupNormClass`：∀ {F : Type u_7} {α : outParam (Type 
u_8)} {β : outParam (Type u_9)} [inst : NonUnitalNonAssocRing α]   [inst_1 : Sem
iring β] [inst_2 : Part…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
If `K` is a field complete with respect to a nontrivial nonarchimedean multiplic
ative norm and
  `L/K` is an algebraic extension, then any power-multiplicative `K`-algebra nor
m on `L` coincides
  with the spectral norm.
-/
theorem spectralNorm_unique [CompleteSpace K] {f : AlgebraNorm K L} (hf_pm : IsPowMul f) :
    f = spectralAlgNorm K L := by
  apply eq_of_powMul_faithful f hf_pm _ spectralAlgNorm_isPowMul
  intro x
  let E : Type v := id K⟮x⟯
  let : Field E := id <| show Field K⟮x⟯ by infer_instance
  let : Module K E := id <| show Module K K⟮x⟯ by infer_instance
  let id1 : K⟮x⟯ →ₗ[K] E := LinearMap.id
  let id2 : E →ₗ[K] K⟮x⟯ := LinearMap.id
  set hs_norm : RingNorm E :=
    { toFun y := spectralNorm K L (id2 y : L)
      map_zero' := by simp [map_zero, spectralNorm_zero, ZeroMemClass.coe_zero]
      add_le' a b := by
        simp only [← spectralAlgNorm_def]
        exact map_add_le_add _ _ _
      neg' a := by simp [map_neg, NegMemClass.coe_neg, ← spectralAlgNorm_def, map_neg_eq_map]
      mul_le' a b := by
        simp only [← spectralAlgNorm_def]
        exact map_mul_le_mul _ _ _
      eq_zero_of_map_eq_zero' a ha := by
        simpa [id_eq, eq_mpr_eq_cast, cast_eq, LinearMap.coe_mk, ← spectralAlgNorm_def,
          map_eq_zero_iff_eq_zero, ZeroMemClass.coe_eq_zero] using! ha }
  let n1 : NormedRing E := RingNorm.toNormedRing hs_norm
  let N1 : NormedSpace K E :=
    { one_smul e := by simp [one_smul]
      mul_smul k1 k2 e := by simp [mul_smul]
      smul_zero e := by simp
      smul_add k e_1 e_ := by simp [smul_add]
      add_smul k1 k2 e := by simp [add_smul]
      zero_smul e := by simp [zero_smul]
      norm_smul_le k y := by
        change (spectralAlgNorm K L (id2 (k • y) : L) : ℝ) ≤
          ‖k‖ * spectralAlgNorm K L (id2 y : L)
        rw [map_smul, IntermediateField.coe_smul, map_smul_eq_mul] }
  set hf_norm : RingNorm K⟮x⟯ :=
    { toFun y := f ((algebraMap K⟮x⟯ L) y)
      map_zero' := map_zero _
      add_le' a b := map_add_le_add _ _ _
      neg' y := by simp [(algebraMap K⟮x⟯ L).map_neg y]
      mul_le' a b := map_mul_le_mul _ _ _
      eq_zero_of_map_eq_zero' a ha := by
        simpa [map_eq_zero_iff_eq_zero, map_eq_zero] using! ha }
  let n2 : NormedRing K⟮x⟯ := RingNorm.toNormedRing hf_norm
  let N2 : NormedSpace K K⟮x⟯ :=
    { one_smul e := by simp [one_smul]
      mul_smul k1 k2 e := by simp [mul_smul]
      smul_zero e := by simp
      smul_add k e1 e2 := by simp [smul_add]
      add_smul k1 k2 e := by simp [add_smul]
      zero_smul e := by simp [zero_smul]
      norm_smul_le k y := by
        change (f ((algebraMap K⟮x⟯ L) (k • y)) : ℝ) ≤ ‖k‖ * f (algebraMap K⟮x⟯ L y)
        have : (algebraMap (↥K⟮x⟯) L) (k • y) = k • algebraMap (↥K⟮x⟯) L y := by
          simp [IntermediateField.algebraMap_apply]
        rw [this, map_smul_eq_mul] }
  have hKx_fin : FiniteDimensional K ↥K⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have : FiniteDimensional K E := hKx_fin
  set Id1 : K⟮x⟯ →L[K] E := ⟨id1, id1.continuous_of_finiteDimensional⟩
  set Id2 : E →L[K] K⟮x⟯ := ⟨id2, id2.continuous_of_finiteDimensional⟩
  obtain ⟨C1, hC1_pos, hC1⟩ : ∃ C1 : ℝ, 0 < C1 ∧ ∀ y : K⟮x⟯, ‖id1 y‖ ≤ C1 * ‖y‖ :=
    Id1.isBoundedLinearMap.bound
  obtain ⟨C2, hC2_pos, hC2⟩ : ∃ C2 : ℝ, 0 < C2 ∧ ∀ y : E, ‖id2 y‖ ≤ C2 * ‖y‖ :=
    Id2.isBoundedLinearMap.bound
  exact ⟨ C2, C1, hC2_pos, hC1_pos,
    forall_and.mpr ⟨fun y ↦ hC2 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩,
      fun y ↦ hC1 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩⟩⟩

/-- If `K` is a field complete with respect to a nontrivial nonarchimedean multiplicative norm and
  `L/K` is an algebraic extension, then any multiplicative ring norm on `L` extending the norm on
  `K` coincides with the spectral norm. -/
/-
**spectralNorm_unique_field_norm_ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralNorm_unique_field_norm_ext [CompleteSpace K] {f : AbsoluteValue L 
Real} (hf_ext : forall (x : K), f (algebraMap K L x) = ‖x‖) (x : L) : f x = spec
tralNorm K L x
参数：hf_ext : forall (x : K), f (algebraMap K L x) = ‖x‖；x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `MulRingSeminormClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {α : out
Param (Type u_8)} {β : outParam (Type u_9)} [inst : NonAssocRing α] [inst_1 : Se
miring β]   [inst_2 : PartialOrder …
· 使用定理 `MulRingNorm.eq_zero_of_map_eq_zero'`：∀ {R : Type u_2} [inst : NonAssocRi
ng R] (self : MulRingNorm R) (x : R), self.toFun x = 0 → x = 0
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulRingNorm.isPowMul`：isPowMul {A : Type*} [Ring A] (f : MulRingNorm A) 
: IsPowMul f
· 使用定理 `spectralNorm_unique`：spectralNorm_unique [CompleteSpace K] {f : AlgebraN
orm K L} (hf_pm : IsPowMul f) : f = spectralAlgNorm K L
· 使用定理 `spectralAlgNorm_def`：spectralAlgNorm_def (x : L) : spectralAlgNorm K L x
 = spectralNorm K L x

--- 原说明 ---
If `K` is a field complete with respect to a nontrivial nonarchimedean multiplic
ative norm and
  `L/K` is an algebraic extension, then any multiplicative ring norm on `L` exte
nding the norm on
  `K` coincides with the spectral norm.
-/
theorem spectralNorm_unique_field_norm_ext [CompleteSpace K]
    {f : AbsoluteValue L ℝ} (hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖) (x : L) :
    f x = spectralNorm K L x := by
  set g : AlgebraNorm K L :=
    { MulRingNorm.mulRingNormEquivAbsoluteValue.invFun f with
      smul' k x := by
        simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
        rw [Algebra.smul_def, map_mul]
        congr
        rw [← hf_ext k]
        rfl
      mul_le' x y := by simp [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe] }
  have hg_pow : IsPowMul g := MulRingNorm.isPowMul _
  have hgx : f x = g x := rfl
  rw [hgx, spectralNorm_unique hg_pow, spectralAlgNorm_def]

variable (K) in
/-- If `K` is a field complete with respect to a nontrivial nonarchimedean multiplicative norm and
  `L/K` is an algebraic normed field extension, then the norm on `L` coincides with the spectral
  norm. -/
/-
**NormedAlgebra.norm_eq_spectralNorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAlgebra.norm_eq_spectralNorm {L : Type*} [NormedField L] [NormedAlge
bra K L] [Algebra.IsAlgebraic K L] [CompleteSpace K] (x : L) : ‖x‖ = spectralNor
m K L x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NormedAlgebra.toMulAlgebraNorm_apply`：toMulAlgebraNorm_apply (x : L) : t
oMulAlgebraNorm K L x = ‖x‖
· 使用定理 `spectralAlgNorm_def`：spectralAlgNorm_def (x : L) : spectralAlgNorm K L x
 = spectralNorm K L x
· 使用引理 `MulAlgebraNorm.coe_AlgebraNorm`：coe_AlgebraNorm (f : MulAlgebraNorm R S)
 : ⇑(f : AlgebraNorm R S) = ⇑f
· 使用定理 `spectralNorm_unique`：spectralNorm_unique [CompleteSpace K] {f : AlgebraN
orm K L} (hf_pm : IsPowMul f) : f = spectralAlgNorm K L
· 使用定理 `MulRingNorm.isPowMul`：isPowMul {A : Type*} [Ring A] (f : MulRingNorm A) 
: IsPowMul f

--- 原说明 ---
If `K` is a field complete with respect to a nontrivial nonarchimedean multiplic
ative norm and
  `L/K` is an algebraic normed field extension, then the norm on `L` coincides w
ith the spectral
  norm.
-/
theorem NormedAlgebra.norm_eq_spectralNorm {L : Type*} [NormedField L] [NormedAlgebra K L]
    [Algebra.IsAlgebraic K L] [CompleteSpace K] (x : L) : ‖x‖ = spectralNorm K L x := by
  rw [← toMulAlgebraNorm_apply K L x, ← spectralAlgNorm_def, ← MulAlgebraNorm.coe_AlgebraNorm,
      spectralNorm_unique (f := (toMulAlgebraNorm K L).toAlgebraNorm)
      (MulRingNorm.isPowMul (toMulAlgebraNorm K L).toMulRingNorm)]

/-- Given a nonzero `x : L`, and assuming that `(spectralAlgNorm h_alg hna) 1 ≤ 1`, this is
  the real-valued function sending `y ∈ L` to the limit of  `(f (y * x^n))/((f x)^n)`,
  regarded as an algebra norm. -/
/-
**algNormFromConst** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：algNormFromConst (h1 : (spectralAlgNorm K L).toRingSeminorm 1 <= 1) {x : L
} (hx : x != 0) : AlgebraNorm K L
参数：h1 : (spectralAlgNorm K L).toRingSeminorm 1 <= 1；hx : x != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a nonzero `x : L`, and assuming that `(spectralAlgNorm h_alg hna) 1 ≤ 1`, 
this is
  the real-valued function sending `y ∈ L` to the limit of  `(f (y * x^n))/((f x
)^n)`,
  regarded as an algebra norm.
-/
def algNormFromConst (h1 : (spectralAlgNorm K L).toRingSeminorm 1 ≤ 1) {x : L} (hx : x ≠ 0) :
    AlgebraNorm K L :=
  have hx' : spectralAlgNorm K L x ≠ 0 :=
    ne_of_gt (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x))
  { normFromConst h1 hx' spectralAlgNorm_isPowMul with
    smul' k y := by
      have h_mul : ∀ y : L, spectralNorm K L (algebraMap K L k * y) =
          spectralNorm K L (algebraMap K L k) * spectralNorm K L y := fun y ↦ by
        rw [spectralNorm_extends, ← Algebra.smul_def, ← spectralAlgNorm_def,
          map_smul_eq_mul _ _ _, spectralAlgNorm_def]
      have h : spectralNorm K L (algebraMap K L k) =
        seminormFromConst' x (spectralAlgNorm K L).toRingSeminorm (algebraMap K L k) := by
          rw [seminormFromConst_apply_of_isMul h1 hx' spectralAlgNorm_isPowMul h_mul]; rfl
      rw [← @spectralNorm_extends K _ L _ _ k, Algebra.smul_def, h]
      exact seminormFromConst_isMul_of_isMul h1 hx' spectralAlgNorm_isPowMul h_mul y }
/-
**algNormFromConst_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algNormFromConst_def (h1 : (spectralAlgNorm K L).toRingSeminorm 1 <= 1) {x
 y : L} (hx : x != 0) : algNormFromConst h1 hx y = seminormFromConst h1 (ne_of_g
t (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x))) isPowMul_spectr
alNorm y
参数：h1 : (spectralAlgNorm K L).toRingSeminorm 1 <= 1；hx : x != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algNormFromConst_def (h1 : (spectralAlgNorm K L).toRingSeminorm 1 ≤ 1) {x y : L}
    (hx : x ≠ 0) :
    algNormFromConst h1 hx y =
      seminormFromConst h1 (ne_of_gt (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x)))
        isPowMul_spectralNorm y := rfl

section CompleteSpace

variable [CompleteSpace K]

/-- If `K` is a field complete with respect to a nontrivial nonarchimedean multiplicative norm and
  `L/K` is an algebraic extension, then the spectral norm on `L` is multiplicative. -/
/-
**spectralAlgNorm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralAlgNorm_mul (x y : L) : spectralAlgNorm K L (x * y) = spectralAlgN
orm K L x * spectralAlgNorm K L y
参数：x y : L。
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
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `AlgebraNormClass.toSeminormClass`：∀ {F : Type u_1} {R : outParam (Type u
_2)} [inst : SeminormedCommRing R] {S : outParam (Type u_3)} [inst_1 : Ring S]  
 [inst_2 : Algebra R S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `spectralNorm_zero_lt`：spectralNorm_zero_lt {y : L} (hy : y != 0) (hy_alg
 : IsAlgebraic K y) : 0 < spectralNorm K L y
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `spectralAlgNorm_one`：spectralAlgNorm_one : spectralAlgNorm K L (1 : L) =
 1
· 使用定理 `seminormFromConst_isPowMul`：seminormFromConst_isPowMul : IsPowMul (semin
ormFromConst' c f)
· 使用定理 `isPowMul_spectralNorm`：isPowMul_spectralNorm : IsPowMul (spectralNorm K 
L)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `spectralNorm_unique`：spectralNorm_unique [CompleteSpace K] {f : AlgebraN
orm K L} (hf_pm : IsPowMul f) : f = spectralAlgNorm K L
· 使用定理 `seminormFromConst_const_mul`：seminormFromConst_const_mul (x : R) : semin
ormFromConst' c f (c * x) = seminormFromConst' c f c * seminormFromConst' c f x

--- 原说明 ---
If `K` is a field complete with respect to a nontrivial nonarchimedean multiplic
ative norm and
  `L/K` is an algebraic extension, then the spectral norm on `L` is multiplicati
ve.
-/
theorem spectralAlgNorm_mul (x y : L) :
    spectralAlgNorm K L (x * y) = spectralAlgNorm K L x * spectralAlgNorm K L y := by
  by_cases hx : x = 0
  · simp [hx, zero_mul, map_zero]
  · have hx' : spectralAlgNorm K L x ≠ 0 :=
      ne_of_gt (spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic x))
    have hf1 : (spectralAlgNorm K L) 1 ≤ 1 := le_of_eq spectralAlgNorm_one
    set f : AlgebraNorm K L := algNormFromConst hf1 hx with hf
    have hf_pow : IsPowMul f := seminormFromConst_isPowMul hf1 hx' isPowMul_spectralNorm
    rw [← spectralNorm_unique hf_pow, hf]
    exact seminormFromConst_const_mul hf1 hx' isPowMul_spectralNorm _

variable (K L) in
/-- The spectral norm is a multiplicative `K`-algebra norm on `L`. -/
/-
**spectralMulAlgNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：spectralMulAlgNorm : MulAlgebraNorm K L
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `spectralAlgNorm_mul`：spectralAlgNorm_mul (x y : L) : spectralAlgNorm K L
 (x * y) = spectralAlgNorm K L x * spectralAlgNorm K L y

--- 原说明 ---
The spectral norm is a multiplicative `K`-algebra norm on `L`.
-/
def spectralMulAlgNorm : MulAlgebraNorm K L :=
  { spectralAlgNorm K L with
    map_one' := spectralAlgNorm_one
    map_mul' := spectralAlgNorm_mul }
/-
**spectralMulAlgNorm_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectralMulAlgNorm_def (x : L) : spectralMulAlgNorm K L x = spectralNorm K
 L x
参数：x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spectralMulAlgNorm_def (x : L) : spectralMulAlgNorm K L x = spectralNorm K L x := rfl

namespace spectralNorm

variable (K L)

/-- `L` with the spectral norm is a `NormedField`. -/
@[instance_reducible]
/-
**spectralNorm.normedField** 是 Mathlib 中的一个定义，位于命名空间 `spectralNorm`。
形式化陈述：normedField : NormedField L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`L` with the spectral norm is a `NormedField`.
-/
def normedField : NormedField L :=
  { (inferInstance : Field L) with
    norm x := (spectralNorm K L x : ℝ)
    dist x y := (spectralNorm K L (x - y) : ℝ)
    dist_self x := by simp [sub_self, spectralNorm_zero]
    dist_comm x y := by rw [← neg_sub, spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)]
    dist_triangle x y z :=
      sub_add_sub_cancel x y z ▸ isNonarchimedean_spectralNorm.add_le spectralNorm_nonneg
    eq_of_dist_eq_zero hxy := by
      rw [← sub_eq_zero]
      exact (map_eq_zero_iff_eq_zero (spectralMulAlgNorm K L)).mp hxy
    dist_eq x y := by
      rw [← spectralNorm_neg, sub_eq_add_neg, neg_add, neg_neg]
      exact Algebra.IsAlgebraic.isAlgebraic (x - y)
    norm_mul x y := by simp [← spectralMulAlgNorm_def, map_mul]
    edist_dist x y := by rw [ENNReal.ofReal_eq_coe_nnreal] }

/-- `L` with the spectral norm is a `NontriviallyNormedField`. -/
@[instance_reducible]
/-
**spectralNorm.nontriviallyNormedField** 是 Mathlib 中的一个定义，位于命名空间 `spectralNorm`。
形式化陈述：nontriviallyNormedField : NontriviallyNormedField L where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`L` with the spectral norm is a `NontriviallyNormedField`.
-/
def nontriviallyNormedField : NontriviallyNormedField L where
  __ := spectralNorm.normedField K L
  non_trivial :=
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    ⟨algebraMap K L x, hx.trans_eq <| (spectralNorm_extends _).symm⟩

/-- `L` with the spectral norm is a `SeminormedRing`. -/
@[instance_reducible]
/-
**spectralNorm.seminormedRing** 是 Mathlib 中的一个定义，位于命名空间 `spectralNorm`。
形式化陈述：seminormedRing : SeminormedRing L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`L` with the spectral norm is a `SeminormedRing`.
-/
def seminormedRing : SeminormedRing L := by
  letI : NormedField L := normedField K L
  infer_instance

/-- `L` with the spectral norm is a `NormedAddCommGroup`. -/
@[instance_reducible]
/-
**spectralNorm.normedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `spectralNorm`。
形式化陈述：normedAddCommGroup : NormedAddCommGroup L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`L` with the spectral norm is a `NormedAddCommGroup`.
-/
def normedAddCommGroup : NormedAddCommGroup L := by
  haveI : NormedField L := normedField K L
  infer_instance

/-- `L` with the spectral norm is a `SeminormedAddCommGroup`. -/
@[instance_reducible]
/-
**spectralNorm.seminormedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `spectralNorm`。
形式化陈述：seminormedAddCommGroup : SeminormedAddCommGroup L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`L` with the spectral norm is a `SeminormedAddCommGroup`.
-/
def seminormedAddCommGroup : SeminormedAddCommGroup L := by
  have : NormedField L := normedField K L
  infer_instance

/-- `L` with the spectral norm is a `NormedSpace` over `K`. -/
@[instance_reducible]
/-
**spectralNorm.normedSpace** 是 Mathlib 中的一个定义，位于命名空间 `spectralNorm`。
形式化陈述：normedSpace : @NormedSpace K L _ (seminormedAddCommGroup K L)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`L` with the spectral norm is a `NormedSpace` over `K`.
-/
def normedSpace : @NormedSpace K L _ (seminormedAddCommGroup K L) :=
  letI _ := seminormedAddCommGroup K L
  { (inferInstance : Module K L) with
    norm_smul_le r x := by
      change spectralAlgNorm K L (r • x) ≤ ‖r‖ * spectralAlgNorm K L x
      exact le_of_eq (map_smul_eq_mul _ _ _) }

/-- `L` with the spectral norm is a `NormedAlgebra` over `K`. -/
@[instance_reducible]
/-
**spectralNorm.normedAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `spectralNorm`。
形式化陈述：normedAlgebra : @NormedAlgebra K L _ (seminormedRing K L)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`L` with the spectral norm is a `NormedAlgebra` over `K`.
-/
def normedAlgebra :
    @NormedAlgebra K L _ (seminormedRing K L) :=
  letI _ := normedField K L
  { normedSpace K L, (inferInstance : Algebra K L) with }

/-- `L` with the spectral norm is a `NormedAlgebra` over any intermediate `E`
that is a normed algebra over `K`. -/
@[instance_reducible]
/-
**spectralNorm.normedAlgebra'** 是 Mathlib 中的一个定义，位于命名空间 `spectralNorm`。
形式化陈述：normedAlgebra' (E L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic 
K L] [NormedField E] [NormedAlgebra K E] [Algebra E L] [IsScalarTower K E L] : @
NormedAlgebra E L _ (seminormedRing K L)
参数：E L : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`L` with the spectral norm is a `NormedAlgebra` over any intermediate `E`
that is a normed algebra over `K`.
-/
def normedAlgebra' (E L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [NormedField E]
    [NormedAlgebra K E] [Algebra E L] [IsScalarTower K E L] :
    @NormedAlgebra E L _ (seminormedRing K L) :=
  letI _ := normedField K L
  letI _ := normedAlgebra K L
  letI _ := Algebra.IsAlgebraic.tower_bot K E L
  { (inferInstance : Algebra E L) with
    norm_smul_le _ _ := by
      apply le_of_eq
      simp only [Algebra.smul_def, norm_mul, mul_eq_mul_right_iff, _root_.norm_eq_zero]
      simp only [NormedAlgebra.norm_eq_spectralNorm K]
      exact Or.inl <| (spectralNorm.eq_of_tower _).symm }

/-- The metric space structure on `L` induced by the spectral norm. -/
@[instance_reducible]
/-
**spectralNorm.metricSpace** 是 Mathlib 中的一个定义，位于命名空间 `spectralNorm`。
形式化陈述：metricSpace : MetricSpace L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The metric space structure on `L` induced by the spectral norm.
-/
def metricSpace : MetricSpace L := (normedField K L).toMetricSpace

/-- The uniform space structure on `L` induced by the spectral norm. -/
@[instance_reducible]
/-
**spectralNorm.uniformSpace** 是 Mathlib 中的一个定义，位于命名空间 `spectralNorm`。
形式化陈述：uniformSpace : UniformSpace L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniform space structure on `L` induced by the spectral norm.
-/
def uniformSpace : UniformSpace L := (metricSpace K L).toUniformSpace

/-- If `L/K` is finite dimensional, then `L` is a complete space with respect to topology induced
  by the spectral norm. -/
/-
**spectralNorm.** 是 Mathlib 中的一个实例，位于命名空间 `spectralNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L/K` is finite dimensional, then `L` is a complete space with respect to top
ology induced
  by the spectral norm.
-/
instance (priority := 100) completeSpace [h_fin : FiniteDimensional K L] :
    @CompleteSpace L (uniformSpace K L) := by
  let := (normedAddCommGroup K L)
  let := (normedSpace K L)
  exact FiniteDimensional.complete K L

omit [Algebra.IsAlgebraic K L] in
/-
**spectralNorm.spectralMulAlgNorm_eq_of_mem_roots** 是 Mathlib 中的一个引理，位于命名空间 `spe
ctralNorm`。
形式化陈述：spectralMulAlgNorm_eq_of_mem_roots (x : L) {E : Type*} [Field E] [Algebra 
K E] [Algebra L E] [IsScalarTower K L E] [Algebra.IsAlgebraic K E] {a : E} (ha :
 a in ((mapAlg K E) (minpoly K x)).roots) : (spectralMulAlgNorm K E) a = (spectr
alMulAlgNorm K E) ((algebraMap L E) x)
参数：x : L；ha : a in ((mapAlg K E) (minpoly K x)).roots。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.mapAlg_eq_map`：mapAlg_eq_map (S : Type v) [Semiring S] [Algeb
ra R S] (p : R[X]) : mapAlg R S p = map (algebraMap R S) p
· 使用定理 `minpoly.algebraMap_eq`：algebraMap_eq {B} [CommRing B] [Algebra A B] [Alg
ebra B B'] [IsScalarTower A B B'] (h : Function.Injective (algebraMap B B')) (x 
: B) : minp…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `minpoly.eq_of_root`：eq_of_root {x y : L} (hx : IsAlgebraic K x) (h_ev : 
Polynomial.aeval y (minpoly K x) = 0) : minpoly K y = minpoly K x
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
-/
lemma spectralMulAlgNorm_eq_of_mem_roots (x : L) {E : Type*} [Field E] [Algebra K E] [Algebra L E]
    [IsScalarTower K L E] [Algebra.IsAlgebraic K E] {a : E}
    (ha : a ∈ ((mapAlg K E) (minpoly K x)).roots) :
    (spectralMulAlgNorm K E) a = (spectralMulAlgNorm K E) ((algebraMap L E) x) := by
  simp only [spectralMulAlgNorm_def, spectralNorm]
  have : (aeval a) (minpoly K ((algebraMap L E) x)) = 0 := by
    simp only [mem_roots', IsRoot.def] at ha
    rw [← ha.2, mapAlg_eq_map, minpoly.algebraMap_eq (algebraMap L E).injective, aeval_def,
      eval_map]
  rw [← minpoly.eq_of_root (Algebra.IsAlgebraic.isAlgebraic ((algebraMap L E) x)) this]

omit [Algebra.IsAlgebraic K L] in
/-- Given an algebraic tower of fields `E/L/K` and an element `x : L` whose minimal polynomial `f`
  over `K` splits into linear factors over `E`, the `degree(f)`th power of the spectral norm of `x`,
  considered as an element of `E`, is equal to the spectral norm of the product of the `E`-valued
  roots of `f`. -/
/-
**spectralNorm.spectralNorm_pow_natDegree_eq_prod_roots** 是 Mathlib 中的一个定理，位于命名空
间 `spectralNorm`。
形式化陈述：spectralNorm_pow_natDegree_eq_prod_roots (x : L) {E : Type*} [Field E] [Al
gebra K E] [Algebra L E] [IsScalarTower K L E] [IsSplittingField L E (mapAlg K L
 (minpoly K x))] [Algebra.IsAlgebraic K E] : (spectralMulAlgNorm K E) ((algebraM
ap L E) x) ^ (minpoly K x).natDegree = (spectralMulAlgNorm K E) ((mapAlg K E) (m
inpoly K x)).roots.prod
参数：x : L；mapAlg K L (minpoly K x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mapAlg_eq_map`：mapAlg_eq_map (S : Type v) [Semiring S] [Algeb
ra R S] (p : R[X]) : mapAlg R S p = map (algebraMap R S) p
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.splits_iff_card_roots`：splits_iff_card_roots : Splits f ↔ f.r
oots.card = f.natDegree
· 使用定理 `Polynomial.IsSplittingField.IsScalarTower.splits`：∀ {F : Type u} {K : Ty
pe v} (L : Type w) [inst : Field K] [inst_1 : Field L] [inst_2 : Field F] [inst_
3 : Algebra K L]   [inst_4 : Algebra F…
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `MulRingSeminormClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {α : out
Param (Type u_8)} {β : outParam (Type u_9)} [inst : NonAssocRing α] [inst_1 : Se
miring β]   [inst_2 : PartialOrder …
· 使用定理 `MulRingNormClass.toMulRingSeminormClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : NonAssocRing α} {inst_1 : Semiring
 β}   {inst_2 : PartialOrder …
· 使用定理 `MulAlgebraNormClass.toMulRingNormClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {inst : SeminormedCommRing R} {S : outParam (Type u_3)} {inst_1 : Rin
g S}   {inst_2 : Algebra R S…
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `Multiset.count_replicate`：count_replicate (a b : α) (n : Nat) : count a 
(replicate n b) = if b = a then n else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用引理 `spectralNorm.spectralMulAlgNorm_eq_of_mem_roots`：spectralMulAlgNorm_eq_o
f_mem_roots (x : L) {E : Type*} [Field E] [Algebra K E] [Algebra L E] [IsScalarT
ower K L E] [Algebra.IsAlgebraic K E]…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.count_eq_card`：count_eq_card {a : α} {s} : count a s = card s ↔
 forall x in s, a = x
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0

--- 原说明 ---
Given an algebraic tower of fields `E/L/K` and an element `x : L` whose minimal 
polynomial `f`
  over `K` splits into linear factors over `E`, the `degree(f)`th power of the s
pectral norm of `x`,
  considered as an element of `E`, is equal to the spectral norm of the product 
of the `E`-valued
  roots of `f`.
-/
theorem spectralNorm_pow_natDegree_eq_prod_roots (x : L) {E : Type*} [Field E] [Algebra K E]
    [Algebra L E] [IsScalarTower K L E] [IsSplittingField L E (mapAlg K L (minpoly K x))]
    [Algebra.IsAlgebraic K E] :
    (spectralMulAlgNorm K E) ((algebraMap L E) x) ^ (minpoly K x).natDegree =
      (spectralMulAlgNorm K E) ((mapAlg K E) (minpoly K x)).roots.prod := by
  have h_deg : (minpoly K x).natDegree = Multiset.card ((mapAlg K E) (minpoly K x)).roots := by
    trans (mapAlg K E (minpoly K x)).natDegree
    · rw [mapAlg_eq_map, natDegree_map]
    · rw [eq_comm, ← splits_iff_card_roots]
      exact IsSplittingField.IsScalarTower.splits (K := L) E (minpoly K x)
  rw [map_multiset_prod, ← Multiset.prod_replicate]
  apply congr_arg
  ext r
  rw [Multiset.count_replicate]
  split_ifs with hr
  · have h : ∀ s ∈ Multiset.map (spectralMulAlgNorm K E) ((mapAlg K E) (minpoly K x)).roots,
        r = s := by
      intro s hs
      obtain ⟨a, ha, has⟩ := Multiset.mem_map.mp hs
      rw [← hr, ← has, spectralMulAlgNorm_eq_of_mem_roots K L x ha]
    rwa [Multiset.count_eq_card.mpr h, Multiset.card_map]
  · rw [Multiset.count_eq_zero_of_notMem]
    intro hr_mem
    obtain ⟨e, he, her⟩ := Multiset.mem_map.mp hr_mem
    rw [spectralMulAlgNorm_eq_of_mem_roots K L x he] at her
    exact hr her

/-- For `x : L` with minimal polynomial `f(X) := X^n + a_{n-1}X^{n-1} + ... + a_0` over `K`,
  the spectral norm of `x` is equal to `‖a_0‖^(1/(degree(f(X))))`. -/
/-
**spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow** 是 Mathlib 中的一个定理，位于命名空间 `s
pectralNorm`。
形式化陈述：spectralNorm_eq_norm_coeff_zero_rpow (x : L) : spectralNorm K L x = ‖(minp
oly K x).coeff 0‖ ^ (1 / (minpoly K x).natDegree : Real)
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsSplittingField.IsScalarTower.splits`：∀ {F : Type u} {K : Ty
pe v} (L : Type w) [inst : Field K] [inst_1 : Field L] [inst_2 : Field F] [inst_
3 : Algebra K L]   [inst_4 : Algebra F…
· 使用定理 `Polynomial.SplittingField.instIsScalarTower`：∀ {K : Type u_2} [inst : Fi
eld K] (f : Polynomial K) {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Alg
ebra R K],   IsScalarTower R K f.…
· 使用定理 `Polynomial.IsSplittingField.splittingField`：∀ {K : Type v} [inst : Field
 K] (f : Polynomial K), Polynomial.IsSplittingField K f.SplittingField f
· 使用定理 `Polynomial.IsSplittingField.IsScalarTower.isAlgebraic`：∀ {F : Type u} {K
 : Type v} (L : Type w) [inst : Field K] [inst_1 : Field L] [inst_2 : Field F] [
inst_3 : Algebra K L]   [inst_4 : Algebra F…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.IsAlgebraic.trans`：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3
) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebr
a R S] [inst_4 …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `Real.eq_rpow_inv`：eq_rpow_inv (hx : 0 <= x) (hy : 0 <= y) (hz : z != 0) 
: x = y ^ z⁻¹ ↔ x ^ z = y
· 使用定理 `spectralNorm_nonneg`：spectralNorm_nonneg (y : L) : 0 <= spectralNorm K L
 y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `minpoly.natDegree_pos`：natDegree_pos [Nontrivial B] (hx : IsIntegral A x
) : 0 < natDegree (minpoly A x)
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `spectralNorm.eq_of_tower`：spectralNorm.eq_of_tower {E : Type*} [Field E]
 [Algebra K E] [Algebra E L] [IsScalarTower K E L] (x : E) : spectralNorm K E x 
= spectralNorm…
· 使用定理 `spectralNorm_extends`：spectralNorm_extends (k : K) : spectralNorm K L (a
lgebraMap K L k) = ‖k‖
· 使用定理 `spectralMulAlgNorm_def`：spectralMulAlgNorm_def (x : L) : spectralMulAlgN
orm K L x = spectralNorm K L x
· 使用定理 `Polynomial.coeff_zero_of_isScalarTower`：coeff_zero_of_isScalarTower (p :
 A[X]) : (algebraMap B C) ((algebraMap A B) (p.coeff 0)) = (mapAlg A C p).coeff 
0
· 使用定理 `Polynomial.Splits.coeff_zero_eq_prod_roots_of_monic`：∀ {R : Type u_1} [i
nst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f.Monic
 → f.coeff 0 = (-1) ^ f.natDegree * f.roo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
For `x : L` with minimal polynomial `f(X) := X^n + a_{n-1}X^{n-1} + ... + a_0` o
ver `K`,
  the spectral norm of `x` is equal to `‖a_0‖^(1/(degree(f(X))))`.
-/
theorem spectralNorm_eq_norm_coeff_zero_rpow (x : L) :
    spectralNorm K L x = ‖(minpoly K x).coeff 0‖ ^ (1 / (minpoly K x).natDegree : ℝ) := by
  set E := (mapAlg K L (minpoly K x)).SplittingField
  have hspl : Splits (mapAlg K E (minpoly K x)) :=
    IsSplittingField.IsScalarTower.splits (K := L) E (minpoly K x)
  have : Algebra.IsAlgebraic L E :=
    IsSplittingField.IsScalarTower.isAlgebraic E (mapAlg K L (minpoly K x))
  have : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.trans K L E
  rw [one_div, Real.eq_rpow_inv (spectralNorm_nonneg x) (norm_nonneg ((minpoly K x).coeff 0)),
    Real.rpow_natCast, @spectralNorm.eq_of_tower K _ E,
    ← @spectralNorm_extends K _ L _ _ ((minpoly K x).coeff 0),
    @spectralNorm.eq_of_tower K _ E _ _ L, ← spectralMulAlgNorm_def,
    ← spectralMulAlgNorm_def, Polynomial.coeff_zero_of_isScalarTower,
    hspl.coeff_zero_eq_prod_roots_of_monic _, map_mul, map_pow,
    map_neg_eq_map, map_one, one_pow, one_mul, spectralNorm_pow_natDegree_eq_prod_roots _ _ x]
  · simp [monic_mapAlg_iff, minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral]
  · exact_mod_cast (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne'

end spectralNorm

end CompleteSpace

end NontriviallyNormedField

end spectralNorm

