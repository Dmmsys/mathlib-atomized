/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Data.Int.WithZero
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ExtendToLocalization
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Adic valuations on Dedekind domains

Given a Dedekind domain `R` of Krull dimension 1 and a maximal ideal `v` of `R`, we define the
`v`-adic valuation on `R` and its extension to the field of fractions `K` of `R`.
We prove several properties of this valuation, including the existence of uniformizers.

We define the completion of `K` with respect to the `v`-adic valuation, denoted
`v.adicCompletion`, and its ring of integers, denoted `v.adicCompletionIntegers`.

## Main definitions
- `IsDedekindDomain.HeightOneSpectrum.intValuation v` is the `v`-adic valuation on `R`.
- `IsDedekindDomain.HeightOneSpectrum.valuation v` is the `v`-adic valuation on `K`.
- `IsDedekindDomain.HeightOneSpectrum.adicCompletion v` is the completion of `K` with respect
  to its `v`-adic valuation.
- `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers v` is the ring of integers of
  `v.adicCompletion`.
- `IsDedekindDomain.HeightOneSpectrum.adicAbv v` is the `v`-adic absolute value on `K` defined as
  `b` raised to negative `v`-adic valuation, for some `b` in `ℝ≥0`.

## Main results
- `IsDedekindDomain.HeightOneSpectrum.intValuation_le_one` : The `v`-adic valuation on `R` is
  bounded above by 1.
- `IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd` : The `v`-adic valuation of
  `r : R` is less than 1 if and only if `v` divides the ideal `(r)`.
- `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd` : The `v`-adic valuation of
  `r : R` is less than or equal to `WithZero.exp (-n)` if and only if `vⁿ` divides the
  ideal `(r)`.
- `IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer` : There exists `π : R`
  with `v`-adic valuation `WithZero.exp (-1)`.
- `IsDedekindDomain.HeightOneSpectrum.valuation_of_mk'` : The `v`-adic valuation of `r / s : K`
  is the valuation of `r` divided by the valuation of `s`.
- `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap` : The `v`-adic valuation on `K`
  extends the `v`-adic valuation on `R`.
- `IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer` : There exists `π : K` with
  `v`-adic valuation `WithZero.exp (-1)`.

## Implementation notes
We are only interested in Dedekind domains with Krull dimension 1.

## References
* [G. J. Janusz, *Algebraic Number Fields*][janusz1996]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags
dedekind domain, dedekind ring, adic valuation
-/

@[expose] public section

noncomputable section

open WithZero Multiplicative IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K S : Type*} [Field K] [CommSemiring S]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

namespace IsDedekindDomain.HeightOneSpectrum

/-! ### Adic valuations on the Dedekind domain R -/

open scoped Classical in
/-- The additive `v`-adic valuation of `r : R` is the exponent of `v` in the factorization of the
ideal `(r)`, if `r` is nonzero, or infinity, if `r = 0`. `intValuationDef` is the corresponding
multiplicative valuation. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuationDef** 是 Mathlib 中的一个定义，位于命名空间 `
IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuationDef (r : R) : Intᵐ⁰
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive `v`-adic valuation of `r : R` is the exponent of `v` in the factori
zation of the
ideal `(r)`, if `r` is nonzero, or infinity, if `r = 0`. `intValuationDef` is th
e corresponding
multiplicative valuation.
-/
def intValuationDef (r : R) : ℤᵐ⁰ :=
  if r = 0 then 0
  else
    exp (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ)
/-
**IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_pos** 是 Mathlib 中的一个定理，位
于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuationDef_if_pos {r : R} (hr : r = 0) : v.intValuationDef r = 0
参数：hr : r = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem intValuationDef_if_pos {r : R} (hr : r = 0) : v.intValuationDef r = 0 :=
  if_pos hr

@[simp]
/-
**IsDedekindDomain.HeightOneSpectrum.intValuationDef_zero** 是 Mathlib 中的一个定理，位于命
名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuationDef_zero : v.intValuationDef 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem intValuationDef_zero : v.intValuationDef 0 = 0 :=
  if_pos rfl
/-
**IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_neg** 是 Mathlib 中的一个定理，位
于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuationDef_if_neg {r : R} (hr : r != 0) : v.intValuationDef r = exp (
-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).fact
ors : Int)
参数：hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem intValuationDef_if_neg {r : R} (hr : r ≠ 0) :
    v.intValuationDef r = exp
        (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ) :=
  if_neg hr

/-- The `v`-adic valuation of `0 : R` equals 0. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation.map_zero'** 是 Mathlib 中的一个定理，位
于命名空间 `IsDedekindDomain.HeightOneSpectrum.intValuation`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : Is
DedekindDomain.HeightOneSpectrum R),   v.intValuationDef 0 = 0
参数：v : IsDedekindDomain.HeightOneSpectrum R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_pos`：intValuationD
ef_if_pos {r : R} (hr : r = 0) : v.intValuationDef r = 0

--- 原说明 ---
The `v`-adic valuation of `0 : R` equals 0.
-/
theorem intValuation.map_zero' : v.intValuationDef 0 = 0 :=
  v.intValuationDef_if_pos rfl

/-- The `v`-adic valuation of `1 : R` equals 1. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation.map_one'** 是 Mathlib 中的一个定理，位于
命名空间 `IsDedekindDomain.HeightOneSpectrum.intValuation`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : Is
DedekindDomain.HeightOneSpectrum R),   v.intValuationDef 1 = 1
参数：v : IsDedekindDomain.HeightOneSpectrum R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_neg`：intValuationD
ef_if_neg {r : R} (hr : r != 0) : v.intValuationDef r = exp (-(Associates.mk v.a
sIdeal).count (Associates.mk (Ideal.span {r} : …
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.span_singleton_one`：span_singleton_one : span ({1} : Set α) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Associates.mk_one`：mk_one [Monoid M] : Associates.mk (1 : M) = 1
· 使用定理 `Associates.factors_one`：factors_one [Nontrivial α] : factors (1 : Associ
ates α) = 0
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `Associates.count_zero`：count_zero (hp : Irreducible p) : count p (0 : Fa
ctorSet α) = 0
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.associates_irreducible`：associates_ir
reducible : Irreducible Associates.mk v.asIdeal
· 使用定理 `Int.ofNat_zero`：↑0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `WithZero.exp_zero`：∀ {M : Type u_4} [inst : AddMonoid M], WithZero.exp 0
 = 1

--- 原说明 ---
The `v`-adic valuation of `1 : R` equals 1.
-/
theorem intValuation.map_one' : v.intValuationDef 1 = 1 := by
  rw [v.intValuationDef_if_neg one_ne_zero, Ideal.span_singleton_one, ← Ideal.one_eq_top,
    Associates.mk_one, Associates.factors_one, Associates.count_zero v.associates_irreducible,
    Int.ofNat_zero, neg_zero, exp_zero]

/-- The `v`-adic valuation of a product equals the product of the valuations. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation.map_mul'** 是 Mathlib 中的一个定理，位于
命名空间 `IsDedekindDomain.HeightOneSpectrum.intValuation`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : Is
DedekindDomain.HeightOneSpectrum R) (x y : R),   v.intValuationDef (x * y) = v.i
ntValuationDef x * v.intValuationDef y
参数：v : IsDedekindDomain.HeightOneSpectrum R；x y : R；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.exp_add`：∀ {M : Type u_4} [inst : AddMonoid M] (a b : M), WithZ
ero.exp (a + b) = WithZero.exp a * WithZero.exp b
· 使用定理 `Ideal.span_singleton_mul_span_singleton`：span_singleton_mul_span_singlet
on (r s : R) [(span {r}).IsTwoSided] : span {r} * span {s} = (span {r * s} : Ide
al R)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Associates.mk_mul_mk`：mk_mul_mk {x y : M} : Associates.mk x * Associates
.mk y = Associates.mk (x * y)
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Associates.count_mul`：count_mul {a : Associates α} (ha : a != 0) {b : As
sociates α} (hb : b != 0) {p : Associates α} (hp : Irreducible p) : count p (fac
tors (a * …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.mk_ne_zero'`：Associates.mk_ne_zero' {R : Type*} [CommSemiring
 R] {r : R} : Associates.mk (Ideal.span {r} : Ideal R) != 0 ↔ r != 0
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.associates_irreducible`：associates_ir
reducible : Irreducible Associates.mk v.asIdeal
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n

--- 原说明 ---
The `v`-adic valuation of a product equals the product of the valuations.
-/
theorem intValuation.map_mul' (x y : R) :
    v.intValuationDef (x * y) = v.intValuationDef x * v.intValuationDef y := by
  simp only [intValuationDef]
  by_cases hx : x = 0
  · rw [hx, zero_mul, if_pos rfl, zero_mul]
  · by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos rfl, mul_zero]
    · rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← exp_add,
        ← Ideal.span_singleton_mul_span_singleton, ← Associates.mk_mul_mk, ← neg_add,
        Associates.count_mul (Associates.mk_ne_zero'.mpr hx) (Associates.mk_ne_zero'.mpr hy)
          v.associates_irreducible,
        Nat.cast_add]

-- TODO: unused, this is general over any linear order
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation.le_max_iff_min_le** 是 Mathlib 
中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.intValuation`。
形式化陈述：∀ {a b c : ℕ}, Multiplicative.ofAdd (-↑c) ≤ max (Multiplicative.ofAdd (-↑a
)) (Multiplicative.ofAdd (-↑b)) ↔ min a b ≤ c
参数：-↑c；Multiplicative.ofAdd (-↑a)；Multiplicative.ofAdd (-↑b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `Multiplicative.ofAdd_le`：ofAdd_le {a b : α} : ofAdd a <= ofAdd b ↔ a <= 
b
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.ofNat_le`：∀ {m n : ℕ}, ↑m ≤ ↑n ↔ m ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `min_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, min b c ≤
 a ↔ b ≤ a ∨ c ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem intValuation.le_max_iff_min_le {a b c : ℕ} :
    Multiplicative.ofAdd (-c : ℤ) ≤
      max (Multiplicative.ofAdd (-a : ℤ)) (Multiplicative.ofAdd (-b : ℤ)) ↔
      min a b ≤ c := by
  rw [le_max_iff, ofAdd_le, ofAdd_le, neg_le_neg_iff, neg_le_neg_iff, Int.ofNat_le, Int.ofNat_le,
    ← min_le_iff]

/-- The `v`-adic valuation of a sum is bounded above by the maximum of the valuations. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation.map_add_le_max'** 是 Mathlib 中的
一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.intValuation`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : Is
DedekindDomain.HeightOneSpectrum R) (x y : R),   v.intValuationDef (x + y) ≤ max
 (v.intValuationDef x) (v.intValuationDef y)
参数：v : IsDedekindDomain.HeightOneSpectrum R；x y : R；x + y；v.intValuationDef x；v.
intValuationDef y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuationDef.eq_1`：∀ {R : Type u_1
} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : IsDedekindDomain.Height
OneSpectrum R) (r : R),   v.intValuationDef r…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_neg`：intValuationD
ef_if_neg {r : R} (hr : r != 0) : v.intValuationDef r = exp (-(Associates.mk v.a
sIdeal).count (Associates.mk (Ideal.span {r} : …
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.le_singleton_iff`：Associates.le_singleton_iff (x : A) (n : Na
t) (I : Ideal A) : Associates.mk I ^ n <= Associates.mk (Ideal.span {x}) ↔ x in 
I ^ n
· 使用定理 `Associates.prime_pow_dvd_iff_le`：prime_pow_dvd_iff_le {m p : Associates 
α} (h₁ : m != 0) (h₂ : Irreducible p) {k : Nat} : p ^ k <= m ↔ k <= count p m.fa
ctors
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.mk_ne_zero'`：Associates.mk_ne_zero' {R : Type*} [CommSemiring
 R] {r : R} : Associates.mk (Ideal.span {r} : Ideal R) != 0 ↔ r != 0
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.associates_irreducible`：associates_ir
reducible : Irreducible Associates.mk v.asIdeal
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I

--- 原说明 ---
The `v`-adic valuation of a sum is bounded above by the maximum of the valuation
s.
-/
theorem intValuation.map_add_le_max' (x y : R) :
    v.intValuationDef (x + y) ≤ max (v.intValuationDef x) (v.intValuationDef y) := by
  by_cases hx : x = 0
  · rw [hx, zero_add]
    order
  · by_cases hy : y = 0
    · rw [hy, add_zero]
      order
    · by_cases hxy : x + y = 0
      · rw [intValuationDef, if_pos hxy]; exact zero_le
      · rw [v.intValuationDef_if_neg hxy, v.intValuationDef_if_neg hx, v.intValuationDef_if_neg hy,
          le_max_iff]
        simp only [exp_le_exp, neg_le_neg_iff, Nat.cast_le, ← min_le_iff]
        set nmin :=
          min ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {x})).factors)
            ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {y})).factors)
        have h_dvd_x : x ∈ v.asIdeal ^ nmin := by
          rw [← Associates.le_singleton_iff x nmin _,
            Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hx) _]
          · exact min_le_left _ _
          exact v.associates_irreducible
        have h_dvd_y : y ∈ v.asIdeal ^ nmin := by
          rw [← Associates.le_singleton_iff y nmin _,
            Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hy) _]
          · exact min_le_right _ _
          exact v.associates_irreducible
        have h_dvd_xy : Associates.mk v.asIdeal ^ nmin ≤ Associates.mk (Ideal.span {x + y}) := by
          rw [Associates.le_singleton_iff]
          exact Ideal.add_mem (v.asIdeal ^ nmin) h_dvd_x h_dvd_y
        rw [Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hxy) _] at h_dvd_xy
        · exact h_dvd_xy
        exact v.associates_irreducible

/-- The `v`-adic valuation on `R`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation** 是 Mathlib 中的一个定义，位于命名空间 `IsD
edekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation : Valuation R Intᵐ⁰ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation.map_zero'`：∀ {R : Type u
_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : IsDedekindDomain.Heig
htOneSpectrum R),   v.intValuationDef 0 = 0
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation.map_one'`：∀ {R : Type u_
1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : IsDedekindDomain.Heigh
tOneSpectrum R),   v.intValuationDef 1 = 1
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation.map_mul'`：∀ {R : Type u_
1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : IsDedekindDomain.Heigh
tOneSpectrum R) (x y : R),   v.intValuationDef…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation.map_add_le_max'`：∀ {R : 
Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : IsDedekindDomai
n.HeightOneSpectrum R) (x y : R),   v.intValuationDef…

--- 原说明 ---
The `v`-adic valuation on `R`.
-/
def intValuation : Valuation R ℤᵐ⁰ where
  toFun := v.intValuationDef
  map_zero' := intValuation.map_zero' v
  map_one' := intValuation.map_one' v
  map_mul' := intValuation.map_mul' v
  map_add_le_max' := intValuation.map_add_le_max' v
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_apply** 是 Mathlib 中的一个定理，位于命名空
间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_apply {r : R} (v : IsDedekindDomain.HeightOneSpectrum R) : in
tValuation v r = intValuationDef v r
参数：v : IsDedekindDomain.HeightOneSpectrum R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem intValuation_apply {r : R} (v : IsDedekindDomain.HeightOneSpectrum R) :
    intValuation v r = intValuationDef v r := rfl

open scoped Classical in
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_def** 是 Mathlib 中的一个定理，位于命名空间 
`IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_def {r : R} : v.intValuation r = if r = 0 then 0 else exp (-(
Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factor
s : Int)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem intValuation_def {r : R} :
    v.intValuation r = if r = 0 then 0 else
    exp (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ) :=
  rfl
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg** 是 Mathlib 中的一个定理，位于命名
空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_if_neg {r : R} (hr : r != 0) : v.intValuation r = exp (-(Asso
ciates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : 
Int)
参数：hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_neg`：intValuationD
ef_if_neg {r : R} (hr : r != 0) : v.intValuationDef r = exp (-(Associates.mk v.a
sIdeal).count (Associates.mk (Ideal.span {r} : …
-/
theorem intValuation_if_neg {r : R} (hr : r ≠ 0) :
    v.intValuation r = exp
        (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ) :=
  intValuationDef_if_neg _ hr
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity** 是 Ma
thlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_eq_exp_neg_multiplicity {r : R} (hr : r != 0) : v.intValuatio
n r = exp (-multiplicity v.asIdeal (Ideal.span {r}) : Int)
参数：hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.span_singleton_eq_bot`：span_singleton_eq_bot : R ∙ x = ⊥ ↔ x =
 0
· 使用定理 `FiniteMultiplicity.of_prime_left`：FiniteMultiplicity.of_prime_left [Comm
MonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α] {a b : α} (ha : Prime a) (
hb : b != 0) : FiniteM…
· 使用定理 `instWfDvdMonoidIdeal`：∀ {A : Type u_2} [inst : CommRing A] [IsDedekindDo
main A], WfDvdMonoid (Ideal A)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.prime`：prime : Prime v.asIdeal
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg`：intValuation_if_
neg {r : R} (hr : r != 0) : v.intValuation r = exp (-(Associates.mk v.asIdeal).c
ount (Associates.mk (Ideal.span {r} : Ideal …
· 使用定理 `WithZero.exp_inj`：∀ {M : Type u_4} {x y : M}, WithZero.exp x = WithZero.
exp y ↔ x = y
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_inj`：natCast_inj {a b : Nat} : (a : Nat∞) = b ↔ a = b
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.irreducible`：irreducible : Irreducibl
e v.asIdeal
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `Ideal.count_associates_factors_eq`：count_associates_factors_eq {I J : Id
eal R} (hI : I != 0) (hJ : J.IsPrime) (hJ₀ : J != ⊥) : (Associates.mk J).count (
Associates.mk I).factor…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
-/
theorem intValuation_eq_exp_neg_multiplicity {r : R} (hr : r ≠ 0) :
    v.intValuation r = exp (-multiplicity v.asIdeal (Ideal.span {r}) : ℤ) := by
  have hsr : Ideal.span {r} ≠ 0 := Submodule.span_singleton_eq_bot.mp.mt hr
  have hfm : FiniteMultiplicity v.asIdeal (Ideal.span {r}) :=
    FiniteMultiplicity.of_prime_left v.prime hsr
  rw [v.intValuation_if_neg hr, exp_inj, neg_inj, Int.natCast_inj, ← ENat.natCast_inj,
    ← FiniteMultiplicity.emultiplicity_eq_multiplicity hfm,
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors (irreducible v) hsr,
    normalize_eq, Ideal.count_associates_factors_eq hsr v.isPrime v.ne_bot]

/-- Nonzero elements have nonzero adic valuation. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero** 是 Mathlib 中的一个定理，位于命
名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_ne_zero (x : R) (hx : x != 0) : v.intValuation x != 0
参数：x : R；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg`：intValuation_if_
neg {r : R} (hr : r != 0) : v.intValuation r = exp (-(Associates.mk v.asIdeal).c
ount (Associates.mk (Ideal.span {r} : Ideal …
· 使用定理 `WithZero.coe_ne_zero`：∀ {α : Type u} {a : α}, ↑a ≠ 0

--- 原说明 ---
Nonzero elements have nonzero adic valuation.
-/
theorem intValuation_ne_zero (x : R) (hx : x ≠ 0) : v.intValuation x ≠ 0 := by
  rw [v.intValuation_if_neg hx]
  exact WithZero.coe_ne_zero

/-- Nonzero divisors have nonzero valuation. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero'** 是 Mathlib 中的一个定理，位于
命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_ne_zero' (x : nonZeroDivisors R) : v.intValuation x != 0
参数：x : nonZeroDivisors R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero`：intValuation_ne
_zero (x : R) (hx : x != 0) : v.intValuation x != 0
· 使用定理 `nonZeroDivisors.coe_ne_zero`：nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x 
: M₀) != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A

--- 原说明 ---
Nonzero divisors have nonzero valuation.
-/
theorem intValuation_ne_zero' (x : nonZeroDivisors R) : v.intValuation x ≠ 0 :=
  v.intValuation_ne_zero x (nonZeroDivisors.coe_ne_zero x)

/-- Nonzero divisors have valuation greater than zero. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_zero_lt** 是 Mathlib 中的一个定理，位于命
名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_zero_lt (x : nonZeroDivisors R) : 0 < v.intValuation x
参数：x : nonZeroDivisors R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg`：intValuation_if_
neg {r : R} (hr : r != 0) : v.intValuation r = exp (-(Associates.mk v.asIdeal).c
ount (Associates.mk (Ideal.span {r} : Ideal …
· 使用定理 `nonZeroDivisors.coe_ne_zero`：nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x 
: M₀) != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `WithZero.zero_lt_coe`：∀ {α : Type u_1} [inst : LT α] (a : α), 0 < ↑a

--- 原说明 ---
Nonzero divisors have valuation greater than zero.
-/
theorem intValuation_zero_lt (x : nonZeroDivisors R) : 0 < v.intValuation x := by
  rw [v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero x)]
  exact WithZero.zero_lt_coe _

/-- The `v`-adic valuation on `R` is bounded above by 1. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_le_one** 是 Mathlib 中的一个定理，位于命名
空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_le_one (x : R) : v.intValuation x <= 1
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg`：intValuation_if_
neg {r : R} (hr : r != 0) : v.intValuation r = exp (-(Associates.mk v.asIdeal).c
ount (Associates.mk (Ideal.span {r} : Ideal …
· 使用定理 `WithZero.exp_zero`：∀ {M : Type u_4} [inst : AddMonoid M], WithZero.exp 0
 = 1
· 使用定理 `WithZero.exp_le_exp`：∀ {G : Type u_3} [inst : Preorder G] {a b : G}, Wit
hZero.exp a ≤ WithZero.exp b ↔ a ≤ b
· 使用定理 `Right.neg_nonpos_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α]
 [AddRightMono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n

--- 原说明 ---
The `v`-adic valuation on `R` is bounded above by 1.
-/
theorem intValuation_le_one (x : R) : v.intValuation x ≤ 1 := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · rw [v.intValuation_if_neg hx, ← exp_zero, exp_le_exp, Right.neg_nonpos_iff]
    exact Int.natCast_nonneg _

/-- The `v`-adic valuation of `r : R` is less than 1 if and only if `v` divides the ideal `(r)`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd** 是 Mathlib 中的一
个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_lt_one_iff_dvd (r : R) : v.intValuation r < 1 ↔ v.asIdeal ∣ I
deal.span {r}
参数：r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg`：intValuation_if_
neg {r : R} (hr : r != 0) : v.intValuation r = exp (-(Associates.mk v.asIdeal).c
ount (Associates.mk (Ideal.span {r} : Ideal …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.exp_zero`：∀ {M : Type u_4} [inst : AddMonoid M], WithZero.exp 0
 = 1
· 使用定理 `WithZero.exp_lt_exp`：∀ {G : Type u_3} [inst : Preorder G] {a b : G}, Wit
hZero.exp a < WithZero.exp b ↔ a < b
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Int.ofNat_zero`：↑0 = 0
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The `v`-adic valuation of `r : R` is less than 1 if and only if `v` divides the 
ideal `(r)`.
-/
theorem intValuation_lt_one_iff_dvd (r : R) :
    v.intValuation r < 1 ↔ v.asIdeal ∣ Ideal.span {r} := by
  by_cases hr : r = 0
  · simp [hr]
  · rw [v.intValuation_if_neg hr, ← exp_zero, exp_lt_exp,
      neg_lt_zero, ← Int.ofNat_zero, Int.ofNat_lt, zero_lt_iff]
    have h : (Ideal.span {r} : Ideal R) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hr
    exact Associates.count_ne_zero_iff_dvd h v.irreducible

/-- The `v`-adic valuation of `r : R` is less than 1 if and only if `r ∈ v`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem** 是 Mathlib 中的一
个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_lt_one_iff_mem (r : R) : v.intValuation r < 1 ↔ r in v.asIdea
l
参数：r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd`：intValua
tion_lt_one_iff_dvd (r : R) : v.intValuation r < 1 ↔ v.asIdeal ∣ Ideal.span {r}
· 使用定理 `Ideal.dvd_span_singleton`：dvd_span_singleton {I : Ideal A} {x : A} : I ∣
 span {x} ↔ x in I
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The `v`-adic valuation of `r : R` is less than 1 if and only if `r ∈ v`.
-/
theorem intValuation_lt_one_iff_mem (r : R) :
    v.intValuation r < 1 ↔ r ∈ v.asIdeal := by
  rw [intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton]

set_option backward.isDefEq.respectTransparency.types false in
/-- The `v`-adic valuation of `r : R` is equal to 1 if and only if `r ∈ vᶜ`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl** 是 
Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_eq_one_iff_mem_primeCompl (r : R) : v.intValuation r = 1 ↔ r 
in v.asIdeal.primeCompl
参数：r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.one_notMem`：one_notMem (I : Ideal α) [hI : I.IsPrime] : 1 ∉ I
· 使用定理 `LE.le.ge_iff_eq`：ge_iff_eq (h : a <= b) : b <= a ↔ a = b
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_one`：intValuation_le_
one (x : R) : v.intValuation x <= 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The `v`-adic valuation of `r : R` is equal to 1 if and only if `r ∈ vᶜ`.
-/
theorem intValuation_eq_one_iff_mem_primeCompl (r : R) :
    v.intValuation r = 1 ↔ r ∈ v.asIdeal.primeCompl := by
  simp [Ideal.primeCompl, ← intValuation_lt_one_iff_mem, LE.le.ge_iff_eq (intValuation_le_one v r)]

/-- The `v`-adic valuation of `r : R` is less than `WithZero.exp (-n)` if and only if
`vⁿ` divides the ideal `(r)`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd** 是 Mathlib 中的一
个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_le_pow_iff_dvd (r : R) (n : Nat) : v.intValuation r <= exp (-
(n : Int)) ↔ v.asIdeal ^ n ∣ Ideal.span {r}
参数：r : R；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Valuation.map_zero`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [in
st_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 0 = 0
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg`：intValuation_if_
neg {r : R} (hr : r != 0) : v.intValuation r = exp (-(Associates.mk v.asIdeal).c
ount (Associates.mk (Ideal.span {r} : Ideal …
· 使用定理 `WithZero.exp_le_exp`：∀ {G : Type u_3} [inst : Preorder G] {a b : G}, Wit
hZero.exp a ≤ WithZero.exp b ↔ a ≤ b
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.ofNat_le`：∀ {m n : ℕ}, ↑m ≤ ↑n ↔ m ≤ n
· 使用定理 `Ideal.dvd_span_singleton`：dvd_span_singleton {I : Ideal A} {x : A} : I ∣
 span {x} ↔ x in I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.le_singleton_iff`：Associates.le_singleton_iff (x : A) (n : Na
t) (I : Ideal A) : Associates.mk I ^ n <= Associates.mk (Ideal.span {x}) ↔ x in 
I ^ n
· 使用定理 `Associates.prime_pow_dvd_iff_le`：prime_pow_dvd_iff_le {m p : Associates 
α} (h₁ : m != 0) (h₂ : Irreducible p) {k : Nat} : p ^ k <= m ↔ k <= count p m.fa
ctors
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.mk_ne_zero'`：Associates.mk_ne_zero' {R : Type*} [CommSemiring
 R] {r : R} : Associates.mk (Ideal.span {r} : Ideal R) != 0 ↔ r != 0
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.associates_irreducible`：associates_ir
reducible : Irreducible Associates.mk v.asIdeal
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The `v`-adic valuation of `r : R` is less than `WithZero.exp (-n)` if and only i
f
`vⁿ` divides the ideal `(r)`.
-/
theorem intValuation_le_pow_iff_dvd (r : R) (n : ℕ) :
    v.intValuation r ≤ exp (-(n : ℤ)) ↔ v.asIdeal ^ n ∣ Ideal.span {r} := by
  by_cases hr : r = 0
  · simp_rw [hr, Valuation.map_zero, Ideal.dvd_span_singleton, zero_le, Submodule.zero_mem]
  · rw [v.intValuation_if_neg hr, exp_le_exp, neg_le_neg_iff, Int.ofNat_le,
      Ideal.dvd_span_singleton, ← Associates.le_singleton_iff,
      Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hr) v.associates_irreducible]

/-- The `v`-adic valuation of `r : R` is less than `WithZero.exp (-n)` if and only if
`r ∈ vⁿ`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem** 是 Mathlib 中的一
个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_le_pow_iff_mem (r : R) (n : Nat) : v.intValuation r <= exp (-
(n : Int)) ↔ r in v.asIdeal ^ n
参数：r : R；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd`：intValua
tion_le_pow_iff_dvd (r : R) (n : Nat) : v.intValuation r <= exp (-(n : Int)) ↔ v
.asIdeal ^ n ∣ Ideal.span {r}
· 使用定理 `Ideal.dvd_span_singleton`：dvd_span_singleton {I : Ideal A} {x : A} : I ∣
 span {x} ↔ x in I
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The `v`-adic valuation of `r : R` is less than `WithZero.exp (-n)` if and only i
f
`r ∈ vⁿ`.
-/
theorem intValuation_le_pow_iff_mem (r : R) (n : ℕ) :
    v.intValuation r ≤ exp (-(n : ℤ)) ↔ r ∈ v.asIdeal ^ n := by
  rw [intValuation_le_pow_iff_dvd, Ideal.dvd_span_singleton]
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_le_exp_iff_le_emultiplicity** 
是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_le_exp_iff_le_emultiplicity {r : R} {n : Nat} : v.intValuatio
n r <= exp (-(n : Int)) ↔ n <= emultiplicity v.asIdeal (Ideal.span {r})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd`：intValua
tion_le_pow_iff_dvd (r : R) (n : Nat) : v.intValuation r <= exp (-(n : Int)) ↔ v
.asIdeal ^ n ∣ Ideal.span {r}
· 使用定理 `pow_dvd_iff_le_emultiplicity`：pow_dvd_iff_le_emultiplicity {k : Nat} : a
 ^ k ∣ b ↔ k <= emultiplicity a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem intValuation_le_exp_iff_le_emultiplicity {r : R} {n : ℕ} :
    v.intValuation r ≤ exp (-(n : ℤ)) ↔ n ≤ emultiplicity v.asIdeal (Ideal.span {r}) := by
  rw [intValuation_le_pow_iff_dvd, pow_dvd_iff_le_emultiplicity]
/-
**IsDedekindDomain.HeightOneSpectrum.exp_le_intValuation_iff_emultiplicity_le** 
是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：exp_le_intValuation_iff_emultiplicity_le {r : R} {n : Nat} : exp (-(n : In
t)) <= v.intValuation r ↔ emultiplicity v.asIdeal (Ideal.span {r}) <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.lt_natCast_add_one_iff`：lt_natCast_add_one_iff {m : Nat∞} {n : Nat}
 : m < n + 1 ↔ m <= n
· 使用定理 `ENat.natCast_one`：natCast_one : ((1 : Nat) : Nat∞) = 1
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
· 使用定理 `emultiplicity_lt_iff_not_dvd`：emultiplicity_lt_iff_not_dvd {k : Nat} : e
multiplicity a b < k ↔ ¬a ^ k ∣ b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd`：intValua
tion_le_pow_iff_dvd (r : R) (n : Nat) : v.intValuation r <= exp (-(n : Int)) ↔ v
.asIdeal ^ n ∣ Ideal.span {r}
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `WithZero.exp_add`：∀ {M : Type u_4} [inst : AddMonoid M] (a b : M), WithZ
ero.exp (a + b) = WithZero.exp a * WithZero.exp b
· 使用定理 `WithZero.exp_neg`：∀ {G : Type u_5} [inst : AddGroup G] (a : G), WithZero
.exp (-a) = (WithZero.exp a)⁻¹
· 使用引理 `mul_inv_lt_iff₀`：mul_inv_lt_iff₀ (hc : 0 < c) : b * c⁻¹ < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `instMulPosStrictMonoWithZeroOfMulRightStrictMono`：∀ {α : Type u_1} [inst
 : Mul α] [inst_1 : Preorder α] [MulRightStrictMono α], MulPosStrictMono (WithZe
ro α)
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
（共 33 条，此处仅展示前 30 条）
-/
theorem exp_le_intValuation_iff_emultiplicity_le {r : R} {n : ℕ} :
    exp (-(n : ℤ)) ≤ v.intValuation r ↔ emultiplicity v.asIdeal (Ideal.span {r}) ≤ n := by
  rw [← ENat.lt_natCast_add_one_iff, ← ENat.natCast_one, ← ENat.natCast_add,
    emultiplicity_lt_iff_not_dvd, ← intValuation_le_pow_iff_dvd, not_le, Nat.cast_add, Nat.cast_one,
    neg_add, exp_add, exp_neg 1, mul_inv_lt_iff₀ (by simp)]
  by_cases hv : v.intValuation r = 0
  · simp [hv]
  · rw [lt_mul_exp_iff_le hv]

/-- There exists `π : R` with `v`-adic valuation `WithZero.exp (-1)`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer** 是 Mathlib
 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_exists_uniformizer : exists π : R, v.intValuation π = WithZer
o.exp (-1 : Int)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.associates_irreducible`：associates_ir
reducible : Irreducible Associates.mk v.asIdeal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.dvdNotUnit_iff_lt`：Ideal.dvdNotUnit_iff_lt {I J : Ideal A} : DvdNo
tUnit I J ↔ J < I
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.isUnit_iff`：isUnit_iff {I : Ideal R} : IsUnit I ↔ I = ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `SetLike.exists_of_lt`：exists_of_lt : p < q -> exists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Associates.mk_ne_zero'`：Associates.mk_ne_zero' {R : Type*} [CommSemiring
 R] {r : R} : Associates.mk (Ideal.span {r} : Ideal R) != 0 ↔ r != 0
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg`：intValuation_if_
neg {r : R} (hr : r != 0) : v.intValuation r = exp (-(Associates.mk v.asIdeal).c
ount (Associates.mk (Ideal.span {r} : Ideal …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithZero.exp_inj`：∀ {M : Type u_4} {x y : M}, WithZero.exp x = WithZero.
exp y ↔ x = y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Int.ofNat_one`：↑1 = 1
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Nat.eq_of_le_of_lt_succ`：∀ {n m : ℕ}, n ≤ m → m < n + 1 → m = n
· 使用定理 `Associates.prime_pow_dvd_iff_le`：prime_pow_dvd_iff_le {m p : Associates 
α} (h₁ : m != 0) (h₂ : Irreducible p) {k : Nat} : p ^ k <= m ↔ k <= count p m.fa
ctors
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Associates.mk_le_mk_iff_dvd`：mk_le_mk_iff_dvd {a b : M} : Associates.mk 
a <= Associates.mk b ↔ a ∣ b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.dvd_span_singleton`：dvd_span_singleton {I : Ideal A} {x : A} : I ∣
 span {x} ↔ x in I
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Associates.mk_pow`：mk_pow (a : M) (n : Nat) : Associates.mk (a ^ n) = As
sociates.mk a ^ n

--- 原说明 ---
There exists `π : R` with `v`-adic valuation `WithZero.exp (-1)`.
-/
theorem intValuation_exists_uniformizer :
    ∃ π : R, v.intValuation π = WithZero.exp (-1 : ℤ) := by
  have hv : Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  have hlt : v.asIdeal ^ 2 < v.asIdeal := by
    rw [← Ideal.dvdNotUnit_iff_lt]
    exact ⟨v.ne_bot, v.asIdeal, Ideal.isUnit_iff.not.mpr v.isPrime.ne_top, sq v.asIdeal⟩
  obtain ⟨π, mem, notMem⟩ := SetLike.exists_of_lt hlt
  have hπ : Associates.mk (Ideal.span {π}) ≠ 0 := by
    rw [Associates.mk_ne_zero']
    intro h
    rw [h] at notMem
    exact notMem (Submodule.zero_mem (v.asIdeal ^ 2))
  use π
  rw [intValuation_if_neg _ (Associates.mk_ne_zero'.mp hπ), exp_inj]
  apply congr_arg
  rw [← Int.ofNat_one, Int.natCast_inj]
  rw [← Ideal.dvd_span_singleton, ← Associates.mk_le_mk_iff_dvd] at mem notMem
  rw [← pow_one (Associates.mk v.asIdeal), Associates.prime_pow_dvd_iff_le hπ hv] at mem
  rw [Associates.mk_pow, Associates.prime_pow_dvd_iff_le hπ hv, not_le] at notMem
  exact Nat.eq_of_le_of_lt_succ mem notMem
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : v.intValuation.IsNontrivial :=
  have ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  ⟨π, by aesop⟩

@[simp]
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_uniformizer** 是 Mathlib 中的一个定理
，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_uniformizer (π : v.intValuation.Uniformizer) : v.intValuation
 (π.val : R) = WithZero.exp (-1)
参数：π : v.intValuation.Uniformizer。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsRankOneDiscrete.mk'`：∀ {Γ : Type u_1} [inst : LinearOrderedC
ommGroupWithZero Γ] {R : Type u_2} [inst_1 : Ring R] (v : Valuation R Γ)   [IsCy
clic ↥(MonoidWithZero…
· 使用定理 `instIsCyclicUnitsWithZero`：∀ (G : Type u_4) [inst : Group G] [IsCyclic G
], IsCyclic (WithZero G)ˣ
· 使用定理 `instIsAddCyclicInt`：IsAddCyclic ℤ
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.instNontrivialSubtypeUnitsMemSubgroupValueGroupOfClassOfIsNont
rivial`：∀ {R : Type u_3} [inst : Ring R] {Γ₀ : Type u_7} [inst_1 : LinearOrdered
CommGroupWithZero Γ₀] {v : Valuation R Γ₀}   [hv : v.IsNontrivial], …
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.instIsNontrivialWithZeroMultiplicativ
eIntIntValuation`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomai
n R] (v : IsDedekindDomain.HeightOneSpectrum R),   v.intValuation.IsNontrivial
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.IsUniformizer.val`：val (hπ : v.IsUniformizer π) : v π = hv.gen
erator
· 使用定理 `Valuation.Uniformizer.valuation_gt_one`：∀ {Γ : Type u_1} [inst : LinearO
rderedCommGroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] {v : Valuation A Γ} 
  [hv : v.IsRankOneDiscrete]…
· 使用定理 `Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range`：gener
ator_eq_exp_neg_one_of_mem_range (hπ : exp (-1) in Set.range v) : hv.generator =
 Units.mk0 (exp (-1 : Int) : Intᵐ⁰) (by simp)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer`：intV
aluation_exists_uniformizer : exists π : R, v.intValuation π = WithZero.exp (-1 
: Int)
-/
theorem intValuation_uniformizer (π : v.intValuation.Uniformizer) :
    v.intValuation (π.val : R) = WithZero.exp (-1) := by
  simpa [Valuation.IsUniformizer.val π.valuation_gt_one, Units.ext_iff]
    using Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
      v.intValuation_exists_uniformizer

/-- The `I`-adic valuation of a generator of `I` equals `(-1 : ℤᵐ⁰)` -/
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_singleton** 是 Mathlib 中的一个定理，位
于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_singleton {r : R} (hr : r != 0) (hv : v.asIdeal = Ideal.span 
{r}) : v.intValuation r = exp (-1 : Int)
参数：hr : r != 0；hv : v.asIdeal = Ideal.span {r}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg`：intValuation_if_
neg {r : R} (hr : r != 0) : v.intValuation r = exp (-(Associates.mk v.asIdeal).c
ount (Associates.mk (Ideal.span {r} : Ideal …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.count_self`：count_self [Nontrivial α] {p : Associates α} (hp 
: Irreducible p) : p.count p.factors = 1
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.associates_irreducible`：associates_ir
reducible : Irreducible Associates.mk v.asIdeal
· 使用定理 `Int.ofNat_one`：↑1 = 1

--- 原说明 ---
The `I`-adic valuation of a generator of `I` equals `(-1 : ℤᵐ⁰)`
-/
theorem intValuation_singleton {r : R} (hr : r ≠ 0) (hv : v.asIdeal = Ideal.span {r}) :
    v.intValuation r = exp (-1 : ℤ) := by
  rw [v.intValuation_if_neg hr, ← hv, Associates.count_self, Int.ofNat_one]
  exact v.associates_irreducible

@[simp]
/-
**IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff** 是 Mathlib 中的一个定理，
位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intValuation_eq_one_iff {v : HeightOneSpectrum R} {x : R} : v.intValuation
 x = 1 ↔ x ∉ v.asIdeal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem`：intValua
tion_lt_one_iff_mem (r : R) : v.intValuation r < 1 ↔ r in v.asIdeal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_one`：intValuation_le_
one (x : R) : v.intValuation x <= 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem intValuation_eq_one_iff {v : HeightOneSpectrum R} {x : R} :
    v.intValuation x = 1 ↔ x ∉ v.asIdeal := by
  refine ⟨fun h ↦ by simp [← (intValuation_lt_one_iff_mem _ _).not, h], fun h ↦ ?_⟩
  exact le_antisymm (v.intValuation_le_one x) <| by
    simp [← not_lt, (v.intValuation_lt_one_iff_mem _).not, h]

/-! ### Adic valuations on the field of fractions `K` -/

variable (K) in
/-- The `v`-adic valuation of `x : K` is the valuation of `r` divided by the valuation of `s`,
where `r` and `s` are chosen so that `x = r/s`. -/
@[no_expose]
/-
**IsDedekindDomain.HeightOneSpectrum.valuation** 是 Mathlib 中的一个定义，位于命名空间 `IsDede
kindDomain.HeightOneSpectrum`。
形式化陈述：valuation (v : HeightOneSpectrum R) : Valuation K Intᵐ⁰
参数：v : HeightOneSpectrum R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `v`-adic valuation of `x : K` is the valuation of `r` divided by the valuati
on of `s`,
where `r` and `s` are chosen so that `x = r/s`.
-/
def valuation (v : HeightOneSpectrum R) : Valuation K ℤᵐ⁰ :=
  v.intValuation.extendToLocalization
    (fun r hr => Set.mem_compl <| v.intValuation_ne_zero' ⟨r, hr⟩) K
/-
**IsDedekindDomain.HeightOneSpectrum.valuation_def** 是 Mathlib 中的一个定理，位于命名空间 `Is
DedekindDomain.HeightOneSpectrum`。
形式化陈述：valuation_def (x : K) : v.valuation K x = v.intValuation.extendToLocalizat
ion (fun r hr => Set.mem_compl (v.intValuation_ne_zero' ⟨r, hr⟩)) K x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Set.mem_compl`：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero'`：intValuation_n
e_zero' (x : nonZeroDivisors R) : v.intValuation x != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.RingTheory.DedekindDomain.AdicValuation.0.IsDedekindDom
ain.HeightOneSpectrum.valuation.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst
_1 : IsDedekindDomain R] (K : Type u_2) [inst_2 : Field K]   [inst_3 : Algebra R
 K] [inst_4 : IsFr…
-/
theorem valuation_def (x : K) :
    v.valuation K x =
      v.intValuation.extendToLocalization
        (fun r hr => Set.mem_compl (v.intValuation_ne_zero' ⟨r, hr⟩)) K x := by rw [valuation]

set_option backward.isDefEq.respectTransparency.types false in
/--
The `v`-adic valuation of `r / s : K` is the valuation of `r` divided by the valuation of `s`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.valuation_of_mk'** 是 Mathlib 中的一个定理，位于命名空间 
`IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuation_of_mk' {r : R} {s : nonZeroDivisors R} : v.valuation K (IsLocali
zation.mk' K r s) = v.intValuation r / v.intValuation s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Set.mem_compl`：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero'`：intValuation_n
e_zero' (x : nonZeroDivisors R) : v.intValuation x != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_def`：valuation_def (x : K) 
: v.valuation K x = v.intValuation.extendToLocalization (fun r hr => Set.mem_com
pl (v.intValuation_ne_zero' ⟨r, hr⟩)) …
· 使用定理 `Valuation.extendToLocalization_mk'`：Valuation.extendToLocalization_mk' (
x : A) (y : S) : (v.extendToLocalization hS B) (IsLocalization.mk' _ x y) = v x 
* (v y)⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹

--- 原说明 ---
The `v`-adic valuation of `r / s : K` is the valuation of `r` divided by the val
uation of `s`.
-/
theorem valuation_of_mk' {r : R} {s : nonZeroDivisors R} :
    v.valuation K (IsLocalization.mk' K r s) = v.intValuation r / v.intValuation s := by
  rw [valuation_def, Valuation.extendToLocalization_mk', div_eq_mul_inv]

set_option backward.isDefEq.respectTransparency.types false in
open scoped algebraMap in
/-- The `v`-adic valuation on `K` extends the `v`-adic valuation on `R`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap** 是 Mathlib 中的一个定理，
位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuation_of_algebraMap (r : R) : v.valuation K r = v.intValuation r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Set.mem_compl`：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero'`：intValuation_n
e_zero' (x : nonZeroDivisors R) : v.intValuation x != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_def`：valuation_def (x : K) 
: v.valuation K x = v.intValuation.extendToLocalization (fun r hr => Set.mem_com
pl (v.intValuation_ne_zero' ⟨r, hr⟩)) …
· 使用定理 `Valuation.extendToLocalization_apply_map_apply`：Valuation.extendToLocali
zation_apply_map_apply (a : A) : v.extendToLocalization hS B (algebraMap A B a) 
= v a

--- 原说明 ---
The `v`-adic valuation on `K` extends the `v`-adic valuation on `R`.
-/
theorem valuation_of_algebraMap (r : R) : v.valuation K r = v.intValuation r := by
  rw [valuation_def, Valuation.extendToLocalization_apply_map_apply]

open scoped algebraMap in
/-- The `v`-adic valuation on `R` is bounded above by 1. -/
/-
**IsDedekindDomain.HeightOneSpectrum.valuation_le_one** 是 Mathlib 中的一个定理，位于命名空间 
`IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuation_le_one (r : R) : v.valuation K r <= 1
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_one`：intValuation_le_
one (x : R) : v.intValuation x <= 1

--- 原说明 ---
The `v`-adic valuation on `R` is bounded above by 1.
-/
theorem valuation_le_one (r : R) : v.valuation K r ≤ 1 := by
  rw [valuation_of_algebraMap]; exact v.intValuation_le_one r

open scoped algebraMap in
/-- The `v`-adic valuation of `r : R` is less than 1 if and only if `v` divides the ideal `(r)`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_dvd** 是 Mathlib 中的一个定理
，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuation_lt_one_iff_dvd (r : R) : v.valuation K r < 1 ↔ v.asIdeal ∣ Ideal
.span {r}
参数：r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd`：intValua
tion_lt_one_iff_dvd (r : R) : v.intValuation r < 1 ↔ v.asIdeal ∣ Ideal.span {r}

--- 原说明 ---
The `v`-adic valuation of `r : R` is less than 1 if and only if `v` divides the 
ideal `(r)`.
-/
theorem valuation_lt_one_iff_dvd (r : R) :
    v.valuation K r < 1 ↔ v.asIdeal ∣ Ideal.span {r} := by
  rw [valuation_of_algebraMap]; exact v.intValuation_lt_one_iff_dvd r

open scoped algebraMap in
/-- The `v`-adic valuation of `r : R` is less than 1 if and only if `r ∈ v`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem** 是 Mathlib 中的一个定理
，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuation_lt_one_iff_mem (r : R) : v.valuation K r < 1 ↔ r in v.asIdeal
参数：r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem`：intValua
tion_lt_one_iff_mem (r : R) : v.intValuation r < 1 ↔ r in v.asIdeal

--- 原说明 ---
The `v`-adic valuation of `r : R` is less than 1 if and only if `r ∈ v`.
-/
theorem valuation_lt_one_iff_mem (r : R) :
    v.valuation K r < 1 ↔ r ∈ v.asIdeal := by
  rw [valuation_of_algebraMap]; exact v.intValuation_lt_one_iff_mem r

@[simp]
/-
**IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem** 是 Mathlib 中的一
个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuation_eq_one_iff_notMem {r : R} : v.valuation K (algebraMap R K r) = 1
 ↔ r ∉ v.asIdeal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem`：valuation_l
t_one_iff_mem (r : R) : v.valuation K r < 1 ↔ r in v.asIdeal
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem valuation_eq_one_iff_notMem {r : R} :
    v.valuation K (algebraMap R K r) = 1 ↔ r ∉ v.asIdeal := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), le_antisymm_iff]
  simp [HeightOneSpectrum.valuation_le_one]

variable (K) in
open scoped algebraMap in
/-- The `v` adic valuation of `a / b : K` is `≤ 1` if and only if `b ∉ v`, provided that `a` and
`b` are coprime at `v`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.valuation_div_le_one_iff** 是 Mathlib 中的一个定理
，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuation_div_le_one_iff (a : R) {b : R} (hb : b != 0) (h : b in v.asIdeal
 -> a ∉ v.asIdeal) : v.valuation K (a / b) <= 1 ↔ b ∉ v.asIdeal
参数：a : R；hb : b != 0；h : b in v.asIdeal -> a ∉ v.asIdeal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Valuation.ne_zero_iff`：ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) 
{x : K} : v x != 0 ↔ x != 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.log_lt_log`：∀ {G : Type u_3} [inst : Preorder G] [inst_1 : AddG
roup G] {x y : WithZero (Multiplicative G)},   x ≠ 0 → y ≠ 0 → (x.log < y.log ↔ 
x < y)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `WithZero.log_div`：log_div {x y : Gᵐ⁰} (hx : x != 0) (hy : y != 0) : log 
(x / y) = log x - log y
· 使用定理 `WithZero.log_one`：∀ {M : Type u_4} [inst : AddMonoid M], WithZero.log 1 
= 0
· 使用定理 `Int.sub_pos`：∀ {a b : ℤ}, 0 < a - b ↔ b < a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff`：intValuation
_eq_one_iff {v : HeightOneSpectrum R} {x : R} : v.intValuation x = 1 ↔ x ∉ v.asI
deal
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The `v` adic valuation of `a / b : K` is `≤ 1` if and only if `b ∉ v`, provided 
that `a` and
`b` are coprime at `v`.
-/
theorem valuation_div_le_one_iff (a : R) {b : R} (hb : b ≠ 0)
    (h : b ∈ v.asIdeal → a ∉ v.asIdeal) :
    v.valuation K (a / b) ≤ 1 ↔ b ∉ v.asIdeal := by
  refine ⟨fun hv ↦ ?_, fun hb ↦ by
    simp [valuation_of_algebraMap, intValuation_eq_one_iff.2 hb, intValuation_le_one]⟩
  contrapose! hv
  have ha₀ : a ≠ 0 := fun _ ↦ by simp_all
  have hva : v.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 (by simp [ha₀])
  have hvb : v.valuation K b ≠ 0 := (Valuation.ne_zero_iff _).2 (by simp [hb])
  rw [← WithZero.log_lt_log one_ne_zero ((Valuation.ne_zero_iff _).2 (by simp [ha₀, hb])),
    map_div₀, WithZero.log_div hva hvb, WithZero.log_one, Int.sub_pos,
    WithZero.log_lt_log hvb hva]
  simpa [valuation_of_algebraMap, intValuation_eq_one_iff.2 <| h hv, intValuation_lt_one_iff_mem]

variable (K)

open scoped algebraMap in
/-- There exists `π : R` with `v`-adic valuation `WithZero.exp (-1)`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer'** 是 Mathlib 中
的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuation_exists_uniformizer' : exists (π : R), (valuation K v) π = WithZe
ro.exp (-1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer`：intV
aluation_exists_uniformizer : exists π : R, v.intValuation π = WithZero.exp (-1 
: Int)

--- 原说明 ---
There exists `π : R` with `v`-adic valuation `WithZero.exp (-1)`.
-/
theorem valuation_exists_uniformizer' :
    ∃ (π : R), (valuation K v) π = WithZero.exp (-1) := by
  have ⟨π, hπ⟩ := intValuation_exists_uniformizer v
  use π
  grind [valuation_of_algebraMap]

/-- There exists `π : K` with `v`-adic valuation `WithZero.exp (-1)`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer** 是 Mathlib 中的
一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuation_exists_uniformizer : exists π : K, v.valuation K π = exp (-1 : I
nt)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer'`：valuat
ion_exists_uniformizer' : exists (π : R), (valuation K v) π = WithZero.exp (-1)

--- 原说明 ---
There exists `π : K` with `v`-adic valuation `WithZero.exp (-1)`.
-/
theorem valuation_exists_uniformizer : ∃ π : K,
    v.valuation K π = exp (-1 : ℤ) := by
  obtain ⟨r, hr⟩ := v.valuation_exists_uniformizer' K
  use (algebraMap _ _ r)
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Valuation.IsNontrivial (v.valuation K) :=
  have ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  ⟨π, by aesop⟩
/-
**IsDedekindDomain.HeightOneSpectrum.valuation_surjective** 是 Mathlib 中的一个引理，位于命
名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuation_surjective : Function.Surjective (v.valuation K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `GroupWithZero.eq_zero_or_unit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G
₀] (a : G₀), a = 0 ∨ ∃ u, a = ↑u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer`：valuati
on_exists_uniformizer : exists π : K, v.valuation K π = exp (-1 : Int)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用引理 `inv_zpow'`：inv_zpow' (a : α) (n : Int) : a⁻¹ ^ n = a ^ (-n)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `WithZero.exp_log`：∀ {M : Type u_4} [inst : AddMonoid M] {x : WithZero (M
ultiplicative M)}, x ≠ 0 → WithZero.exp x.log = x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma valuation_surjective :
    Function.Surjective (v.valuation K) := by
  intro x
  rcases GroupWithZero.eq_zero_or_unit x with (rfl | ⟨x, rfl⟩)
  · simp
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    refine ⟨π ^ (- log x.val), ?_⟩
    simp [hπ, exp_log]

/-- Uniformizers are nonzero. -/
/-
**IsDedekindDomain.HeightOneSpectrum.valuation_uniformizer_ne_zero** 是 Mathlib 中
的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuation_uniformizer_ne_zero : Classical.choose (v.valuation_exists_unifo
rmizer K) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer`：valuati
on_exists_uniformizer : exists π : K, v.valuation K π = exp (-1 : Int)
· 使用定理 `Valuation.ne_zero_iff`：ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) 
{x : K} : v x != 0 ↔ x != 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `WithZero.coe_ne_zero`：∀ {α : Type u} {a : α}, ↑a ≠ 0

--- 原说明 ---
Uniformizers are nonzero.
-/
theorem valuation_uniformizer_ne_zero : Classical.choose (v.valuation_exists_uniformizer K) ≠ 0 :=
  haveI hu := Classical.choose_spec (v.valuation_exists_uniformizer K)
  (Valuation.ne_zero_iff _).mp (ne_of_eq_of_ne hu WithZero.coe_ne_zero)
/-
**IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one** 是 Mathli
b 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：mem_integers_of_valuation_le_one (x : K) (h : forall v : HeightOneSpectrum
 R, v.valuation K x <= 1) : x in (algebraMap R K).range
参数：x : K；h : forall v : HeightOneSpectrum R, v.valuation K x <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `Associates.mk_le_mk_iff_dvd`：mk_le_mk_iff_dvd {a b : M} : Associates.mk 
a <= Associates.mk b ↔ a ∣ b
· 使用定理 `Associates.factors_le`：factors_le {a b : Associates α} : a.factors <= b.
factors ↔ a <= b
· 使用定理 `Associates.factors_mk`：factors_mk (a : α) (h : a != 0) : (Associates.mk 
a).factors = factors' a
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `Multiset.le_iff_count`：le_iff_count {s t : Multiset α} : s <= t ↔ forall
 a, count a s <= count a t
（共 61 条，此处仅展示前 30 条）
-/
theorem mem_integers_of_valuation_le_one (x : K)
    (h : ∀ v : HeightOneSpectrum R, v.valuation K x ≤ 1) : x ∈ (algebraMap R K).range := by
  obtain ⟨⟨n, d, hd⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  obtain rfl : x = IsLocalization.mk' K n ⟨d, hd⟩ := IsLocalization.eq_mk'_iff_mul_eq.mpr hx
  obtain rfl | hn0 := eq_or_ne n 0
  · simp
  have hd0 := nonZeroDivisors.ne_zero hd
  suffices Ideal.span {d} ∣ (Ideal.span {n} : Ideal R) by
    obtain ⟨z, rfl⟩ := Ideal.span_singleton_le_span_singleton.1 (Ideal.le_of_dvd this)
    use z
    rw [map_mul, mul_comm, mul_eq_mul_left_iff] at hx
    exact (hx.resolve_right fun h => by simp [hd0] at h).symm
  have ine {r : R} : r ≠ 0 → Ideal.span {r} ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp
  rw [← Associates.mk_le_mk_iff_dvd, ← Associates.factors_le, Associates.factors_mk _ (ine hn0),
    Associates.factors_mk _ (ine hd0), WithTop.coe_le_coe, Multiset.le_iff_count]
  rintro ⟨v, hv⟩
  obtain ⟨v, rfl⟩ := Associates.mk_surjective v
  have hv' := hv
  rw [Associates.irreducible_mk, irreducible_iff_prime] at hv
  specialize h ⟨v, Ideal.isPrime_of_prime hv, hv.ne_zero⟩
  simp_rw [valuation_of_mk', intValuation_if_neg _ hn0, intValuation_if_neg _ hd0, ← exp_sub,
    ← exp_zero, exp_le_exp, Associates.factors_mk _ (ine hn0),
    Associates.factors_mk _ (ine hd0), Associates.count_some hv'] at h
  simpa using h

variable {K}
/-
**IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation** 是 Mathl
ib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：eq_of_valuation_isEquiv_valuation {p q : HeightOneSpectrum R} (hpq : (valu
ation K p).IsEquiv (valuation K q)) : p = q
参数：hpq : (valuation K p).IsEquiv (valuation K q)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem`：valuation_l
t_one_iff_mem (r : R) : v.valuation K r < 1 ↔ r in v.asIdeal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem eq_of_valuation_isEquiv_valuation {p q : HeightOneSpectrum R}
    (hpq : (valuation K p).IsEquiv (valuation K q)) : p = q := by
  simp_all [Valuation.isEquiv_iff_val_lt_one, HeightOneSpectrum.ext_iff, Ideal.ext_iff,
    ← valuation_lt_one_iff_mem (K := K)]

section Localization

open Localization

local instance : IsDedekindDomain
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) :=
  IsLocalization.AtPrime.isDedekindDomain R v.asIdeal
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors)

local instance : IsLocalRing (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) :=
  IsLocalization.AtPrime.isLocalRing
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) v.asIdeal

variable (K) in
/-- Given a Dedekind domain `R` in `K`, its field of fractions, the localization of `R` at
a nonzero prime is a valuation subring of `K`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime** 是 Mathlib 中的一个定义，
位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuationSubringAtPrime : ValuationSubring K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime

--- 原说明 ---
Given a Dedekind domain `R` in `K`, its field of fractions, the localization of 
`R` at
a nonzero prime is a valuation subring of `K`.
-/
def valuationSubringAtPrime : ValuationSubring K :=
  .ofSubring (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).toSubring fun x ↦
    by simpa [IsLocalization.IsInteger] using ValuationRing.isInteger_or_isInteger
        (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) x

open IsDedekindDomain
/-
**IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_toSubring** 是 Mathl
ib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuationSubringAtPrime_toSubring : (valuationSubringAtPrime K v).toSubrin
g = (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).toSubring
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem valuationSubringAtPrime_toSubring : (valuationSubringAtPrime K v).toSubring
    = (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).toSubring := rfl

open scoped algebraMap in
/-
**IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_le_valuation** 是 Ma
thlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuationSubringAtPrime_le_valuation : valuationSubringAtPrime K v <= (val
uation K v).valuationSubring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_div_le_one_iff`：valuation_d
iv_le_one_iff (a : R) {b : R} (hb : b != 0) (h : b in v.asIdeal -> a ∉ v.asIdeal
) : v.valuation K (a / b) <= 1 ↔ b ∉ v.asIdeal
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `division_def`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a b : G), a / b 
= a * b⁻¹
-/
theorem valuationSubringAtPrime_le_valuation :
    valuationSubringAtPrime K v ≤ (valuation K v).valuationSubring := by
  rintro x ⟨a, s, hs, rfl⟩
  suffices (valuation K v) (a / (s : K)) ≤ 1 by rwa [division_def (a : K) s] at this
  rwa [valuation_div_le_one_iff (K := K) v a (by aesop) (fun _ ↦ by contradiction)]
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R (valuationSubringAtPrime K v) :=
  (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).algebra'
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R (valuationSubringAtPrime K v) K :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDedekindDomain (valuationSubringAtPrime K v) :=
  IsLocalization.AtPrime.isDedekindDomain R v.asIdeal
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors)
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ring.KrullDimLE 1 (valuationSubringAtPrime K v) :=
  Ring.KrullDimLE.mk₁' (fun _ a _ ↦ IsPrime.to_maximal_ideal a)
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalization (v.asIdeal.primeCompl) (valuationSubringAtPrime K v) :=
  Localization.subalgebra.isLocalization_ofField K (v.asIdeal.primeCompl) _

end Localization

/-- Given `v : HeightOneSpectrum R`, the valuation associated to `v` has the localization of
  `R` at `v` as valuation subring. -/
/-
**IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuationSubringAtPrime_eq_valuationSubring : valuationSubringAtPrime K v 
= (v.valuation K).valuationSubring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.eq_of_le_of_ne_top`：eq_of_le_of_ne_top (hle : A <= B) (
hTop : B != ⊤) : A = B
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.instKrullDimLEOfNatNatSubtypeMemValua
tionSubringValuationSubringAtPrime`：∀ {R : Type u_1} [inst : CommRing R] [inst_1
 : IsDedekindDomain R] {K : Type u_2} [inst_2 : Field K]   [inst_3 : Algebra R K
] [inst_4 : IsFr…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_le_valuation`
：valuationSubringAtPrime_le_valuation : valuationSubringAtPrime K v <= (valuatio
n K v).valuationSubring
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.instIsNontrivialWithZeroMultiplicativ
eIntValuation`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R
] (K : Type u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFr…

--- 原说明 ---
Given `v : HeightOneSpectrum R`, the valuation associated to `v` has the localiz
ation of
  `R` at `v` as valuation subring.
-/
theorem valuationSubringAtPrime_eq_valuationSubring :
    valuationSubringAtPrime K v = (v.valuation K).valuationSubring :=
  ValuationSubring.eq_of_le_of_ne_top _ (valuationSubringAtPrime_le_valuation v)
    (by simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]; infer_instance)

/-- All `x : K` can be written as `n / d` or `d / n` with `n : R` and `d ∈ v.asIdealᶜ`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq** 是 Math
lib 中的一个引理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：exists_primeCompl_mul_eq_or_mul_eq (x : K) : exists (n : R) (d : v.asIdeal
.primeCompl), x * (algebraMap R K d) = (algebraMap R K n) ∨ x * (algebraMap R K 
n) = (algebraMap R K d)
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `ValuationRing.isInteger_or_isInteger`：isInteger_or_isInteger [h : Valuat
ionRing R] (x : K) : IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x
⁻¹
· 使用定理 `ValuationSubring.instIsDomainSubtypeMem`：∀ {K : Type u} [inst : Field K]
 (A : ValuationSubring K), IsDomain ↥A
· 使用定理 `ValuationSubring.instIsFractionRingSubtypeMem`：∀ {K : Type u} [inst : Fi
eld K] (A : ValuationSubring K), IsFractionRing (↥A) K
· 使用定理 `ValuationSubring.instValuationRingSubtypeMem`：∀ {K : Type u} [inst : Fie
ld K] (A : ValuationSubring K), ValuationRing ↥A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.instIsLocalizationPrimeComplAsIdealSu
btypeMemValuationSubringValuationSubringAtPrime`：∀ {R : Type u_1} [inst : CommRi
ng R] [inst_1 : IsDedekindDomain R] {K : Type u_2} [inst_2 : Field K]   [inst_3 
: Algebra R K] [inst_4 : IsFr…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
All `x : K` can be written as `n / d` or `d / n` with `n : R` and `d ∈ v.asIdeal
ᶜ`.
-/
lemma exists_primeCompl_mul_eq_or_mul_eq (x : K) :
    ∃ (n : R) (d : v.asIdeal.primeCompl), x * (algebraMap R K d) = (algebraMap R K n) ∨
        x * (algebraMap R K n) = (algebraMap R K d) := by
  -- It's already known that the localization of `R` at `v` is a (discrete) valuation ring, so
  -- write `x` or `x⁻¹` as `n / d` with `d ∈ vᶜ`.
  obtain (⟨r, hr⟩ | ⟨r, hr⟩) :=
    ValuationRing.isInteger_or_isInteger (valuationSubringAtPrime K v) x
  <;> obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj v.asIdeal.primeCompl r
  <;> use n, d
  <;> apply_fun algebraMap _ K at hnd
  <;> grind [=_ IsScalarTower.algebraMap_apply]

/-- All `x ∈ 𝓞[K]` can be written as `n / d` with `n : R` and `d ∈ v.asIdealᶜ`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer** 是 Mat
hlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：exists_primeCompl_mul_eq_of_integer (x : K) (hv : v.valuation K x <= 1) : 
exists (n : R) (d : v.asIdeal.primeCompl), x * (algebraMap R K d) = algebraMap R
 K n
参数：x : K；hv : v.valuation K x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq`：e
xists_primeCompl_mul_eq_or_mul_eq (x : K) : exists (n : R) (d : v.asIdeal.primeC
ompl), x * (algebraMap R K d) = (algebraMap R K n) ∨ x * (a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeComp
l`：intValuation_eq_one_iff_mem_primeCompl (r : R) : v.intValuation r = 1 ↔ r in 
v.asIdeal.primeCompl
· 使用定理 `eq_one_of_one_le_mul_right`：eq_one_of_one_le_mul_right (ha : a <= 1) (hb
 : b <= 1) (hab : 1 <= a * b) : b = 1
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_one`：intValuation_le_
one (x : R) : v.intValuation x <= 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
All `x ∈ 𝓞[K]` can be written as `n / d` with `n : R` and `d ∈ v.asIdealᶜ`.
-/
theorem exists_primeCompl_mul_eq_of_integer (x : K) (hv : v.valuation K x ≤ 1) :
    ∃ (n : R) (d : v.asIdeal.primeCompl), x * (algebraMap R K d) = algebraMap R K n := by
  obtain ⟨n, d, (hnd | hnd)⟩ := exists_primeCompl_mul_eq_or_mul_eq v x
  · use n, d
  · refine ⟨d, ⟨n, ?_⟩, hnd⟩
    rw [← v.intValuation_eq_one_iff_mem_primeCompl]
    apply eq_one_of_one_le_mul_right hv (intValuation_le_one v n)
    rw [← (v.intValuation_eq_one_iff_mem_primeCompl d).mpr d.prop,
      ← valuation_of_algebraMap (K := K), ← valuation_of_algebraMap (K := K), ← map_mul, hnd]

/-- Given `a, b ∈ A` and `v b ≤ v a` we can find `y : A` such that `y * a` is close to `b` by
the valuation `v`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.exists_intValuation_mul_sub_lt** 是 Mathlib 
中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：exists_intValuation_mul_sub_lt {a b : R} (hv : v.intValuation b <= v.intVa
luation a) (γ : Multiplicative Int) : exists y, v.intValuation (b - y * a) < γ
参数：hv : v.intValuation b <= v.intValuation a；γ : Multiplicative Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `le_zero_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero`：intValuation_ne
_zero (x : R) (hx : x != 0) : v.intValuation x != 0
· 使用定理 `WithZero.coe_ne_zero`：∀ {α : Type u} {a : α}, ↑a ≠ 0
· 使用引理 `WithZero.exists_exp_neg_natCast_lt_and_lt`：exists_exp_neg_natCast_lt_and
_lt {x y : Intᵐ⁰} (hx : x != 0) (hy : y != 0) : exists (k : Nat), exp (-(k : Int
)) < x ∧ exp (-(k : Int)) < y
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.exp_le_intValuation_iff_emultiplicity
_le`：exp_le_intValuation_iff_emultiplicity_le {r : R} {n : Nat} : exp (-(n : Int
)) <= v.intValuation r ↔ emultiplicity v.asIdeal (Ideal.span {r})…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem`：intValua
tion_le_pow_iff_mem (r : R) (n : Nat) : v.intValuation r <= exp (-(n : Int)) ↔ r
 in v.asIdeal ^ n
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity`
：intValuation_eq_exp_neg_multiplicity {r : R} (hr : r != 0) : v.intValuation r =
 exp (-multiplicity v.asIdeal (Ideal.span {r}) : Int)
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `Ideal.irreducible_pow_sup_of_ge`：irreducible_pow_sup_of_ge (hI : I != ⊥)
 (hJ : Irreducible J) (n : Nat) (hn : emultiplicity J I <= n) : J ^ n ⊔ I = J ^ 
multiplicity J I
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.irreducible`：irreducible : Irreducibl
e v.asIdeal
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Given `a, b ∈ A` and `v b ≤ v a` we can find `y : A` such that `y * a` is close 
to `b` by
the valuation `v`.
-/
theorem exists_intValuation_mul_sub_lt {a b : R} (hv : v.intValuation b ≤ v.intValuation a)
    (γ : Multiplicative ℤ) : ∃ y, v.intValuation (b - y * a) < γ := by
  -- If `a = 0`, then `b = 0`, so we can take `y = 0`.
  by_cases ha: a = 0
  · subst ha
    rw [map_zero, le_zero_iff] at hv
    exact ⟨0, by simp [hv]⟩
  · have hvaz := intValuation_ne_zero v a ha
    have hγz : WithZero.coe γ ≠ 0 := WithZero.coe_ne_zero
    -- Otherwise, find `n : ℕ` such that `exp (-n) < γ` and `exp(-n) < v a`.
    obtain ⟨n, hna, hnγ⟩ := exists_exp_neg_natCast_lt_and_lt hvaz hγz
    apply Exists.imp (fun _ h ↦ lt_of_le_of_lt h hnγ)
    -- `v b ≤ v a`, so `b ∈ v.asIdeal ^ -log (v a)`.
    -- From `irreducible_pow_sup_of_ge` we know that
    -- `v.asIdeal ^ -log (v a) = v.asIdeal ^ n ⊔ Ideal.span {a}`.
    -- So, `∃ z ∈ v.asIdeal ^ n, ∃ (y: R), b = z + y * a`. This gives `z` and `y` such that
    -- `b - y * a = z` and `v z ≤ exp (-n)`, as required.
    have hvn : emultiplicity v.asIdeal (Ideal.span {a}) ≤ n := by
      grw [← exp_le_intValuation_iff_emultiplicity_le, hna]
    have hb : b ∈ v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {a}) := by
      rwa [← intValuation_le_pow_iff_mem, ← v.intValuation_eq_exp_neg_multiplicity ha]
    have hnz : Ideal.span {a} ≠ ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
    simpa [← Ideal.irreducible_pow_sup_of_ge hnz v.irreducible n hvn, Submodule.mem_sup,
      ← eq_sub_iff_add_eq, ← intValuation_le_pow_iff_mem, Ideal.mem_span_singleton'] using hb

/-- Given `x ∈ 𝒪[K]` we can find `a : A` such that `a` is close to `x` by the valuation `v`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer** 是 Math
lib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：exists_valuation_sub_lt_of_integer {x : K} (hv : v.valuation K x <= 1) (γ 
: (Intᵐ⁰)ˣ) : existsa, v.valuation K (algebraMap R K a - x) < γ
参数：hv : v.valuation K x <= 1；γ : (Intᵐ⁰)ˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer`：
exists_primeCompl_mul_eq_of_integer (x : K) (hv : v.valuation K x <= 1) : exists
 (n : R) (d : v.asIdeal.primeCompl), x * (algebraMap R K d) …
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_one`：intValuation_le_
one (x : R) : v.intValuation x <= 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeComp
l`：intValuation_eq_one_iff_mem_primeCompl (r : R) : v.intValuation r = 1 ↔ r in 
v.asIdeal.primeCompl
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.exists_intValuation_mul_sub_lt`：exist
s_intValuation_mul_sub_lt {a b : R} (hv : v.intValuation b <= v.intValuation a) 
(γ : Multiplicative Int) : exists y, v.intValuation (b …
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用定理 `Algebra.cast.eq_1`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   Algebra.cast = ⇑(algebraMap R
 A)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Valuation.map_sub_swap`：map_sub_swap (x y : R) : v (x - y) = v (y - x)
· 使用定理 `WithZero.coe_unzero`：∀ {α : Type u} {x : WithZero α} (hx : x ≠ 0), ↑(Wit
hZero.unzero hx) = x
· 使用定理 `WithZero.unitsWithZeroEquiv_apply`：∀ {α : Type u_1} [inst : Group α] (a 
: (WithZero α)ˣ), WithZero.unitsWithZeroEquiv a = WithZero.unzero ⋯

--- 原说明 ---
Given `x ∈ 𝒪[K]` we can find `a : A` such that `a` is close to `x` by the valuat
ion `v`.
-/
theorem exists_valuation_sub_lt_of_integer {x : K} (hv : v.valuation K x ≤ 1)
    (γ : (ℤᵐ⁰)ˣ) : ∃a, v.valuation K (algebraMap R K a - x) < γ := by
  -- Write `x = n / d`, with `v d = 1`.
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := exists_primeCompl_mul_eq_of_integer v x hv
  rw [← intValuation_eq_one_iff_mem_primeCompl] at hd
  have hd' : v.intValuation n ≤ v.intValuation d := by grw [v.intValuation_le_one n, hd]
  -- Get `a` such that `v (n - a * d) < γ` from the previous theorem.
  obtain ⟨a, hval⟩ := exists_intValuation_mul_sub_lt v hd' (WithZero.unitsWithZeroEquiv γ)
  rw [unitsWithZeroEquiv_apply, coe_unzero] at hval
  use a
  -- `v d = 1`, so `v (a - x) = v (x - a) = v (x - a) * v d = v (n - a * d) < γ`.
  suffices h : v.valuation K (algebraMap R K a - x) = v.intValuation (n - a * d) by rwa [h]
  rw [← valuation_of_algebraMap (K := K), Algebra.cast, map_sub _ n, map_mul, ← hnd, ← sub_mul,
    map_mul, valuation_of_algebraMap, hd, mul_one, Valuation.map_sub_swap]

/-! ### Completions with respect to adic valuations

Given a Dedekind domain `R` with field of fractions `K` and a maximal ideal `v` of `R`, we define
the completion of `K` with respect to its `v`-adic valuation, denoted `v.adicCompletion`, and its
ring of integers, denoted `v.adicCompletionIntegers`. -/


/-- `K` as a valued field with the `v`-adic valuation. -/
@[instance_reducible]
/-
**IsDedekindDomain.HeightOneSpectrum.adicValued** 是 Mathlib 中的一个定义，位于命名空间 `IsDed
ekindDomain.HeightOneSpectrum`。
形式化陈述：adicValued : Valued K Intᵐ⁰
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`K` as a valued field with the `v`-adic valuation.
-/
def adicValued : Valued K ℤᵐ⁰ :=
  Valued.mk' (v.valuation K)
/-
**IsDedekindDomain.HeightOneSpectrum.adicValued_apply** 是 Mathlib 中的一个定理，位于命名空间 
`IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：adicValued_apply {x : K} : v.adicValued.v x = v.valuation K x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adicValued_apply {x : K} : v.adicValued.v x = v.valuation K x :=
  rfl

@[deprecated adicValued_apply (since := "2026-01-28")]
/-
**IsDedekindDomain.HeightOneSpectrum.adicValued_apply'** 是 Mathlib 中的一个定理，位于命名空间
 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：adicValued_apply' (x : WithVal (v.valuation K)) : v.adicValued.v (WithVal.
equiv _ x) = v.valuation K (WithVal.equiv _ x)
参数：x : WithVal (v.valuation K)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adicValued_apply' (x : WithVal (v.valuation K)) :
    v.adicValued.v (WithVal.equiv _ x) = v.valuation K (WithVal.equiv _ x) :=
  rfl

variable (K)

/-- The completion of `K` with respect to its `v`-adic valuation, defined as a one-field structure
wrapping the uniform-space completion `(v.valuation K).Completion`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion** 是 Mathlib 中的一个归纳类型，位于命名空间 
`IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     [IsDedekindDomain R] →       
(K : Type u_2) →         [inst_2 : Field K] →           [inst_3 : Algebra R K] →
 [IsFractionRing R K] → IsDedekindDomain.HeightOneSpectrum R → Type u_2
参数：K : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completion of `K` with respect to its `v`-adic valuation, defined as a one-f
ield structure
wrapping the uniform-space completion `(v.valuation K).Completion`.
-/
structure adicCompletion where
  /-- Wrap an element of the underlying completion `(v.valuation K).Completion` into
  `adicCompletion`. -/
  ofCompletion ::
  /-- The underlying element of the completion `(v.valuation K).Completion`. -/
  toCompletion : (v.valuation K).Completion

namespace adicCompletion

open UniformSpace MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Filter Topology Valuation

/-- `adicCompletion.toCompletion` and `adicCompletion.ofCompletion` as an equivalence. -/
@[simps]
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.equivCompletion** 是 Mathlib 
中的一个定义，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：equivCompletion : adicCompletion K v ≃ (v.valuation K).Completion where to
Fun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`adicCompletion.toCompletion` and `adicCompletion.ofCompletion` as an equivalenc
e.
-/
def equivCompletion : adicCompletion K v ≃ (v.valuation K).Completion where
  toFun := toCompletion
  invFun := ofCompletion
  left_inv _ := rfl
  right_inv _ := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `
IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Field (adicCompletion K v) := fast_instance% (equivCompletion K v).field

/-- `adicCompletion.toCompletion` as a ring isomorphism onto the underlying completion. -/
@[simps! apply]
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv** 是 Mathlib 中的一个定义，位于命
名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：equiv : adicCompletion K v ≃+* (v.valuation K).Completion where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`adicCompletion.toCompletion` as a ring isomorphism onto the underlying completi
on.
-/
def equiv : adicCompletion K v ≃+* (v.valuation K).Completion where
  toEquiv := equivCompletion K v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion** 
是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   (x : (IsDedekindDomain.HeightOneS
pectrum.valuation K v).Completion), { toCompletion := x }.toCompletion = x
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；x : (IsDedekindDomain.H
eightOneSpectrum.valuation K v).Completion。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCompletion_ofCompletion (x : (v.valuation K).Completion) :
    toCompletion (ofCompletion x : adicCompletion K v) = x := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_toCompletion** 
是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   (x : IsDedekindDomain.HeightOneSp
ectrum.adicCompletion K v), { toCompletion := x.toCompletion } = x
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；x : IsDedekindDomain.He
ightOneSpectrum.adicCompletion K v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofCompletion_toCompletion (x : adicCompletion K v) :
    ofCompletion x.toCompletion = x := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion_zero** 是 Mathli
b 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R),   IsDedekindDomain.HeightOneSpectr
um.adicCompletion.toCompletion 0 = 0
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCompletion_zero : (0 : adicCompletion K v).toCompletion = 0 := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion_one** 是 Mathlib
 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R),   IsDedekindDomain.HeightOneSpectr
um.adicCompletion.toCompletion 1 = 1
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCompletion_one : (1 : adicCompletion K v).toCompletion = 1 := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion_add** 是 Mathlib
 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   (x y : IsDedekindDomain.HeightOne
Spectrum.adicCompletion K v), (x + y).toCompletion = x.toCompletion + y.toComple
tion
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；x y : IsDedekindDomain.
HeightOneSpectrum.adicCompletion K v；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCompletion_add (x y : adicCompletion K v) :
    (x + y).toCompletion = x.toCompletion + y.toCompletion := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion_mul** 是 Mathlib
 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   (x y : IsDedekindDomain.HeightOne
Spectrum.adicCompletion K v), (x * y).toCompletion = x.toCompletion * y.toComple
tion
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；x y : IsDedekindDomain.
HeightOneSpectrum.adicCompletion K v；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCompletion_mul (x y : adicCompletion K v) :
    (x * y).toCompletion = x.toCompletion * y.toCompletion := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion_surjective** 是 
Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：toCompletion_surjective : Function.Surjective (toCompletion (K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem toCompletion_surjective : Function.Surjective (toCompletion (K := K) (v := v)) :=
  (equivCompletion K v).surjective
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective** 是 
Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：ofCompletion_surjective : Function.Surjective (ofCompletion (K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem ofCompletion_surjective : Function.Surjective (ofCompletion (K := K) (v := v)) :=
  (equivCompletion K v).symm.surjective
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `
IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : UniformSpace (adicCompletion K v) := .comap toCompletion inferInstance
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.isUniformInducing_toCompleti
on** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`
。
形式化陈述：isUniformInducing_toCompletion : IsUniformInducing (toCompletion (K
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isUniformInducing_toCompletion :
    IsUniformInducing (toCompletion (K := K) (v := v)) := ⟨rfl⟩
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `
IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsUniformAddGroup (adicCompletion K v) :=
  IsUniformInducing.isUniformAddGroup (equiv K v).toRingHom (isUniformInducing_toCompletion K v)

/-- The `v`-adic valuation on `adicCompletion K v`, transported from the completion along `equiv`.
-/
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.valuation** 是 Mathlib 中的一个定义
，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：valuation : Valuation (adicCompletion K v) Intᵐ⁰
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `v`-adic valuation on `adicCompletion K v`, transported from the completion 
along `equiv`.
-/
noncomputable def valuation : Valuation (adicCompletion K v) ℤᵐ⁰ :=
  Valued.v.comap (equiv K v).toRingHom
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.valueGroup_eq** 是 Mathlib 中的
一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：valueGroup_eq : valueGroup (.ofClass (valuation K v)) = valueGroup (.ofCla
ss (Valued.v : Valuation (v.valuation K).Completion Intᵐ⁰))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.range_comp`：∀ {α : Type u_1} {ι : Sort u_3} {ι' : So
rt u_4} {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α), Set.range (g ∘ f
) = Set.range g
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion_surjectiv
e`：toCompletion_surjective : Function.Surjective (toCompletion (K
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
-/
theorem valueGroup_eq :
    valueGroup (.ofClass (valuation K v)) =
      valueGroup (.ofClass (Valued.v : Valuation (v.valuation K).Completion ℤᵐ⁰)) := by
  simp [valuation, valueGroup, valueMonoid, ← (toCompletion_surjective K v).range_comp]; rfl

/-- The multiplicative equivalence between the value group of the completion's valuation, pulled
back along `equiv`, and that of the completion. -/
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.valueGroupEquiv** 是 Mathlib 
中的一个定义，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：valueGroupEquiv : valueGroup (.ofClass (valuation K v)) ≃* valueGroup (.of
Class (Valued.v : Valuation (v.valuation K).Completion Intᵐ⁰)) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative equivalence between the value group of the completion's valua
tion, pulled
back along `equiv`, and that of the completion.
-/
def valueGroupEquiv :
    valueGroup (.ofClass (valuation K v)) ≃*
      valueGroup (.ofClass (Valued.v : Valuation (v.valuation K).Completion ℤᵐ⁰)) where
  __ := Equiv.setCongr (by rw [valueGroup_eq K v])
  map_mul' _ _ := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.coe_valueGroupEquiv** 是 Math
lib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   (a : ↥(MonoidWithZeroHom.ofClass 
(IsDedekindDomain.HeightOneSpectrum.adicCompletion.valuation K v)).valueGroup), 
  ↑((IsDedekindDomain.HeightOneSpectrum.adicCompletion.valueGroupEquiv K v) a) =
 ↑a
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；a : ↥(MonoidWithZeroHom
.ofClass (IsDedekindDomain.HeightOneSpectrum.adicCompletion.valuation K v)).valu
eGroup；(IsDedekindDomain.HeightOneSpectrum.adicCompletion.valueGroupEquiv K v) a
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
-/
@[simp] theorem coe_valueGroupEquiv (a : valueGroup (.ofClass (valuation K v))) :
    ((valueGroupEquiv K v a : _) : ℤᵐ⁰ˣ) = a := rfl

/-- The order-preserving multiplicative equivalence between the `ValueGroup₀` of the completion's
valuation, pulled back along `equiv`, and that of the completion. -/
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.valueGroupOrderIso** 是 Mathl
ib 中的一个定义，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：valueGroupOrderIso : ValueGroup₀ (.ofClass (valuation K v)) ≃*o ValueGroup
₀ (.ofClass (Valued.v : Valuation (v.valuation K).Completion Intᵐ⁰)) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order-preserving multiplicative equivalence between the `ValueGroup₀` of the
 completion's
valuation, pulled back along `equiv`, and that of the completion.
-/
noncomputable def valueGroupOrderIso :
    ValueGroup₀ (.ofClass (valuation K v)) ≃*o
      ValueGroup₀ (.ofClass (Valued.v : Valuation (v.valuation K).Completion ℤᵐ⁰)) where
  toFun := WithZero.map' (valueGroupEquiv K v)
  invFun := WithZero.map' (valueGroupEquiv K v).symm
  left_inv x := by match x with | 0 => simp | .coe a => simp
  right_inv y := by match y with | 0 => simp | .coe b => simp
  map_mul' := by simp
  map_le_map_iff' {a b} := by
    match a, b with
    | 0, 0 => simp
    | 0, .coe _ => simp
    | .coe _, 0 => simp
    | .coe a, .coe b => simp [← Subtype.coe_le_coe]
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.coe_valueGroupOrderIso_coe**
 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   (a : ↥(MonoidWithZeroHom.ofClass 
(IsDedekindDomain.HeightOneSpectrum.adicCompletion.valuation K v)).valueGroup), 
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.valueGroupOrderIso K v) ↑a 
=     ↑((IsDedekindDomain.HeightOneSpectrum.adicCompletion.valueGroupEquiv K v) 
a)
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；a : ↥(MonoidWithZeroHom
.ofClass (IsDedekindDomain.HeightOneSpectrum.adicCompletion.valuation K v)).valu
eGroup；IsDedekindDomain.HeightOneSpectrum.adicCompletion.valueGroupOrderIso K v；
(IsDedekindDomain.HeightOneSpectrum.adicCompletion.valueGroupEquiv K v) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem coe_valueGroupOrderIso_coe (a : valueGroup (.ofClass (valuation K v))) :
    valueGroupOrderIso K v (a : ValueGroup₀ _) = (valueGroupEquiv K v a : ValueGroup₀ _) := by
  simp [valueGroupOrderIso]
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.embedding_valueGroupOrderIso
** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：embedding_valueGroupOrderIso (g : ValueGroup₀ (.ofClass (valuation K v))) 
: embedding (valueGroupOrderIso K v g) = embedding g
参数：g : ValueGroup₀ (.ofClass (valuation K v))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.coe_valueGroupOrderIso
_coe`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFr…
· 使用定理 `MonoidWithZeroHom.ValueGroup₀.embedding_apply`：∀ {A : Type u_1} {B : Typ
e u_2} [inst : MonoidWithZero A] [inst_1 : GroupWithZero B] {f : A →*₀ B} (a : f
.ValueGroup₀),   MonoidWithZeroHom.…
-/
theorem embedding_valueGroupOrderIso (g : ValueGroup₀ (.ofClass (valuation K v))) :
    embedding (valueGroupOrderIso K v g) = embedding g := by
  match g with
  | 0 => simp [valueGroupOrderIso]
  | .coe a => simp [coe_valueGroupOrderIso_coe, embedding_apply, coe_valueGroupEquiv]
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.valueGroupOrderIso_restrict*
* 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：valueGroupOrderIso_restrict (x : adicCompletion K v) : valueGroupOrderIso 
K v ((valuation K v).restrict x) = Valued.v.restrict (toCompletion x)
参数：x : adicCompletion K v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono`：embedding_strictMono
 : StrictMono (embedding (f
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.embedding_valueGroupOr
derIso`：embedding_valueGroupOrderIso (g : ValueGroup₀ (.ofClass (valuation K v))
) : embedding (valueGroupOrderIso K v g) = embedding g
· 使用引理 `Valuation.embedding_restrict`：embedding_restrict (x : R) : embedding (v.
restrict x) = v x
-/
theorem valueGroupOrderIso_restrict (x : adicCompletion K v) :
    valueGroupOrderIso K v ((valuation K v).restrict x) =
      Valued.v.restrict (toCompletion x) := by
  apply embedding_strictMono.injective
  rw [embedding_valueGroupOrderIso, embedding_restrict, embedding_restrict]; rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `
IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Valued (adicCompletion K v) ℤᵐ⁰ where
  v := valuation K v
  is_topological_valuation s := by
    rw [(isUniformInducing_toCompletion K v).isInducing.nhds_eq_comap 0, toCompletion_zero,
      Filter.mem_comap]
    refine ⟨fun ⟨t, ht, hts⟩ ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
    · obtain ⟨δ, hδ⟩ := Valued.mem_nhds_zero.1 ht
      refine ⟨Units.mapEquiv (valueGroupOrderIso K v).symm.toMulEquiv δ, fun x hx ↦ hts (hδ ?_)⟩
      rw [Set.mem_ofPred_eq] at hx ⊢
      simpa [← map_lt_map_iff (valueGroupOrderIso K v), valueGroupOrderIso_restrict] using hx
    · refine ⟨{y | Valued.v.restrict y < ↑(Units.mapEquiv (valueGroupOrderIso K v).toMulEquiv γ)},
        ?_, fun x hx ↦ hγ ?_⟩
      · rw [Valued.mem_nhds_zero]
        exact ⟨Units.mapEquiv (valueGroupOrderIso K v).toMulEquiv γ, subset_rfl⟩
      · rw [Set.mem_ofPred_eq, ← map_lt_map_iff (valueGroupOrderIso K v),
          valueGroupOrderIso_restrict]
        simpa using hx
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `
IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CompleteSpace (adicCompletion K v) :=
  ((isUniformInducing_toCompletion K v).completeSpace_congr (toCompletion_surjective K v)).mpr
    inferInstance

/-- Coercion of an element of `WithVal (v.valuation K)` into the adic completion. -/
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `
IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of an element of `WithVal (v.valuation K)` into the adic completion.
-/
instance : Coe (WithVal (v.valuation K)) (adicCompletion K v) where
  coe x := ofCompletion (x : (v.valuation K).Completion)

/-- Coercion of an element of `K` into the adic completion. -/
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `
IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of an element of `K` into the adic completion.
-/
instance (priority := 99) : Coe K (adicCompletion K v) where
  coe k := ofCompletion (k : (v.valuation K).Completion)
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.coe_toCompletion** 是 Mathlib
 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R) (k : K),   { toCompletion := ↑((Wit
hVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation K v)).symm k) }.toCompl
etion =     ↑((WithVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation K v))
.symm k)
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；k : K；(WithVal.equiv (I
sDedekindDomain.HeightOneSpectrum.valuation K v)).symm k；(WithVal.equiv (IsDedek
indDomain.HeightOneSpectrum.valuation K v)).symm k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toCompletion (k : K) :
    (↑k : adicCompletion K v).toCompletion = (k : (v.valuation K).Completion) := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.valuedAdicCompletion_def** 是
 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：valuedAdicCompletion_def {x : adicCompletion K v} : Valued.v x = Valued.ex
tensionValuation x.toCompletion
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem valuedAdicCompletion_def {x : adicCompletion K v} :
    Valued.v x = Valued.extensionValuation x.toCompletion := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_toCompletion** 是 Math
lib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   (x : IsDedekindDomain.HeightOneSp
ectrum.adicCompletion K v), Valued.v x.toCompletion = Valued.v x
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；x : IsDedekindDomain.He
ightOneSpectrum.adicCompletion K v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
-/
@[simp] theorem valued_toCompletion (x : adicCompletion K v) :
    Valued.v x.toCompletion = Valued.v x := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_ofCompletion** 是 Math
lib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   (y : (IsDedekindDomain.HeightOneS
pectrum.valuation K v).Completion), Valued.v { toCompletion := y } = Valued.v y
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；y : (IsDedekindDomain.H
eightOneSpectrum.valuation K v).Completion。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem valued_ofCompletion (y : (v.valuation K).Completion) :
    Valued.v (ofCompletion y : adicCompletion K v) = Valued.v y := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe** 是 Mathlib 中的一个定
理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：valued_coe (k : K) : Valued.v (↑k : adicCompletion K v) = v.valuation K k
参数：k : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithVal.equiv_symm_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : Linea
rOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (ofVal : 
R), (WithVal.e…
· 使用定理 `Valued.valuedCompletion_apply`：valuedCompletion_apply (x : K) : Valued.v
 (x : hat K) = v x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem valued_coe (k : K) :
    Valued.v (↑k : adicCompletion K v) = v.valuation K k := by
  simp
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext** 是 Mathlib 中的一个定理，位于命名空
间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   {x y : IsDedekindDomain.HeightOne
Spectrum.adicCompletion K v}, x.toCompletion = y.toCompletion → x = y
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[ext] theorem ext {x y : adicCompletion K v} (h : x.toCompletion = y.toCompletion) : x = y := by
  cases x; cases y; exact congrArg ofCompletion h
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.coe_zero** 是 Mathlib 中的一个定理，
位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R),   { toCompletion := ↑((WithVal.equ
iv (IsDedekindDomain.HeightOneSpectrum.valuation K v)).symm 0) } = 0
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；(WithVal.equiv (IsDedek
indDomain.HeightOneSpectrum.valuation K v)).symm 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext`：∀ {R : Type u_1} 
[inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Type u_2) [inst_2 : Field
 K]   [inst_3 : Algebra R K] [inst_4 : IsFr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithVal.equiv_symm_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : Linea
rOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (ofVal : 
R), (WithVal.e…
· 使用定理 `CompletableTopField.toT0Space`：∀ {K : Type u_1} {inst : Field K} {inst_1
 : UniformSpace K} [self : CompletableTopField K], T0Space K
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[norm_cast] lemma coe_zero : ((0 : K) : adicCompletion K v) = 0 := by
  apply adicCompletion.ext; simp
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.coe_one** 是 Mathlib 中的一个定理，位
于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R),   { toCompletion := ↑((WithVal.equ
iv (IsDedekindDomain.HeightOneSpectrum.valuation K v)).symm 1) } = 1
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；(WithVal.equiv (IsDedek
indDomain.HeightOneSpectrum.valuation K v)).symm 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext`：∀ {R : Type u_1} 
[inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Type u_2) [inst_2 : Field
 K]   [inst_3 : Algebra R K] [inst_4 : IsFr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithVal.equiv_symm_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : Linea
rOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (ofVal : 
R), (WithVal.e…
· 使用定理 `CompletableTopField.toT0Space`：∀ {K : Type u_1} {inst : Field K} {inst_1
 : UniformSpace K} [self : CompletableTopField K], T0Space K
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[norm_cast] lemma coe_one : ((1 : K) : adicCompletion K v) = 1 := by
  apply adicCompletion.ext; simp
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.coe_add** 是 Mathlib 中的一个定理，位
于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R) (x y : K),   { toCompletion := ↑((W
ithVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation K v)).symm (x + y)) }
 =     { toCompletion := ↑((WithVal.equiv (IsDedekindDomain.HeightOneSpectrum.va
luation K v)).symm x) } +       { toCompletion := ↑((WithVal.equiv (IsDedekindDo
main.HeightOneSpectrum.valuation K v)).symm y) }
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；x y : K；(WithVal.equiv 
(IsDedekindDomain.HeightOneSpectrum.valuation K v)).symm (x + y)；(WithVal.equiv 
(IsDedekindDomain.HeightOneSpectrum.valuation K v)).symm x；(WithVal.equiv (IsDed
ekindDomain.HeightOneSpectrum.valuation K v)).symm y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext`：∀ {R : Type u_1} 
[inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Type u_2) [inst_2 : Field
 K]   [inst_3 : Algebra R K] [inst_4 : IsFr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithVal.equiv_symm_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : Linea
rOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (ofVal : 
R), (WithVal.e…
· 使用定理 `UniformSpace.Completion.coe_add`：coe_add (a b : α) : ((a + b : α) : Comp
letion α) = a + b
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[norm_cast] lemma coe_add (x y : K) :
    ((x + y : K) : adicCompletion K v) = ↑x + ↑y := by
  apply adicCompletion.ext; simp [UniformSpace.Completion.coe_add]
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.coe_mul** 是 Mathlib 中的一个定理，位
于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R) (x y : K),   { toCompletion := ↑((W
ithVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation K v)).symm (x * y)) }
 =     { toCompletion := ↑((WithVal.equiv (IsDedekindDomain.HeightOneSpectrum.va
luation K v)).symm x) } *       { toCompletion := ↑((WithVal.equiv (IsDedekindDo
main.HeightOneSpectrum.valuation K v)).symm y) }
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；x y : K；(WithVal.equiv 
(IsDedekindDomain.HeightOneSpectrum.valuation K v)).symm (x * y)；(WithVal.equiv 
(IsDedekindDomain.HeightOneSpectrum.valuation K v)).symm x；(WithVal.equiv (IsDed
ekindDomain.HeightOneSpectrum.valuation K v)).symm y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext`：∀ {R : Type u_1} 
[inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Type u_2) [inst_2 : Field
 K]   [inst_3 : Algebra R K] [inst_4 : IsFr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithVal.equiv_symm_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : Linea
rOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (ofVal : 
R), (WithVal.e…
· 使用定理 `UniformSpace.Completion.coe_mul`：coe_mul (a b : α) : ((a * b : α) : Comp
letion α) = a * b
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[norm_cast] lemma coe_mul (x y : K) :
    ((x * y : K) : adicCompletion K v) = ↑x * ↑y := by
  apply adicCompletion.ext; simp [UniformSpace.Completion.coe_mul]

/-- `toCompletion` as a uniform-space isomorphism onto the underlying completion. -/
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv** 是 Mathlib 中的一
个定义，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：uniformEquiv : adicCompletion K v ≃ᵤ (v.valuation K).Completion where toEq
uiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toCompletion` as a uniform-space isomorphism onto the underlying completion.
-/
def uniformEquiv : adicCompletion K v ≃ᵤ (v.valuation K).Completion where
  toEquiv := equivCompletion K v
  uniformContinuous_toFun := uniformContinuous_comap
  uniformContinuous_invFun :=
    (isUniformInducing_toCompletion K v).uniformContinuous_iff.mpr uniformContinuous_id
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion** 是 
Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：continuous_toCompletion : Continuous (toCompletion (K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquiv.continuous`：∀ {α : Type u} {β : Type u_1} [inst : UniformSp
ace α] [inst_1 : UniformSpace β] (h : α ≃ᵤ β), Continuous ⇑h
-/
theorem continuous_toCompletion : Continuous (toCompletion (K := K) (v := v)) :=
  (uniformEquiv K v).continuous
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion** 是 
Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：continuous_ofCompletion : Continuous (ofCompletion (K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquiv.continuous`：∀ {α : Type u} {β : Type u_1} [inst : UniformSp
ace α] [inst_1 : UniformSpace β] (h : α ≃ᵤ β), Continuous ⇑h
-/
theorem continuous_ofCompletion : Continuous (ofCompletion (K := K) (v := v)) :=
  (uniformEquiv K v).symm.continuous
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `
IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T0Space (adicCompletion K v) :=
  (uniformEquiv K v).toHomeomorph.isEmbedding.t0Space

end adicCompletion

/-
**IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective** 是 Mathlib
 中的一个引理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuedAdicCompletion_surjective : Function.Surjective (Valued.v : (v.adicC
ompletion K) -> Intᵐ⁰)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Valued.valuedCompletion_surjective_iff`：valuedCompletion_surjective_iff 
: Function.Surjective (v : hat K -> Γ₀) ↔ Function.Surjective (v : K -> Γ₀)
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.valuation_surjective`：valuation_surje
ctive : Function.Surjective (v.valuation K)
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion_surjectiv
e`：toCompletion_surjective : Function.Surjective (toCompletion (K
-/
lemma valuedAdicCompletion_surjective :
    Function.Surjective (Valued.v : (v.adicCompletion K) → ℤᵐ⁰) := by
  have h : Function.Surjective (Valued.v : (v.valuation K).Completion → ℤᵐ⁰) :=
    Valued.valuedCompletion_surjective_iff.mpr <| .of_comp (v.valuation_surjective K)
  exact h.comp (adicCompletion.toCompletion_surjective K v)
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion_valueGroup_eq** 是 Mathlib 中的
一个引理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：adicCompletion_valueGroup_eq : MonoidWithZeroHom.valueGroup (.ofClass (Val
ued.v (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.valuation_surjective`：valuation_surje
ctive : Function.Surjective (v.valuation K)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithVal.equiv_symm_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : Linea
rOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (ofVal : 
R), (WithVal.e…
· 使用定理 `Valued.valuedCompletion_apply`：valuedCompletion_apply (x : K) : Valued.v
 (x : hat K) = v x
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma adicCompletion_valueGroup_eq : MonoidWithZeroHom.valueGroup (.ofClass (Valued.v
      (R := adicCompletion K v))) =
    MonoidWithZeroHom.valueGroup (.ofClass (valuation K v)) := by
  ext n
  simp only [MonoidWithZeroHom.mem_valueGroup_iff_of_comm, ne_eq, MonoidWithZeroHom.coe_ofClass]
  refine ⟨fun ⟨a, ha0, x, hx⟩ ↦ ?_, fun ⟨a, ha0, x, hx⟩ ↦
    ⟨↑a, by simpa using ha0, ↑x, by simpa using hx⟩⟩
  obtain ⟨b, hb⟩ := valuation_surjective K v (Valued.v a)
  obtain ⟨y, hy⟩ := valuation_surjective K v (Valued.v x)
  exact ⟨b, by rw [hb]; exact ha0, y, by rw [hb, hy]; exact hx⟩

/-- The ring of integers of `adicCompletion`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers** 是 Mathlib 中的一个定义，位
于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：adicCompletionIntegers : ValuationSubring (v.adicCompletion K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring of integers of `adicCompletion`.
-/
def adicCompletionIntegers : ValuationSubring (v.adicCompletion K) :=
  Valued.v.valuationSubring
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (adicCompletionIntegers K v) :=
  ⟨0⟩

variable (R)
/-
**IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers** 是 Mathlib 中的一个
定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：mem_adicCompletionIntegers {x : v.adicCompletion K} : x in v.adicCompletio
nIntegers K ↔ Valued.v x <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_adicCompletionIntegers {x : v.adicCompletion K} :
    x ∈ v.adicCompletionIntegers K ↔ Valued.v x ≤ 1 :=
  Iff.rfl
/-
**IsDedekindDomain.HeightOneSpectrum.notMem_adicCompletionIntegers** 是 Mathlib 中
的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：notMem_adicCompletionIntegers {x : v.adicCompletion K} : x ∉ v.adicComplet
ionIntegers K ↔ 1 < Valued.v x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers`：mem_adicC
ompletionIntegers {x : v.adicCompletion K} : x in v.adicCompletionIntegers K ↔ V
alued.v x <= 1
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
theorem notMem_adicCompletionIntegers {x : v.adicCompletion K} :
    x ∉ v.adicCompletionIntegers K ↔ 1 < Valued.v x := by
  rw [not_congr <| mem_adicCompletionIntegers R K v]
  exact not_le

section AlgebraInstances

/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) adicValued.has_uniform_continuous_const_smul' :
    UniformContinuousConstSMul R (WithVal <| v.valuation K) :=
  uniformContinuousConstSMul_of_continuousConstSMul R (WithVal <| v.valuation K)

section Algebra
variable [Algebra S K]

/-
**IsDedekindDomain.HeightOneSpectrum.adicValued.uniformContinuousConstSMul** 是 M
athlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicValued`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) {S : Type u_3} [inst_2 : Field K]   [inst_3 : CommSemiring S] [inst_4 : 
Algebra R K] [inst_5 : IsFractionRing R K]   (v : IsDedekindDomain.HeightOneSpec
trum R) [inst_6 : Algebra S K],   UniformContinuousConstSMul S (WithVal (IsDedek
indDomain.HeightOneSpectrum.valuation K v))
参数：R : Type u_1；K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；WithVal (I
sDedekindDomain.HeightOneSpectrum.valuation K v)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `UniformContinuousConstSMul.uniformContinuous_const_smul`：∀ {M : Type v} 
{X : Type x} {inst : UniformSpace X} {inst_1 : SMul M X} [self : UniformContinuo
usConstSMul M X] (c : M),   UniformContinuous…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
-/
instance adicValued.uniformContinuousConstSMul :
    UniformContinuousConstSMul S (WithVal <| v.valuation K) := by
  refine ⟨fun l ↦ ?_⟩
  simp_rw [WithVal.smul_right_def, Algebra.smul_def]
  exact (Ring.uniformContinuousConstSMul (WithVal <| v.valuation K)).uniformContinuous_const_smul _

open UniformSpace in
/-- The `S`-algebra structure on the underlying completion. -/
/-
**IsDedekindDomain.HeightOneSpectrum.instAlgebraCompletion** 是 Mathlib 中的一个实例，位于
命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：instAlgebraCompletion : Algebra S ((v.valuation K).Completion) where toSMu
l
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `S`-algebra structure on the underlying completion.
-/
noncomputable instance instAlgebraCompletion : Algebra S ((v.valuation K).Completion) where
  toSMul := Completion.instSMul _ _
  algebraMap := Completion.coeRingHom.comp (algebraMap S (WithVal (v.valuation K)))
  commutes' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)
    | ih x => rw [mul_comm]
  smul_def' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_const_smul _) (continuous_const_mul _)
    | ih x =>
      simp [Algebra.smul_def, Completion.algebraMap_def, WithVal.algebraMap_right_apply,
        Completion.coeRingHom]
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Algebra S (v.adicCompletion K) :=
  fast_instance% (adicCompletion.equivCompletion K v).algebra S
/-
**IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion_toCompletion** 是 
Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：algebraMap_adicCompletion_toCompletion (r : S) : (algebraMap S (v.adicComp
letion K) r).toCompletion = algebraMap S ((v.valuation K).Completion) r
参数：r : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_adicCompletion_toCompletion (r : S) :
    (algebraMap S (v.adicCompletion K) r).toCompletion =
      algebraMap S ((v.valuation K).Completion) r := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S₀ : Type*} [CommSemiring S₀] [Algebra S₀ S] [Algebra S₀ K] [IsScalarTower S₀ S K] :
    IsScalarTower S₀ S ((v.valuation K).Completion) :=
  .of_algebraMap_eq fun x ↦ by
    exact congrArg (UniformSpace.Completion.coeRingHom (α := WithVal (v.valuation K)))
      (IsScalarTower.algebraMap_apply S₀ S (WithVal (v.valuation K)) x)
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S₀ : Type*} [CommSemiring S₀] [Algebra S₀ S] [Algebra S₀ K] [IsScalarTower S₀ S K] :
    IsScalarTower S₀ S (v.adicCompletion K) :=
  .of_algebraMap_eq fun x ↦ by
    apply adicCompletion.ext
    rw [algebraMap_adicCompletion_toCompletion, algebraMap_adicCompletion_toCompletion,
      IsScalarTower.algebraMap_apply S₀ S ((v.valuation K).Completion)]
/-
**IsDedekindDomain.HeightOneSpectrum.coe_smul_adicCompletion** 是 Mathlib 中的一个定理，
位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：coe_smul_adicCompletion (r : S) (x : WithVal (v.valuation K)) : (↑(r • x) 
: v.adicCompletion K) = r • (↑x : v.adicCompletion K)
参数：r : S；x : WithVal (v.valuation K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext`：∀ {R : Type u_1} 
[inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Type u_2) [inst_2 : Field
 K]   [inst_3 : Algebra R K] [inst_4 : IsFr…
· 使用定理 `UniformSpace.Completion.coe_smul`：coe_smul (c : M) (x : X) : (↑(c • x) :
 Completion X) = c • (x : Completion X)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicValued.uniformContinuousConstSMul
`：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Type u
_2) {S : Type u_3} [inst_2 : Field K]   [inst_3 : CommSemiring…
-/
theorem coe_smul_adicCompletion (r : S) (x : WithVal (v.valuation K)) :
    (↑(r • x) : v.adicCompletion K) = r • (↑x : v.adicCompletion K) := by
  apply adicCompletion.ext
  exact UniformSpace.Completion.coe_smul r x
/-
**IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion** 是 Mathlib 中的一个定
理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：algebraMap_adicCompletion : ⇑(algebraMap S <| v.adicCompletion K) = (↑) ∘ 
algebraMap S K
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_adicCompletion : ⇑(algebraMap S <| v.adicCompletion K) = (↑) ∘ algebraMap S K :=
  rfl

variable {R} in
/-
**IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap** 是 Mathlib 中的一个定理，位于
命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：denseRange_algebraMap : DenseRange (algebraMap K (v.adicCompletion K))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion`：algebraMap
_adicCompletion : ⇑(algebraMap S <| v.adicCompletion K) = (↑) ∘ algebraMap S K
· 使用定理 `DenseRange.comp`：DenseRange.comp {g : Y -> Z} {f : α -> Y} (hg : DenseRa
nge g) (hf : DenseRange f) (cg : Continuous g) : DenseRange (g ∘ f)
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjectiv
e`：ofCompletion_surjective : Function.Surjective (ofCompletion (K
· 使用定理 `UniformSpace.Completion.denseRange_coe`：denseRange_coe : DenseRange ((↑)
 : α -> Completion α)
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
· 使用定理 `UniformSpace.Completion.continuous_coe`：continuous_coe : Continuous ((↑)
 : α -> Completion α)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletio
n`：continuous_ofCompletion : Continuous (ofCompletion (K
-/
theorem denseRange_algebraMap : DenseRange (algebraMap K (v.adicCompletion K)) := by
  rw [algebraMap_adicCompletion]
  exact (adicCompletion.ofCompletion_surjective K v).denseRange.comp
    (UniformSpace.Completion.denseRange_coe.comp (WithVal.equiv _).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _))
    (adicCompletion.continuous_ofCompletion K v)

end Algebra

/-
**IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem** 是 Mathlib 中的一个定理，位于命名空
间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：coe_algebraMap_mem (r : R) : ↑((algebraMap R K) r) in adicCompletionIntege
rs K v
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers`：mem_adicC
ompletionIntegers {x : v.adicCompletion K} : x in v.adicCompletionIntegers K ↔ V
alued.v x <= 1
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `Valued.valuedCompletion_apply`：valuedCompletion_apply (x : K) : Valued.v
 (x : hat K) = v x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithVal.equiv_symm_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : Linea
rOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (ofVal : 
R), (WithVal.e…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_le_one`：valuation_le_one (r
 : R) : v.valuation K r <= 1
-/
theorem coe_algebraMap_mem (r : R) : ↑((algebraMap R K) r) ∈ adicCompletionIntegers K v := by
  rw [mem_adicCompletionIntegers]
  change Valued.v (↑((algebraMap R K) r) : adicCompletion K v).toCompletion ≤ 1
  rw [Valued.valuedCompletion_apply]
  simpa using v.valuation_le_one _
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R (v.adicCompletionIntegers K) where
  smul r x :=
    ⟨r • (x : v.adicCompletion K), by
      rw [Algebra.smul_def]
      refine ValuationSubring.mul_mem _ _ _ ?_ x.2
      rw [algebraMap_adicCompletion]
      exact coe_algebraMap_mem _ _ v r⟩
  algebraMap :=
  { toFun r :=
      ⟨(algebraMap R K r : adicCompletion K v), coe_algebraMap_mem _ _ v r⟩
    map_one' := by ext; simp
    map_mul' x y := by
      ext
      simp [map_mul, UniformSpace.Completion.coe_mul]
    map_zero' := by ext; simp
    map_add' x y := by
      ext
      simp [map_add, UniformSpace.Completion.coe_add] }
  commutes' r x := by
    rw [mul_comm]
  smul_def' r x := by
    ext
    simp +instances only [Algebra.smul_def]
    rfl

@[simp]
/-
**IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply** 是
 Mathlib 中的一个引理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：algebraMap_adicCompletionIntegers_apply (r : R) : algebraMap R (v.adicComp
letionIntegers K) r = (algebraMap R K r : v.adicCompletion K)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
-/
lemma algebraMap_adicCompletionIntegers_apply (r : R) :
    algebraMap R (v.adicCompletionIntegers K) r = (algebraMap R K r : v.adicCompletion K) := by
  rfl
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FaithfulSMul R K] : FaithfulSMul R (v.adicCompletionIntegers K) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y
  rw [Subtype.ext_iff]
  simp

variable {R K} in
open scoped algebraMap in -- to make the coercions from `R` fire
/-- The valuation on the completion agrees with the global valuation on elements of the
integer ring. -/
/-
**IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation** 是 Mathl
ib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuedAdicCompletion_eq_valuation (r : R) : Valued.v (r : v.adicCompletion
 K) = v.valuation K r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_toCompletion`：∀
 {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Type u_2)
 [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFr…
· 使用定理 `Valued.valuedCompletion_apply`：valuedCompletion_apply (x : K) : Valued.v
 (x : hat K) = v x

--- 原说明 ---
The valuation on the completion agrees with the global valuation on elements of 
the
integer ring.
-/
theorem valuedAdicCompletion_eq_valuation (r : R) :
    Valued.v (r : v.adicCompletion K) = v.valuation K r := by
  rw [← adicCompletion.valued_toCompletion]
  exact Valued.valuedCompletion_apply _

variable {R K} in
/-- The valuation on the completion agrees with the global valuation on elements of the field. -/
/-
**IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'** 是 Math
lib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：valuedAdicCompletion_eq_valuation' (k : K) : Valued.v (k : v.adicCompletio
n K) = v.valuation K k
参数：k : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_toCompletion`：∀
 {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Type u_2)
 [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFr…
· 使用定理 `Valued.valuedCompletion_apply`：valuedCompletion_apply (x : K) : Valued.v
 (x : hat K) = v x

--- 原说明 ---
The valuation on the completion agrees with the global valuation on elements of 
the field.
-/
theorem valuedAdicCompletion_eq_valuation' (k : K) :
    Valued.v (k : v.adicCompletion K) = v.valuation K k := by
  rw [← adicCompletion.valued_toCompletion]
  exact Valued.valuedCompletion_apply _

variable {R K} in
open scoped algebraMap in -- to make the coercion from `R` fire
/-- A global integer is in the local integers. -/
/-
**IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers** 是 Mathlib 
中的一个引理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：coe_mem_adicCompletionIntegers (r : R) : (r : adicCompletion K v) in adicC
ompletionIntegers K v
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers`：mem_adicC
ompletionIntegers {x : v.adicCompletion K} : x in v.adicCompletionIntegers K ↔ V
alued.v x <= 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation`：va
luedAdicCompletion_eq_valuation (r : R) : Valued.v (r : v.adicCompletion K) = v.
valuation K r
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_le_one`：valuation_le_one (r
 : R) : v.valuation K r <= 1

--- 原说明 ---
A global integer is in the local integers.
-/
lemma coe_mem_adicCompletionIntegers (r : R) :
    (r : adicCompletion K v) ∈ adicCompletionIntegers K v := by
  rw [mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation]
  exact valuation_le_one v r

@[simp]
/-
**IsDedekindDomain.HeightOneSpectrum.coe_smul_adicCompletionIntegers** 是 Mathlib
 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：coe_smul_adicCompletionIntegers (r : R) (x : v.adicCompletionIntegers K) :
 (↑(r • x) : v.adicCompletion K) = r • (x : v.adicCompletion K)
参数：r : R；x : v.adicCompletionIntegers K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
-/
theorem coe_smul_adicCompletionIntegers (r : R) (x : v.adicCompletionIntegers K) :
    (↑(r • x) : v.adicCompletion K) = r • (x : v.adicCompletion K) :=
  rfl
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.IsTorsionFree R (v.adicCompletionIntegers K) := .of_smul_eq_zero <| by simp
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsScalarTower'** 是 Mathl
ib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletion`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R),   IsScalarTower R (↥(IsDedekindDom
ain.HeightOneSpectrum.adicCompletionIntegers K v))     (IsDedekindDomain.HeightO
neSpectrum.adicCompletion K v)
参数：R : Type u_1；K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；↥(IsDedeki
ndDomain.HeightOneSpectrum.adicCompletionIntegers K v)；IsDedekindDomain.HeightOn
eSpectrum.adicCompletion K v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
instance adicCompletion.instIsScalarTower' :
    IsScalarTower R (v.adicCompletionIntegers K) (v.adicCompletion K) where
  smul_assoc x y z := by simp only [Algebra.smul_def]; apply mul_assoc

end AlgebraInstances

variable {R}

open nonZeroDivisors algebraMap in
variable {K} in
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicC
ompletionIntegers** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.
adicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] {K : Ty
pe u_2} [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R)   (a : IsDedekindDomain.HeightOneSp
ectrum.adicCompletion K v),   ∃ b ∈ nonZeroDivisors R, a * ↑b ∈ IsDedekindDomain
.HeightOneSpectrum.adicCompletionIntegers K v
参数：v : IsDedekindDomain.HeightOneSpectrum R；a : IsDedekindDomain.HeightOneSpectr
um.adicCompletion K v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer`：intV
aluation_exists_uniformizer : exists π : R, v.intValuation π = WithZero.exp (-1 
: Int)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation`：va
luedAdicCompletion_eq_valuation (r : R) : Valued.v (r : v.adicCompletion K) = v.
valuation K r
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `WithZero.exp_ne_zero`：∀ {M : Type u_4} {a : M}, WithZero.exp a ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
（共 51 条，此处仅展示前 30 条）
-/
lemma adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers (v : HeightOneSpectrum R)
    (a : v.adicCompletion K) : ∃ b ∈ R⁰, a * b ∈ v.adicCompletionIntegers K := by
  by_cases ha : a ∈ v.adicCompletionIntegers K
  · use 1
    simp [ha]
  · rw [notMem_adicCompletionIntegers] at ha
    -- let ϖ be a uniformiser
    obtain ⟨ϖ, hϖ⟩ := intValuation_exists_uniformizer v
    have : Valued.v (algebraMap R (v.adicCompletion K) ϖ) = (exp (1 : ℤ))⁻¹ := by
      simp [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap, hϖ, exp]
    have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp [exp_ne_zero.symm] at hϖ
    refine ⟨ϖ^(log (Valued.v a)).natAbs, pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ0) _, ?_⟩
    -- now manually translate the goal (an inequality in ℤᵐ⁰) to an inequality of "log" of ℤ
    simp only [map_pow, mem_adicCompletionIntegers, map_mul, this, inv_pow, ← exp_nsmul, nsmul_one,
      Int.natCast_natAbs]
    exact mul_inv_le_one_of_le₀ (le_exp_log.trans (by simp [le_abs_self])) zero_le
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FaithfulSMul (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  Subsemiring.faithfulSMul _
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers** 是 Mathlib
 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Ty
pe u_2) [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (v : IsDedekindDomain.HeightOneSpectrum R),   Valued.v.Integers ↥(IsDedekindDo
main.HeightOneSpectrum.adicCompletionIntegers K v)
参数：K : Type u_2；v : IsDedekindDomain.HeightOneSpectrum R；IsDedekindDomain.Height
OneSpectrum.adicCompletionIntegers K v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.instFaithfulSMulSubtypeAdicCompletion
MemValuationSubringAdicCompletionIntegers_1`：∀ {R : Type u_1} [inst : CommRing R
] [inst_1 : IsDedekindDomain R] (K : Type u_2) [inst_2 : Field K]   [inst_3 : Al
gebra R K] [inst_4 : IsFr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem adicCompletionIntegers.integers :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Integers ↥(adicCompletionIntegers K v) where
  hom_inj := FaithfulSMul.algebraMap_injective _ _
  map_le_one := by simp [mem_adicCompletionIntegers]
  exists_of_le_one := by simp [mem_adicCompletionIntegers]

variable {K v}
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq
_one** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicCompletio
nIntegers`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] {K : Ty
pe u_2} [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] {v : IsDedekindDomain.HeightOneSpectrum R}   {a : ↥(IsDedekindDomain.HeightOne
Spectrum.adicCompletionIntegers K v)}, IsUnit a ↔ Valued.v ↑a = 1
参数：IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.Integers.isUnit_iff_valuation_eq_one`：isUnit_iff_valuation_eq_
one (hv : Integers v O) {x : O} : IsUnit x ↔ v (algebraMap O F x) = 1
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers`：∀ {R
 : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Type u_2) [i
nst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFr…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem adicCompletionIntegers.isUnit_iff_valued_eq_one {a : v.adicCompletionIntegers K} :
    IsUnit a ↔ Valued.v a.1 = 1 := by
  simp [Valuation.Integers.isUnit_iff_valuation_eq_one (integers K v)]
/-
**IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued
_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.adicComple
tionIntegers`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] {K : Ty
pe u_2} [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] {v : IsDedekindDomain.HeightOneSpectrum R}   {a : (IsDedekindDomain.HeightOneS
pectrum.adicCompletion K v)ˣ},   a ∈ (IsDedekindDomain.HeightOneSpectrum.adicCom
pletionIntegers K v).units ↔ Valued.v ↑a = 1
参数：IsDedekindDomain.HeightOneSpectrum.adicCompletion K v；IsDedekindDomain.Height
OneSpectrum.adicCompletionIntegers K v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_val
ued_eq_one`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] {
K : Type u_2} [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFr…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `instPosMulStrictMonoWithZeroOfMulLeftStrictMono`：∀ {α : Type u_1} [inst 
: Mul α] [inst_1 : Preorder α] [MulLeftStrictMono α], PosMulStrictMono (WithZero
 α)
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem adicCompletionIntegers.mem_units_iff_valued_eq_one {a : (v.adicCompletion K)ˣ} :
    a ∈ (v.adicCompletionIntegers K).units ↔ Valued.v a.1 = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦
     ⟨h.le, by simp [mem_adicCompletionIntegers, inv_le_one_iff₀, h.symm.le]⟩⟩
  convert! isUnit_iff_valued_eq_one.1 (Submonoid.unitsEquivIsUnitSubmonoid _ ⟨_, h⟩).2

section AbsoluteValue

open WithZeroMulInt NNReal

variable (v) {b : ℝ≥0} (hb : 1 < b) (r : R) (x : K)

/-- The `v`-adic absolute value function on `R` defined as `b` raised to negative `v`-adic
valuation, for some `b` in `ℝ≥0` -/
/-
**IsDedekindDomain.HeightOneSpectrum.intAdicAbvDef** 是 Mathlib 中的一个定义，位于命名空间 `Is
DedekindDomain.HeightOneSpectrum`。
形式化陈述：intAdicAbvDef (r : R) : Real>=0
参数：r : R。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `v`-adic absolute value function on `R` defined as `b` raised to negative `v
`-adic
valuation, for some `b` in `ℝ≥0`
-/
def intAdicAbvDef (r : R) : ℝ≥0 := toNNReal (ne_zero_of_lt hb) (v.intValuation r)
/-
**IsDedekindDomain.HeightOneSpectrum.isNonarchimedean_intAdicAbvDef** 是 Mathlib 
中的一个引理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：isNonarchimedean_intAdicAbvDef : IsNonarchimedean (v.intAdicAbvDef hb)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `WithZeroMulInt.toNNReal_strictMono`：toNNReal_strictMono {e : Real>=0} (h
e : 1 < e) : StrictMono (toNNReal he.ne_zero)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
lemma isNonarchimedean_intAdicAbvDef : IsNonarchimedean (v.intAdicAbvDef hb) := by
  intro x y
  simp only [intAdicAbvDef]
  have h_mono := (toNNReal_strictMono hb).monotone
  rw [← h_mono.map_max]
  exact h_mono <| v.intValuation.map_add x y

/-- The `v`-adic absolute value on `R` defined as `b` raised to negative `v`-adic
valuation, for some `b` in `ℝ≥0` -/
/-
**IsDedekindDomain.HeightOneSpectrum.intAdicAbv** 是 Mathlib 中的一个定义，位于命名空间 `IsDed
ekindDomain.HeightOneSpectrum`。
形式化陈述：intAdicAbv : AbsoluteValue R Real where toFun r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `v`-adic absolute value on `R` defined as `b` raised to negative `v`-adic
valuation, for some `b` in `ℝ≥0`
-/
def intAdicAbv : AbsoluteValue R ℝ where
  toFun r := v.intAdicAbvDef hb r
  map_mul' _ _ := by simp [intAdicAbvDef]
  nonneg' _ := zero_le_coe
  eq_zero' _ := by simp [intAdicAbvDef, intValuation_def]
  add_le' _ _ := (isNonarchimedean_intAdicAbvDef v hb).add_le fun _ ↦ bot_le

/-- The `v`-adic absolute value is nonarchimedean -/
/-
**IsDedekindDomain.HeightOneSpectrum.isNonarchimedean_intAdicAbv** 是 Mathlib 中的一
个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：isNonarchimedean_intAdicAbv : IsNonarchimedean (v.intAdicAbv hb)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.isNonarchimedean_intAdicAbvDef`：isNon
archimedean_intAdicAbvDef : IsNonarchimedean (v.intAdicAbvDef hb)

--- 原说明 ---
The `v`-adic absolute value is nonarchimedean
-/
theorem isNonarchimedean_intAdicAbv : IsNonarchimedean (v.intAdicAbv hb) :=
  isNonarchimedean_intAdicAbvDef v hb
/-
**IsDedekindDomain.HeightOneSpectrum.intAdicAbv_le_one** 是 Mathlib 中的一个定理，位于命名空间
 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intAdicAbv_le_one : v.intAdicAbv hb r <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `WithZeroMulInt.toNNReal_le_one_iff`：toNNReal_le_one_iff {e : Real>=0} {m
 : Intᵐ⁰} (he : 1 < e) : toNNReal (ne_zero_of_lt he) m <= 1 ↔ m <= 1
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_one`：intValuation_le_
one (x : R) : v.intValuation x <= 1
-/
theorem intAdicAbv_le_one : v.intAdicAbv hb r ≤ 1 := by
  simpa [intAdicAbv, intAdicAbvDef, toNNReal_le_one_iff hb] using intValuation_le_one v r
/-
**IsDedekindDomain.HeightOneSpectrum.intAdicAbv_lt_one_iff** 是 Mathlib 中的一个定理，位于
命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intAdicAbv_lt_one_iff : v.intAdicAbv hb r < 1 ↔ r in v.asIdeal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `WithZeroMulInt.toNNReal_lt_one_iff`：toNNReal_lt_one_iff {e : Real>=0} {m
 : Intᵐ⁰} (he : 1 < e) : toNNReal (ne_zero_of_lt he) m < 1 ↔ m < 1
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem`：intValua
tion_lt_one_iff_mem (r : R) : v.intValuation r < 1 ↔ r in v.asIdeal
-/
theorem intAdicAbv_lt_one_iff : v.intAdicAbv hb r < 1 ↔ r ∈ v.asIdeal := by
  simpa [intAdicAbv, intAdicAbvDef, toNNReal_lt_one_iff hb] using intValuation_lt_one_iff_mem v r
/-
**IsDedekindDomain.HeightOneSpectrum.intAdicAbv_eq_one_iff** 是 Mathlib 中的一个定理，位于
命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：intAdicAbv_eq_one_iff : v.intAdicAbv hb r = 1 ↔ r ∉ v.asIdeal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intAdicAbv_lt_one_iff`：intAdicAbv_lt_
one_iff : v.intAdicAbv hb r < 1 ↔ r in v.asIdeal
· 使用定理 `ne_iff_lt_iff_le`：ne_iff_lt_iff_le : (a != b ↔ a < b) ↔ a <= b
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intAdicAbv_le_one`：intAdicAbv_le_one 
: v.intAdicAbv hb r <= 1
-/
theorem intAdicAbv_eq_one_iff : v.intAdicAbv hb r = 1 ↔ r ∉ v.asIdeal := by
  contrapose
  rw [← v.intAdicAbv_lt_one_iff hb, ne_iff_lt_iff_le]
  exact intAdicAbv_le_one v hb r

/-- The `v`-adic absolute value function on `K` defined as `b` raised to negative `v`-adic
valuation, for some `b` in `ℝ≥0` -/
/-
**IsDedekindDomain.HeightOneSpectrum.adicAbvDef** 是 Mathlib 中的一个定义，位于命名空间 `IsDed
ekindDomain.HeightOneSpectrum`。
形式化陈述：adicAbvDef (x : K) : Real>=0
参数：x : K。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `v`-adic absolute value function on `K` defined as `b` raised to negative `v
`-adic
valuation, for some `b` in `ℝ≥0`
-/
def adicAbvDef (x : K) : ℝ≥0 := toNNReal (ne_zero_of_lt hb) (v.valuation K x)
/-
**IsDedekindDomain.HeightOneSpectrum.isNonarchimedean_adicAbvDef** 是 Mathlib 中的一
个引理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：isNonarchimedean_adicAbvDef : IsNonarchimedean (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `WithZeroMulInt.toNNReal_strictMono`：toNNReal_strictMono {e : Real>=0} (h
e : 1 < e) : StrictMono (toNNReal he.ne_zero)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
lemma isNonarchimedean_adicAbvDef : IsNonarchimedean (α := K) (v.adicAbvDef hb) := by
  intro x y
  simp only [adicAbvDef]
  have h_mono := (toNNReal_strictMono hb).monotone
  rw [← h_mono.map_max]
  exact h_mono ((v.valuation _).map_add x y)

/-- The `v`-adic absolute value on `K` defined as `b` raised to negative `v`-adic
valuation, for some `b` in `ℝ≥0` -/
/-
**IsDedekindDomain.HeightOneSpectrum.adicAbv** 是 Mathlib 中的一个定义，位于命名空间 `IsDedeki
ndDomain.HeightOneSpectrum`。
形式化陈述：adicAbv : AbsoluteValue K Real where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `v`-adic absolute value on `K` defined as `b` raised to negative `v`-adic
valuation, for some `b` in `ℝ≥0`
-/
def adicAbv : AbsoluteValue K ℝ where
  toFun x := v.adicAbvDef hb x
  map_mul' _ _ := by simp [adicAbvDef]
  nonneg' _ := zero_le_coe
  eq_zero' _ := by simp [adicAbvDef]
  add_le' _ _ := (isNonarchimedean_adicAbvDef v hb).add_le fun _ ↦ bot_le

/-- The `v`-adic absolute value is nonarchimedean -/
/-
**IsDedekindDomain.HeightOneSpectrum.isNonarchimedean_adicAbv** 是 Mathlib 中的一个定理
，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：isNonarchimedean_adicAbv : IsNonarchimedean (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.isNonarchimedean_adicAbvDef`：isNonarc
himedean_adicAbvDef : IsNonarchimedean (α

--- 原说明 ---
The `v`-adic absolute value is nonarchimedean
-/
theorem isNonarchimedean_adicAbv : IsNonarchimedean (α := K) (v.adicAbv hb) :=
  isNonarchimedean_adicAbvDef v hb

/-- The `v`-adic absolute value of `r / s : K` is the absolute value of `r` divided by the absolute
value of `s`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.adicAbv_of_mk'** 是 Mathlib 中的一个定理，位于命名空间 `I
sDedekindDomain.HeightOneSpectrum`。
形式化陈述：adicAbv_of_mk' {s : nonZeroDivisors R} : v.adicAbv hb (IsLocalization.mk' 
K r s) = v.intAdicAbv hb r / v.intAdicAbv hb s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `v`-adic absolute value of `r / s : K` is the absolute value of `r` divided 
by the absolute
value of `s`.
-/
theorem adicAbv_of_mk' {s : nonZeroDivisors R} :
    v.adicAbv hb (IsLocalization.mk' K r s) = v.intAdicAbv hb r / v.intAdicAbv hb s := by
  simp [adicAbv, adicAbvDef, intAdicAbv, intAdicAbvDef, valuation_of_algebraMap]

/-- The `v`-adic absolute value on `K` extends the `v`-adic absolute value on `R`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.adicAbv_of_algebraMap** 是 Mathlib 中的一个定理，位于
命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：adicAbv_of_algebraMap (r : R) : v.adicAbv hb (algebraMap R K r) = v.intAdi
cAbv hb r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `v`-adic absolute value on `K` extends the `v`-adic absolute value on `R`.
-/
theorem adicAbv_of_algebraMap (r : R) : v.adicAbv hb (algebraMap R K r) = v.intAdicAbv hb r := by
  simp [adicAbv, adicAbvDef, intAdicAbv, intAdicAbvDef, valuation_of_algebraMap]
/-
**IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one** 是 Mathlib 中的一个定理，位于命名空
间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：adicAbv_coe_le_one : v.adicAbv hb (algebraMap R K r) <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicAbv_of_algebraMap`：adicAbv_of_alg
ebraMap (r : R) : v.adicAbv hb (algebraMap R K r) = v.intAdicAbv hb r
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intAdicAbv_le_one`：intAdicAbv_le_one 
: v.intAdicAbv hb r <= 1
-/
theorem adicAbv_coe_le_one : v.adicAbv hb (algebraMap R K r) ≤ 1 := by
  rw [adicAbv_of_algebraMap]
  exact intAdicAbv_le_one v hb r
/-
**IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_lt_one_iff** 是 Mathlib 中的一个定理，位
于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：adicAbv_coe_lt_one_iff : v.adicAbv hb (algebraMap R K r) < 1 ↔ r in v.asId
eal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicAbv_of_algebraMap`：adicAbv_of_alg
ebraMap (r : R) : v.adicAbv hb (algebraMap R K r) = v.intAdicAbv hb r
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intAdicAbv_lt_one_iff`：intAdicAbv_lt_
one_iff : v.intAdicAbv hb r < 1 ↔ r in v.asIdeal
-/
theorem adicAbv_coe_lt_one_iff : v.adicAbv hb (algebraMap R K r) < 1 ↔ r ∈ v.asIdeal := by
  rw [adicAbv_of_algebraMap]
  exact intAdicAbv_lt_one_iff v hb r
/-
**IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_eq_one_iff** 是 Mathlib 中的一个定理，位
于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：adicAbv_coe_eq_one_iff : v.adicAbv hb (algebraMap R K r) = 1 ↔ r ∉ v.asIde
al
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicAbv_of_algebraMap`：adicAbv_of_alg
ebraMap (r : R) : v.adicAbv hb (algebraMap R K r) = v.intAdicAbv hb r
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intAdicAbv_eq_one_iff`：intAdicAbv_eq_
one_iff : v.intAdicAbv hb r = 1 ↔ r ∉ v.asIdeal
-/
theorem adicAbv_coe_eq_one_iff : v.adicAbv hb (algebraMap R K r) = 1 ↔ r ∉ v.asIdeal := by
  rw [adicAbv_of_algebraMap]
  exact intAdicAbv_eq_one_iff v hb r

end AbsoluteValue

end IsDedekindDomain.HeightOneSpectrum

namespace Rat

open IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]

/-
**Rat.valuation_le_one_iff_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：valuation_le_one_iff_den {𝔭 : HeightOneSpectrum R} {x : Rat} : 𝔭.valuation
 Rat x <= 1 ↔ ↑x.den ∉ 𝔭.asIdeal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `algebraMap_comp_natCast`：algebraMap_comp_natCast (R A : Type*) [CommSemi
ring R] [Semiring A] [Algebra R A] : algebraMap R A ∘ Nat.cast = Nat.cast
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_div_le_one_iff`：valuation_d
iv_le_one_iff (a : R) {b : R} (hb : b != 0) (h : b in v.asIdeal -> a ∉ v.asIdeal
) : v.valuation K (a / b) <= 1 ↔ b ∉ v.asIdeal
· 使用定理 `Ideal.IsPrime.notMem_of_isCoprime_of_mem`：∀ {R : Type u} [inst : CommSem
iring R] {I : Ideal R} [I.IsPrime] {x y : R}, IsCoprime x y → x ∈ I → y ∉ I
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `IsCoprime.intCast`：IsCoprime.intCast {R : Type*} [CommRing R] {a b : Int
} (h : IsCoprime a b) : IsCoprime (a : R) (b : R)
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
· 使用定理 `Rat.isCoprime_num_den`：Rat.isCoprime_num_den (x : Rat) : IsCoprime x.num
 x.den
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用引理 `Rat.num_div_den`：num_div_den (r : Rat) : (r.num : Rat) / (r.den : Rat) =
 r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem valuation_le_one_iff_den {𝔭 : HeightOneSpectrum R} {x : ℚ} :
    𝔭.valuation ℚ x ≤ 1 ↔ ↑x.den ∉ 𝔭.asIdeal := by
  have : CharZero R := ⟨.of_comp (f := algebraMap R ℚ) (by simpa using Nat.cast_injective)⟩
  have : (x.den : R) ≠ 0 := by simp
  simp [x.num_div_den, ← 𝔭.valuation_div_le_one_iff ℚ x.num this
    (Ideal.IsPrime.notMem_of_isCoprime_of_mem (mod_cast x.isCoprime_num_den.symm.intCast))]

end Rat

