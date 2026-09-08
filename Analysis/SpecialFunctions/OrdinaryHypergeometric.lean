/-
Copyright (c) 2024 Edward Watine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward Watine
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.RCLike.Basic

/-!
# Ordinary hypergeometric function in a Banach algebra

In this file, we define `ordinaryHypergeometric`, the _ordinary_ or _Gaussian_ hypergeometric
function in a topological algebra `𝔸` over a field `𝕂` given by:
$$
_2\mathrm{F}_1(a\ b\ c : \mathbb{K}, x : \mathbb{A}) = \sum_{n=0}^{\infty}\frac{(a)_n(b)_n}{(c)_n}
\frac{x^n}{n!}   \,,
$$
with $(a)_n$ is the ascending Pochhammer symbol (see `ascPochhammer`).

This file contains the basic definitions over a general field `𝕂` and notation for `₂F₁`,
as well as showing that terms of the series are zero if any of the `(a b c : 𝕂)` are sufficiently
large non-positive integers, rendering the series finite. In this file "sufficiently large" means
that `-n < a` for the `n`-th term, and similarly for `b` and `c`.

- `ordinaryHypergeometricSeries` is the `FormalMultilinearSeries` given above for some `(a b c : 𝕂)`
- `ordinaryHypergeometric` is the sum of the series for some `(x : 𝔸)`
- `ordinaryHypergeometricSeries_eq_zero_of_nonpos_int` shows that the `n`-th term of the series is
  zero if any of the parameters are sufficiently large non-positive integers

## `[RCLike 𝕂]`

If we have `[RCLike 𝕂]`, then we show that the latter result is an iff, and hence prove that the
radius of convergence of the series is unity if the series is infinite, or `⊤` otherwise.

- `ordinaryHypergeometricSeries_eq_zero_iff` is iff variant of
  `ordinaryHypergeometricSeries_eq_zero_of_nonpos_int`
- `ordinaryHypergeometricSeries_radius_eq_one` proves that the radius of convergence of the
  `ordinaryHypergeometricSeries` is unity under non-trivial parameters

## Notation

`₂F₁` is notation for `ordinaryHypergeometric`.

## References

See <https://en.wikipedia.org/wiki/Hypergeometric_function>.

## Tags

hypergeometric, gaussian, ordinary
-/

@[expose] public section

open Nat FormalMultilinearSeries

section Field

variable {𝕂 : Type*} (𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

/-- The coefficients in the ordinary hypergeometric sum. -/
/-
**ordinaryHypergeometricCoefficient** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ordinaryHypergeometricCoefficient (a b c : 𝕂) (n : Nat)
参数：a b c : 𝕂；n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coefficients in the ordinary hypergeometric sum.
-/
noncomputable abbrev ordinaryHypergeometricCoefficient (a b c : 𝕂) (n : ℕ) := ((n !⁻¹ : 𝕂) *
    (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b * ((ascPochhammer 𝕂 n).eval c)⁻¹)

/-- `ordinaryHypergeometricSeries 𝔸 (a b c : 𝕂)` is a `FormalMultilinearSeries`.
Its sum is the `ordinaryHypergeometric` map. -/
/-
**ordinaryHypergeometricSeries** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ordinaryHypergeometricSeries (a b c : 𝕂) : FormalMultilinearSeries 𝕂 𝔸 𝔸
参数：a b c : 𝕂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ordinaryHypergeometricSeries 𝔸 (a b c : 𝕂)` is a `FormalMultilinearSeries`.
Its sum is the `ordinaryHypergeometric` map.
-/
noncomputable def ordinaryHypergeometricSeries (a b c : 𝕂) : FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  ofScalars 𝔸 (ordinaryHypergeometricCoefficient a b c)

variable {𝔸} (a b c : 𝕂)

/-- `ordinaryHypergeometric (a b c : 𝕂) : 𝔸 → 𝔸`, denoted `₂F₁`, is the ordinary hypergeometric map,
defined as the sum of the `FormalMultilinearSeries` `ordinaryHypergeometricSeries 𝔸 a b c`.

Note that this takes the junk value `0` outside the radius of convergence.
-/
/-
**ordinaryHypergeometric** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ordinaryHypergeometric (x : 𝔸) : 𝔸
参数：x : 𝔸。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ordinaryHypergeometric (a b c : 𝕂) : 𝔸 → 𝔸`, denoted `₂F₁`, is the ordinary hyp
ergeometric map,
defined as the sum of the `FormalMultilinearSeries` `ordinaryHypergeometricSerie
s 𝔸 a b c`.

Note that this takes the junk value `0` outside the radius of convergence.
-/
noncomputable def ordinaryHypergeometric (x : 𝔸) : 𝔸 :=
  (ordinaryHypergeometricSeries 𝔸 a b c).sum x

@[inherit_doc]
notation "₂F₁" => ordinaryHypergeometric
/-
**ordinaryHypergeometricSeries_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ordinaryHypergeometricSeries_apply_eq (x : 𝔸) (n : Nat) : (ordinaryHyperge
ometricSeries 𝔸 a b c n fun _ => x) = ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a 
* (ascPochhammer 𝕂 n).eval b * ((ascPochhammer 𝕂 n).eval c)⁻¹) • x ^ n
参数：x : 𝔸；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ordinaryHypergeometricSeries.eq_1`：∀ {𝕂 : Type u_1} (𝔸 : Type u_2) [inst
 : Field 𝕂] [inst_1 : Ring 𝔸] [inst_2 : Algebra 𝕂 𝔸] [inst_3 : TopologicalSpace 
𝔸]   [inst_4 : IsTopolo…
· 使用定理 `FormalMultilinearSeries.ofScalars_apply_eq`：ofScalars_apply_eq (x : E) (
n : Nat) : ofScalars E c n (fun _ => x) = c n • x ^ n
-/
theorem ordinaryHypergeometricSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (ordinaryHypergeometricSeries 𝔸 a b c n fun _ => x) =
      ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
        ((ascPochhammer 𝕂 n).eval c)⁻¹) • x ^ n := by
  rw [ordinaryHypergeometricSeries, ofScalars_apply_eq]

/-- This naming follows the convention of `NormedSpace.expSeries_apply_eq'`. -/
/-
**ordinaryHypergeometricSeries_apply_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ordinaryHypergeometricSeries_apply_eq' (x : 𝔸) : (fun n => ordinaryHyperge
ometricSeries 𝔸 a b c n fun _ => x) = fun n => ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n
).eval a * (ascPochhammer 𝕂 n).eval b * ((ascPochhammer 𝕂 n).eval c)⁻¹) • x ^ n
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ordinaryHypergeometricSeries.eq_1`：∀ {𝕂 : Type u_1} (𝔸 : Type u_2) [inst
 : Field 𝕂] [inst_1 : Ring 𝔸] [inst_2 : Algebra 𝕂 𝔸] [inst_3 : TopologicalSpace 
𝔸]   [inst_4 : IsTopolo…
· 使用定理 `FormalMultilinearSeries.ofScalars_apply_eq'`：ofScalars_apply_eq' (x : E)
 : (fun n => ofScalars E c n (fun _ => x)) = fun n => c n • x ^ n

--- 原说明 ---
This naming follows the convention of `NormedSpace.expSeries_apply_eq'`.
-/
theorem ordinaryHypergeometricSeries_apply_eq' (x : 𝔸) :
    (fun n => ordinaryHypergeometricSeries 𝔸 a b c n fun _ => x) =
      fun n => ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
        ((ascPochhammer 𝕂 n).eval c)⁻¹) • x ^ n := by
  rw [ordinaryHypergeometricSeries, ofScalars_apply_eq']
/-
**ordinaryHypergeometric_sum_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ordinaryHypergeometric_sum_eq (x : 𝔸) : (ordinaryHypergeometricSeries 𝔸 a 
b c).sum x = ∑' n : Nat, ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochham
mer 𝕂 n).eval b * ((ascPochhammer 𝕂 n).eval c)⁻¹) • x ^ n
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `ordinaryHypergeometricSeries_apply_eq`：ordinaryHypergeometricSeries_appl
y_eq (x : 𝔸) (n : Nat) : (ordinaryHypergeometricSeries 𝔸 a b c n fun _ => x) = (
(n !⁻¹ : 𝕂) * (ascPochhamme…
-/
theorem ordinaryHypergeometric_sum_eq (x : 𝔸) : (ordinaryHypergeometricSeries 𝔸 a b c).sum x =
    ∑' n : ℕ, ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
      ((ascPochhammer 𝕂 n).eval c)⁻¹) • x ^ n :=
  tsum_congr fun n => ordinaryHypergeometricSeries_apply_eq a b c x n
/-
**ordinaryHypergeometric_eq_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ordinaryHypergeometric_eq_tsum : ₂F₁ a b c = fun (x : 𝔸) => ∑' n : Nat, ((
n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b * ((ascPoch
hammer 𝕂 n).eval c)⁻¹) • x ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ordinaryHypergeometric_sum_eq`：ordinaryHypergeometric_sum_eq (x : 𝔸) : (
ordinaryHypergeometricSeries 𝔸 a b c).sum x = ∑' n : Nat, ((n !⁻¹ : 𝕂) * (ascPoc
hhammer 𝕂 n).eval a…
-/
theorem ordinaryHypergeometric_eq_tsum : ₂F₁ a b c =
    fun (x : 𝔸) => ∑' n : ℕ, ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a *
      (ascPochhammer 𝕂 n).eval b * ((ascPochhammer 𝕂 n).eval c)⁻¹) • x ^ n :=
  funext (ordinaryHypergeometric_sum_eq a b c)
/-
**ordinaryHypergeometricSeries_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ordinaryHypergeometricSeries_apply_zero (n : Nat) : ordinaryHypergeometric
Series 𝔸 a b c n (fun _ => 0) = Pi.single (M
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ordinaryHypergeometricSeries.eq_1`：∀ {𝕂 : Type u_1} (𝔸 : Type u_2) [inst
 : Field 𝕂] [inst_1 : Ring 𝔸] [inst_2 : Algebra 𝕂 𝔸] [inst_3 : TopologicalSpace 
𝔸]   [inst_4 : IsTopolo…
· 使用定理 `FormalMultilinearSeries.ofScalars_apply_eq`：ofScalars_apply_eq (x : E) (
n : Nat) : ofScalars E c n (fun _ => x) = c n • x ^ n
· 使用定理 `ordinaryHypergeometricCoefficient.eq_1`：∀ {𝕂 : Type u_1} [inst : Field 𝕂
] (a b c : 𝕂) (n : ℕ),   ordinaryHypergeometricCoefficient a b c n =     (↑n.fac
torial)⁻¹ * Polynomial.eval …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
-/
theorem ordinaryHypergeometricSeries_apply_zero (n : ℕ) :
    ordinaryHypergeometricSeries 𝔸 a b c n (fun _ => 0) = Pi.single (M := fun _ => 𝔸) 0 1 n := by
  rw [ordinaryHypergeometricSeries, ofScalars_apply_eq, ordinaryHypergeometricCoefficient]
  cases n <;> simp

@[simp]
/-
**ordinaryHypergeometric_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ordinaryHypergeometric_zero : ₂F₁ a b c (0 : 𝔸) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ordinaryHypergeometric_eq_tsum`：ordinaryHypergeometric_eq_tsum : ₂F₁ a b
 c = fun (x : 𝔸) => ∑' n : Nat, ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (asc
Pochhammer 𝕂 n).eval…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ordinaryHypergeometricSeries_apply_zero`：ordinaryHypergeometricSeries_ap
ply_zero (n : Nat) : ordinaryHypergeometricSeries 𝔸 a b c n (fun _ => 0) = Pi.si
ngle (M
· 使用定理 `tsum_pi_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] [inst_2 : DecidableEq β] (b : β)   (a : α), ∑' (b
' : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ordinaryHypergeometric_zero : ₂F₁ a b c (0 : 𝔸) = 1 := by
  simp [ordinaryHypergeometric_eq_tsum, ← ordinaryHypergeometricSeries_apply_eq,
    ordinaryHypergeometricSeries_apply_zero]
/-
**ordinaryHypergeometricSeries_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ordinaryHypergeometricSeries_symm : ordinaryHypergeometricSeries 𝔸 a b c =
 ordinaryHypergeometricSeries 𝔸 b a c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ordinaryHypergeometricSeries_symm :
    ordinaryHypergeometricSeries 𝔸 a b c = ordinaryHypergeometricSeries 𝔸 b a c := by
  unfold ordinaryHypergeometricSeries ordinaryHypergeometricCoefficient
  simp [mul_assoc, mul_left_comm]

/-- If any parameter to the series is a sufficiently large nonpositive integer, then the series
term is zero. -/
/-
**ordinaryHypergeometricSeries_eq_zero_of_neg_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ordinaryHypergeometricSeries_eq_zero_of_neg_nat {n k : Nat} (habc : k = -a
 ∨ k = -b ∨ k = -c) (hk : k < n) : ordinaryHypergeometricSeries 𝔸 a b c n = 0
参数：habc : k = -a ∨ k = -b ∨ k = -c；hk : k < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ordinaryHypergeometricSeries.eq_1`：∀ {𝕂 : Type u_1} (𝔸 : Type u_2) [inst
 : Field 𝕂] [inst_1 : Ring 𝔸] [inst_2 : Algebra 𝕂 𝔸] [inst_3 : TopologicalSpace 
𝔸]   [inst_4 : IsTopolo…
· 使用定理 `FormalMultilinearSeries.ofScalars.eq_1`：∀ {𝕜 : Type u_1} (E : Type u_2) 
[inst : Field 𝕜] [inst_1 : Ring E] [inst_2 : Algebra 𝕜 E] [inst_3 : TopologicalS
pace E]   [inst_4 : IsTopolo…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ascPochhammer_eval_eq_zero_iff`：ascPochhammer_eval_eq_zero_iff [IsDomain
 R] (n : Nat) (r : R) : (ascPochhammer R n).eval r = 0 ↔ exists k < n, k = -r
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If any parameter to the series is a sufficiently large nonpositive integer, then
 the series
term is zero.
-/
lemma ordinaryHypergeometricSeries_eq_zero_of_neg_nat {n k : ℕ} (habc : k = -a ∨ k = -b ∨ k = -c)
    (hk : k < n) : ordinaryHypergeometricSeries 𝔸 a b c n = 0 := by
  rw [ordinaryHypergeometricSeries, ofScalars]
  rcases habc with h | h | h
  all_goals
    ext
    simp [(ascPochhammer_eval_eq_zero_iff n _).2 ⟨k, hk, h⟩]

end Field

section RCLike

open Asymptotics Filter Real Set Nat

open scoped Topology

variable {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  (a b c : 𝕂)

/-
**ordinaryHypergeometric_radius_top_of_neg_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ordinaryHypergeometric_radius_top_of_neg_nat₁ {k : ℕ} :
    (ordinaryHypergeometricSeries 𝔸 (-(k : 𝕂)) b c).radius = ⊤ := by
  refine FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ (1 + k) fun n ↦ ?_
  exact ordinaryHypergeometricSeries_eq_zero_of_neg_nat (-(k : 𝕂)) b c (by aesop) (by lia)
/-
**ordinaryHypergeometric_radius_top_of_neg_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ordinaryHypergeometric_radius_top_of_neg_nat₂ {k : ℕ} :
    (ordinaryHypergeometricSeries 𝔸 a (-(k : 𝕂)) c).radius = ⊤ := by
  rw [ordinaryHypergeometricSeries_symm]
  exact ordinaryHypergeometric_radius_top_of_neg_nat₁ 𝔸 a c
/-
**ordinaryHypergeometric_radius_top_of_neg_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ordinaryHypergeometric_radius_top_of_neg_nat₃ {k : ℕ} :
    (ordinaryHypergeometricSeries 𝔸 a b (-(k : 𝕂))).radius = ⊤ := by
  refine FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ (1 + k) fun n ↦ ?_
  exact ordinaryHypergeometricSeries_eq_zero_of_neg_nat a b (-(k : 𝕂)) (by aesop) (by lia)

/-- An iff variation on `ordinaryHypergeometricSeries_eq_zero_of_nonpos_int` for `[RCLike 𝕂]`. -/
/-
**ordinaryHypergeometricSeries_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ordinaryHypergeometricSeries_eq_zero_iff (n : Nat) : ordinaryHypergeometri
cSeries 𝔸 a b c n = 0 ↔ exists k < n, k = -a ∨ k = -b ∨ k = -c
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FormalMultilinearSeries.ofScalars_eq_zero`：ofScalars_eq_zero [Nontrivial
 E] (n : Nat) : ofScalars E c n = 0 ↔ c n = 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ordinaryHypergeometricSeries.eq_1`：∀ {𝕂 : Type u_1} (𝔸 : Type u_2) [inst
 : Field 𝕂] [inst_1 : Ring 𝔸] [inst_2 : Algebra 𝕂 𝔸] [inst_3 : TopologicalSpace 
𝔸]   [inst_4 : IsTopolo…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ascPochhammer_eval_eq_zero_iff`：ascPochhammer_eval_eq_zero_iff [IsDomain
 R] (n : Nat) (r : R) : (ascPochhammer R n).eval r = 0 ↔ exists k < n, k = -r
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用引理 `ordinaryHypergeometricSeries_eq_zero_of_neg_nat`：ordinaryHypergeometricS
eries_eq_zero_of_neg_nat {n k : Nat} (habc : k = -a ∨ k = -b ∨ k = -c) (hk : k <
 n) : ordinaryHypergeometricSeries 𝔸 …

--- 原说明 ---
An iff variation on `ordinaryHypergeometricSeries_eq_zero_of_nonpos_int` for `[R
CLike 𝕂]`.
-/
lemma ordinaryHypergeometricSeries_eq_zero_iff (n : ℕ) :
    ordinaryHypergeometricSeries 𝔸 a b c n = 0 ↔ ∃ k < n, k = -a ∨ k = -b ∨ k = -c := by
  refine ⟨fun h ↦ ?_, fun zero ↦ ?_⟩
  · rw [ordinaryHypergeometricSeries, ofScalars_eq_zero] at h
    simp only [_root_.mul_eq_zero, inv_eq_zero] at h
    rcases h with ((hn | h) | h) | h
    · simp [Nat.factorial_ne_zero] at hn
    all_goals
      obtain ⟨kn, hkn, hn⟩ := (ascPochhammer_eval_eq_zero_iff _ _).1 h
      exact ⟨kn, hkn, by tauto⟩
  · obtain ⟨_, h, hn⟩ := zero
    exact ordinaryHypergeometricSeries_eq_zero_of_neg_nat a b c hn h
/-
**ordinaryHypergeometricSeries_norm_div_succ_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ordinaryHypergeometricSeries_norm_div_succ_norm (n : Nat) (habc : forall k
n < n, (↑kn != -a ∧ ↑kn != -b ∧ ↑kn != -c)) : ‖ordinaryHypergeometricCoefficient
 a b c n‖ / ‖ordinaryHypergeometricCoefficient a b c n.succ‖ = ‖a + n‖⁻¹ * ‖b + 
n‖⁻¹ * ‖c + n‖ * ‖1 + (n : 𝕂)‖
参数：n : Nat；habc : forall kn < n, (↑kn != -a ∧ ↑kn != -b ∧ ↑kn != -c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `ascPochhammer_succ_eval`：ascPochhammer_succ_eval {S : Type*} [Semiring S
] (n : Nat) (k : S) : (ascPochhammer S (n + 1)).eval k = (ascPochhammer S n).eva
l k * (k + n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 62 条，此处仅展示前 30 条）
-/
theorem ordinaryHypergeometricSeries_norm_div_succ_norm (n : ℕ)
    (habc : ∀ kn < n, (↑kn ≠ -a ∧ ↑kn ≠ -b ∧ ↑kn ≠ -c)) :
    ‖ordinaryHypergeometricCoefficient a b c n‖ / ‖ordinaryHypergeometricCoefficient a b c n.succ‖ =
      ‖a + n‖⁻¹ * ‖b + n‖⁻¹ * ‖c + n‖ * ‖1 + (n : 𝕂)‖ := by
  simp only [mul_inv_rev, factorial_succ, cast_mul, cast_add,
    cast_one, ascPochhammer_succ_eval, norm_mul, norm_inv]
  calc
    _ = ‖Polynomial.eval a (ascPochhammer 𝕂 n)‖ * ‖Polynomial.eval a (ascPochhammer 𝕂 n)‖⁻¹ *
        ‖Polynomial.eval b (ascPochhammer 𝕂 n)‖ * ‖Polynomial.eval b (ascPochhammer 𝕂 n)‖⁻¹ *
        ‖Polynomial.eval c (ascPochhammer 𝕂 n)‖⁻¹⁻¹ * ‖Polynomial.eval c (ascPochhammer 𝕂 n)‖⁻¹ *
        ‖(n ! : 𝕂)‖⁻¹⁻¹ * ‖(n ! : 𝕂)‖⁻¹ * ‖a + n‖⁻¹ * ‖b + n‖⁻¹ * ‖c + n‖⁻¹⁻¹ *
        ‖1 + (n : 𝕂)‖⁻¹⁻¹ := by ring_nf
    _ = _ := by
      simp only [inv_inv]
      repeat rw [DivisionRing.mul_inv_cancel, one_mul]
      all_goals
        rw [norm_ne_zero_iff]
      any_goals
        apply (ascPochhammer_eval_eq_zero_iff n _).not.2
        push Not
        exact fun kn hkn ↦ by simp [habc kn hkn]
      exact cast_ne_zero.2 (factorial_ne_zero n)

/-- The radius of convergence of `ordinaryHypergeometricSeries` is unity if none of the parameters
are non-positive integers. -/
/-
**ordinaryHypergeometricSeries_radius_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ordinaryHypergeometricSeries_radius_eq_one (habc : forall kn : Nat, ↑kn !=
 -a ∧ ↑kn != -b ∧ ↑kn != -c) : (ordinaryHypergeometricSeries 𝔸 a b c).radius = 1
参数：habc : forall kn : Nat, ↑kn != -a ∧ ↑kn != -b ∧ ↑kn != -c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto`：ofScalars_radius
_eq_of_tendsto [NormOneClass E] {r : NNReal} (hr : r != 0) (hc : Tendsto (fun n 
=> ‖c n‖ / ‖c n.succ‖) atTop (𝓝 r)) : (ofSca…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
（共 87 条，此处仅展示前 30 条）

--- 原说明 ---
The radius of convergence of `ordinaryHypergeometricSeries` is unity if none of 
the parameters
are non-positive integers.
-/
theorem ordinaryHypergeometricSeries_radius_eq_one
    (habc : ∀ kn : ℕ, ↑kn ≠ -a ∧ ↑kn ≠ -b ∧ ↑kn ≠ -c) :
    (ordinaryHypergeometricSeries 𝔸 a b c).radius = 1 := by
  convert! ofScalars_radius_eq_of_tendsto 𝔸 _ one_ne_zero ?_
  suffices Tendsto (fun k : ℕ ↦ (a + k)⁻¹ * (b + k)⁻¹ * (c + k) * ((1 : 𝕂) + k)) atTop (𝓝 1) by
    simp_rw [ordinaryHypergeometricSeries_norm_div_succ_norm a b c _ (fun n _ ↦ habc n)]
    simp only [← norm_inv, ← norm_mul, NNReal.coe_one]
    convert! Filter.Tendsto.norm this
    exact norm_one.symm
  have (k : ℕ) : (a + k)⁻¹ * (b + k)⁻¹ * (c + k) * ((1 : 𝕂) + k) =
        (c + k) / (a + k) * ((1 + k) / (b + k)) := by field
  simp_rw [this]
  apply (mul_one (1 : 𝕂)) ▸ Filter.Tendsto.mul <;>
  convert! tendsto_add_mul_div_add_mul_atTop_nhds _ _ (1 : 𝕂) one_ne_zero <;> simp

end RCLike

