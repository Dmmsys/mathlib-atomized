/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.UniformSpace.DiscreteUniformity


/-!
# Laurent Series

In this file we define `LaurentSeries R`, the formal Laurent series over `R`, here an *arbitrary*
type with a zero. They are denoted `R⸨X⸩`.

## Main Definitions

* Defines `LaurentSeries` as an abbreviation for `HahnSeries ℤ`.
* Defines `hasseDeriv` of a Laurent series with coefficients in a module over a ring.
* Provides a coercion from power series `R⟦X⟧` into `R⸨X⸩` given by `HahnSeries.ofPowerSeries`.
* Defines `LaurentSeries.powerSeriesPart`
* Defines the localization map `LaurentSeries.of_powerSeries_localization` which evaluates to
  `HahnSeries.ofPowerSeries`.
* Embedding of rational functions into Laurent series, provided as a coercion, utilizing
  the underlying `RatFunc.coeAlgHom`.
* Study of the `X`-Adic valuation on the ring of Laurent series over a field
* In `LaurentSeries.uniformContinuous_coeff` we show that sending a Laurent series to its `d`th
  coefficient is uniformly continuous, ensuring that it sends a Cauchy filter `ℱ` in `K⸨X⸩`
  to a Cauchy filter in `K`: since this latter is given the discrete topology, this provides an
  element `LaurentSeries.Cauchy.coeff ℱ d` in `K` that serves as `d`th coefficient of the Laurent
  series to which the filter `ℱ` converges.

## Main Results

* Basic properties of Hasse derivatives

### About the `X`-Adic valuation:
* The (integral) valuation of a power series is the order of the first non-zero coefficient, see
  `LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero`.
* The valuation of a Laurent series is the order of the first non-zero coefficient, see
  `LaurentSeries.valuation_le_iff_coeff_lt_eq_zero`.
* Every Laurent series of valuation less than `(1 : ℤᵐ⁰)` comes from a power series, see
  `LaurentSeries.val_le_one_iff_eq_coe`.
* The uniform space of `LaurentSeries` over a field is complete, formalized in the instance
  `instLaurentSeriesComplete`.
* The field of rational functions is dense in `LaurentSeries`: this is the declaration
  `LaurentSeries.coe_range_dense` and relies principally upon `LaurentSeries.exists_ratFunc_val_lt`,
  stating that for every Laurent series `f` and every `γ : ℤᵐ⁰` one can find a rational function `Q`
  such that the `X`-adic valuation `v` satisfies `v (f - Q) < γ`.
* In `LaurentSeries.valuation_compare` we prove that the extension of the `X`-adic valuation from
  `K⟮X⟯` up to its abstract completion coincides, modulo the isomorphism with `K⸨X⸩`, with the
  `X`-adic valuation on `K⸨X⸩`.
* The two declarations `LaurentSeries.mem_integers_of_powerSeries` and
  `LaurentSeries.exists_powerSeries_of_memIntegers` show that an element in the completion of
  `K⟮X⟯` is in the unit ball if and only if it comes from a power series through the
  isomorphism `LaurentSeriesRingEquiv`.
* `LaurentSeries.powerSeriesAlgEquiv` is the `K`-algebra isomorphism between `K⟦X⟧`
  and the unit ball inside the `X`-adic completion of `K⟮X⟯`.

## Implementation details

* Since `LaurentSeries` is just an abbreviation of `HahnSeries ℤ`, the definition of the
  coefficients is given in terms of `HahnSeries.coeff` and this forces sometimes to go
  back-and-forth from `X : R⸨X⸩` to `single 1 1 : R⟦ℤ⟧`.
* To prove the isomorphism between the `X`-adic completion of `K⟮X⟯` and `K⸨X⸩` we construct
  two completions of `K⟮X⟯`: the first (`LaurentSeries.ratfuncAdicComplPkg`) is its abstract
  uniform completion; the second (`LaurentSeries.LaurentSeriesPkg`) is simply `K⸨X⸩`, once we prove
  that it is complete and contains `K⟮X⟯` as a dense subspace. The isomorphism is the
  comparison equivalence, expressing the mathematical idea that the completion "is unique". It is
  `LaurentSeries.comparePkg`.
* For applications to `K⟦X⟧` it is actually more handy to use the *inverse* of the above
  equivalence: `LaurentSeries.LaurentSeriesAlgEquiv` is the *topological, algebra equivalence*
  `K⸨X⸩ ≃ₐ[K] RatFuncAdicCompl K`.
* In order to compare `K⟦X⟧` with the valuation subring in the `X`-adic completion of
  `K⟮X⟯` we consider its alias `LaurentSeries.powerSeries_as_subring` as a subring of `K⸨X⸩`,
  that is itself clearly isomorphic (via the inverse of `LaurentSeries.powerSeriesEquivSubring`)
  to `K⟦X⟧`.

-/

@[expose] public section
universe u

open scoped PowerSeries
open HahnSeries Polynomial

noncomputable section

/-- `LaurentSeries R` is the type of formal Laurent series with coefficients in `R`, denoted `R⸨X⸩`.

  It is implemented as a `HahnSeries` with value group `ℤ`.
-/
/-
**LaurentSeries** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LaurentSeries (R : Type u) [Zero R]
参数：R : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LaurentSeries R` is the type of formal Laurent series with coefficients in `R`,
 denoted `R⸨X⸩`.

  It is implemented as a `HahnSeries` with value group `ℤ`.
-/
abbrev LaurentSeries (R : Type u) [Zero R] := R⟦ℤ⟧

variable {R : Type*}

namespace LaurentSeries

section

/-- `R⸨X⸩` is notation for `LaurentSeries R`. -/
scoped notation:9000 R "⸨X⸩" => LaurentSeries R

end

section HasseDeriv

/-- The Hasse derivative of Laurent series, as a linear map. -/
/-
**LaurentSeries.hasseDeriv** 是 Mathlib 中的一个定义，位于命名空间 `LaurentSeries`。
形式化陈述：hasseDeriv (R : Type*) {V : Type*} [AddCommGroup V] [Semiring R] [Module R
 V] (k : Nat) : V⸨X⸩ ->ₗ[R] V⸨X⸩ where toFun f
参数：R : Type*；k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Hasse derivative of Laurent series, as a linear map.
-/
def hasseDeriv (R : Type*) {V : Type*} [AddCommGroup V] [Semiring R] [Module R V] (k : ℕ) :
    V⸨X⸩ →ₗ[R] V⸨X⸩ where
  toFun f := HahnSeries.ofSuppBddBelow (fun n ↦ Ring.choose (n + k) k • f.coeff (n + k)) <| by
    refine ⟨f.order - k, fun x h ↦ ?_⟩
    contrapose! h
    rw [Function.notMem_support, coeff_eq_zero_of_lt_order <| lt_sub_iff_add_lt.mp h, smul_zero]
  map_add' f g := by
    ext
    simp only [ofSuppBddBelow, coeff_add', Pi.add_apply, smul_add]
  map_smul' r f := by
    ext
    simp only [ofSuppBddBelow, HahnSeries.coeff_smul, RingHom.id_apply, smul_comm r]

variable [Semiring R] {V : Type*} [AddCommGroup V] [Module R V]

@[simp]
/-
**LaurentSeries.hasseDeriv_coeff** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：hasseDeriv_coeff (k : Nat) (f : LaurentSeries V) (n : Int) : (hasseDeriv R
 k f).coeff n = Ring.choose (n + k) k • f.coeff (n + k)
参数：k : Nat；f : LaurentSeries V；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasseDeriv_coeff (k : ℕ) (f : LaurentSeries V) (n : ℤ) :
    (hasseDeriv R k f).coeff n = Ring.choose (n + k) k • f.coeff (n + k) :=
  rfl

@[simp]
/-
**LaurentSeries.hasseDeriv_zero** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：hasseDeriv_zero : hasseDeriv R 0 = LinearMap.id (M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ring.choose_zero_right'`：choose_zero_right' (r : R) : choose r 0 = (r + 
1) ^ 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hasseDeriv_zero : hasseDeriv R 0 = LinearMap.id (M := LaurentSeries V) := by
  ext f n
  simp
/-
**LaurentSeries.hasseDeriv_single_add** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：hasseDeriv_single_add (k : Nat) (n : Int) (x : V) : hasseDeriv R k (single
 (n + k) x) = single n ((Ring.choose (n + k) k) • x)
参数：k : Nat；n : Int；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.coeff_single_same`：coeff_single_same (a : Γ) (r : R) : (singl
e a r).coeff a = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.coeff_single_of_ne`：coeff_single_of_ne (h : b != a) : (single
 a r).coeff b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem hasseDeriv_single_add (k : ℕ) (n : ℤ) (x : V) :
    hasseDeriv R k (single (n + k) x) = single n ((Ring.choose (n + k) k) • x) := by
  ext m
  dsimp only [hasseDeriv_coeff]
  by_cases h : m = n
  · simp [h]
  · simp [h, show m + k ≠ n + k by lia]

@[simp]
/-
**LaurentSeries.hasseDeriv_single** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：hasseDeriv_single (k : Nat) (n : Int) (x : V) : hasseDeriv R k (single n x
) = single (n - k) ((Ring.choose n k) • x)
参数：k : Nat；n : Int；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.sub_add_cancel`：∀ (a b : ℤ), a - b + b = a
· 使用定理 `LaurentSeries.hasseDeriv_single_add`：hasseDeriv_single_add (k : Nat) (n 
: Int) (x : V) : hasseDeriv R k (single (n + k) x) = single n ((Ring.choose (n +
 k) k) • x)
-/
theorem hasseDeriv_single (k : ℕ) (n : ℤ) (x : V) :
    hasseDeriv R k (single n x) = single (n - k) ((Ring.choose n k) • x) := by
  rw [← Int.sub_add_cancel n k, hasseDeriv_single_add, Int.sub_add_cancel n k]
/-
**LaurentSeries.hasseDeriv_comp_coeff** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：hasseDeriv_comp_coeff (k l : Nat) (f : LaurentSeries V) (n : Int) : (hasse
Deriv R k (hasseDeriv R l f)).coeff n = ((Nat.choose (k + l) k) • hasseDeriv R (
k + l) f).coeff n
参数：k l : Nat；f : LaurentSeries V；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.coeff_nsmul`：coeff_nsmul {x : R⟦Γ⟧} {n : Nat} : (n • x).coeff
 = n • x.coeff
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.choose_add_smul_choose`：choose_add_smul_choose [NatPowAssoc R] (r :
 R) (n k : Nat) : (Nat.choose (n + k) k) • choose (r + k) (n + k) = choose (r + 
k) k * choose r n
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.choose_symm_add`：choose_symm_add {a b : Nat} : choose (a + b) a = ch
oose (a + b) b
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
theorem hasseDeriv_comp_coeff (k l : ℕ) (f : LaurentSeries V) (n : ℤ) :
    (hasseDeriv R k (hasseDeriv R l f)).coeff n =
      ((Nat.choose (k + l) k) • hasseDeriv R (k + l) f).coeff n := by
  rw [coeff_nsmul]
  simp only [hasseDeriv_coeff, Pi.smul_apply, Nat.cast_add]
  rw [smul_smul, mul_comm, ← Ring.choose_add_smul_choose (n + k), add_assoc, Nat.choose_symm_add,
    smul_assoc]

@[simp]
/-
**LaurentSeries.hasseDeriv_comp** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：hasseDeriv_comp (k l : Nat) (f : LaurentSeries V) : hasseDeriv R k (hasseD
eriv R l f) = (k + l).choose k • hasseDeriv R (k + l) f
参数：k l : Nat；f : LaurentSeries V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentSeries.hasseDeriv_comp_coeff`：hasseDeriv_comp_coeff (k l : Nat) (
f : LaurentSeries V) (n : Int) : (hasseDeriv R k (hasseDeriv R l f)).coeff n = (
(Nat.choose (k + l) k) • …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hasseDeriv_comp (k l : ℕ) (f : LaurentSeries V) :
    hasseDeriv R k (hasseDeriv R l f) = (k + l).choose k • hasseDeriv R (k + l) f := by
  ext n
  simp [hasseDeriv_comp_coeff k l f n]

/-- The derivative of a Laurent series. -/
/-
**LaurentSeries.derivative** 是 Mathlib 中的一个定义，位于命名空间 `LaurentSeries`。
形式化陈述：derivative (R : Type*) {V : Type*} [AddCommGroup V] [Semiring R] [Module R
 V] : LaurentSeries V ->ₗ[R] LaurentSeries V
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivative of a Laurent series.
-/
def derivative (R : Type*) {V : Type*} [AddCommGroup V] [Semiring R] [Module R V] :
    LaurentSeries V →ₗ[R] LaurentSeries V :=
  hasseDeriv R 1

@[simp]
/-
**LaurentSeries.derivative_apply** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：derivative_apply (f : LaurentSeries V) : derivative R f = hasseDeriv R 1 f
参数：f : LaurentSeries V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem derivative_apply (f : LaurentSeries V) : derivative R f = hasseDeriv R 1 f := by
  exact rfl
/-
**LaurentSeries.derivative_iterate** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：derivative_iterate (k : Nat) (f : LaurentSeries V) : (derivative R)^[k] f 
= k.factorial • (hasseDeriv R k f)
参数：k : Nat；f : LaurentSeries V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LaurentSeries.hasseDeriv_zero`：hasseDeriv_zero : hasseDeriv R 0 = Linear
Map.id (M
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `LaurentSeries.derivative_apply`：derivative_apply (f : LaurentSeries V) :
 derivative R f = hasseDeriv R 1 f
· 使用定理 `LaurentSeries.hasseDeriv_comp`：hasseDeriv_comp (k l : Nat) (f : LaurentS
eries V) : hasseDeriv R k (hasseDeriv R l f) = (k + l).choose k • hasseDeriv R (
k + l) f
· 使用定理 `Nat.choose_symm_add`：choose_symm_add {a b : Nat} : choose (a + b) a = ch
oose (a + b) b
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
· 使用定理 `Nat.factorial.eq_2`：∀ (n : ℕ), n.succ.factorial = n.succ * n.factorial
· 使用定理 `mul_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m *
 n) • a = n • m • a
-/
theorem derivative_iterate (k : ℕ) (f : LaurentSeries V) :
    (derivative R)^[k] f = k.factorial • (hasseDeriv R k f) := by
  ext n
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ, Function.comp_apply, ih, derivative_apply, hasseDeriv_comp,
      Nat.choose_symm_add, Nat.choose_one_right, Nat.factorial, mul_nsmul]

@[simp]
/-
**LaurentSeries.derivative_iterate_coeff** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSerie
s`。
形式化陈述：derivative_iterate_coeff (k : Nat) (f : LaurentSeries V) (n : Int) : ((der
ivative R)^[k] f).coeff n = (descPochhammer Int k).smeval (n + k) • f.coeff (n +
 k)
参数：k : Nat；f : LaurentSeries V；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentSeries.derivative_iterate`：derivative_iterate (k : Nat) (f : Laur
entSeries V) : (derivative R)^[k] f = k.factorial • (hasseDeriv R k f)
· 使用定理 `HahnSeries.coeff_nsmul`：coeff_nsmul {x : R⟦Γ⟧} {n : Nat} : (n • x).coeff
 = n • x.coeff
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用定理 `LaurentSeries.hasseDeriv_coeff`：hasseDeriv_coeff (k : Nat) (f : LaurentS
eries V) (n : Int) : (hasseDeriv R k f).coeff n = Ring.choose (n + k) k • f.coef
f (n + k)
· 使用定理 `Ring.descPochhammer_eq_factorial_smul_choose`：descPochhammer_eq_factoria
l_smul_choose [NatPowAssoc R] (r : R) (n : Nat) : (descPochhammer Int n).smeval 
r = n.factorial • choose r n
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
theorem derivative_iterate_coeff (k : ℕ) (f : LaurentSeries V) (n : ℤ) :
    ((derivative R)^[k] f).coeff n = (descPochhammer ℤ k).smeval (n + k) • f.coeff (n + k) := by
  rw [derivative_iterate, coeff_nsmul, Pi.smul_apply, hasseDeriv_coeff,
    Ring.descPochhammer_eq_factorial_smul_choose, smul_assoc]

end HasseDeriv

section Semiring

variable [Semiring R]

/-
**LaurentSeries.** 是 Mathlib 中的一个实例，位于命名空间 `LaurentSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe R⟦X⟧ R⸨X⸩ :=
  ⟨HahnSeries.ofPowerSeries ℤ R⟩

@[simp]
/-
**LaurentSeries.coeff_coe_powerSeries** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：coeff_coe_powerSeries (x : R⟦X⟧) (n : Nat) : HahnSeries.coeff (x : R⸨X⸩) n
 = PowerSeries.coeff n x
参数：x : R⟦X⟧；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `HahnSeries.ofPowerSeries_apply_coeff`：ofPowerSeries_apply_coeff (x : Pow
erSeries R) (n : Nat) : (ofPowerSeries Γ R x).coeff n = PowerSeries.coeff n x
-/
theorem coeff_coe_powerSeries (x : R⟦X⟧) (n : ℕ) :
    HahnSeries.coeff (x : R⸨X⸩) n = PowerSeries.coeff n x := by
  rw [ofPowerSeries_apply_coeff]

/-- This is a power series that can be multiplied by an integer power of `X` to give our
  Laurent series. If the Laurent series is nonzero, `powerSeriesPart` has a nonzero
  constant term. -/
/-
**LaurentSeries.powerSeriesPart** 是 Mathlib 中的一个定义，位于命名空间 `LaurentSeries`。
形式化陈述：powerSeriesPart (x : R⸨X⸩) : R⟦X⟧
参数：x : R⸨X⸩。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a power series that can be multiplied by an integer power of `X` to give
 our
  Laurent series. If the Laurent series is nonzero, `powerSeriesPart` has a nonz
ero
  constant term.
-/
def powerSeriesPart (x : R⸨X⸩) : R⟦X⟧ :=
  PowerSeries.mk fun n => x.coeff (x.order + n)

@[simp]
/-
**LaurentSeries.powerSeriesPart_coeff** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：powerSeriesPart_coeff (x : R⸨X⸩) (n : Nat) : PowerSeries.coeff n x.powerSe
riesPart = x.coeff (x.order + n)
参数：x : R⸨X⸩；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
-/
theorem powerSeriesPart_coeff (x : R⸨X⸩) (n : ℕ) :
    PowerSeries.coeff n x.powerSeriesPart = x.coeff (x.order + n) :=
  PowerSeries.coeff_mk _ _

@[simp]
/-
**LaurentSeries.powerSeriesPart_zero** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：powerSeriesPart_zero : powerSeriesPart (0 : R⸨X⸩) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentSeries.powerSeriesPart_coeff`：powerSeriesPart_coeff (x : R⸨X⸩) (n
 : Nat) : PowerSeries.coeff n x.powerSeriesPart = x.coeff (x.order + n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.order_zero`：order_zero : order (0 : R⟦Γ⟧) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem powerSeriesPart_zero : powerSeriesPart (0 : R⸨X⸩) = 0 := by
  ext
  simp

@[simp]
/-
**LaurentSeries.powerSeriesPart_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries
`。
形式化陈述：powerSeriesPart_eq_zero (x : R⸨X⸩) : x.powerSeriesPart = 0 ↔ x = 0
参数：x : R⸨X⸩。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.ext_iff`：∀ {R : Type u_1} [inst : Semiring R] {φ ψ : PowerSe
ries R},   φ = ψ ↔ ∀ (n : ℕ), (PowerSeries.coeff n) φ = (PowerSeries.coeff n) ψ
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LaurentSeries.powerSeriesPart_coeff`：powerSeriesPart_coeff (x : R⸨X⸩) (n
 : Nat) : PowerSeries.coeff n x.powerSeriesPart = x.coeff (x.order + n)
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LaurentSeries.powerSeriesPart_zero`：powerSeriesPart_zero : powerSeriesPa
rt (0 : R⸨X⸩) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem powerSeriesPart_eq_zero (x : R⸨X⸩) : x.powerSeriesPart = 0 ↔ x = 0 := by
  constructor
  · contrapose!
    simp only [ne_eq]
    intro h
    rw [PowerSeries.ext_iff, not_forall]
    use 0
    simpa
  · rintro rfl
    simp

@[simp]
/-
**LaurentSeries.single_order_mul_powerSeriesPart** 是 Mathlib 中的一个定理，位于命名空间 `Laur
entSeries`。
形式化陈述：single_order_mul_powerSeriesPart (x : R⸨X⸩) : (single x.order 1 : R⸨X⸩) * 
x.powerSeriesPart = x
参数：x : R⸨X⸩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `HahnSeries.coeff_single_mul_add`：coeff_single_mul_add [NonUnitalNonAssoc
Semiring R] {r : R} {x : R⟦Γ⟧} {a : Γ} {b : Γ} : (single b r * x).coeff (a + b) 
= r * x.coeff a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Int.eq_natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → a = ↑a.natAbs
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LaurentSeries.coeff_coe_powerSeries`：coeff_coe_powerSeries (x : R⟦X⟧) (n
 : Nat) : HahnSeries.coeff (x : R⸨X⸩) n = PowerSeries.coeff n x
· 使用定理 `LaurentSeries.powerSeriesPart_coeff`：powerSeriesPart_coeff (x : R⸨X⸩) (n
 : Nat) : PowerSeries.coeff n x.powerSeriesPart = x.coeff (x.order + n)
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `HahnSeries.ofPowerSeries_apply`：ofPowerSeries_apply (x : PowerSeries R) 
: ofPowerSeries Γ R x = embDomain Nat.castOrderEmbedding (toPowerSeries.symm x)
· 使用定理 `HahnSeries.embDomain_of_notMem_range`：embDomain_of_notMem_range {f : Γ ↪
o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ Set.range f) : (embDomain f x).coeff b = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.castOrderEmbedding_apply`：∀ {α : Type u_1} [inst : AddMonoidWithOne 
α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α]   [inst_3 : ZeroLEOneClass
 α] [inst_4 : Char…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `HahnSeries.order_le_of_coeff_ne_zero`：order_le_of_coeff_ne_zero {Γ} [Zer
o Γ] [LinearOrder Γ] {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0) : x.order <= g
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem single_order_mul_powerSeriesPart (x : R⸨X⸩) :
    (single x.order 1 : R⸨X⸩) * x.powerSeriesPart = x := by
  ext n
  rw [← sub_add_cancel n x.order, coeff_single_mul_add, sub_add_cancel, one_mul]
  by_cases h : x.order ≤ n
  · rw [Int.eq_natAbs_of_nonneg (sub_nonneg_of_le h), coeff_coe_powerSeries,
      powerSeriesPart_coeff, ← Int.eq_natAbs_of_nonneg (sub_nonneg_of_le h),
      add_sub_cancel]
  · rw [ofPowerSeries_apply, embDomain_of_notMem_range]
    · contrapose! h
      exact order_le_of_coeff_ne_zero h.symm
    · contrapose h
      simp only [Nat.castOrderEmbedding_apply, Set.mem_range] at h
      lia
/-
**LaurentSeries.ofPowerSeries_powerSeriesPart** 是 Mathlib 中的一个定理，位于命名空间 `Laurent
Series`。
形式化陈述：ofPowerSeries_powerSeriesPart (x : R⸨X⸩) : ofPowerSeries Int R x.powerSeri
esPart = single (-x.order) 1 * x
参数：x : R⸨X⸩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `HahnSeries.single_mul_single`：single_mul_single {a b : Γ} {r s : R} : si
ngle a r * single b s = single (a + b) (r * s)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HahnSeries.C_apply`：∀ {Γ : Type u_1} {R : Type u_3} [inst : AddCommMonoi
d Γ] [inst_1 : PartialOrder Γ] [inst_2 : IsOrderedCancelAddMonoid Γ]   [inst_3 :
 NonAsso…
· 使用定理 `HahnSeries.C_one`：C_one : C (1 : R) = (1 : R⟦Γ⟧)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LaurentSeries.single_order_mul_powerSeriesPart`：single_order_mul_powerSe
riesPart (x : R⸨X⸩) : (single x.order 1 : R⸨X⸩) * x.powerSeriesPart = x
-/
theorem ofPowerSeries_powerSeriesPart (x : R⸨X⸩) :
    ofPowerSeries ℤ R x.powerSeriesPart = single (-x.order) 1 * x := by
  refine Eq.trans ?_ (congr rfl x.single_order_mul_powerSeriesPart)
  rw [← mul_assoc, single_mul_single, neg_add_cancel, mul_one, ← C_apply, C_one, one_mul]
/-
**LaurentSeries.X_order_mul_powerSeriesPart** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSe
ries`。
形式化陈述：X_order_mul_powerSeriesPart {n : Nat} {f : R⸨X⸩} (hn : n = f.order) : (Pow
erSeries.X ^ n * f.powerSeriesPart : R⟦X⟧) = f
参数：hn : n = f.order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
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
· 使用定理 `HahnSeries.ofPowerSeries_X`：ofPowerSeries_X : ofPowerSeries Γ R PowerSer
ies.X = single 1 1
· 使用定理 `HahnSeries.single_pow`：single_pow (a : Γ) (n : Nat) (r : R) : single a r
 ^ n = single (n • a) (r ^ n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `LaurentSeries.single_order_mul_powerSeriesPart`：single_order_mul_powerSe
riesPart (x : R⸨X⸩) : (single x.order 1 : R⸨X⸩) * x.powerSeriesPart = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem X_order_mul_powerSeriesPart {n : ℕ} {f : R⸨X⸩} (hn : n = f.order) :
    (PowerSeries.X ^ n * f.powerSeriesPart : R⟦X⟧) = f := by
  simp only [map_mul, map_pow, ofPowerSeries_X, single_pow, nsmul_eq_mul, mul_one, one_pow, hn,
    single_order_mul_powerSeriesPart]

end Semiring

/-
**LaurentSeries.** 是 Mathlib 中的一个实例，位于命名空间 `LaurentSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring R] : Algebra R⟦X⟧ R⸨X⸩ := (HahnSeries.ofPowerSeries ℤ R).toAlgebra

@[simp]
/-
**LaurentSeries.coe_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：coe_algebraMap [CommSemiring R] : ⇑(algebraMap R⟦X⟧ R⸨X⸩) = HahnSeries.ofP
owerSeries Int R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem coe_algebraMap [CommSemiring R] :
    ⇑(algebraMap R⟦X⟧ R⸨X⸩) = HahnSeries.ofPowerSeries ℤ R :=
  rfl

/-- The localization map from power series to Laurent series. -/
@[simps (rhsMd := .all) +simpRhs]
/-
**LaurentSeries.of_powerSeries_localization** 是 Mathlib 中的一个实例，位于命名空间 `LaurentSe
ries`。
形式化陈述：of_powerSeries_localization [CommRing R] : IsLocalization (Submonoid.power
s (PowerSeries.X : R⟦X⟧)) R⸨X⸩ where map_units
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.single_mul_single`：single_mul_single {a b : Γ} {r s : R} : si
ngle a r * single b s = single (a + b) (r * s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `HahnSeries.ofPowerSeries_X_pow`：ofPowerSeries_X_pow {R} [Semiring R] (n 
: Nat) : ofPowerSeries Γ R (PowerSeries.X ^ n) = single (n : Γ) 1
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
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Int.natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.natAbs = a
· 使用定理 `LaurentSeries.single_order_mul_powerSeriesPart`：single_order_mul_powerSe
riesPart (x : R⸨X⸩) : (single x.order 1 : R⸨X⸩) * x.powerSeriesPart = x
· 使用定理 `LaurentSeries.ofPowerSeries_powerSeriesPart`：ofPowerSeries_powerSeriesPa
rt (x : R⸨X⸩) : ofPowerSeries Int R x.powerSeriesPart = single (-x.order) 1 * x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Int.ofNat_natAbs_of_nonpos`：∀ {a : ℤ}, a ≤ 0 → ↑a.natAbs = -a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LaurentSeries.coe_algebraMap`：coe_algebraMap [CommSemiring R] : ⇑(algebr
aMap R⟦X⟧ R⸨X⸩) = HahnSeries.ofPowerSeries Int R
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `HahnSeries.ofPowerSeries_injective`：ofPowerSeries_injective : Function.I
njective (ofPowerSeries Γ R)

--- 原说明 ---
The localization map from power series to Laurent series.
-/
instance of_powerSeries_localization [CommRing R] :
    IsLocalization (Submonoid.powers (PowerSeries.X : R⟦X⟧)) R⸨X⸩ where
  map_units := by
    rintro ⟨_, n, rfl⟩
    refine ⟨⟨single (n : ℤ) 1, single (-n : ℤ) 1, ?_, ?_⟩, ?_⟩
    · simp
    · simp
    · dsimp; rw [ofPowerSeries_X_pow]
  surj z := by
    by_cases! h : 0 ≤ z.order
    · refine ⟨⟨PowerSeries.X ^ Int.natAbs z.order * powerSeriesPart z, 1⟩, ?_⟩
      simp only [map_one, mul_one, map_mul, coe_algebraMap, ofPowerSeries_X_pow,
        Submonoid.coe_one]
      rw [Int.natAbs_of_nonneg h, single_order_mul_powerSeriesPart]
    · refine ⟨⟨powerSeriesPart z, PowerSeries.X ^ Int.natAbs z.order, ⟨_, rfl⟩⟩, ?_⟩
      simp only [coe_algebraMap, ofPowerSeries_powerSeriesPart]
      rw [mul_comm _ z]
      refine congr rfl ?_
      rw [ofPowerSeries_X_pow, Int.ofNat_natAbs_of_nonpos]
      exact h.le
  exists_of_eq {x y} := by
    rw [coe_algebraMap, ofPowerSeries_injective.eq_iff]
    rintro rfl
    exact ⟨1, rfl⟩
/-
**LaurentSeries.** 是 Mathlib 中的一个实例，位于命名空间 `LaurentSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K : Type*} [Field K] : IsFractionRing K⟦X⟧ K⸨X⸩ :=
  IsLocalization.of_le (Submonoid.powers (PowerSeries.X : K⟦X⟧)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero) fun _ hf =>
    isUnit_of_mem_nonZeroDivisors <| map_mem_nonZeroDivisors _ HahnSeries.ofPowerSeries_injective hf

end LaurentSeries

namespace PowerSeries

open LaurentSeries

variable {R' : Type*} [Semiring R] [Ring R'] (f g : R⟦X⟧) (f' g' : R'⟦X⟧)

@[norm_cast]
/-
**PowerSeries.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_zero : ((0 : R⟦X⟧) : R⸨X⸩) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem coe_zero : ((0 : R⟦X⟧) : R⸨X⸩) = 0 :=
  (ofPowerSeries ℤ R).map_zero

@[norm_cast]
/-
**PowerSeries.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_one : ((1 : R⟦X⟧) : R⸨X⸩) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem coe_one : ((1 : R⟦X⟧) : R⸨X⸩) = 1 :=
  (ofPowerSeries ℤ R).map_one

@[norm_cast]
/-
**PowerSeries.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_add : ((f + g : R⟦X⟧) : R⸨X⸩) = f + g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_add`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a + b) = f a + f b
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem coe_add : ((f + g : R⟦X⟧) : R⸨X⸩) = f + g :=
  (ofPowerSeries ℤ R).map_add _ _

@[norm_cast]
/-
**PowerSeries.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_sub : ((f' - g' : R'⟦X⟧) : R'⸨X⸩) = f' - g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x y : α),   f (x - y) = f x - f y
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem coe_sub : ((f' - g' : R'⟦X⟧) : R'⸨X⸩) = f' - g' :=
  (ofPowerSeries ℤ R').map_sub _ _

@[norm_cast]
/-
**PowerSeries.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_neg : ((-f' : R'⟦X⟧) : R'⸨X⸩) = -f'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x : α), f (-x) = -f x
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem coe_neg : ((-f' : R'⟦X⟧) : R'⸨X⸩) = -f' :=
  (ofPowerSeries ℤ R').map_neg _

@[norm_cast]
/-
**PowerSeries.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_mul : ((f * g : R⟦X⟧) : R⸨X⸩) = f * g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem coe_mul : ((f * g : R⟦X⟧) : R⸨X⸩) = f * g :=
  (ofPowerSeries ℤ R).map_mul _ _
/-
**PowerSeries.coeff_coe** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_coe (i : Int) : ((f : R⟦X⟧) : R⸨X⸩).coeff i = if i < 0 then 0 else P
owerSeries.coeff i.natAbs f
参数：i : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `LaurentSeries.coeff_coe_powerSeries`：coeff_coe_powerSeries (x : R⟦X⟧) (n
 : Nat) : HahnSeries.coeff (x : R⸨X⸩) n = PowerSeries.coeff n x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `HahnSeries.ofPowerSeries_apply`：ofPowerSeries_apply (x : PowerSeries R) 
: ofPowerSeries Γ R x = embDomain Nat.castOrderEmbedding (toPowerSeries.symm x)
· 使用定理 `HahnSeries.embDomain_notin_image_support`：embDomain_notin_image_support 
{f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ f '' x.support) : (embDomain f x).co
eff b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Nat.castOrderEmbedding_apply`：∀ {α : Type u_1} [inst : AddMonoidWithOne 
α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α]   [inst_3 : ZeroLEOneClass
 α] [inst_4 : Char…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HahnSeries.toPowerSeries_symm_apply_coeff`：∀ {R : Type u_2} [inst : Semi
ring R] (f : PowerSeries R) (n : ℕ),   (HahnSeries.toPowerSeries.symm f).coeff n
 = (PowerSeries.coeff n) f
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 32 条，此处仅展示前 30 条）
-/
theorem coeff_coe (i : ℤ) :
    ((f : R⟦X⟧) : R⸨X⸩).coeff i =
      if i < 0 then 0 else PowerSeries.coeff i.natAbs f := by
  cases i
  · rw [Int.ofNat_eq_natCast, coeff_coe_powerSeries, if_neg (Int.natCast_nonneg _).not_gt,
      Int.natAbs_natCast]
  · rw [ofPowerSeries_apply, embDomain_notin_image_support, if_pos (Int.negSucc_lt_zero _)]
    simp
/-
**PowerSeries.coe_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_C (r : R) : ((C r : R⟦X⟧) : R⸨X⸩) = HahnSeries.C r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ofPowerSeries_C`：ofPowerSeries_C (r : R) : ofPowerSeries Γ R 
(PowerSeries.C r) = HahnSeries.C r
-/
theorem coe_C (r : R) : ((C r : R⟦X⟧) : R⸨X⸩) = HahnSeries.C r :=
  ofPowerSeries_C _
/-
**PowerSeries.coe_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_X : ((X : R⟦X⟧) : R⸨X⸩) = single 1 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ofPowerSeries_X`：ofPowerSeries_X : ofPowerSeries Γ R PowerSer
ies.X = single 1 1
-/
theorem coe_X : ((X : R⟦X⟧) : R⸨X⸩) = single 1 1 :=
  ofPowerSeries_X

@[simp, norm_cast]
/-
**PowerSeries.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_smul {S : Type*} [Semiring S] [Module R S] (r : R) (x : S⟦X⟧) : ((r • 
x : S⟦X⟧) : S⸨X⸩) = r • (ofPowerSeries Int S x)
参数：r : R；x : S⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_coe`：coeff_coe (i : Int) : ((f : R⟦X⟧) : R⸨X⸩).coeff i
 = if i < 0 then 0 else PowerSeries.coeff i.natAbs f
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_smul {S : Type*} [Semiring S] [Module R S] (r : R) (x : S⟦X⟧) :
    ((r • x : S⟦X⟧) : S⸨X⸩) = r • (ofPowerSeries ℤ S x) := by
  ext
  simp [coeff_coe, coeff_smul, smul_ite]

@[norm_cast]
/-
**PowerSeries.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_pow (n : Nat) : ((f ^ n : R⟦X⟧) : R⸨X⸩) = (ofPowerSeries Int R f) ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem coe_pow (n : ℕ) : ((f ^ n : R⟦X⟧) : R⸨X⸩) = (ofPowerSeries ℤ R f) ^ n :=
  (ofPowerSeries ℤ R).map_pow _ _

end PowerSeries

namespace RatFunc

open scoped LaurentSeries

variable {F : Type u} [Field F] (p q : F[X]) (f g : RatFunc F)

/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FaithfulSMul F[X] F⸨X⸩ := by
  refine (faithfulSMul_iff_algebraMap_injective F[X] F⸨X⸩).mpr ?_
  exact algebraMap_hahnSeries_injective ℤ
/-
**RatFunc.coeToLaurentSeries** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
形式化陈述：coeToLaurentSeries : Coe (RatFunc F) F⸨X⸩
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)
-/
instance coeToLaurentSeries : Coe (RatFunc F) F⸨X⸩ :=
  ⟨algebraMap (RatFunc F) F⸨X⸩⟩
/-
**RatFunc.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：coe_coe (P : Polynomial F) : ((P : F⟦X⟧) : F⸨X⸩) = (P : RatFunc F)
参数：P : Polynomial F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_coe (P : Polynomial F) : ((P : F⟦X⟧) : F⸨X⸩) = (P : RatFunc F) := by
  simp [coePolynomial, coe_def, ← IsScalarTower.algebraMap_apply]

-- Porting note: removed `norm_cast` because "badly shaped lemma, rhs can't start with coe"
-- even though `single 1 1` is a bundled function application, not a "real" coercion
@[simp]
/-
**RatFunc.coe_X** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：coe_X : ((X : RatFunc F) : F⸨X⸩) = single 1 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `Polynomial.coe_X`：coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X
· 使用定理 `HahnSeries.ofPowerSeries_X`：ofPowerSeries_X : ofPowerSeries Γ R PowerSer
ies.X = single 1 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_X : ((X : RatFunc F) : F⸨X⸩) = single 1 1 := by
  simp [← algebraMap_X, ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) F⸨X⸩]
/-
**RatFunc.single_one_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：single_one_eq_pow {R : Type*} [Semiring R] (n : Nat) : single (n : Int) (1
 : R) = single (1 : Int) 1 ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.single_pow`：single_pow (a : Γ) (n : Nat) (r : R) : single a r
 ^ n = single (n • a) (r ^ n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_one_eq_pow {R : Type*} [Semiring R] (n : ℕ) :
    single (n : ℤ) (1 : R) = single (1 : ℤ) 1 ^ n := by
  simp
/-
**RatFunc.single_zpow** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：single_zpow (n : Int) : single (n : Int) (1 : F) = single (1 : Int) 1 ^ n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.single_one_eq_pow`：single_one_eq_pow {R : Type*} [Semiring R] (n
 : Nat) : single (n : Int) (1 : R) = single (1 : Int) 1 ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `HahnSeries.inv_single`：inv_single (a : Γ) (r : R) : (single a r)⁻¹ = sin
gle (-a) r⁻¹
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem single_zpow (n : ℤ) :
    single (n : ℤ) (1 : F) = single (1 : ℤ) 1 ^ n := by
  match n with
  | (n : ℕ) => apply single_one_eq_pow
  | -(n + 1 : ℕ) =>
    rw [← Nat.cast_one, ← inv_one, ← HahnSeries.inv_single, zpow_neg,
      ← Nat.cast_one, Nat.cast_one,
      inv_inj, zpow_natCast, single_one_eq_pow, inv_one]
/-
**RatFunc.algebraMap_apply_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：algebraMap_apply_div : algebraMap (RatFunc F) F⸨X⸩ (algebraMap _ _ p / alg
ebraMap _ _ q) = algebraMap F[X] F⸨X⸩ p / algebraMap _ _ q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_apply_div :
    algebraMap (RatFunc F) F⸨X⸩ (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap F[X] F⸨X⸩ p / algebraMap _ _ q := by
  simp only [map_div₀, IsScalarTower.algebraMap_apply F[X] (RatFunc F) F⸨X⸩]

end RatFunc

section AdicValuation

open scoped WithZero

variable (K : Type*) [Field K]
namespace PowerSeries

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The prime ideal `(X)` of `K⟦X⟧`, when `K` is a field, as a term of the `HeightOneSpectrum`. -/
/-
**PowerSeries.idealX** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：idealX : IsDedekindDomain.HeightOneSpectrum K⟦X⟧ where asIdeal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prime ideal `(X)` of `K⟦X⟧`, when `K` is a field, as a term of the `HeightOn
eSpectrum`.
-/
def idealX : IsDedekindDomain.HeightOneSpectrum K⟦X⟧ where
  asIdeal := Ideal.span {X}
  isPrime := PowerSeries.span_X_isPrime
  ne_bot  := by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact X_ne_zero

open IsDedekindDomain.HeightOneSpectrum RatFunc WithZero

variable {K}

/- The `X`-adic valuation of a polynomial equals the `X`-adic valuation of
its coercion to `K⟦X⟧`. -/
/-
**PowerSeries.intValuation_eq_of_coe** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：intValuation_eq_of_coe (P : K[X]) : (Polynomial.idealX K).intValuation P =
 (idealX K).intValuation (P : K⟦X⟧)
参数：P : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `PowerSeries.instIsDomain`：∀ {R : Type u_1} [inst : Ring R] [IsDomain R],
 IsDomain (PowerSeries R)
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `PowerSeries.instIsDiscreteValuationRing`：∀ {k : Type u_2} [inst : Field 
k], IsDiscreteValuationRing (PowerSeries k)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.map_zero`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [in
st_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 0 = 0
· 使用定理 `Polynomial.coe_zero`：coe_zero : ((0 : R[X]) : PowerSeries R) = 0
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg`：intValuation_if_
neg {r : R} (hr : r != 0) : v.intValuation r = exp (-(Associates.mk v.asIdeal).c
ount (Associates.mk (Ideal.span {r} : Ideal …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Ideal.count_associates_factors_eq`：count_associates_factors_eq {I J : Id
eal R} (hI : I != 0) (hJ : J.IsPrime) (hJ₀ : J != ⊥) : (Associates.mk J).count (
Associates.mk I).factor…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Polynomial.X_ne_zero`：X_ne_zero [Nontrivial R] : (X : R[X]) != 0
· 使用定理 `Polynomial.prime_X`：prime_X : Prime (X : R[X])
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
The `X`-adic valuation of a polynomial equals the `X`-adic valuation of
its coercion to `K⟦X⟧`.
-/
theorem intValuation_eq_of_coe (P : K[X]) :
    (Polynomial.idealX K).intValuation P = (idealX K).intValuation (P : K⟦X⟧) := by
  by_cases hP : P = 0
  · rw [hP, Valuation.map_zero, Polynomial.coe_zero, Valuation.map_zero]
  rw [intValuation_if_neg _ hP, intValuation_if_neg _ <| (by simp [hP])]
  simp only [idealX_span, exp_neg, inv_inj, exp_inj, Nat.cast_inj]
  have span_ne_zero :
    (Ideal.span {P} : Ideal K[X]) ≠ 0 ∧ (Ideal.span {Polynomial.X} : Ideal K[X]) ≠ 0 := by
    simp only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot, hP, Polynomial.X_ne_zero,
      not_false_iff, and_self_iff]
  have span_ne_zero' :
    (Ideal.span {↑P} : Ideal K⟦X⟧) ≠ 0 ∧ ((idealX K).asIdeal : Ideal K⟦X⟧) ≠ 0 := by
    simp only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot, coe_eq_zero_iff, hP,
      not_false_eq_true, true_and, (idealX K).3]
  classical
  rw [Ideal.count_associates_factors_eq span_ne_zero.1
    (Ideal.span_singleton_prime Polynomial.X_ne_zero |>.mpr prime_X) span_ne_zero.2,
    Ideal.count_associates_factors_eq]
  on_goal 1 => convert! (normalized_count_X_eq_of_coe hP).symm
  exacts [Ideal.count_span_normalizedFactors_eq_of_normUnit hP Polynomial.normUnit_X prime_X,
    Ideal.count_span_normalizedFactors_eq_of_normUnit (by simp [hP]) normUnit_X X_prime,
    span_ne_zero'.1, (idealX K).isPrime, span_ne_zero'.2]

/-- The integral valuation of the power series `X : K⟦X⟧` equals `(ofAdd -1) : ℤᵐ⁰`. -/
@[simp]
/-
**PowerSeries.intValuation_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：intValuation_X : (idealX K).intValuation X = exp (-1 : Int)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `PowerSeries.instIsDomain`：∀ {R : Type u_1} [inst : Ring R] [IsDomain R],
 IsDomain (PowerSeries R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `PowerSeries.instIsDiscreteValuationRing`：∀ {k : Type u_2} [inst : Field 
k], IsDiscreteValuationRing (PowerSeries k)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coe_X`：coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `PowerSeries.intValuation_eq_of_coe`：intValuation_eq_of_coe (P : K[X]) : 
(Polynomial.idealX K).intValuation P = (idealX K).intValuation (P : K⟦X⟧)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_singleton`：intValuation_
singleton {r : R} (hr : r != 0) (hv : v.asIdeal = Ideal.span {r}) : v.intValuati
on r = exp (-1 : Int)
· 使用定理 `Polynomial.X_ne_zero`：X_ne_zero [Nontrivial R] : (X : R[X]) != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.idealX_span`：idealX_span : (idealX K).asIdeal = Ideal.span {X
}

--- 原说明 ---
The integral valuation of the power series `X : K⟦X⟧` equals `(ofAdd -1) : ℤᵐ⁰`.
-/
theorem intValuation_X : (idealX K).intValuation X = exp (-1 : ℤ) := by
  rw [← Polynomial.coe_X, ← intValuation_eq_of_coe]
  exact intValuation_singleton _ Polynomial.X_ne_zero (idealX_span _)

end PowerSeries

namespace RatFunc

open IsDedekindDomain.HeightOneSpectrum PowerSeries
open scoped LaurentSeries

/-- `polynomialValuationX` is an abbreviation for the `X`-adic valuation given by
`(Polynomial.idealX K).valuation K⟮X⟯`. -/
/-
**RatFunc.polynomialValuationX** 是 Mathlib 中的一个缩写定义，位于命名空间 `RatFunc`。
形式化陈述：polynomialValuationX : Valuation K⟮X⟯ Intᵐ⁰
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`polynomialValuationX` is an abbreviation for the `X`-adic valuation given by
`(Polynomial.idealX K).valuation K⟮X⟯`.
-/
abbrev polynomialValuationX : Valuation K⟮X⟯ ℤᵐ⁰ :=
  (Polynomial.idealX K).valuation _
/-
**RatFunc.valuation_eq_LaurentSeries_valuation** 是 Mathlib 中的一个定理，位于命名空间 `RatFun
c`。
形式化陈述：valuation_eq_LaurentSeries_valuation (P : K⟮X⟯) : polynomialValuationX K P
 = (PowerSeries.idealX K).valuation K⸨X⸩ P
参数：P : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.induction_on'`：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDo
main K] {P : RatFunc K → Prop} (x : RatFunc K),   (∀ (p q : Polynomial K), q ≠ 0
 → P (RatFu…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `PowerSeries.instIsDomain`：∀ {R : Type u_1} [inst : Ring R] [IsDomain R],
 IsDomain (PowerSeries R)
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `PowerSeries.instIsDiscreteValuationRing`：∀ {k : Type u_2} [inst : Field 
k], IsDiscreteValuationRing (PowerSeries k)
· 使用定理 `LaurentSeries.instIsFractionRingPowerSeries`：∀ {K : Type u_2} [inst : Fi
eld K], IsFractionRing (PowerSeries K) (LaurentSeries K)
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `Polynomial.valuation_of_mk`：valuation_of_mk (f : Polynomial K) {g : Poly
nomial K} (hg : g != 0) : (Polynomial.idealX K).valuation _ (RatFunc.mk f g) = (
Polynomial.ideal…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `RatFunc.mk_eq_mk'`：mk_eq_mk' (f : Polynomial K) {g : Polynomial K} (hg :
 g != 0) : RatFunc.mk f g = IsLocalization.mk' K⟮X⟯ f ⟨g, mem_nonZeroDivisors_if
f_ne_ze…
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `PowerSeries.instNoZeroDivisors`：∀ {R : Type u_1} [inst : Semiring R] [No
ZeroDivisors R], NoZeroDivisors (PowerSeries R)
· 使用定理 `MvPowerSeries.instNontrivial`：∀ {σ : Type u_1} {R : Type u_2} [Nontrivia
l R], Nontrivial (MvPowerSeries σ R)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 41 条，此处仅展示前 30 条）
-/
theorem valuation_eq_LaurentSeries_valuation (P : K⟮X⟯) :
    polynomialValuationX K P = (PowerSeries.idealX K).valuation K⸨X⸩ P := by
  refine RatFunc.induction_on' P ?_
  intro f g h
  rw [Polynomial.valuation_of_mk K f h, RatFunc.mk_eq_mk' f h, Eq.comm]
  convert!
    @valuation_of_mk' K⟦X⟧ _ _ K⸨X⸩ _ _ _ (PowerSeries.idealX K) f
      ⟨g, mem_nonZeroDivisors_iff_ne_zero.2 <| (by simp [h])⟩
  · simp [← IsScalarTower.algebraMap_apply K[X] K⟮X⟯ K⸨X⸩]
  exacts [intValuation_eq_of_coe _, intValuation_eq_of_coe _]

end RatFunc

namespace LaurentSeries


open IsDedekindDomain.HeightOneSpectrum PowerSeries RatFunc WithZero

/-
**LaurentSeries.valued** 是 Mathlib 中的一个实例，位于命名空间 `LaurentSeries`。
形式化陈述：valued : Valued K⸨X⸩ Intᵐ⁰
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LaurentSeries.instIsFractionRingPowerSeries`：∀ {K : Type u_2} [inst : Fi
eld K], IsFractionRing (PowerSeries K) (LaurentSeries K)
-/
instance valued : Valued K⸨X⸩ ℤᵐ⁰ := Valued.mk' ((PowerSeries.idealX K).valuation _)
/-
**LaurentSeries.valuation_def** 是 Mathlib 中的一个引理，位于命名空间 `LaurentSeries`。
形式化陈述：valuation_def : (Valued.v : Valuation K⸨X⸩ Intᵐ⁰) = (PowerSeries.idealX K)
.valuation _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
lemma valuation_def : (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰) = (PowerSeries.idealX K).valuation _ := rfl
/-
**LaurentSeries.valuation_coe_ratFunc** 是 Mathlib 中的一个引理，位于命名空间 `LaurentSeries`。
形式化陈述：valuation_coe_ratFunc (f : K⟮X⟯) : Valued.v (f : K⸨X⸩) = Valued.v f
参数：f : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma valuation_coe_ratFunc (f : K⟮X⟯) :
    Valued.v (f : K⸨X⸩) = Valued.v f := by
  simp [adicValued_apply, ← valuation_eq_LaurentSeries_valuation]
/-
**LaurentSeries.valuation_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：valuation_X_pow (s : Nat) : Valued.v (((X : K⟦X⟧) : K⸨X⸩) ^ s) = exp (-(s 
: Int))
参数：s : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `PowerSeries.instIsDomain`：∀ {R : Type u_1} [inst : Ring R] [IsDomain R],
 IsDomain (PowerSeries R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `PowerSeries.instIsDiscreteValuationRing`：∀ {k : Type u_2} [inst : Field 
k], IsDiscreteValuationRing (PowerSeries k)
· 使用定理 `LaurentSeries.instIsFractionRingPowerSeries`：∀ {K : Type u_2} [inst : Fi
eld K], IsFractionRing (PowerSeries K) (LaurentSeries K)
· 使用引理 `LaurentSeries.valuation_def`：valuation_def : (Valued.v : Valuation K⸨X⸩ 
Intᵐ⁰) = (PowerSeries.idealX K).valuation _
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentSeries.coe_algebraMap`：coe_algebraMap [CommSemiring R] : ⇑(algebr
aMap R⟦X⟧ R⸨X⸩) = HahnSeries.ofPowerSeries Int R
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用定理 `PowerSeries.intValuation_X`：intValuation_X : (idealX K).intValuation X =
 exp (-1 : Int)
· 使用定理 `WithZero.exp_nsmul`：∀ {M : Type u_4} [inst : AddMonoid M] (n : ℕ) (a : M
), WithZero.exp (n • a) = WithZero.exp a ^ n
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
-/
theorem valuation_X_pow (s : ℕ) :
    Valued.v (((X : K⟦X⟧) : K⸨X⸩) ^ s) = exp (-(s : ℤ)) := by
  rw [map_pow, valuation_def, ← LaurentSeries.coe_algebraMap,
    valuation_of_algebraMap, intValuation_X, ← exp_nsmul, smul_neg, nsmul_one]
/-
**LaurentSeries.valuation_single_zpow** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：valuation_single_zpow (s : Int) : Valued.v (HahnSeries.single s (1 : K) : 
K⸨X⸩) = exp (-(s : Int))
参数：s : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.ofPowerSeries_X_pow`：ofPowerSeries_X_pow {R} [Semiring R] (n 
: Nat) : ofPowerSeries Γ R (PowerSeries.X ^ n) = single (n : Γ) 1
· 使用定理 `PowerSeries.coe_pow`：coe_pow (n : Nat) : ((f ^ n : R⟦X⟧) : R⸨X⸩) = (ofPo
werSeries Int R f) ^ n
· 使用定理 `LaurentSeries.valuation_X_pow`：valuation_X_pow (s : Nat) : Valued.v (((X
 : K⟦X⟧) : K⸨X⸩) ^ s) = exp (-(s : Int))
· 使用定理 `Int.negSucc_eq`：∀ (n : ℕ), Int.negSucc n = -(↑n + 1)
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `HahnSeries.inv_single`：inv_single (a : Γ) (r : R) : (single a r)⁻¹ = sin
gle (-a) r⁻¹
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Int.natCast_succ`：∀ (n : ℕ), ↑n.succ = ↑n + 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `WithZero.exp_neg`：∀ {G : Type u_5} [inst : AddGroup G] (a : G), WithZero
.exp (-a) = (WithZero.exp a)⁻¹
-/
theorem valuation_single_zpow (s : ℤ) :
    Valued.v (HahnSeries.single s (1 : K) : K⸨X⸩) = exp (-(s : ℤ)) := by
  obtain s | s := s
  · rw [Int.ofNat_eq_natCast, ← HahnSeries.ofPowerSeries_X_pow, PowerSeries.coe_pow,
      valuation_X_pow]
  · rw [Int.negSucc_eq, ← inv_inj, ← map_inv₀, inv_single, neg_neg, ← Int.natCast_succ, inv_one,
      ← HahnSeries.ofPowerSeries_X_pow, PowerSeries.coe_pow, valuation_X_pow, exp_neg]

/-- The coefficients of a power series vanish in degree strictly less than its valuation. -/
/-
**LaurentSeries.coeff_zero_of_lt_intValuation** 是 Mathlib 中的一个定理，位于命名空间 `Laurent
Series`。
形式化陈述：coeff_zero_of_lt_intValuation {n d : Nat} {f : K⟦X⟧} (H : Valued.v (f : K⸨
X⸩) <= exp (-d : Int)) : n < d -> coeff n f = 0
参数：H : Valued.v (f : K⸨X⸩) <= exp (-d : Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PowerSeries.X_pow_dvd_iff`：X_pow_dvd_iff {n : Nat} {φ : R⟦X⟧} : (X : R⟦X
⟧) ^ n ∣ φ ↔ forall m, m < n -> coeff m φ = 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_singleton_dvd_span_singleton_iff_dvd`：span_singleton_dvd_span
_singleton_iff_dvd {a b : R} : span {a} ∣ span ({b} : Set R) ↔ a ∣ b
· 使用定理 `PowerSeries.instIsDomain`：∀ {R : Type u_1} [inst : Ring R] [IsDomain R],
 IsDomain (PowerSeries R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `PowerSeries.instIsDiscreteValuationRing`：∀ {k : Type u_2} [inst : Field 
k], IsDiscreteValuationRing (PowerSeries k)
· 使用定理 `Ideal.span_singleton_pow`：span_singleton_pow (s : R) [(span {s}).IsTwoSi
ded] (n : Nat) : span {s} ^ n = (span {s ^ n} : Ideal R)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `PowerSeries.idealX.eq_1`：∀ (K : Type u_2) [inst : Field K],   PowerSerie
s.idealX K = { asIdeal := Ideal.span {PowerSeries.X}, isPrime := ⋯, ne_bot := ⋯ 
}
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd`：intValua
tion_le_pow_iff_dvd (r : R) (n : Nat) : v.intValuation r <= exp (-(n : Int)) ↔ v
.asIdeal ^ n ∣ Ideal.span {r}
· 使用定理 `LaurentSeries.instIsFractionRingPowerSeries`：∀ {K : Type u_2} [inst : Fi
eld K], IsFractionRing (PowerSeries K) (LaurentSeries K)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用引理 `LaurentSeries.valuation_def`：valuation_def : (Valued.v : Valuation K⸨X⸩ 
Intᵐ⁰) = (PowerSeries.idealX K).valuation _
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentSeries.coe_algebraMap`：coe_algebraMap [CommSemiring R] : ⇑(algebr
aMap R⟦X⟧ R⸨X⸩) = HahnSeries.ofPowerSeries Int R

--- 原说明 ---
The coefficients of a power series vanish in degree strictly less than its valua
tion.
-/
theorem coeff_zero_of_lt_intValuation {n d : ℕ} {f : K⟦X⟧}
    (H : Valued.v (f : K⸨X⸩) ≤ exp (-d : ℤ)) :
    n < d → coeff n f = 0 := by
  intro hnd
  apply (PowerSeries.X_pow_dvd_iff).mp _ n hnd
  rwa [← LaurentSeries.coe_algebraMap, valuation_def, valuation_of_algebraMap,
    intValuation_le_pow_iff_dvd (PowerSeries.idealX K) f d, PowerSeries.idealX,
    Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd] at H

/-- The valuation of a power series is the order of the first non-zero coefficient. -/
/-
**LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
LaurentSeries`。
形式化陈述：intValuation_le_iff_coeff_lt_eq_zero {d : Nat} (f : K⟦X⟧) : Valued.v (f : 
K⸨X⸩) <= exp (-d : Int) ↔ forall n : Nat, n < d -> coeff n f = 0
参数：f : K⟦X⟧。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PowerSeries.X_pow_dvd_iff`：X_pow_dvd_iff {n : Nat} {φ : R⟦X⟧} : (X : R⟦X
⟧) ^ n ∣ φ ↔ forall m, m < n -> coeff m φ = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentSeries.coe_algebraMap`：coe_algebraMap [CommSemiring R] : ⇑(algebr
aMap R⟦X⟧ R⸨X⸩) = HahnSeries.ofPowerSeries Int R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `PowerSeries.instIsDomain`：∀ {R : Type u_1} [inst : Ring R] [IsDomain R],
 IsDomain (PowerSeries R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `PowerSeries.instIsDiscreteValuationRing`：∀ {k : Type u_2} [inst : Field 
k], IsDiscreteValuationRing (PowerSeries k)
· 使用定理 `LaurentSeries.instIsFractionRingPowerSeries`：∀ {K : Type u_2} [inst : Fi
eld K], IsFractionRing (PowerSeries K) (LaurentSeries K)
· 使用引理 `LaurentSeries.valuation_def`：valuation_def : (Valued.v : Valuation K⸨X⸩ 
Intᵐ⁰) = (PowerSeries.idealX K).valuation _
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.span_singleton_dvd_span_singleton_iff_dvd`：span_singleton_dvd_span
_singleton_iff_dvd {a b : R} : span {a} ∣ span ({b} : Set R) ↔ a ∣ b
· 使用定理 `Ideal.span_singleton_pow`：span_singleton_pow (s : R) [(span {s}).IsTwoSi
ded] (n : Nat) : span {s} ^ n = (span {s ^ n} : Ideal R)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd`：intValua
tion_le_pow_iff_dvd (r : R) (n : Nat) : v.intValuation r <= exp (-(n : Int)) ↔ v
.asIdeal ^ n ∣ Ideal.span {r}

--- 原说明 ---
The valuation of a power series is the order of the first non-zero coefficient.
-/
theorem intValuation_le_iff_coeff_lt_eq_zero {d : ℕ} (f : K⟦X⟧) :
    Valued.v (f : K⸨X⸩) ≤ exp (-d : ℤ) ↔
      ∀ n : ℕ, n < d → coeff n f = 0 := by
  have : PowerSeries.X ^ d ∣ f ↔ ∀ n : ℕ, n < d → (PowerSeries.coeff n) f = 0 :=
    ⟨PowerSeries.X_pow_dvd_iff.mp, PowerSeries.X_pow_dvd_iff.mpr⟩
  rw [← this, ← LaurentSeries.coe_algebraMap, valuation_def, valuation_of_algebraMap,
    ← Ideal.span_singleton_dvd_span_singleton_iff_dvd, ← Ideal.span_singleton_pow]
  apply intValuation_le_pow_iff_dvd

/-- The coefficients of a Laurent series vanish in degree strictly less than its valuation. -/
/-
**LaurentSeries.coeff_zero_of_lt_valuation** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSer
ies`。
形式化陈述：coeff_zero_of_lt_valuation {n D : Int} {f : K⸨X⸩} (H : Valued.v f <= exp (
-D)) : n < D -> f.coeff n = 0
参数：H : Valued.v f <= exp (-D)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `HahnSeries.coeff_eq_zero_of_lt_order`：coeff_eq_zero_of_lt_order {x : R⟦Γ
⟧} {i : Γ} (hi : i < x.order) : x.coeff i = 0
· 使用定理 `Int.exists_eq_neg_ofNat`：∀ {a : ℤ}, a ≤ 0 → ∃ n, a = -↑n
· 使用定理 `Int.eq_ofNat_of_zero_le`：∀ {a : ℤ}, 0 ≤ a → ∃ n, a = ↑n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_le_iff_add_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α
] [AddRightMono α] {a b : α}, -a ≤ b ↔ 0 ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_add_neg_of_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, 
a + c = b → a = b + -c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentSeries.powerSeriesPart_coeff`：powerSeriesPart_coeff (x : R⸨X⸩) (n
 : Nat) : PowerSeries.coeff n x.powerSeriesPart = x.coeff (x.order + n)
· 使用定理 `LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero`：intValuation_le_iff_
coeff_lt_eq_zero {d : Nat} (f : K⟦X⟧) : Valued.v (f : K⸨X⸩) <= exp (-d : Int) ↔ 
forall n : Nat, n < d -> coeff n f = 0
· 使用定理 `LaurentSeries.ofPowerSeries_powerSeriesPart`：ofPowerSeries_powerSeriesPa
rt (x : R⸨X⸩) : ofPowerSeries Int R x.powerSeriesPart = single (-x.order) 1 * x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `WithZero.exp_add`：∀ {M : Type u_4} [inst : AddMonoid M] (a b : M), WithZ
ero.exp (a + b) = WithZero.exp a * WithZero.exp b
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
· 使用定理 `HahnSeries.ofPowerSeries_X_pow`：ofPowerSeries_X_pow {R} [Semiring R] (n 
: Nat) : ofPowerSeries Γ R (PowerSeries.X ^ n) = single (n : Γ) 1
· 使用定理 `PowerSeries.coe_pow`：coe_pow (n : Nat) : ((f ^ n : R⟦X⟧) : R⸨X⸩) = (ofPo
werSeries Int R f) ^ n
· 使用定理 `LaurentSeries.valuation_X_pow`：valuation_X_pow (s : Nat) : Valued.v (((X
 : K⟦X⟧) : K⸨X⸩) ^ s) = exp (-(s : Int))
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
The coefficients of a Laurent series vanish in degree strictly less than its val
uation.
-/
theorem coeff_zero_of_lt_valuation {n D : ℤ} {f : K⸨X⸩}
    (H : Valued.v f ≤ exp (-D)) : n < D → f.coeff n = 0 := by
  intro hnd
  by_cases! h_n_ord : n < f.order
  · exact coeff_eq_zero_of_lt_order h_n_ord
  set F := powerSeriesPart f with hF
  by_cases! ord_nonpos : f.order ≤ 0
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_le_iff_add_nonneg.mp (hs ▸ h_n_ord))
    obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (a := D + s) (by lia)
    rw [eq_add_neg_of_add_eq hm, add_comm, ← hs, ← powerSeriesPart_coeff]
    apply (intValuation_le_iff_coeff_lt_eq_zero K F).mp _ m (by linarith)
    rw [hF, ofPowerSeries_powerSeriesPart f, hs, neg_neg, ← hd, neg_add_rev, exp_add, map_mul,
      ← ofPowerSeries_X_pow s, PowerSeries.coe_pow, valuation_X_pow K s]
    gcongr
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (Int.neg_nonpos_of_nonneg (le_of_lt ord_nonpos))
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (a := n - s) (by grind)
    obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (a := D - s) (by lia)
    rw [sub_eq_iff_eq_add.mp hm, add_comm, ← neg_neg (s : ℤ), ← hs, neg_neg,
      ← powerSeriesPart_coeff]
    apply (intValuation_le_iff_coeff_lt_eq_zero K F).mp _ m (by linarith)
    rw [hF, ofPowerSeries_powerSeriesPart f, map_mul, ← hd, hs, neg_sub, sub_eq_add_neg,
      exp_add, valuation_single_zpow, neg_neg]
    gcongr

/-- The valuation of a Laurent series is the order of the first non-zero coefficient. -/
/-
**LaurentSeries.valuation_le_iff_coeff_lt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Lau
rentSeries`。
形式化陈述：valuation_le_iff_coeff_lt_eq_zero {D : Int} {f : K⸨X⸩} : Valued.v f <= exp
 (-D : Int) ↔ forall n : Int, n < D -> f.coeff n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `LaurentSeries.coeff_zero_of_lt_valuation`：coeff_zero_of_lt_valuation {n 
D : Int} {f : K⸨X⸩} (H : Valued.v f <= exp (-D)) : n < D -> f.coeff n = 0
· 使用定理 `Int.exists_eq_neg_ofNat`：∀ {a : ℤ}, a ≤ 0 → ∃ n, a = -↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentSeries.single_order_mul_powerSeriesPart`：single_order_mul_powerSe
riesPart (x : R⸨X⸩) : (single x.order 1 : R⸨X⸩) * x.powerSeriesPart = x
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
· 使用定理 `LaurentSeries.valuation_single_zpow`：valuation_single_zpow (s : Int) : V
alued.v (HahnSeries.single s (1 : K) : K⸨X⸩) = exp (-(s : Int))
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `le_mul_inv_iff₀`：le_mul_inv_iff₀ (hc : 0 < c) : a <= b * c⁻¹ ↔ a * c <= 
b
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
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `WithZero.exp_neg`：∀ {G : Type u_5} [inst : AddGroup G] (a : G), WithZero
.exp (-a) = (WithZero.exp a)⁻¹
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `WithZero.exp_add`：∀ {M : Type u_4} [inst : AddMonoid M] (a b : M), WithZ
ero.exp (a + b) = WithZero.exp a * WithZero.exp b
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
The valuation of a Laurent series is the order of the first non-zero coefficient
.
-/
theorem valuation_le_iff_coeff_lt_eq_zero {D : ℤ} {f : K⸨X⸩} :
    Valued.v f ≤ exp (-D : ℤ) ↔ ∀ n : ℤ, n < D → f.coeff n = 0 := by
  refine ⟨fun hnD n hn => coeff_zero_of_lt_valuation K hnD hn, fun h_val_f => ?_⟩
  let F := powerSeriesPart f
  by_cases! ord_nonpos : f.order ≤ 0
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat ord_nonpos
    rw [← f.single_order_mul_powerSeriesPart, hs, map_mul, valuation_single_zpow, neg_neg, mul_comm,
      ← le_mul_inv_iff₀, exp_neg, ← mul_inv, ← exp_add, ← exp_neg]
    · by_cases! hDs : D + s ≤ 0
      · apply le_trans ((PowerSeries.idealX K).valuation_le_one F)
        rwa [← log_le_iff_le_exp one_ne_zero, le_neg, log_one, neg_zero]
      · obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le hDs.le
        rw [hd]
        apply (intValuation_le_iff_coeff_lt_eq_zero K F).mpr
        intro n hn
        rw [powerSeriesPart_coeff f n, hs]
        apply h_val_f
        lia
    · simp [ne_eq, zero_lt_iff]
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat <| neg_nonpos_of_nonneg ord_nonpos.le
    rw [neg_inj] at hs
    rw [← f.single_order_mul_powerSeriesPart, hs, map_mul, valuation_single_zpow, mul_comm,
      ← le_mul_inv_iff₀, ← exp_neg, ← exp_add, neg_neg]
    · by_cases! hDs : D - s ≤ 0
      · apply le_trans ((PowerSeries.idealX K).valuation_le_one F)
        rw [← log_le_iff_le_exp one_ne_zero, log_one]
        lia
      · obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le hDs.le
        rw [← neg_neg (-D + ↑s), ← sub_eq_neg_add, neg_sub, hd]
        apply (intValuation_le_iff_coeff_lt_eq_zero K F).mpr
        intro n hn
        rw [powerSeriesPart_coeff f n, hs]
        apply h_val_f (s + n)
        lia
    · simp [ne_eq, zero_lt_iff]
/-
**LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`LaurentSeries`。
形式化陈述：valuation_le_iff_coeff_lt_log_eq_zero {D : Intᵐ⁰} (hD : D != 0) {f : K⸨X⸩}
 : Valued.v f <= D ↔ forall n : Int, n < -log D -> f.coeff n = 0
参数：hD : D != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.exp.eq_1`：∀ {M : Type u_4} (a : M), WithZero.exp a = ↑(Multipli
cative.ofAdd a)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `LaurentSeries.valuation_le_iff_coeff_lt_eq_zero`：valuation_le_iff_coeff_
lt_eq_zero {D : Int} {f : K⸨X⸩} : Valued.v f <= exp (-D : Int) ↔ forall n : Int,
 n < D -> f.coeff n = 0
· 使用定理 `WithZero.log_exp`：∀ {M : Type u_4} [inst : AddMonoid M] (a : M), (WithZe
ro.exp a).log = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem valuation_le_iff_coeff_lt_log_eq_zero {D : ℤᵐ⁰} (hD : D ≠ 0) {f : K⸨X⸩} :
    Valued.v f ≤ D ↔ ∀ n : ℤ, n < -log D → f.coeff n = 0 := by
  cases D
  · simp_all
  · rename_i D
    cases D
    rename_i D
    rw [← exp, ← neg_neg D, valuation_le_iff_coeff_lt_eq_zero, log_exp, neg_neg]

/-- Two Laurent series whose difference has small valuation have the same coefficients for
small enough indices. -/
/-
**LaurentSeries.eq_coeff_of_valuation_sub_lt** 是 Mathlib 中的一个定理，位于命名空间 `LaurentS
eries`。
形式化陈述：eq_coeff_of_valuation_sub_lt {d n : Int} {f g : K⸨X⸩} (H : Valued.v (g - f
) <= exp (-d)) : n < d -> g.coeff n = f.coeff n
参数：H : Valued.v (g - f) <= exp (-d)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.coeff_sub`：coeff_sub {x y : R⟦Γ⟧} {a : Γ} : (x - y).coeff a =
 x.coeff a - y.coeff a
· 使用定理 `LaurentSeries.coeff_zero_of_lt_valuation`：coeff_zero_of_lt_valuation {n 
D : Int} {f : K⸨X⸩} (H : Valued.v f <= exp (-D)) : n < D -> f.coeff n = 0

--- 原说明 ---
Two Laurent series whose difference has small valuation have the same coefficien
ts for
small enough indices.
-/
theorem eq_coeff_of_valuation_sub_lt {d n : ℤ} {f g : K⸨X⸩}
    (H : Valued.v (g - f) ≤ exp (-d)) : n < d → g.coeff n = f.coeff n := by
  by_cases triv : g = f
  · exact fun _ => by rw [triv]
  · intro hn
    apply eq_of_sub_eq_zero
    rw [← HahnSeries.coeff_sub]
    apply coeff_zero_of_lt_valuation K H hn

/-- Every Laurent series of valuation less than `(1 : ℤᵐ⁰)` comes from a power series. -/
/-
**LaurentSeries.val_le_one_iff_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：val_le_one_iff_eq_coe (f : K⸨X⸩) : Valued.v f <= (1 : Intᵐ⁰) ↔ exists F : 
K⟦X⟧, F = f
参数：f : K⸨X⸩。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero`：valuation_le_iff_co
eff_lt_log_eq_zero {D : Intᵐ⁰} (hD : D != 0) {f : K⸨X⸩} : Valued.v f <= D ↔ fora
ll n : Int, n < -log D -> f.coeff n = 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `WithZero.log_one`：∀ {M : Type u_4} [inst : AddMonoid M], WithZero.log 1 
= 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LaurentSeries.coeff_coe_powerSeries`：coeff_coe_powerSeries (x : R⟦X⟧) (n
 : Nat) : HahnSeries.coeff (x : R⸨X⸩) n = PowerSeries.coeff n x
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.negSucc_lt_zero`：∀ (n : ℕ), Int.negSucc n < 0
· 使用定理 `HahnSeries.embDomain_of_notMem_range`：embDomain_of_notMem_range {f : Γ ↪
o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ Set.range f) : (embDomain f x).coeff b = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Every Laurent series of valuation less than `(1 : ℤᵐ⁰)` comes from a power serie
s.
-/
theorem val_le_one_iff_eq_coe (f : K⸨X⸩) : Valued.v f ≤ (1 : ℤᵐ⁰) ↔
    ∃ F : K⟦X⟧, F = f := by
  rw [valuation_le_iff_coeff_lt_log_eq_zero _ one_ne_zero, log_one, neg_zero]
  refine ⟨fun h => ⟨PowerSeries.mk fun n => f.coeff n, ?_⟩, ?_⟩
  on_goal 1 => ext (_ | n)
  · simp only [Int.ofNat_eq_natCast, coeff_coe_powerSeries, coeff_mk]
  on_goal 1 => simp only [h (Int.negSucc n) (Int.negSucc_lt_zero n)]
  on_goal 2 => rintro ⟨F, rfl⟩ _ _
  all_goals
    apply HahnSeries.embDomain_of_notMem_range
    simp only [Nat.coe_castAddMonoidHom, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
      Set.mem_range, not_exists, reduceCtorEq]
    intro
  · simp only [not_false_eq_true]
  · lia

end LaurentSeries

end AdicValuation

namespace LaurentSeries

variable {K : Type*} [Field K]

section Complete

open Filter WithZero PowerSeries

variable (K) in
/-
**LaurentSeries.valuation_surjective** 是 Mathlib 中的一个引理，位于命名空间 `LaurentSeries`。
形式化陈述：valuation_surjective : Function.Surjective (Valued.v (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
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
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LaurentSeries.valuation_single_zpow`：valuation_single_zpow (s : Int) : V
alued.v (HahnSeries.single s (1 : K) : K⸨X⸩) = exp (-(s : Int))
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `WithZero.exp_log`：∀ {M : Type u_4} [inst : AddMonoid M] {x : WithZero (M
ultiplicative M)}, x ≠ 0 → WithZero.exp x.log = x
-/
lemma valuation_surjective : Function.Surjective (Valued.v (R := K⸨X⸩)) := by
  intro n
  by_cases hn0 : n = 0
  · use 0; simp [hn0]
  · use ((HahnSeries.single (-WithZero.log n)) 1)
    simp [LaurentSeries.valuation_single_zpow, exp_log hn0]

/-- Sending a Laurent series to its `d`-th coefficient is uniformly continuous (independently of the
uniformity with which `K` is endowed). -/
/-
**LaurentSeries.uniformContinuous_coeff** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries
`。
形式化陈述：uniformContinuous_coeff {uK : UniformSpace K} (d : Int) : UniformContinuou
s fun f : K⸨X⸩ => f.coeff d
参数：d : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `uniformContinuous_iff_eventually`：uniformContinuous_iff_eventually {f : 
α -> β} : UniformContinuous f ↔ forall r in 𝓤 β, forallᶠ x : α × α in 𝓤 α, (f x.
1, f x.2) in r
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `WithZero.coe_ne_zero`：∀ {α : Type u} {a : α}, ↑a ≠ 0
· 使用引理 `LaurentSeries.valuation_surjective`：valuation_surjective : Function.Surj
ective (Valued.v (R
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Invertible.toNeZero`：∀ {α : Type u} [inst : MulZeroOneClass α] [Nontrivi
al α] (a : α) [Invertible a], NeZero a
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff`：restrict₀_eq_zero_i
ff {a : A} : restrict₀ f a = 0 ↔ f a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.coe_ofClass`：coe_ofClass : ⇑(MonoidWithZeroHom.ofClass v) = v
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀`：embedding_restrict₀ (
a : A) : ValueGroup₀.embedding (restrict₀ f a) = f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Valuation.restrict_lt_iff_lt_embedding`：restrict_lt_iff_lt_embedding {x 
: R} {g : ValueGroup₀ (.ofClass v)} : v.restrict x < g ↔ v x < embedding g
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Valued.hasBasis_uniformity`：hasBasis_uniformity : (𝓤 R).HasBasis (fun _ 
=> True) fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ => { p : R × R
 | v.restrict (p…
· 使用定理 `LaurentSeries.eq_coeff_of_valuation_sub_lt`：eq_coeff_of_valuation_sub_lt
 {d n : Int} {f g : K⸨X⸩} (H : Valued.v (g - f) <= exp (-d)) : n < d -> g.coeff 
n = f.coeff n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Sending a Laurent series to its `d`-th coefficient is uniformly continuous (inde
pendently of the
uniformity with which `K` is endowed).
-/
theorem uniformContinuous_coeff {uK : UniformSpace K} (d : ℤ) :
    UniformContinuous fun f : K⸨X⸩ ↦ f.coeff d := by
  refine uniformContinuous_iff_eventually.mpr fun S hS ↦ eventually_iff_exists_mem.mpr ?_
  let γ : (ℤᵐ⁰)ˣ := Units.mk0 (exp (-(d + 1))) coe_ne_zero
  use {P | Valued.v (P.snd - P.fst) < ↑γ}
  refine ⟨?_, fun _ hP ↦ ?_⟩
  · obtain ⟨x, hx⟩ := LaurentSeries.valuation_surjective K γ
    have : Valued.v.restrict x ≠ 0 := fun h ↦ NeZero.ne γ.1 <|
      hx ▸ MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff.1 h
    rw [← hx]
    nth_rw 2 [← Valuation.coe_ofClass]
    rw [← MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
    simp_rw [← Valued.v.restrict_lt_iff_lt_embedding]
    exact (Valued.hasBasis_uniformity K⸨X⸩ ℤᵐ⁰).mem_of_mem
      (i := Units.mk0 (Valued.v.restrict x) this) (by tauto)
  · simpa [eq_coeff_of_valuation_sub_lt K hP.le (lt_add_one _)] using mem_uniformity_of_eq hS rfl

/-- Since extracting coefficients is uniformly continuous, every Cauchy filter in
`K⸨X⸩` gives rise to a Cauchy filter in `K` for every `d : ℤ`, and such Cauchy filter
in `K` converges to a principal filter -/
/-
**LaurentSeries.Cauchy.coeff** 是 Mathlib 中的一个定义，位于命名空间 `LaurentSeries.Cauchy`。
形式化陈述：{K : Type u_2} → [inst : Field K] → {ℱ : Filter (LaurentSeries K)} → Cauch
y ℱ → ℤ → K
参数：LaurentSeries K。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X

--- 原说明 ---
Since extracting coefficients is uniformly continuous, every Cauchy filter in
`K⸨X⸩` gives rise to a Cauchy filter in `K` for every `d : ℤ`, and such Cauchy f
ilter
in `K` converges to a principal filter
-/
def Cauchy.coeff {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) : ℤ → K :=
  let _ : UniformSpace K := ⊥
  fun d ↦ DiscreteUniformity.cauchyConst <| hℱ.map (uniformContinuous_coeff d)
/-
**LaurentSeries.Cauchy.coeff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries.Ca
uchy`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] {ℱ : Filter (LaurentSeries K)} (hℱ : Cau
chy ℱ) (D : ℤ),   Filter.Tendsto (fun f => f.coeff D) ℱ (Filter.principal {Laure
ntSeries.Cauchy.coeff hℱ D})
参数：LaurentSeries K；hℱ : Cauchy ℱ；D : ℤ；fun f => f.coeff D；Filter.principal {Laur
entSeries.Cauchy.coeff hℱ D}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `Cauchy.map`：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α] 
[inst : UniformSpace β] {f : Filter α} {m : α → β},   Cauchy f → UniformContinuo
…
· 使用定理 `LaurentSeries.uniformContinuous_coeff`：uniformContinuous_coeff {uK : Uni
formSpace K} (d : Int) : UniformContinuous fun f : K⸨X⸩ => f.coeff d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `DiscreteUniformity.eq_pure_cauchyConst`：eq_pure_cauchyConst {f : Filter 
α} (hf : Cauchy f) : f = pure (cauchyConst hf)
-/
theorem Cauchy.coeff_tendsto {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) (D : ℤ) :
    Tendsto (fun f : K⸨X⸩ ↦ f.coeff D) ℱ (𝓟 {coeff hℱ D}) :=
  let _ : UniformSpace K := ⊥
  le_of_eq <| DiscreteUniformity.eq_pure_cauchyConst
    (hℱ.map (uniformContinuous_coeff D)) ▸ (principal_singleton _).symm

/- For every Cauchy filter of Laurent series, there is some `N` such that the `n`-th coefficient
vanishes for all `n ≤ N` and almost all series in the filter. This is an auxiliary lemma used
to construct the limit of the Cauchy filter as a Laurent series, ensuring that the support of the
limit is `PWO`.
The result is true also for more general Hahn Series indexed over a partially ordered group `Γ`
beyond the special case `Γ = ℤ`, that corresponds to Laurent Series: nevertheless the proof below
does not generalise, as it relies on the study of the `X`-adic valuation attached to the height-one
prime `X`, and this is peculiar to the one-variable setting. In the future we should prove this
result in full generality and deduce the case `Γ = ℤ` from that one. -/
/-
**LaurentSeries.Cauchy.exists_lb_eventual_support** 是 Mathlib 中的一个定理，位于命名空间 `Lau
rentSeries.Cauchy`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] {ℱ : Filter (LaurentSeries K)},   Cauchy
 ℱ → ∃ N, ∀ᶠ (f : LaurentSeries K) in ℱ, ∀ n < N, f.coeff n = 0
参数：LaurentSeries K；f : LaurentSeries K。
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
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `Filter.le_def`：le_def : f <= g ↔ forall x in g, x in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Valued.hasBasis_uniformity`：hasBasis_uniformity : (𝓤 R).HasBasis (fun _ 
=> True) fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ => { p : R × R
 | v.restrict (p…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.forall_mem_nonempty_iff_neBot`：forall_mem_nonempty_iff_neBot {f :
 Filter α} : (forall s : Set α, s in f -> s.Nonempty) ↔ NeBot f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.inter_mem_iff`：inter_mem_iff {s t : Set α} : s inter t in f ↔ s i
n f ∧ t in f
· 使用定理 `LaurentSeries.valuation_le_iff_coeff_lt_eq_zero`：valuation_le_iff_coeff_
lt_eq_zero {D : Int} {f : K⸨X⸩} : Valued.v f <= exp (-D : Int) ↔ forall n : Int,
 n < D -> f.coeff n = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Set.IsPWO.isWF`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.IsPW
O → s.IsWF
· 使用定理 `HahnSeries.isPWO_support'`：∀ {Γ : Type u_1} {R : Type u_2} [inst : Parti
alOrder Γ] [inst_1 : Zero R] (self : HahnSeries Γ R),   (Function.support self.c
oeff).IsPWO
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `LaurentSeries.eq_coeff_of_valuation_sub_lt`：eq_coeff_of_valuation_sub_lt
 {d n : Int} {f g : K⸨X⸩} (H : Valued.v (g - f) <= exp (-d)) : n < d -> g.coeff 
n = f.coeff n
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.sub_one_lt_of_le`：∀ {a b : ℤ}, a ≤ b → a - 1 < b
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `Function.notMem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {x : ι}, x ∉ Function.support f ↔ f x = 0
· 使用定理 `Set.IsWF.not_lt_min`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} {a
 : α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → ¬a < hs.min hn
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
For every Cauchy filter of Laurent series, there is some `N` such that the `n`-t
h coefficient
vanishes for all `n ≤ N` and almost all series in the filter. This is an auxilia
ry lemma used
to construct the limit of the Cauchy filter as a Laurent series, ensuring that t
he support of the
limit is `PWO`.
The result is true also for more general Hahn Series indexed over a partially or
dered group `Γ`
beyond the special case `Γ = ℤ`, that corresponds to Laurent Series: nevertheles
s the proof below
does not generalise, as it relies on the study of the `X`-adic valuation attache
d to the height-one
prime `X`, and this is peculiar to the one-variable setting. In the future we sh
ould prove this
result in full generality and deduce the case `Γ = ℤ` from that one.
-/
lemma Cauchy.exists_lb_eventual_support {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) :
    ∃ N, ∀ᶠ f : K⸨X⸩ in ℱ, ∀ n < N, f.coeff n = (0 : K) := by
  let entourage : Set (K⸨X⸩ × K⸨X⸩) := {P : K⸨X⸩ × K⸨X⸩ | Valued.v.restrict (P.snd - P.fst) < 1}
  let ζ : (MonoidWithZeroHom.ValueGroup₀ <| .ofClass (Valued.v (R := K⸨X⸩)))ˣ :=
    Units.mk0 1 (zero_ne_one.symm)
  obtain ⟨S, ⟨hS, ⟨T, ⟨hT, H⟩⟩⟩⟩ := mem_prod_iff.mp <| Filter.le_def.mp hℱ.2 entourage
    <| (Valued.hasBasis_uniformity K⸨X⸩ ℤᵐ⁰).mem_of_mem (i := ζ) (by tauto)
  obtain ⟨f, hf⟩ := forall_mem_nonempty_iff_neBot.mpr hℱ.1 (S ∩ T) (inter_mem_iff.mpr ⟨hS, hT⟩)
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ g : K⸨X⸩,
    Valued.v (g - f) ≤ 1 → ∀ n < N, g.coeff n = 0 := by
    by_cases hf : f = 0
    · refine ⟨0, fun x hg ↦ ?_⟩
      rw [hf, sub_zero] at hg
      exact (valuation_le_iff_coeff_lt_eq_zero K).mp hg
    · refine ⟨min (f.2.isWF.min (HahnSeries.support_nonempty_iff.mpr hf)) 0 - 1, fun _ hg n hn ↦ ?_⟩
      rw [eq_coeff_of_valuation_sub_lt K hg (d := 0)]
      · exact Function.notMem_support.mp fun h ↦
        f.2.isWF.not_lt_min (HahnSeries.support_nonempty_iff.mpr hf) h
        <| lt_trans hn <| Int.sub_one_lt_iff.mpr <| min_le_left _ _
      exact lt_of_lt_of_le hn <| le_of_lt (Int.sub_one_lt_of_le <| min_le_right _ _)
  use N
  apply mem_of_superset (inter_mem hS hT)
  intro g hg
  have h_prod : (f, g) ∈ S ×ˢ T := by simp [hf.1, hg.2]
  refine hN g (le_of_lt ?_)
  simpa [Valuation.restrict_def, ← Valuation.restrict_lt_one_iff] using! H h_prod

/-- The support of `Cauchy.coeff` has a lower bound. -/
/-
**LaurentSeries.Cauchy.exists_lb_support** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSerie
s.Cauchy`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] {ℱ : Filter (LaurentSeries K)} (hℱ : Cau
chy ℱ),   ∃ N, ∀ n < N, LaurentSeries.Cauchy.coeff hℱ n = 0
参数：LaurentSeries K；hℱ : Cauchy ℱ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `LaurentSeries.Cauchy.exists_lb_eventual_support`：∀ {K : Type u_2} [inst 
: Field K] {ℱ : Filter (LaurentSeries K)},   Cauchy ℱ → ∃ N, ∀ᶠ (f : LaurentSeri
es K) in ℱ, ∀ n < N, f.coeff n = 0
· 使用定理 `Ultrafilter.eq_of_le_pure`：eq_of_le_pure {X : Type _} {α : Filter X} (hα
 : α.NeBot) {x y : X} (hx : α <= pure x) (hy : α <= pure y) : x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Cauchy.map`：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α] 
[inst : UniformSpace β] {f : Filter α} {m : α → β},   Cauchy f → UniformContinuo
…
· 使用定理 `LaurentSeries.uniformContinuous_coeff`：uniformContinuous_coeff {uK : Uni
formSpace K} (d : Int) : UniformContinuous fun f : K⸨X⸩ => f.coeff d
· 使用定理 `LaurentSeries.Cauchy.coeff_tendsto`：∀ {K : Type u_2} [inst : Field K] {ℱ
 : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ) (D : ℤ),   Filter.Tendsto (fun f =>
 f.coeff D) ℱ (Filter.pr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f

--- 原说明 ---
The support of `Cauchy.coeff` has a lower bound.
-/
theorem Cauchy.exists_lb_support {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) :
    ∃ N, ∀ n, n < N → coeff hℱ n = 0 := by
  let _ : UniformSpace K := ⊥
  obtain ⟨N, hN⟩ := exists_lb_eventual_support hℱ
  refine ⟨N, fun n hn ↦ Ultrafilter.eq_of_le_pure (hℱ.map (uniformContinuous_coeff n)).1
      ((principal_singleton _).symm ▸ coeff_tendsto _ _) ?_⟩
  simp only [pure_zero, nonpos_iff]
  apply Filter.mem_of_superset hN (fun _ ha ↦ ha _ hn)

/-- The support of `Cauchy.coeff` is bounded below -/
/-
**LaurentSeries.Cauchy.coeff_support_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `Laurent
Series.Cauchy`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] {ℱ : Filter (LaurentSeries K)} (hℱ : Cau
chy ℱ),   BddBelow (Function.support (LaurentSeries.Cauchy.coeff hℱ))
参数：LaurentSeries K；hℱ : Cauchy ℱ；Function.support (LaurentSeries.Cauchy.coeff hℱ
)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `LaurentSeries.Cauchy.exists_lb_support`：∀ {K : Type u_2} [inst : Field K
] {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ),   ∃ N, ∀ n < N, LaurentSeries.
Cauchy.coeff hℱ n = 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a

--- 原说明 ---
The support of `Cauchy.coeff` is bounded below
-/
theorem Cauchy.coeff_support_bddBelow {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) :
    BddBelow (coeff hℱ).support := by
  refine ⟨(exists_lb_support hℱ).choose, fun d hd ↦ ?_⟩
  by_contra hNd
  exact hd ((exists_lb_support hℱ).choose_spec d (not_le.mp hNd))

/-- To any Cauchy filter ℱ of `K⸨X⸩`, we can attach a laurent series that is the limit
of the filter. Its `d`-th coefficient is defined as the limit of `Cauchy.coeff hℱ d`, which is
again Cauchy but valued in the discrete space `K`. That sufficiently negative coefficients vanish
follows from `Cauchy.coeff_support_bddBelow` -/
/-
**LaurentSeries.Cauchy.limit** 是 Mathlib 中的一个定义，位于命名空间 `LaurentSeries.Cauchy`。
形式化陈述：{K : Type u_2} → [inst : Field K] → {ℱ : Filter (LaurentSeries K)} → Cauch
y ℱ → LaurentSeries K
参数：LaurentSeries K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To any Cauchy filter ℱ of `K⸨X⸩`, we can attach a laurent series that is the lim
it
of the filter. Its `d`-th coefficient is defined as the limit of `Cauchy.coeff h
ℱ d`, which is
again Cauchy but valued in the discrete space `K`. That sufficiently negative co
efficients vanish
follows from `Cauchy.coeff_support_bddBelow`
-/
def Cauchy.limit {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) : K⸨X⸩ :=
  HahnSeries.mk (coeff hℱ) <| Set.IsWF.isPWO (coeff_support_bddBelow _).wellFoundedOn_lt

/-- The following lemma shows that for every `d` smaller than the minimum between the integers
produced in `Cauchy.exists_lb_eventual_support` and `Cauchy.exists_lb_support`, for almost all
series in `ℱ` the `d`th coefficient coincides with the `d`th coefficient of `Cauchy.coeff hℱ`. -/
/-
**LaurentSeries.Cauchy.exists_lb_coeff_ne** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeri
es.Cauchy`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] {ℱ : Filter (LaurentSeries K)} (hℱ : Cau
chy ℱ),   ∃ N, ∀ᶠ (f : LaurentSeries K) in ℱ, ∀ d < N, LaurentSeries.Cauchy.coef
f hℱ d = f.coeff d
参数：LaurentSeries K；hℱ : Cauchy ℱ；f : LaurentSeries K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `LaurentSeries.Cauchy.exists_lb_eventual_support`：∀ {K : Type u_2} [inst 
: Field K] {ℱ : Filter (LaurentSeries K)},   Cauchy ℱ → ∃ N, ∀ᶠ (f : LaurentSeri
es K) in ℱ, ∀ n < N, f.coeff n = 0
· 使用定理 `LaurentSeries.Cauchy.exists_lb_support`：∀ {K : Type u_2} [inst : Field K
] {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ),   ∃ N, ∀ n < N, LaurentSeries.
Cauchy.coeff hℱ n = 0
· 使用定理 `Filter.sets_of_superset`：∀ {α : Type u_1} (self : Filter α) {x y : Set α
}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b

--- 原说明 ---
The following lemma shows that for every `d` smaller than the minimum between th
e integers
produced in `Cauchy.exists_lb_eventual_support` and `Cauchy.exists_lb_support`, 
for almost all
series in `ℱ` the `d`th coefficient coincides with the `d`th coefficient of `Cau
chy.coeff hℱ`.
-/
theorem Cauchy.exists_lb_coeff_ne {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) :
    ∃ N, ∀ᶠ f : K⸨X⸩ in ℱ, ∀ d < N, coeff hℱ d = f.coeff d := by
  obtain ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩ := exists_lb_eventual_support hℱ, exists_lb_support hℱ
  refine ⟨min N₁ N₂, ℱ.3 hN₁ fun _ hf d hd ↦ ?_⟩
  rw [hf d (lt_of_lt_of_le hd (min_le_left _ _)), hN₂ d (lt_of_lt_of_le hd (min_le_right _ _))]

/-- Given a Cauchy filter `ℱ` in the Laurent Series and a bound `D`, for almost all series in the
filter the coefficients below `D` coincide with `Cauchy.coeff hℱ`. -/
/-
**LaurentSeries.Cauchy.coeff_eventually_equal** 是 Mathlib 中的一个定理，位于命名空间 `Laurent
Series.Cauchy`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] {ℱ : Filter (LaurentSeries K)} (hℱ : Cau
chy ℱ) {D : ℤ},   ∀ᶠ (f : LaurentSeries K) in ℱ, ∀ d < D, LaurentSeries.Cauchy.c
oeff hℱ d = f.coeff d
参数：LaurentSeries K；hℱ : Cauchy ℱ；f : LaurentSeries K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LaurentSeries.Cauchy.exists_lb_coeff_ne`：∀ {K : Type u_2} [inst : Field 
K] {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ),   ∃ N, ∀ᶠ (f : LaurentSeries 
K) in ℱ, ∀ d < N, LaurentSeri…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Filter.eventually_iff`：eventually_iff {f : Filter α} {P : α -> Prop} : (
forallᶠ x in f, P x) ↔ { x | P x } in f
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用引理 `Set.finite_Icc`：finite_Icc : (Icc a b).Finite
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `LaurentSeries.Cauchy.coeff_tendsto`：∀ {K : Type u_2} [inst : Field K] {ℱ
 : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ) (D : ℤ),   Filter.Tendsto (fun f =>
 f.coeff D) ℱ (Filter.pr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.sets_of_superset`：∀ {α : Type u_1} (self : Filter α) {x y : Set α
}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
Given a Cauchy filter `ℱ` in the Laurent Series and a bound `D`, for almost all 
series in the
filter the coefficients below `D` coincide with `Cauchy.coeff hℱ`.
-/
theorem Cauchy.coeff_eventually_equal {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ) {D : ℤ} :
    ∀ᶠ f : K⸨X⸩ in ℱ, ∀ d, d < D → coeff hℱ d = f.coeff d := by
  -- `φ` sends `d` to the set of Laurent Series having `d`th coefficient equal to `ℱ.coeff`.
  let φ : ℤ → Set K⸨X⸩ := fun d ↦ {f | coeff hℱ d = f.coeff d}
  have intersec₁ :
    (⋂ n ∈ Set.Iio D, φ n) ⊆ {x : K⸨X⸩ | ∀ d : ℤ, d < D → coeff hℱ d = x.coeff d} := by
    intro _ hf
    simpa only [Set.mem_iInter] using! hf
  -- The goal is now to show that the intersection of all `φ d` (for `d < D`) is in `ℱ`.
  let ℓ := (exists_lb_coeff_ne hℱ).choose
  let N := max ℓ D
  have intersec₂ : ⋂ n ∈ Set.Iio D, φ n ⊇ (⋂ n ∈ Set.Iio ℓ, φ n) ∩ (⋂ n ∈ Set.Icc ℓ N, φ n) := by
    simp only [Set.mem_Iio, Set.mem_Icc, Set.subset_iInter_iff]
    intro i hi x hx
    simp only [Set.mem_inter_iff, Set.mem_iInter, and_imp] at hx
    by_cases! H : i < ℓ
    exacts [hx.1 _ H, hx.2 _ H <| le_of_lt <| lt_max_of_lt_right hi]
  suffices (⋂ n ∈ Set.Iio ℓ, φ n) ∩ (⋂ n ∈ Set.Icc ℓ N, φ n) ∈ ℱ by
    exact ℱ.sets_of_superset this <| intersec₂.trans intersec₁
  /- To show that the intersection we have in sight is in `ℱ`, we use that it contains a double
  intersection (an infinite and a finite one): by general properties of filters, we are reduced
  to show that both terms are in `ℱ`, which is easy in light of their definition. -/
  · simp only [Set.mem_Iio, inter_mem_iff]
    constructor
    · have := (exists_lb_coeff_ne hℱ).choose_spec
      rw [Filter.eventually_iff] at this
      convert! this
      ext
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]; rfl
    · rw [biInter_mem (Set.finite_Icc ℓ N)]
      intro i _
      apply (coeff_tendsto hℱ _).eventually
      simp

open scoped Topology
open MonoidWithZeroHom.ValueGroup₀

/-- The main result showing that the Cauchy filter tends to the `Cauchy.limit` -/
/-
**LaurentSeries.Cauchy.eventually_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSer
ies.Cauchy`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] {ℱ : Filter (LaurentSeries K)} (hℱ : Cau
chy ℱ) {U : Set (LaurentSeries K)},   U ∈ nhds (LaurentSeries.Cauchy.limit hℱ) →
 ∀ᶠ (f : LaurentSeries K) in ℱ, f ∈ U
参数：LaurentSeries K；hℱ : Cauchy ℱ；LaurentSeries K；LaurentSeries.Cauchy.limit hℱ；f
 : LaurentSeries K。
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Valued.mem_nhds`：mem_nhds {s : Set R} {x : R} : s in 𝓝 x ↔ exists γ : (M
onoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ, { y | (v.restrict (y - x) ) < γ.
1 } s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithZero.lt_log_iff_exp_lt`：lt_log_iff_exp_lt (hx : x != 0) : a < log x 
↔ exp a < x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LaurentSeries.Cauchy.coeff_eventually_equal`：∀ {K : Type u_2} [inst : Fi
eld K] {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ) {D : ℤ},   ∀ᶠ (f : Laurent
Series K) in ℱ, ∀ d < D, LaurentS…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LaurentSeries.valuation_le_iff_coeff_lt_eq_zero`：valuation_le_iff_coeff_
lt_eq_zero {D : Int} {f : K⸨X⸩} : Valued.v f <= exp (-D : Int) ↔ forall n : Int,
 n < D -> f.coeff n = 0
· 使用定理 `HahnSeries.coeff_sub`：coeff_sub {x y : R⟦Γ⟧} {a : Γ} : (x - y).coeff a =
 x.coeff a - y.coeff a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The main result showing that the Cauchy filter tends to the `Cauchy.limit`
-/
theorem Cauchy.eventually_mem_nhds {ℱ : Filter K⸨X⸩} (hℱ : Cauchy ℱ)
    {U : Set K⸨X⸩} (hU : U ∈ 𝓝 (Cauchy.limit hℱ)) : ∀ᶠ f in ℱ, f ∈ U := by
  obtain ⟨γ, hU₁⟩ := Valued.mem_nhds.mp hU
  suffices ∀ᶠ f in ℱ, f ∈ {y : K⸨X⸩ | Valued.v (y - limit hℱ) < embedding γ.1} by
    simp_rw [← Valued.v.restrict_lt_iff_lt_embedding] at this
    apply this.mono fun _ hf ↦ hU₁ hf
  set D := -(log (embedding γ.1) - 1) with hD₀
  have hD : exp (-D) < embedding γ.1 := by
    rw [← lt_log_iff_exp_lt (by simp), hD₀]
    simp
  apply coeff_eventually_equal (D := D) hℱ |>.mono
  intro _ hf
  apply lt_of_le_of_lt (valuation_le_iff_coeff_lt_eq_zero K |>.mpr _) hD
  intro n hn
  rw [HahnSeries.coeff_sub, sub_eq_zero, eq_comm]
  exact hf _ hn

/-- Laurent Series with coefficients in a field are complete w.r.t. the `X`-adic valuation -/
/-
**LaurentSeries.instLaurentSeriesComplete** 是 Mathlib 中的一个实例，位于命名空间 `LaurentSeri
es`。
形式化陈述：instLaurentSeriesComplete : CompleteSpace K⸨X⸩
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `LaurentSeries.Cauchy.eventually_mem_nhds`：∀ {K : Type u_2} [inst : Field
 K] {ℱ : Filter (LaurentSeries K)} (hℱ : Cauchy ℱ) {U : Set (LaurentSeries K)}, 
  U ∈ nhds (LaurentSeries.Cauc…

--- 原说明 ---
Laurent Series with coefficients in a field are complete w.r.t. the `X`-adic val
uation
-/
instance instLaurentSeriesComplete : CompleteSpace K⸨X⸩ :=
  ⟨fun hℱ ↦ ⟨Cauchy.limit hℱ, fun _ hS ↦ Cauchy.eventually_mem_nhds hℱ hS⟩⟩

end Complete

section Dense

open scoped Multiplicative

open LaurentSeries PowerSeries IsDedekindDomain.HeightOneSpectrum WithZero RatFunc

/-
**LaurentSeries.exists_Polynomial_intValuation_lt** 是 Mathlib 中的一个定理，位于命名空间 `Lau
rentSeries`。
形式化陈述：exists_Polynomial_intValuation_lt (F : K⟦X⟧) (η : Intᵐ⁰ˣ) : exists P : K[X
], (PowerSeries.idealX K).intValuation (F - P) < η
参数：F : K⟦X⟧；η : Intᵐ⁰ˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `PowerSeries.instIsDomain`：∀ {R : Type u_1} [inst : Ring R] [IsDomain R],
 IsDomain (PowerSeries R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `PowerSeries.instIsDiscreteValuationRing`：∀ {k : Type u_2} [inst : Field 
k], IsDiscreteValuationRing (PowerSeries k)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_one`：intValuation_le_
one (x : R) : v.intValuation x <= 1
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Int.exists_eq_neg_ofNat`：∀ {a : ℤ}, a ≤ 0 → ∃ n, a = -↑n
· 使用定理 `toAdd_one`：toAdd_one [Zero α] : (1 : Multiplicative α).toAdd = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiplicative.toAdd_le`：toAdd_le {a b : Multiplicative α} : a.toAdd <= 
b.toAdd ↔ a <= b
· 使用定理 `WithZero.coe_le_coe`：∀ {α : Type u_1} [inst : LE α] {a b : α}, ↑a ≤ ↑b ↔
 a ≤ b
· 使用定理 `WithZero.coe_unzero`：∀ {α : Type u} {x : WithZero α} (hx : x ≠ 0), ↑(Wit
hZero.unzero hx) = x
· 使用定理 `WithZero.coe_one`：∀ {α : Type u_1} [inst : One α], ↑1 = 1
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `Units.val_le_val`：val_le_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α
) <= b ↔ a <= b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero`：intValuation_le_iff_
coeff_lt_eq_zero {d : Nat} (f : K⟦X⟧) : Valued.v (f : K⸨X⸩) <= exp (-d : Int) ↔ 
forall n : Nat, n < d -> coeff n f = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
（共 62 条，此处仅展示前 30 条）
-/
theorem exists_Polynomial_intValuation_lt (F : K⟦X⟧) (η : ℤᵐ⁰ˣ) :
    ∃ P : K[X], (PowerSeries.idealX K).intValuation (F - P) < η := by
  by_cases! h_neg : 1 < η
  · use 0
    simpa using (intValuation_le_one (PowerSeries.idealX K) F).trans_lt h_neg
  · rw [← Units.val_le_val, Units.val_one, ← WithZero.coe_one, ← coe_unzero η.ne_zero,
      coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one] at h_neg
    obtain ⟨d, hd⟩ := Int.exists_eq_neg_ofNat h_neg
    use F.trunc (d + 1)
    have : Valued.v ((ofPowerSeries ℤ K) (F - (trunc (d + 1) F))) ≤
      (Multiplicative.ofAdd (-(d + 1 : ℤ))) := by
      apply (intValuation_le_iff_coeff_lt_eq_zero K _).mpr
      simpa only [map_sub, sub_eq_zero, Polynomial.coeff_coe, coeff_trunc] using
        fun _ h ↦ (if_pos h).symm
    rw [neg_add, ofAdd_add, ← hd, ofAdd_toAdd, WithZero.coe_mul, coe_unzero,
      ← coe_algebraMap] at this
    rw [← valuation_of_algebraMap (K := K⸨X⸩) (PowerSeries.idealX K) (F - F.trunc (d + 1))]
    apply lt_of_le_of_lt this
    rw [← mul_one (η : ℤᵐ⁰), mul_assoc, one_mul]
    gcongr
    · exact zero_lt_iff.2 η.ne_zero
    rw [← WithZero.coe_one, coe_lt_coe, ofAdd_neg, Right.inv_lt_one_iff, ← ofAdd_zero,
      Multiplicative.ofAdd_lt]
    exact Int.zero_lt_one

/-- For every Laurent series `f` and every `γ : ℤᵐ⁰` one can find a rational function `Q` such
that the `X`-adic valuation `v` satisfies `v (f - Q) < γ`. -/
/-
**LaurentSeries.exists_ratFunc_val_lt** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：exists_ratFunc_val_lt (f : K⸨X⸩) (γ : Intᵐ⁰ˣ) : exists Q : K⟮X⟯, Valued.v 
(f - Q) < γ
参数：f : K⸨X⸩；γ : Intᵐ⁰ˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)
· 使用定理 `WithZero.coe_ne_zero`：∀ {α : Type u} {a : α}, ↑a ≠ 0
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `PowerSeries.instIsDomain`：∀ {R : Type u_1} [inst : Ring R] [IsDomain R],
 IsDomain (PowerSeries R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `PowerSeries.instIsDiscreteValuationRing`：∀ {k : Type u_2} [inst : Field 
k], IsDiscreteValuationRing (PowerSeries k)
· 使用定理 `LaurentSeries.exists_Polynomial_intValuation_lt`：exists_Polynomial_intVa
luation_lt (F : K⟦X⟧) (η : Intᵐ⁰ˣ) : exists P : K[X], (PowerSeries.idealX K).int
Valuation (F - P) < η
· 使用定理 `LaurentSeries.ofPowerSeries_powerSeriesPart`：ofPowerSeries_powerSeriesPa
rt (x : R⸨X⸩) : ofPowerSeries Int R x.powerSeriesPart = single (-x.order) 1 * x
· 使用定理 `Int.exists_eq_neg_ofNat`：∀ {a : ℤ}, a ≤ 0 → ∃ n, a = -↑n
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `algebraMap.coe_one`：coe_one : (↑(1 : R) : A) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_mul_eq_iff_eq_mul₀`：inv_mul_eq_iff_eq_mul₀ (ha : a != 0) : a⁻¹ * b =
 c ↔ b = a * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `HahnSeries.ofPowerSeries_X`：ofPowerSeries_X : ofPowerSeries Γ R PowerSer
ies.X = single 1 1
· 使用定理 `HahnSeries.single_pow`：single_pow (a : Γ) (n : Nat) (r : R) : single a r
 ^ n = single (n • a) (r ^ n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
For every Laurent series `f` and every `γ : ℤᵐ⁰` one can find a rational functio
n `Q` such
that the `X`-adic valuation `v` satisfies `v (f - Q) < γ`.
-/
theorem exists_ratFunc_val_lt (f : K⸨X⸩) (γ : ℤᵐ⁰ˣ) :
    ∃ Q : K⟮X⟯, Valued.v (f - Q) < γ := by
  set F := f.powerSeriesPart with hF
  by_cases! ord_nonpos : f.order < 0
  · set η : ℤᵐ⁰ˣ := Units.mk0 (exp f.order) coe_ne_zero
      with hη
    obtain ⟨P, hP⟩ := exists_Polynomial_intValuation_lt F (η * γ)
    use RatFunc.X ^ f.order * (P : K⟮X⟯)
    have F_mul := f.ofPowerSeries_powerSeriesPart
    obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (le_of_lt ord_nonpos)
    rw [← hF, hs, neg_neg, ← ofPowerSeries_X_pow s, ← inv_mul_eq_iff_eq_mul₀] at F_mul
    · have : (algebraMap K⟮X⟯ K⸨X⸩) 1 = 1 := by exact algebraMap.coe_one
      rw [hs, ← F_mul, PowerSeries.coe_pow, PowerSeries.coe_X, map_mul, zpow_neg,
        zpow_natCast, inv_eq_one_div (RatFunc.X ^ s), map_div₀, map_pow,
        RatFunc.coe_X]
      simp only [map_one]
      rw [← inv_eq_one_div, ← mul_sub, map_mul, map_inv₀,
        ← PowerSeries.coe_X, valuation_X_pow, ← hs, ← RatFunc.coe_coe, ← PowerSeries.coe_sub,
        ← coe_algebraMap, adicValued_apply, valuation_of_algebraMap,
        ← Units.val_mk0 (a := exp f.order) exp_ne_zero, ← hη]
      apply inv_mul_lt_of_lt_mul₀
      rwa [← Units.val_mul]
    · simp
  · obtain ⟨s, hs⟩ := Int.exists_eq_neg_ofNat (Int.neg_nonpos_of_nonneg ord_nonpos)
    obtain ⟨P, hP⟩ := exists_Polynomial_intValuation_lt (PowerSeries.X ^ s * F) γ
    use P
    rw [← X_order_mul_powerSeriesPart (neg_inj.1 hs).symm, ← RatFunc.coe_coe,
      ← PowerSeries.coe_sub, ← coe_algebraMap, adicValued_apply, valuation_of_algebraMap]
    exact hP

open MonoidWithZeroHom.ValueGroup₀
/-
**LaurentSeries.coe_range_dense** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：coe_range_dense : DenseRange ((↑) : K⟮X⟯ -> K⸨X⸩)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `denseRange_iff_closure_range`：denseRange_iff_closure_range : DenseRange 
f ↔ closure (range f) = univ
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `uniformity_eq_comap_neg_add_nhds_zero_swapped`：∀ (Gₗ : Type u_2) [inst :
 UniformSpace Gₗ] [inst_1 : AddGroup Gₗ] [IsLeftUniformAddGroup Gₗ],   uniformit
y Gₗ = Filter.comap (fun x => -x.2 …
· 使用定理 `IsUniformAddGroup.isLeftUniformAddGroup`：∀ (α : Type u_1) [inst : Unifor
mSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsLeftUniformAddGroup α
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Valued.mem_nhds_zero`：mem_nhds_zero {s : Set R} : s in 𝓝 (0 : R) ↔ exist
s γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ, { x | v.restrict x < γ.1
 } subsete…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `LaurentSeries.exists_ratFunc_val_lt`：exists_ratFunc_val_lt (f : K⸨X⸩) (γ
 : Intᵐ⁰ˣ) : exists Q : K⟮X⟯, Valued.v (f - Q) < γ
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem coe_range_dense : DenseRange ((↑) : K⟮X⟯ → K⸨X⸩) := by
  rw [denseRange_iff_closure_range]
  ext f
  simp only [UniformSpace.mem_closure_iff_symm_ball, Set.mem_univ, iff_true, Set.Nonempty,
    Set.mem_inter_iff, Set.mem_range, exists_exists_eq_and]
  intro V hV h_symm
  rw [uniformity_eq_comap_neg_add_nhds_zero_swapped] at hV
  obtain ⟨T, hT₀, hT₁⟩ := hV
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hT₀
  have := (embedding γ.1)
  obtain ⟨P, hP⟩ := exists_ratFunc_val_lt f
    <| γ.map (embedding (f := .ofClass (valued K).v))
  use P
  apply hT₁
  apply hγ
  simpa only [Units.coe_map, MonoidHom.coe_mk, ZeroHom.toFun_eq_coe, OneHom.coe_mk, add_comm,
    MonoidWithZeroHom.toZeroHom_coe, ← sub_eq_add_neg, Set.mem_ofPred_eq,
    Valuation.restrict_lt_iff_lt_embedding]

end Dense

section Comparison

open RatFunc AbstractCompletion IsDedekindDomain.HeightOneSpectrum WithZero

/-
**LaurentSeries.exists_ratFunc_eq_v** 是 Mathlib 中的一个引理，位于命名空间 `LaurentSeries`。
形式化陈述：exists_ratFunc_eq_v (x : K⸨X⸩) : exists f : K⟮X⟯, Valued.v f = Valued.v x
参数：x : K⸨X⸩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
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
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `RatFunc.v_def`：v_def {x : K⟮X⟯} : Valued.v x = (idealX K).valuation _ x
· 使用定理 `Polynomial.valuation_X_eq_neg_one`：valuation_X_eq_neg_one : (idealX K).v
aluation K⟮X⟯ RatFunc.X = exp (-1 : Int)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.exp_zsmul`：∀ {G : Type u_5} [inst : AddGroup G] (n : ℤ) (a : G)
, WithZero.exp (n • a) = WithZero.exp a ^ n
· 使用定理 `WithZero.exp_neg`：∀ {G : Type u_5} [inst : AddGroup G] (a : G), WithZero
.exp (-a) = (WithZero.exp a)⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `WithZero.exp_log`：∀ {M : Type u_4} [inst : AddMonoid M] {x : WithZero (M
ultiplicative M)}, x ≠ 0 → WithZero.exp x.log = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 31 条，此处仅展示前 30 条）
-/
lemma exists_ratFunc_eq_v (x : K⸨X⸩) : ∃ f : K⟮X⟯, Valued.v f = Valued.v x := by
  by_cases hx : Valued.v x = 0
  · use 0
    simp [hx]
  use RatFunc.X ^ (-log (Valued.v x))
  rw [zpow_neg, map_inv₀, map_zpow₀, v_def, valuation_X_eq_neg_one, ← exp_zsmul, ← exp_neg]
  simp [exp_log, hx]

open MonoidWithZeroHom.ValueGroup₀

set_option backward.isDefEq.respectTransparency.types false in
/-
**LaurentSeries.inducing_coe** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：inducing_coe : IsUniformInducing ((↑) : K⟮X⟯ -> K⸨X⸩)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUniformInducing_iff`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpac
e α] [inst_1 : UniformSpace β] (f : α → β),   IsUniformInducing f ↔ Filter.comap
 (fun x => …
· 使用定理 `Filter.comap.eq_1`：∀ {α : Type u_1} {β : Type u_2} (m : α → β) (f : Filt
er β),   Filter.comap m f = { sets := {s | ∃ t ∈ f, m ⁻¹' t ⊆ s}, univ_sets := ⋯
, sets_…
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `uniformity_eq_comap_nhds_zero`：∀ (Gᵣ : Type u_3) [inst : UniformSpace Gᵣ
] [inst_1 : AddGroup Gᵣ] [IsRightUniformAddGroup Gᵣ],   uniformity Gᵣ = Filter.c
omap (fun x => x.2 …
· 使用定理 `IsUniformAddGroup.isRightUniformAddGroup`：∀ (α : Type u_1) [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsRightUniformAddGroup α
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `Filter.mk.congr_simp`：∀ {α : Type u_1} (sets sets_1 : Set (Set α)) (e_se
ts : sets = sets_1) (univ_sets : Set.univ ∈ sets)   (sets_of_superset : ∀ {x y :
 Set α}, x…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Valued.mem_nhds`：mem_nhds {s : Set R} {x : R} : s in 𝓝 x ↔ exists γ : (M
onoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ, { y | (v.restrict (y - x) ) < γ.
1 } s…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `RatFunc.valuation_surjective`：valuation_surjective : Function.Surjective
 (Valued.v (R
· 使用引理 `Valuation.restrict_def`：restrict_def (x : R) : v.restrict x = restrict₀ 
(.ofClass v) x
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff`：restrict₀_eq_zero_i
ff {a : A} : restrict₀ f a = 0 ↔ f a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
（共 60 条，此处仅展示前 30 条）
-/
theorem inducing_coe : IsUniformInducing ((↑) : K⟮X⟯ → K⸨X⸩) := by
  rw [isUniformInducing_iff, Filter.comap]
  ext S
  simp only [Filter.mem_mk, Set.mem_ofPred_eq, uniformity_eq_comap_nhds_zero,
    Filter.mem_comap]
  constructor
  · rintro ⟨T, ⟨⟨R, ⟨hR, pre_R⟩⟩, pre_T⟩⟩
    obtain ⟨d, hd⟩ := Valued.mem_nhds.mp hR
    use {P : K⟮X⟯ | Valued.v P < embedding d.1}
    simp only [Valued.mem_nhds, sub_zero]
    refine ⟨?_, subset_trans (fun _ _ ↦ pre_R ?_) pre_T⟩
    · obtain ⟨x, hx⟩ := RatFunc.valuation_surjective K (embedding d.1)
      use Units.mk0 (Valued.v.restrict x) (by
        rw [Valuation.restrict_def, ne_eq, restrict₀_eq_zero_iff]; simp [hx])
      simp [v_def, Valuation.restrict_lt_iff, ← hx]
    apply hd
    simp only [sub_zero, Set.mem_ofPred_eq]
    rw [← map_sub, Valuation.restrict_lt_iff_lt_embedding]
    simp only [valuation_def]
    rwa [← valuation_eq_LaurentSeries_valuation]
  · rintro ⟨_, ⟨hT, pre_T⟩⟩
    obtain ⟨d, hd⟩ := Valued.mem_nhds.mp hT
    set X := {f : K⸨X⸩ | Valued.v f < embedding d.1} with X_def
    refine ⟨(fun x : K⸨X⸩ × K⸨X⸩ ↦ x.snd - x.fst) ⁻¹' X, ⟨X, ?_⟩, ?_⟩
    · refine ⟨?_, Set.Subset.refl _⟩
      · simp only [Valued.mem_nhds, sub_zero, Valuation.restrict_lt_iff_lt_embedding]
        obtain ⟨x, hx⟩ := restrict₀_surjective _ d.1
        use Units.mk0 (Valued.v.restrict (x : K⸨X⸩)) (by
          simp only [ne_eq, map_eq_zero]
          intro h
          simp only [h, map_zero] at hx
          exact Units.ne_zero _ hx.symm)
        simp only [Units.val_mk0, ← Valuation.restrict_lt_iff_lt_embedding,
          X_def, Set.ofPred_subset_ofPred, Valuation.restrict_lt_iff]
        rw [← hx, embedding_restrict₀]
        simp [v_def, valuation_coe_ratFunc]
    · refine subset_trans (fun _ _ ↦ ?_) pre_T
      apply hd
      rw [Set.mem_ofPred_eq, sub_zero, Valuation.restrict_lt_iff_lt_embedding, v_def,
        valuation_eq_LaurentSeries_valuation, map_sub]
      assumption
/-
**LaurentSeries.uniformContinuous_withVal_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Laure
ntSeries`。
形式化陈述：uniformContinuous_withVal_equiv : UniformContinuous (WithVal.equiv (polyno
mialValuationX K))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.uniformContinuous_equiv`：∀ {R : Type u_4} {Γ₀ : Type u
_5} {Γ₀' : Type u_6} [inst : Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀
]   [inst_2 : LinearOrderedComm…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Valuation.IsEquiv.refl`：refl : v.IsEquiv v
-/
theorem uniformContinuous_withVal_equiv :
    UniformContinuous (WithVal.equiv (polynomialValuationX K)) :=
  (Valuation.IsEquiv.refl).uniformContinuous_equiv rfl
/-
**LaurentSeries.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：continuous_coe : Continuous ((↑) : K⟮X⟯ -> K⸨X⸩)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isUniformInducing_iff'`：isUniformInducing_iff' {f : α -> β} : IsUniformI
nducing f ↔ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) <= 𝓤 α
· 使用定理 `LaurentSeries.inducing_coe`：inducing_coe : IsUniformInducing ((↑) : K⟮X⟯
 -> K⸨X⸩)
-/
theorem continuous_coe : Continuous ((↑) : K⟮X⟯ → K⸨X⸩) :=
  (isUniformInducing_iff'.1 (inducing_coe)).1.continuous

variable (K) in
/-- An abbreviation for the `X`-adic completion of `K⟮X⟯` -/
/-
**LaurentSeries.RatFuncAdicCompl** 是 Mathlib 中的一个缩写定义，位于命名空间 `LaurentSeries`。
形式化陈述：RatFuncAdicCompl
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for the `X`-adic completion of `K⟮X⟯`
-/
abbrev RatFuncAdicCompl := adicCompletion K⟮X⟯ (idealX K)

/-- The `X`-adic completion as an abstract completion of `K⟮X⟯` -/
/-
**LaurentSeries.ratfuncAdicComplPkg** 是 Mathlib 中的一个缩写定义，位于命名空间 `LaurentSeries`。
形式化陈述：ratfuncAdicComplPkg : AbstractCompletion (WithVal (polynomialValuationX K)
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `X`-adic completion as an abstract completion of `K⟮X⟯`
-/
abbrev ratfuncAdicComplPkg : AbstractCompletion (WithVal (polynomialValuationX K)) :=
  UniformSpace.Completion.cPkg
/-
**LaurentSeries.** 是 Mathlib 中的一个实例，位于命名空间 `LaurentSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Field (ratfuncAdicComplPkg (K := K).space) :=
  inferInstanceAs (Field ((polynomialValuationX K).Completion))
/-
**LaurentSeries.** 是 Mathlib 中的一个实例，位于命名空间 `LaurentSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Valued (ratfuncAdicComplPkg (K := K).space) (WithZero (Multiplicative ℤ)) :=
  inferInstanceAs (Valued ((polynomialValuationX K).Completion) (WithZero (Multiplicative ℤ)))

variable (K)
/-- Having established that the `K⸨X⸩` is complete and contains `K⟮X⟯` as a dense
subspace, it gives rise to an abstract completion of `K⟮X⟯`. -/
/-
**LaurentSeries.LaurentSeriesPkg** 是 Mathlib 中的一个定义，位于命名空间 `LaurentSeries`。
形式化陈述：LaurentSeriesPkg : AbstractCompletion (WithVal (polynomialValuationX K)) w
here space
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)

--- 原说明 ---
Having established that the `K⸨X⸩` is complete and contains `K⟮X⟯` as a dense
subspace, it gives rise to an abstract completion of `K⟮X⟯`.
-/
noncomputable def LaurentSeriesPkg :
    AbstractCompletion (WithVal (polynomialValuationX K)) where
  space := K⸨X⸩
  coe := (↑) ∘ WithVal.equiv _
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing :=
    inducing_coe.comp (WithVal.uniformEquiv rfl Valuation.IsEquiv.refl).isUniformInducing
  dense := .comp coe_range_dense (WithVal.equiv _).surjective.denseRange continuous_coe
/-
**LaurentSeries.continuous_coe'** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：continuous_coe' : Continuous (((↑) : K⟮X⟯ -> K⸨X⸩) ∘ WithVal.equiv (polyno
mialValuationX K))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)
· 使用定理 `LaurentSeries.continuous_coe`：continuous_coe : Continuous ((↑) : K⟮X⟯ ->
 K⸨X⸩)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `LaurentSeries.uniformContinuous_withVal_equiv`：uniformContinuous_withVal
_equiv : UniformContinuous (WithVal.equiv (polynomialValuationX K))
-/
theorem continuous_coe' :
    Continuous (((↑) : K⟮X⟯ → K⸨X⸩) ∘ WithVal.equiv (polynomialValuationX K)) :=
  continuous_coe.comp uniformContinuous_withVal_equiv.continuous
/-
**LaurentSeries.** 是 Mathlib 中的一个实例，位于命名空间 `LaurentSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (LaurentSeriesPkg K).space :=
  (LaurentSeriesPkg K).uniformStruct.toTopologicalSpace

@[simp]
/-
**LaurentSeries.LaurentSeries_coe** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：LaurentSeries_coe (x : K⟮X⟯) : (LaurentSeriesPkg K).coe (WithVal.toVal _ x
) = (x : K⸨X⸩)
参数：x : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem LaurentSeries_coe (x : K⟮X⟯) :
    (LaurentSeriesPkg K).coe (WithVal.toVal _ x) = (x : K⸨X⸩) := by
  rfl

/-- Reinterpret the extension of `coe : WithVal ((idealX K).valuation _) → K⸨X⸩` as a ring
homomorphism -/
/-
**LaurentSeries.extensionAsRingHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `LaurentSeries`。
形式化陈述：extensionAsRingHom
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)

--- 原说明 ---
Reinterpret the extension of `coe : WithVal ((idealX K).valuation _) → K⸨X⸩` as 
a ring
homomorphism
-/
abbrev extensionAsRingHom :=
  UniformSpace.Completion.extensionHom <|
    (algebraMap K⟮X⟯ K⸨X⸩).comp (WithVal.equiv (polynomialValuationX K)).toRingHom

/-! The two instances below make `comparePkg` and `comparePkg_eq_extension` slightly faster. -/
/-
**LaurentSeries.** 是 Mathlib 中的一个实例，位于命名空间 `LaurentSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The two instances below make `comparePkg` and `comparePkg_eq_extension` slightly
 faster.
-/
instance : UniformSpace (RatFuncAdicCompl K) := inferInstance
/-
**LaurentSeries.** 是 Mathlib 中的一个实例，位于命名空间 `LaurentSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : UniformSpace K⸨X⸩ := inferInstance

/-- The uniform space isomorphism between two abstract completions of `ratfunc K` -/
/-
**LaurentSeries.comparePkg** 是 Mathlib 中的一个缩写定义，位于命名空间 `LaurentSeries`。
形式化陈述：comparePkg : RatFuncAdicCompl K ≃ᵤ K⸨X⸩
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniform space isomorphism between two abstract completions of `ratfunc K`
-/
abbrev comparePkg : RatFuncAdicCompl K ≃ᵤ K⸨X⸩ :=
  (adicCompletion.uniformEquiv _ _).trans <| compareEquiv ratfuncAdicComplPkg (LaurentSeriesPkg K)
/-
**LaurentSeries.comparePkg_eq_extension** 是 Mathlib 中的一个引理，位于命名空间 `LaurentSeries
`。
形式化陈述：comparePkg_eq_extension (x : RatFuncAdicCompl K) : (comparePkg K) x = (ext
ensionAsRingHom K (continuous_coe' _)) (adicCompletion.toCompletion x)
参数：x : RatFuncAdicCompl K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comparePkg_eq_extension (x : RatFuncAdicCompl K) :
    (comparePkg K) x =
      (extensionAsRingHom K (continuous_coe' _)) (adicCompletion.toCompletion x) := rfl

/-- The ring equivalence between `RatFuncAdicCompl K` and `K⸨X⸩`. -/
/-
**LaurentSeries.ratfuncAdicComplRingEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `LaurentSe
ries`。
形式化陈述：ratfuncAdicComplRingEquiv : RatFuncAdicCompl K ≃+* K⸨X⸩
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring equivalence between `RatFuncAdicCompl K` and `K⸨X⸩`.
-/
abbrev ratfuncAdicComplRingEquiv : RatFuncAdicCompl K ≃+* K⸨X⸩ :=
  { comparePkg K with
    map_mul' x y :=
      (comparePkg_eq_extension K (x * y)).trans <|
        (map_mul _ x.toCompletion y.toCompletion).trans <|
        (congrArg₂ (· * ·) (comparePkg_eq_extension K x) (comparePkg_eq_extension K y)).symm
    map_add' x y :=
      (comparePkg_eq_extension K (x + y)).trans <|
        (map_add _ x.toCompletion y.toCompletion).trans <|
        (congrArg₂ (· + ·) (comparePkg_eq_extension K x) (comparePkg_eq_extension K y)).symm }

/-- The uniform space equivalence between two abstract completions of `ratfunc K` as a ring
equivalence: it goes from `K⸨X⸩` to `RatFuncAdicCompl K` -/
/-
**LaurentSeries.LaurentSeriesRingEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `LaurentSerie
s`。
形式化陈述：LaurentSeriesRingEquiv : K⸨X⸩ ≃+* RatFuncAdicCompl K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniform space equivalence between two abstract completions of `ratfunc K` as
 a ring
equivalence: it goes from `K⸨X⸩` to `RatFuncAdicCompl K`
-/
abbrev LaurentSeriesRingEquiv : K⸨X⸩ ≃+* RatFuncAdicCompl K :=
  (ratfuncAdicComplRingEquiv K).symm
/-
**LaurentSeries.LaurentSeriesRingEquiv_def** 是 Mathlib 中的一个引理，位于命名空间 `LaurentSer
ies`。
形式化陈述：LaurentSeriesRingEquiv_def (f : K⟦X⟧) : (LaurentSeriesRingEquiv K) f = adi
cCompletion.ofCompletion ((LaurentSeriesPkg K).compare ratfuncAdicComplPkg (f : 
K⸨X⸩))
参数：f : K⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
lemma LaurentSeriesRingEquiv_def (f : K⟦X⟧) :
    (LaurentSeriesRingEquiv K) f = adicCompletion.ofCompletion
      ((LaurentSeriesPkg K).compare ratfuncAdicComplPkg (f : K⸨X⸩)) :=
  rfl

@[simp]
/-
**LaurentSeries.ratfuncAdicComplRingEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Laure
ntSeries`。
形式化陈述：ratfuncAdicComplRingEquiv_apply (x : RatFuncAdicCompl K) : ratfuncAdicComp
lRingEquiv K x = ratfuncAdicComplPkg.compare (LaurentSeriesPkg K) (adicCompletio
n.toCompletion x)
参数：x : RatFuncAdicCompl K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem ratfuncAdicComplRingEquiv_apply (x : RatFuncAdicCompl K) :
    ratfuncAdicComplRingEquiv K x =
      ratfuncAdicComplPkg.compare (LaurentSeriesPkg K) (adicCompletion.toCompletion x) := rfl
/-
**LaurentSeries.coe_X_compare** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：coe_X_compare : (ratfuncAdicComplRingEquiv K) ((RatFunc.X : K⟮X⟯) : RatFun
cAdicCompl K) = ((PowerSeries.X : K⟦X⟧) : K⸨X⸩)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentSeries.ratfuncAdicComplRingEquiv_apply`：ratfuncAdicComplRingEquiv
_apply (x : RatFuncAdicCompl K) : ratfuncAdicComplRingEquiv K x = ratfuncAdicCom
plPkg.compare (LaurentSeriesPkg K) …
· 使用定理 `PowerSeries.coe_X`：coe_X : ((X : R⟦X⟧) : R⸨X⸩) = single 1 1
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.coe_X`：coe_X : ((X : RatFunc F) : F⸨X⸩) = single 1 1
· 使用定理 `LaurentSeries.LaurentSeries_coe`：LaurentSeries_coe (x : K⟮X⟯) : (Laurent
SeriesPkg K).coe (WithVal.toVal _ x) = (x : K⸨X⸩)
· 使用定理 `AbstractCompletion.compare_coe`：compare_coe (a : α) : pkg.compare pkg' (
pkg.coe a) = pkg'.coe a
-/
theorem coe_X_compare :
    (ratfuncAdicComplRingEquiv K) ((RatFunc.X : K⟮X⟯) : RatFuncAdicCompl K) =
      ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) := by
  rw [ratfuncAdicComplRingEquiv_apply, PowerSeries.coe_X, ← RatFunc.coe_X, ← LaurentSeries_coe,
    ← compare_coe]
  rfl
/-
**LaurentSeries.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：algebraMap_apply (a : K) : algebraMap K K⸨X⸩ a = HahnSeries.C a
参数：a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.ofPowerSeries_C`：ofPowerSeries_C (r : R) : ofPowerSeries Γ R 
(PowerSeries.C r) = HahnSeries.C r
· 使用定理 `HahnSeries.C_apply`：∀ {Γ : Type u_1} {R : Type u_3} [inst : AddCommMonoi
d Γ] [inst_1 : PartialOrder Γ] [inst_2 : IsOrderedCancelAddMonoid Γ]   [inst_3 :
 NonAsso…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_apply (a : K) : algebraMap K K⸨X⸩ a = HahnSeries.C a := by
  simp [RingHom.algebraMap_toAlgebra]
/-
**LaurentSeries.** 是 Mathlib 中的一个实例，位于命名空间 `LaurentSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra K (RatFuncAdicCompl K) :=
  RingHom.toAlgebra ((LaurentSeriesRingEquiv K).toRingHom.comp HahnSeries.C)

/-- The algebra equivalence between `K⸨X⸩` and the `X`-adic completion of `RatFunc X` -/
/-
**LaurentSeries.LaurentSeriesAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LaurentSeries`。
形式化陈述：LaurentSeriesAlgEquiv : K⸨X⸩ ≃ₐ[K] RatFuncAdicCompl K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra equivalence between `K⸨X⸩` and the `X`-adic completion of `RatFunc X
`
-/
def LaurentSeriesAlgEquiv : K⸨X⸩ ≃ₐ[K] RatFuncAdicCompl K :=
  AlgEquiv.ofRingEquiv (f := LaurentSeriesRingEquiv K)
    (fun a ↦ by simp [RingHom.algebraMap_toAlgebra])

open Filter WithZero

open scoped WithZeroTopology Topology Multiplicative
/-
**LaurentSeries.valuation_LaurentSeries_equal_extension** 是 Mathlib 中的一个定理，位于命名空
间 `LaurentSeries`。
形式化陈述：valuation_LaurentSeries_equal_extension : (LaurentSeriesPkg K).isDenseIndu
cing.extend Valued.v = (Valued.v : K⸨X⸩ -> Intᵐ⁰)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_unique`：extend_unique [T2Space γ] {f : α -> γ} {g
 : β -> γ} (di : IsDenseInducing i) (hf : forall x, g (i x) = f x) (hg : Continu
ous g) : di.extend …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `WithZeroTopology.t5Space`：∀ {Γ₀ : Type u_2} [inst : LinearOrderedCommGro
upWithZero Γ₀], T5Space Γ₀
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `AbstractCompletion.isDenseInducing`：isDenseInducing : IsDenseInducing ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithVal.apply_ofVal`：apply_ofVal (r : WithVal v) : v r.ofVal = Valued.v 
r
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `PowerSeries.instIsDomain`：∀ {R : Type u_1} [inst : Ring R] [IsDomain R],
 IsDomain (PowerSeries R)
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `PowerSeries.instIsDiscreteValuationRing`：∀ {k : Type u_2} [inst : Field 
k], IsDiscreteValuationRing (PowerSeries k)
· 使用定理 `LaurentSeries.instIsFractionRingPowerSeries`：∀ {K : Type u_2} [inst : Fi
eld K], IsFractionRing (PowerSeries K) (LaurentSeries K)
· 使用定理 `RatFunc.instFaithfulSMulPolynomialLaurentSeries`：∀ {F : Type u} [inst : 
Field F], FaithfulSMul (Polynomial F) (LaurentSeries F)
· 使用定理 `RatFunc.valuation_eq_LaurentSeries_valuation`：valuation_eq_LaurentSeries
_valuation (P : K⟮X⟯) : polynomialValuationX K P = (PowerSeries.idealX K).valuat
ion K⸨X⸩ P
· 使用定理 `Valued.continuous_valuation_of_surjective`：Valued.continuous_valuation_o
f_surjective [hv : Valued K Γ₀] (hsurj : Function.Surjective hv.v) : Continuous 
hv.v
· 使用引理 `LaurentSeries.valuation_surjective`：valuation_surjective : Function.Surj
ective (Valued.v (R
-/
theorem valuation_LaurentSeries_equal_extension :
    (LaurentSeriesPkg K).isDenseInducing.extend Valued.v = (Valued.v : K⸨X⸩ → ℤᵐ⁰) := by
  apply IsDenseInducing.extend_unique
  · intro x
    rw [← WithVal.apply_ofVal, valuation_eq_LaurentSeries_valuation K]
    rfl
  · exact Valued.continuous_valuation_of_surjective (valuation_surjective K)

set_option backward.isDefEq.respectTransparency.types false in
/-
**LaurentSeries.tendsto_valuation** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：tendsto_valuation (a : (idealX K).adicCompletion K⟮X⟯) : Tendsto (Valued.v
 : K⟮X⟯ -> Intᵐ⁰) (comap (↑) (𝓝 a)) (𝓝 (Valued.v a : Intᵐ⁰))
参数：a : (idealX K).adicCompletion K⟮X⟯。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valued.is_topological_valuation`：∀ {R : Type u} {inst : Ring R} {Γ₀ : ou
tParam (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R
 Γ₀] (s : Set R), s ∈…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_def`：tendsto_def {f : α -> β} {l₁ : Filter α} {l₂ : Filte
r β} : Tendsto f l₁ l₂ ↔ forall s in l₂, f ⁻¹' s in l₁
· 使用定理 `Filter.HasBasis.mem_iff'`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (t : Set α), t ∈ l ↔ ∃ i, 
p i ∧ s i ⊆ t
· 使用定理 `WithZeroTopology.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 (0 : Γ₀)).H
asBasis (fun γ : Γ₀ => γ != 0) Iio
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective`：valu
edAdicCompletion_surjective : Function.Surjective (Valued.v : (v.adicCompletion 
K) -> Intᵐ⁰)
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
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
（共 47 条，此处仅展示前 30 条）
-/
theorem tendsto_valuation (a : (idealX K).adicCompletion K⟮X⟯) :
    Tendsto (Valued.v : K⟮X⟯ → ℤᵐ⁰) (comap (↑) (𝓝 a)) (𝓝 (Valued.v a : ℤᵐ⁰)) := by
  have := Valued.is_topological_valuation (R := (idealX K).adicCompletion K⟮X⟯)
  by_cases ha : a = 0
  · rw [tendsto_def]
    intro S hS
    rw [ha, map_zero, WithZeroTopology.hasBasis_nhds_zero.1 S] at hS
    obtain ⟨γ, γ_ne_zero, γ_le⟩ := hS
    use {t | Valued.v t < γ}
    constructor
    · rw [ha, this]
      obtain ⟨x, hx⟩ := valuedAdicCompletion_surjective K⟮X⟯ (idealX K) γ
      use Units.mk0 (Valued.v.restrict x) (by
        simp only [Valuation.restrict_def, ne_eq, map_eq_zero]
        intro h
        simp only [h, map_zero] at hx
        tauto)
      simp [Units.val_mk0, Valuation.restrict_lt_iff, hx]
    · refine Set.Subset.trans (fun a _ ↦ ?_) (Set.preimage_mono γ_le)
      rw [Set.mem_preimage, Set.mem_Iio, ← Valued.valuedCompletion_apply a]
      simp_all
  · rw [WithZeroTopology.tendsto_of_ne_zero ((Valuation.ne_zero_iff Valued.v).mpr ha),
      Filter.eventually_comap, Filter.Eventually, Valued.mem_nhds]
    use Units.mk0 (Valued.v.restrict a) (by simp [Valuation.restrict_def, ha])
    simp only [Units.val_mk0, v_def, Set.ofPred_subset_ofPred]
    rintro y val_y b rfl
    rw [← valuedAdicCompletion_eq_valuation']
    exact (Valuation.restrict_inj _).mp <| Valuation.map_eq_of_sub_lt Valued.v.restrict val_y

set_option backward.isDefEq.respectTransparency false in
/-- The extension of the `X`-adic valuation from `K⟮X⟯` up to its abstract completion coincides,
modulo the isomorphism with `K⸨X⸩`, with the `X`-adic valuation on `K⸨X⸩`. -/
/-
**LaurentSeries.valuation_compare** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries`。
形式化陈述：valuation_compare (f : K⸨X⸩) : Valued.v (LaurentSeriesRingEquiv K f) = Val
ued.v f
参数：f : K⸨X⸩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
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
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_ofCompletion`：∀
 {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Type u_2)
 [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFr…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Valued.valuedCompletion_surjective_iff`：valuedCompletion_surjective_iff 
: Function.Surjective (v : hat K -> Γ₀) ↔ Function.Surjective (v : K -> Γ₀)
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.valuation_surjective`：valuation_surje
ctive : Function.Surjective (v.valuation K)
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `AbstractCompletion.isDenseInducing`：isDenseInducing : IsDenseInducing ι
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentSeries.valuation_LaurentSeries_equal_extension`：valuation_Laurent
Series_equal_extension : (LaurentSeriesPkg K).isDenseInducing.extend Valued.v = 
(Valued.v : K⸨X⸩ -> Intᵐ⁰)
· 使用定理 `AbstractCompletion.compare_comp_eq_compare`：compare_comp_eq_compare (γ :
 Type uγ) [TopologicalSpace γ] [T3Space γ] {f : α -> γ} (cont_f : Continuous f) 
: letI
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `WithZeroTopology.t5Space`：∀ {Γ₀ : Type u_2} [inst : LinearOrderedCommGro
upWithZero Γ₀], T5Space Γ₀
· 使用定理 `Valued.continuous_valuation_of_surjective`：Valued.continuous_valuation_o
f_surjective [hv : Valued K Γ₀] (hsurj : Function.Surjective hv.v) : Continuous 
hv.v
· 使用引理 `RatFunc.valuation_surjective`：valuation_surjective : Function.Surjective
 (Valued.v (R
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `IsDenseInducing.extend_unique`：extend_unique [T2Space γ] {f : α -> γ} {g
 : β -> γ} (di : IsDenseInducing i) (hf : forall x, g (i x) = f x) (hg : Continu
ous g) : di.extend …
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `Valued.valuedCompletion_apply`：valuedCompletion_apply (x : K) : Valued.v
 (x : hat K) = v x
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The extension of the `X`-adic valuation from `K⟮X⟯` up to its abstract completio
n coincides,
modulo the isomorphism with `K⸨X⸩`, with the `X`-adic valuation on `K⸨X⸩`.
-/
theorem valuation_compare (f : K⸨X⸩) :
    Valued.v (LaurentSeriesRingEquiv K f) = Valued.v f := by
  change Valued.v (adicCompletion.ofCompletion
    ((LaurentSeriesPkg K).compare ratfuncAdicComplPkg f)) = Valued.v f
  rw [adicCompletion.valued_ofCompletion]
  let : UniformSpace (ratfuncAdicComplPkg (K := K).space) :=
      ratfuncAdicComplPkg.uniformStruct
  have raw_surj : Function.Surjective (Valued.v : (polynomialValuationX K).Completion → ℤᵐ⁰) :=
    Valued.valuedCompletion_surjective_iff.mpr <| .of_comp ((idealX K).valuation_surjective K⟮X⟯)
  rw [← valuation_LaurentSeries_equal_extension, ← compare_comp_eq_compare ratfuncAdicComplPkg _]
  · exact congr_fun (ratfuncAdicComplPkg.isDenseInducing.extend_unique
      Valued.valuedCompletion_apply (Valued.continuous_valuation_of_surjective raw_surj)).symm _
  · refine Valued.continuous_valuation_of_surjective (fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := RatFunc.valuation_surjective K x
    exact ⟨.toVal _ y, rfl⟩
  · intro x
    have h_cont := Valued.continuous_valuation_of_surjective raw_surj
    rw [ratfuncAdicComplPkg.isDenseInducing.extend_unique
        Valued.valuedCompletion_apply h_cont]
    exact (h_cont.continuousAt.tendsto.comp tendsto_comap).congr
      Valued.valuedCompletion_apply

section PowerSeries

/-- In order to compare `K⟦X⟧` with the valuation subring in the `X`-adic completion of
`K⟮X⟯` we consider its alias as a subring of `K⸨X⸩`. -/
/-
**LaurentSeries.powerSeries_as_subring** 是 Mathlib 中的一个缩写定义，位于命名空间 `LaurentSerie
s`。
形式化陈述：powerSeries_as_subring : Subring K⸨X⸩
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In order to compare `K⟦X⟧` with the valuation subring in the `X`-adic completion
 of
`K⟮X⟯` we consider its alias as a subring of `K⸨X⸩`.
-/
abbrev powerSeries_as_subring : Subring K⸨X⸩ :=
  Subring.map (HahnSeries.ofPowerSeries ℤ K) ⊤

/-- The ring `K⟦X⟧` is isomorphic to the subring `powerSeries_as_subring K` -/
/-
**LaurentSeries.powerSeriesEquivSubring** 是 Mathlib 中的一个缩写定义，位于命名空间 `LaurentSeri
es`。
形式化陈述：powerSeriesEquivSubring : K⟦X⟧ ≃+* powerSeries_as_subring K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring `K⟦X⟧` is isomorphic to the subring `powerSeries_as_subring K`
-/
abbrev powerSeriesEquivSubring : K⟦X⟧ ≃+* powerSeries_as_subring K :=
  ((Subring.topEquiv).symm).trans (Subring.equivMapOfInjective ⊤ (ofPowerSeries ℤ K)
    ofPowerSeries_injective)
/-
**LaurentSeries.powerSeriesEquivSubring_apply** 是 Mathlib 中的一个引理，位于命名空间 `Laurent
Series`。
形式化陈述：powerSeriesEquivSubring_apply (f : K⟦X⟧) : powerSeriesEquivSubring K f = ⟨
HahnSeries.ofPowerSeries Int K f, Subring.mem_map.mpr ⟨f, trivial, rfl⟩⟩
参数：f : K⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
lemma powerSeriesEquivSubring_apply (f : K⟦X⟧) :
    powerSeriesEquivSubring K f =
      ⟨HahnSeries.ofPowerSeries ℤ K f, Subring.mem_map.mpr ⟨f, trivial, rfl⟩⟩ :=
  rfl
/-
**LaurentSeries.powerSeriesEquivSubring_coe_apply** 是 Mathlib 中的一个引理，位于命名空间 `Lau
rentSeries`。
形式化陈述：powerSeriesEquivSubring_coe_apply (f : K⟦X⟧) : (powerSeriesEquivSubring K 
f : K⸨X⸩) = ofPowerSeries Int K f
参数：f : K⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
lemma powerSeriesEquivSubring_coe_apply (f : K⟦X⟧) :
    (powerSeriesEquivSubring K f : K⸨X⸩) = ofPowerSeries ℤ K f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Through the isomorphism `LaurentSeriesRingEquiv`, power series land in the unit ball inside the
completion of `K⟮X⟯`. -/
/-
**LaurentSeries.mem_integers_of_powerSeries** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSe
ries`。
形式化陈述：mem_integers_of_powerSeries (F : K⟦X⟧) : (LaurentSeriesRingEquiv K) F in (
idealX K).adicCompletionIntegers K⟮X⟯
参数：F : K⟦X⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers`：mem_adicC
ompletionIntegers {x : v.adicCompletion K} : x in v.adicCompletionIntegers K ↔ V
alued.v x <= 1
· 使用定理 `LaurentSeries.valuation_compare`：valuation_compare (f : K⸨X⸩) : Valued.v
 (LaurentSeriesRingEquiv K f) = Valued.v f
· 使用定理 `LaurentSeries.val_le_one_iff_eq_coe`：val_le_one_iff_eq_coe (f : K⸨X⸩) : 
Valued.v f <= (1 : Intᵐ⁰) ↔ exists F : K⟦X⟧, F = f

--- 原说明 ---
Through the isomorphism `LaurentSeriesRingEquiv`, power series land in the unit 
ball inside the
completion of `K⟮X⟯`.
-/
theorem mem_integers_of_powerSeries (F : K⟦X⟧) :
    (LaurentSeriesRingEquiv K) F ∈ (idealX K).adicCompletionIntegers K⟮X⟯ := by
  rw [mem_adicCompletionIntegers, valuation_compare, val_le_one_iff_eq_coe]
  exact ⟨F, rfl⟩

/-- Conversely, all elements in the unit ball inside the completion of `K⟮X⟯` come from a power
series through the isomorphism `LaurentSeriesRingEquiv`. -/
/-
**LaurentSeries.exists_powerSeries_of_memIntegers** 是 Mathlib 中的一个定理，位于命名空间 `Lau
rentSeries`。
形式化陈述：exists_powerSeries_of_memIntegers {x : RatFuncAdicCompl K} (hx : x in (ide
alX K).adicCompletionIntegers K⟮X⟯) : exists F : K⟦X⟧, (LaurentSeriesRingEquiv K
) F = x
参数：hx : x in (idealX K).adicCompletionIntegers K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentSeries.valuation_compare`：valuation_compare (f : K⸨X⸩) : Valued.v
 (LaurentSeriesRingEquiv K f) = Valued.v f
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers`：mem_adicC
ompletionIntegers {x : v.adicCompletion K} : x in v.adicCompletionIntegers K ↔ V
alued.v x <= 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LaurentSeries.val_le_one_iff_eq_coe`：val_le_one_iff_eq_coe (f : K⸨X⸩) : 
Valued.v f <= (1 : Intᵐ⁰) ↔ exists F : K⟦X⟧, F = f

--- 原说明 ---
Conversely, all elements in the unit ball inside the completion of `K⟮X⟯` come f
rom a power
series through the isomorphism `LaurentSeriesRingEquiv`.
-/
theorem exists_powerSeries_of_memIntegers {x : RatFuncAdicCompl K}
    (hx : x ∈ (idealX K).adicCompletionIntegers K⟮X⟯) :
    ∃ F : K⟦X⟧, (LaurentSeriesRingEquiv K) F = x := by
  set f := (ratfuncAdicComplRingEquiv K) x with hf
  have hval : Valued.v f ≤ 1 := by
    rw [← valuation_compare (K := K) f, hf, RingEquiv.symm_apply_apply,
      ← mem_adicCompletionIntegers]
    exact hx
  obtain ⟨F, hF⟩ := (val_le_one_iff_eq_coe K f).mp hval
  exact ⟨F, by rw [hF, hf, RingEquiv.symm_apply_apply]⟩
/-
**LaurentSeries.powerSeries_ext_subring** 是 Mathlib 中的一个定理，位于命名空间 `LaurentSeries
`。
形式化陈述：powerSeries_ext_subring : Subring.map (LaurentSeriesRingEquiv K).toRingHom
 (powerSeries_as_subring K) = ((idealX K).adicCompletionIntegers K⟮X⟯).toSubring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.ext`：ext {S T : Subring R} (h : forall x, x in S ↔ x in T) : S =
 T
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentSeries.mem_integers_of_powerSeries`：mem_integers_of_powerSeries (
F : K⟦X⟧) : (LaurentSeriesRingEquiv K) F in (idealX K).adicCompletionIntegers K⟮
X⟯
· 使用定理 `LaurentSeries.exists_powerSeries_of_memIntegers`：exists_powerSeries_of_m
emIntegers {x : RatFuncAdicCompl K} (hx : x in (idealX K).adicCompletionIntegers
 K⟮X⟯) : exists F : K⟦X⟧, (LaurentSer…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `trivial`：True
-/
theorem powerSeries_ext_subring :
    Subring.map (LaurentSeriesRingEquiv K).toRingHom (powerSeries_as_subring K) =
      ((idealX K).adicCompletionIntegers K⟮X⟯).toSubring := by
  ext x
  refine ⟨fun ⟨f, ⟨F, _, coe_F⟩, hF⟩ ↦ ?_, fun H ↦ ?_⟩
  · simp only [ValuationSubring.mem_toSubring, ← hF, ← coe_F]
    apply mem_integers_of_powerSeries
  · obtain ⟨F, hF⟩ := exists_powerSeries_of_memIntegers K H
    simp only [Subring.mem_map]
    exact ⟨F, ⟨F, trivial, rfl⟩, hF⟩

/-- The ring isomorphism between `K⟦X⟧` and the unit ball inside the `X`-adic completion of
`K⟮X⟯`. -/
/-
**LaurentSeries.powerSeriesRingEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `LaurentSeries`
。
形式化陈述：powerSeriesRingEquiv : K⟦X⟧ ≃+* (idealX K).adicCompletionIntegers K⟮X⟯
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LaurentSeries.powerSeries_ext_subring`：powerSeries_ext_subring : Subring
.map (LaurentSeriesRingEquiv K).toRingHom (powerSeries_as_subring K) = ((idealX 
K).adicCompletionIntegers K…

--- 原说明 ---
The ring isomorphism between `K⟦X⟧` and the unit ball inside the `X`-adic comple
tion of
`K⟮X⟯`.
-/
abbrev powerSeriesRingEquiv : K⟦X⟧ ≃+* (idealX K).adicCompletionIntegers K⟮X⟯ :=
  ((powerSeriesEquivSubring K).trans (LaurentSeriesRingEquiv K).subringMap).trans
    <| RingEquiv.subringCongr (powerSeries_ext_subring K)
/-
**LaurentSeries.powerSeriesRingEquiv_coe_apply** 是 Mathlib 中的一个引理，位于命名空间 `Lauren
tSeries`。
形式化陈述：powerSeriesRingEquiv_coe_apply (f : K⟦X⟧) : powerSeriesRingEquiv K f = Lau
rentSeriesRingEquiv K (f : K⸨X⸩)
参数：f : K⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
-/
lemma powerSeriesRingEquiv_coe_apply (f : K⟦X⟧) :
    powerSeriesRingEquiv K f = LaurentSeriesRingEquiv K (f : K⸨X⸩) :=
  rfl
/-
**LaurentSeries.LaurentSeriesRingEquiv_mem_valuationSubring** 是 Mathlib 中的一个引理，位
于命名空间 `LaurentSeries`。
形式化陈述：LaurentSeriesRingEquiv_mem_valuationSubring (f : K⟦X⟧) : LaurentSeriesRing
Equiv K f in Valued.v.valuationSubring
参数：f : K⟦X⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentSeries.valuation_compare`：valuation_compare (f : K⸨X⸩) : Valued.v
 (LaurentSeriesRingEquiv K f) = Valued.v f
· 使用定理 `LaurentSeries.val_le_one_iff_eq_coe`：val_le_one_iff_eq_coe (f : K⸨X⸩) : 
Valued.v f <= (1 : Intᵐ⁰) ↔ exists F : K⟦X⟧, F = f
-/
lemma LaurentSeriesRingEquiv_mem_valuationSubring (f : K⟦X⟧) :
    LaurentSeriesRingEquiv K f ∈ Valued.v.valuationSubring := by
  simp only [Valuation.mem_valuationSubring_iff]
  rw [valuation_compare, val_le_one_iff_eq_coe]
  use f
/-
**LaurentSeries.algebraMap_C_mem_adicCompletionIntegers** 是 Mathlib 中的一个引理，位于命名空
间 `LaurentSeries`。
形式化陈述：algebraMap_C_mem_adicCompletionIntegers (x : K) : ((LaurentSeriesRingEquiv
 K).toRingHom.comp HahnSeries.C) x in adicCompletionIntegers K⟮X⟯ (idealX K)
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.C_apply`：∀ {Γ : Type u_1} {R : Type u_3} [inst : AddCommMonoi
d Γ] [inst_1 : PartialOrder Γ] [inst_2 : IsOrderedCancelAddMonoid Γ]   [inst_3 :
 NonAsso…
· 使用定理 `HahnSeries.ofPowerSeries_C`：ofPowerSeries_C (r : R) : ofPowerSeries Γ R 
(PowerSeries.C r) = HahnSeries.C r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `LaurentSeries.LaurentSeriesRingEquiv_mem_valuationSubring`：LaurentSeries
RingEquiv_mem_valuationSubring (f : K⟦X⟧) : LaurentSeriesRingEquiv K f in Valued
.v.valuationSubring
-/
lemma algebraMap_C_mem_adicCompletionIntegers (x : K) :
    ((LaurentSeriesRingEquiv K).toRingHom.comp HahnSeries.C) x ∈
      adicCompletionIntegers K⟮X⟯ (idealX K) := by
  have : HahnSeries.C x = ofPowerSeries ℤ K (PowerSeries.C x) := by
    simp [C_apply, ofPowerSeries_C]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this]
  apply LaurentSeriesRingEquiv_mem_valuationSubring
/-
**LaurentSeries.** 是 Mathlib 中的一个实例，位于命名空间 `LaurentSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra K ((idealX K).adicCompletionIntegers K⟮X⟯) :=
  RingHom.toAlgebra <|
    ((LaurentSeriesRingEquiv K).toRingHom.comp HahnSeries.C).codRestrict _
      (algebraMap_C_mem_adicCompletionIntegers K)

/-- The algebra isomorphism between `K⟦X⟧` and the unit ball inside the `X`-adic completion of
`K⟮X⟯`. -/
/-
**LaurentSeries.powerSeriesAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LaurentSeries`。
形式化陈述：powerSeriesAlgEquiv : K⟦X⟧ ≃ₐ[K] (idealX K).adicCompletionIntegers K⟮X⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra isomorphism between `K⟦X⟧` and the unit ball inside the `X`-adic com
pletion of
`K⟮X⟯`.
-/
def powerSeriesAlgEquiv : K⟦X⟧ ≃ₐ[K] (idealX K).adicCompletionIntegers K⟮X⟯ := by
  apply AlgEquiv.ofRingEquiv (f := powerSeriesRingEquiv K)
  intro a
  rw [PowerSeries.algebraMap_eq, RingHom.algebraMap_toAlgebra, ← Subtype.coe_inj,
    powerSeriesRingEquiv_coe_apply,
    RingHom.codRestrict_apply _ _ (algebraMap_C_mem_adicCompletionIntegers K)]
  simp

end PowerSeries

end Comparison

end LaurentSeries

