/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, Ralf Stephan
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.MoveAdd
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Ideal.Basic

/-!
# Formal power series (in one variable)

This file defines (univariate) formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

Formal power series in one variable are defined from multivariate
power series as `PowerSeries R := MvPowerSeries Unit R`.

The file sets up the (semi)ring structure on univariate power series.

We provide the natural inclusion from polynomials to formal power series.

Additional results can be found in:
* `Mathlib/RingTheory/PowerSeries/Trunc.lean`, truncation of power series;
* `Mathlib/RingTheory/PowerSeries/Inverse.lean`, about inverses of power series,
  and the fact that power series over a local ring form a local ring;
* `Mathlib/RingTheory/PowerSeries/Order.lean`, the order of a power series at 0,
  and application to the fact that power series over an integral domain form an integral domain.

## Implementation notes

Because of its definition,
  `PowerSeries R := MvPowerSeries Unit R`.
a lot of proofs and properties from the multivariate case
can be ported to the single variable case.
However, it means that formal power series are indexed by `Unit →₀ ℕ`,
which is of course canonically isomorphic to `ℕ`.
We then build some glue to treat formal power series as if they were indexed by `ℕ`.
Occasionally this leads to proofs that are uglier than expected.

-/

@[expose] public section

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

/-- Formal power series over a coefficient type `R` -/
@[wikidata Q1003025]
/-
**PowerSeries** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PowerSeries (R : Type*)
参数：R : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Formal power series over a coefficient type `R`
-/
abbrev PowerSeries (R : Type*) :=
  MvPowerSeries Unit R

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

/--
`R⟦X⟧` is notation for `PowerSeries R`,
the semiring of formal power series in one variable over a semiring `R`.
-/
scoped notation:9000 R "⟦X⟧" => PowerSeries R

section Semiring

variable [Semiring R]

/-- The `n`th coefficient of a formal power series. -/
/-
**PowerSeries.coeff** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：coeff (n : Nat) : R⟦X⟧ ->ₗ[R] R
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th coefficient of a formal power series.
-/
def coeff (n : ℕ) : R⟦X⟧ →ₗ[R] R :=
  MvPowerSeries.coeff (single () n)

/-- The `n`th monomial with coefficient `a` as formal power series. -/
/-
**PowerSeries.monomial** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：monomial (n : Nat) : R ->ₗ[R] R⟦X⟧
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th monomial with coefficient `a` as formal power series.
-/
def monomial (n : ℕ) : R →ₗ[R] R⟦X⟧ :=
  MvPowerSeries.monomial (single () n)
/-
**PowerSeries.coeff_def** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_def {s : Unit ->₀ Nat} {n : Nat} (h : s () = n) : coeff (R
参数：h : s () = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), Po
werSeries.coeff n = MvPowerSeries.coeff fun₀ | () => n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.unique_single`：unique_single [Unique α] (x : α ->₀ M) : x = sing
le default (x default)
-/
theorem coeff_def {s : Unit →₀ ℕ} {n : ℕ} (h : s () = n) :
    coeff (R := R) n = MvPowerSeries.coeff s := by
  rw [coeff, ← h, ← Finsupp.unique_single s]

@[simp]
/-
**PowerSeries.coeff_coeToMvPowerSeries** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_coeToMvPowerSeries {f : R⟦X⟧} (n : Nat) : MvPowerSeries.coeff (Finsu
pp.single () n) f = f.coeff n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeff_coeToMvPowerSeries {f : R⟦X⟧} (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single () n) f = f.coeff n := rfl

/-- Two formal power series are equal if all their coefficients are equal. -/
@[ext]
/-
**PowerSeries.ext** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) : φ = ψ
参数：h : forall n, coeff n φ = coeff n ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coeff_def`：coeff_def {s : Unit ->₀ Nat} {n : Nat} (h : s () 
= n) : coeff (R

--- 原说明 ---
Two formal power series are equal if all their coefficients are equal.
-/
theorem ext {φ ψ : R⟦X⟧} (h : ∀ n, coeff n φ = coeff n ψ) : φ = ψ :=
  MvPowerSeries.ext fun n => by
    rw [← coeff_def]
    · apply h
    rfl

@[simp]
/-
**PowerSeries.forall_coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：forall_coeff_eq_zero (φ : R⟦X⟧) : (forall n, coeff n φ = 0) ↔ φ = 0
参数：φ : R⟦X⟧。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem forall_coeff_eq_zero (φ : R⟦X⟧) : (∀ n, coeff n φ = 0) ↔ φ = 0 :=
  ⟨fun h => ext h, fun h => by simp [h]⟩

/-- Two formal power series are equal if all their coefficients are equal. -/
add_decl_doc PowerSeries.ext_iff

/-
**PowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton R] : Subsingleton R⟦X⟧ := by
  simp only [subsingleton_iff, PowerSeries.ext_iff]
  subsingleton

/-- Constructor for formal power series. -/
/-
**PowerSeries.mk** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：mk {R} (f : Nat -> R) : R⟦X⟧
参数：f : Nat -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for formal power series.
-/
def mk {R} (f : ℕ → R) : R⟦X⟧ := fun s => f (s ())

@[simp]
/-
**PowerSeries.coeff_mk** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f) = f n
参数：n : Nat；f : Nat -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
theorem coeff_mk (n : ℕ) (f : ℕ → R) : coeff n (mk f) = f n :=
  congr_arg f Finsupp.single_eq_same
/-
**PowerSeries.coeff_monomial** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_monomial (m n : Nat) (a : R) : coeff m (monomial n a) = if m = n the
n a else 0
参数：m n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_monomial (m n : ℕ) (a : R) : coeff m (monomial n a) = if m = n then a else 0 :=
  calc
    coeff m (monomial n a) = _ := MvPowerSeries.coeff_monomial _ _ _
    _ = if m = n then a else 0 := by simp only [Finsupp.unique_single_eq_iff]
/-
**PowerSeries.monomial_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：monomial_eq_mk (n : Nat) (a : R) : monomial n a = mk fun m => if m = n the
n a else 0
参数：n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_monomial`：coeff_monomial (m n : Nat) (a : R) : coeff m
 (monomial n a) = if m = n then a else 0
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
-/
theorem monomial_eq_mk (n : ℕ) (a : R) : monomial n a = mk fun m => if m = n then a else 0 :=
  ext fun m => by rw [coeff_monomial, coeff_mk]

@[simp]
/-
**PowerSeries.coeff_monomial_same** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_monomial_same (n : Nat) (a : R) : coeff n (monomial n a) = a
参数：n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_monomial_same`：coeff_monomial_same (n : σ ->₀ Nat) (
a : R) : coeff n (monomial n a) = a
-/
theorem coeff_monomial_same (n : ℕ) (a : R) : coeff n (monomial n a) = a :=
  MvPowerSeries.coeff_monomial_same _ _

@[simp]
/-
**PowerSeries.coeff_comp_monomial** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_comp_monomial (n : Nat) : (coeff (R
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `PowerSeries.coeff_monomial_same`：coeff_monomial_same (n : Nat) (a : R) :
 coeff n (monomial n a) = a
-/
theorem coeff_comp_monomial (n : ℕ) : (coeff (R := R) n).comp (monomial n) = LinearMap.id :=
  LinearMap.ext <| coeff_monomial_same n
/-
**PowerSeries.monomial_mul_monomial** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：monomial_mul_monomial (m n : Nat) (a b : R) : monomial m a * monomial n b 
= monomial (m + n) (a * b)
参数：m n : Nat；a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `MvPowerSeries.monomial_mul_monomial`：monomial_mul_monomial (m n : σ ->₀ 
Nat) (a b : R) : monomial m a * monomial n b = monomial (m + n) (a * b)
-/
theorem monomial_mul_monomial (m n : ℕ) (a b : R) :
    monomial m a * monomial n b = monomial (m + n) (a * b) := by
  simpa [monomial] using
    MvPowerSeries.monomial_mul_monomial (Finsupp.single () m) (Finsupp.single () n) a b

/-- The constant coefficient of a formal power series. -/
/-
**PowerSeries.constantCoeff** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff : R⟦X⟧ ->+* R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant coefficient of a formal power series.
-/
def constantCoeff : R⟦X⟧ →+* R :=
  MvPowerSeries.constantCoeff
/-
**PowerSeries.constantCoeff_eq** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_eq (f : R⟦X⟧) : constantCoeff f = MvPowerSeries.constantCoef
f f
参数：f : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_eq (f : R⟦X⟧) :
    constantCoeff f = MvPowerSeries.constantCoeff f := rfl

/-- The constant formal power series. -/
/-
**PowerSeries.C** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：C : R ->+* R⟦X⟧
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant formal power series.
-/
def C : R →+* R⟦X⟧ :=
  MvPowerSeries.C
/-
**PowerSeries.C_apply** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：C_apply {r : R} : C r = MvPowerSeries.C r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma C_apply {r : R} : C r = MvPowerSeries.C r := rfl
/-
**PowerSeries.algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {R : Type u_2} [inst : CommSemiring R], algebraMap R (PowerSeries R) = P
owerSeries.C
参数：PowerSeries R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma algebraMap_eq {R : Type*} [CommSemiring R] : algebraMap R R⟦X⟧ = C := rfl

/-- The variable of the formal power series ring. -/
/-
**PowerSeries.X** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：X : R⟦X⟧
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The variable of the formal power series ring.
-/
def X : R⟦X⟧ :=
  MvPowerSeries.X ()
/-
**PowerSeries.X_apply** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：X_apply : X (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma X_apply : X (R := R) = MvPowerSeries.X () := rfl
/-
**PowerSeries.commute_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：commute_X (φ : R⟦X⟧) : Commute φ X
参数：φ : R⟦X⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.commute_X`：commute_X (φ : MvPowerSeries σ R) (s : σ) : Com
mute φ (X s)
-/
theorem commute_X (φ : R⟦X⟧) : Commute φ X :=
  MvPowerSeries.commute_X _ _
/-
**PowerSeries.X_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_mul {φ : R⟦X⟧} : X * φ = φ * X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.X_mul`：X_mul {φ : MvPowerSeries σ R} {s : σ} : X s * φ = φ
 * X s
-/
theorem X_mul {φ : R⟦X⟧} : X * φ = φ * X :=
  MvPowerSeries.X_mul
/-
**PowerSeries.commute_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：commute_X_pow (φ : R⟦X⟧) (n : Nat) : Commute φ (X ^ n)
参数：φ : R⟦X⟧；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.commute_X_pow`：commute_X_pow (φ : MvPowerSeries σ R) (s : 
σ) (n : Nat) : Commute φ (X s ^ n)
-/
theorem commute_X_pow (φ : R⟦X⟧) (n : ℕ) : Commute φ (X ^ n) :=
  MvPowerSeries.commute_X_pow _ _ _
/-
**PowerSeries.X_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_pow_mul {φ : R⟦X⟧} {n : Nat} : X ^ n * φ = φ * X ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.X_pow_mul`：X_pow_mul {φ : MvPowerSeries σ R} {s : σ} {n : 
Nat} : X s ^ n * φ = φ * X s ^ n
-/
theorem X_pow_mul {φ : R⟦X⟧} {n : ℕ} : X ^ n * φ = φ * X ^ n :=
  MvPowerSeries.X_pow_mul

@[simp]
/-
**PowerSeries.coeff_zero_eq_constantCoeff** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries
`。
形式化陈述：coeff_zero_eq_constantCoeff : ⇑(coeff (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), Po
werSeries.coeff n = MvPowerSeries.coeff fun₀ | () => n
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
-/
theorem coeff_zero_eq_constantCoeff : ⇑(coeff (R := R) 0) = constantCoeff := by
  rw [coeff, Finsupp.single_zero]
  rfl
/-
**PowerSeries.coeff_zero_eq_constantCoeff_apply** 是 Mathlib 中的一个定理，位于命名空间 `Power
Series`。
形式化陈述：coeff_zero_eq_constantCoeff_apply (φ : R⟦X⟧) : coeff 0 φ = constantCoeff φ
参数：φ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
-/
theorem coeff_zero_eq_constantCoeff_apply (φ : R⟦X⟧) : coeff 0 φ = constantCoeff φ := by
  rw [coeff_zero_eq_constantCoeff]

@[simp]
/-
**PowerSeries.monomial_zero_eq_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：monomial_zero_eq_C : ⇑(monomial (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.monomial.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ),
 PowerSeries.monomial n = MvPowerSeries.monomial fun₀ | () => n
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `MvPowerSeries.monomial_zero_eq_C`：monomial_zero_eq_C : ⇑(monomial (R
-/
theorem monomial_zero_eq_C : ⇑(monomial (R := R) 0) = C := by
  -- This used to be `rw`, but we need `rw; rfl` after https://github.com/leanprover/lean4/pull/2644
  rw [monomial, Finsupp.single_zero, MvPowerSeries.monomial_zero_eq_C]
  rfl
/-
**PowerSeries.monomial_zero_eq_C_apply** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：monomial_zero_eq_C_apply (a : R) : monomial 0 a = C a
参数：a : R。
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
· 使用定理 `PowerSeries.monomial_zero_eq_C`：monomial_zero_eq_C : ⇑(monomial (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem monomial_zero_eq_C_apply (a : R) : monomial 0 a = C a := by simp
/-
**PowerSeries.coeff_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_C (n : Nat) (a : R) : coeff n (C a : R⟦X⟧) = if n = 0 then a else 0
参数：n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.monomial_zero_eq_C_apply`：monomial_zero_eq_C_apply (a : R) :
 monomial 0 a = C a
· 使用定理 `PowerSeries.coeff_monomial`：coeff_monomial (m n : Nat) (a : R) : coeff m
 (monomial n a) = if m = n then a else 0
-/
theorem coeff_C (n : ℕ) (a : R) : coeff n (C a : R⟦X⟧) = if n = 0 then a else 0 := by
  rw [← monomial_zero_eq_C_apply, coeff_monomial]

@[simp]
/-
**PowerSeries.coeff_zero_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_zero_C (a : R) : coeff 0 (C a) = a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_C`：coeff_C (n : Nat) (a : R) : coeff n (C a : R⟦X⟧) = 
if n = 0 then a else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem coeff_zero_C (a : R) : coeff 0 (C a) = a := by
  rw [coeff_C, if_pos rfl]
/-
**PowerSeries.coeff_C_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_C_of_ne_zero {a : R} {n : Nat} (h : n != 0) : coeff n (C a) = 0
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_C`：coeff_C (n : Nat) (a : R) : coeff n (C a : R⟦X⟧) = 
if n = 0 then a else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem coeff_C_of_ne_zero {a : R} {n : ℕ} (h : n ≠ 0) : coeff n (C a) = 0 := by
  rw [coeff_C, if_neg h]

@[deprecated (since := "2026-05-20")] alias coeff_ne_zero_C := coeff_C_of_ne_zero

@[simp]
/-
**PowerSeries.coeff_succ_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_succ_C {a : R} {n : Nat} : coeff (n + 1) (C a) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_C_of_ne_zero`：coeff_C_of_ne_zero {a : R} {n : Nat} (h 
: n != 0) : coeff n (C a) = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
theorem coeff_succ_C {a : R} {n : ℕ} : coeff (n + 1) (C a) = 0 :=
  coeff_C_of_ne_zero n.succ_ne_zero

@[grind inj]
/-
**PowerSeries.C_injective** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：C_injective : Function.Injective (C (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.C_injective`：C_injective : Function.Injective (C : R -> Mv
PowerSeries σ R)
-/
theorem C_injective : Function.Injective (C (R := R)) := MvPowerSeries.C_injective
/-
**PowerSeries.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {R : Type u_1} [Semiring R], Subsingleton (PowerSeries R) ↔ Subsingleton
 R
参数：PowerSeries R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subsingleton_iff`：subsingleton_iff : Subsingleton α ↔ forall x y : α, x 
= y
· 使用定理 `PowerSeries.C_injective`：C_injective : Function.Injective (C (R
· 使用定理 `PowerSeries.instSubsingleton`：∀ {R : Type u_1} [Semiring R] [Subsingleto
n R], Subsingleton (PowerSeries R)
-/
protected theorem subsingleton_iff : Subsingleton R⟦X⟧ ↔ Subsingleton R := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rw [subsingleton_iff] at h ⊢
  exact fun a b ↦ C_injective (h (C a) (C b))
/-
**PowerSeries.X_eq** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_eq : (X : R⟦X⟧) = monomial 1 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem X_eq : (X : R⟦X⟧) = monomial 1 1 :=
  rfl
/-
**PowerSeries.coeff_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_X (n : Nat) : coeff n (X : R⟦X⟧) = if n = 1 then 1 else 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.X_eq`：X_eq : (X : R⟦X⟧) = monomial 1 1
· 使用定理 `PowerSeries.coeff_monomial`：coeff_monomial (m n : Nat) (a : R) : coeff m
 (monomial n a) = if m = n then a else 0
-/
theorem coeff_X (n : ℕ) : coeff n (X : R⟦X⟧) = if n = 1 then 1 else 0 := by
  rw [X_eq, coeff_monomial]

@[simp]
/-
**PowerSeries.coeff_zero_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_zero_X : coeff 0 (X : R⟦X⟧) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), Po
werSeries.coeff n = MvPowerSeries.coeff fun₀ | () => n
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `PowerSeries.X.eq_1`：∀ {R : Type u_1} [inst : Semiring R], PowerSeries.X 
= MvPowerSeries.X ()
· 使用定理 `MvPowerSeries.coeff_zero_X`：coeff_zero_X (s : σ) : coeff (0 : σ ->₀ Nat)
 (X s : MvPowerSeries σ R) = 0
-/
theorem coeff_zero_X : coeff 0 (X : R⟦X⟧) = 0 := by
  rw [coeff, Finsupp.single_zero, X, MvPowerSeries.coeff_zero_X]

@[simp]
/-
**PowerSeries.coeff_one_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_one_X : coeff 1 (X : R⟦X⟧) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_X`：coeff_X (n : Nat) : coeff n (X : R⟦X⟧) = if n = 1 t
hen 1 else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem coeff_one_X : coeff 1 (X : R⟦X⟧) = 1 := by rw [coeff_X, if_pos rfl]

@[simp]
/-
**PowerSeries.X_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_ne_zero [Nontrivial R] : (X : R⟦X⟧) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_one_X`：coeff_one_X : coeff 1 (X : R⟦X⟧) = 1
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
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem X_ne_zero [Nontrivial R] : (X : R⟦X⟧) ≠ 0 := fun H => by
  simpa only [coeff_one_X, one_ne_zero, map_zero] using congr_arg (coeff 1) H
/-
**PowerSeries.X_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_pow_eq (n : Nat) : (X : R⟦X⟧) ^ n = monomial n 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.X_pow_eq`：X_pow_eq (s : σ) (n : Nat) : (X s : MvPowerSerie
s σ R) ^ n = monomial (single s n) 1
-/
theorem X_pow_eq (n : ℕ) : (X : R⟦X⟧) ^ n = monomial n 1 :=
  MvPowerSeries.X_pow_eq _ n

@[simp, grind =]
/-
**PowerSeries.coeff_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_X_pow (m n : Nat) : coeff m ((X : R⟦X⟧) ^ n) = if m = n then 1 else 
0
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.X_pow_eq`：X_pow_eq (n : Nat) : (X : R⟦X⟧) ^ n = monomial n 1
· 使用定理 `PowerSeries.coeff_monomial`：coeff_monomial (m n : Nat) (a : R) : coeff m
 (monomial n a) = if m = n then a else 0
-/
theorem coeff_X_pow (m n : ℕ) : coeff m ((X : R⟦X⟧) ^ n) = if m = n then 1 else 0 := by
  rw [X_pow_eq, coeff_monomial]
/-
**PowerSeries.coeff_X_pow_self** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_X_pow_self (n : Nat) : coeff n ((X : R⟦X⟧) ^ n) = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_X_pow`：coeff_X_pow (m n : Nat) : coeff m ((X : R⟦X⟧) ^
 n) = if m = n then 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_X_pow_self (n : ℕ) : coeff n ((X : R⟦X⟧) ^ n) = 1 := by
  simp

@[simp]
/-
**PowerSeries.coeff_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_one (n : Nat) : coeff n (1 : R⟦X⟧) = if n = 0 then 1 else 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_C`：coeff_C (n : Nat) (a : R) : coeff n (C a : R⟦X⟧) = 
if n = 0 then a else 0
-/
theorem coeff_one (n : ℕ) : coeff n (1 : R⟦X⟧) = if n = 0 then 1 else 0 :=
  coeff_C n 1
/-
**PowerSeries.coeff_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_zero_one : coeff 0 (1 : R⟦X⟧) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_zero_C`：coeff_zero_C (a : R) : coeff 0 (C a) = a
-/
theorem coeff_zero_one : coeff 0 (1 : R⟦X⟧) = 1 :=
  coeff_zero_C 1
/-
**PowerSeries.coeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ) = ∑ p in antidiagonal n
, coeff p.1 φ * coeff p.2 ψ
参数：n : Nat；φ ψ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finsupp.single_injective`：single_injective (a : α) : Function.Injective 
(single a : M -> α ->₀ M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.antidiagonal_single`：antidiagonal_single (a : α) (n : Nat) : ant
idiagonal (single a n) = (antidiagonal n).map (Function.Embedding.prodMap ⟨_, si
ngle_injective a⟩…
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
-/
theorem coeff_mul (n : ℕ) (φ ψ : R⟦X⟧) :
    coeff n (φ * ψ) = ∑ p ∈ antidiagonal n, coeff p.1 φ * coeff p.2 ψ := by
  -- `rw` can't see that `PowerSeries = MvPowerSeries Unit`, so use `.trans`
  refine (MvPowerSeries.coeff_mul _ φ ψ).trans ?_
  rw [Finsupp.antidiagonal_single, Finset.sum_map]
  rfl

@[simp]
/-
**PowerSeries.coeff_mul_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_mul_C (n : Nat) (φ : R⟦X⟧) (a : R) : coeff n (φ * C a) = coeff n φ *
 a
参数：n : Nat；φ : R⟦X⟧；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_mul_C`：coeff_mul_C (n : σ ->₀ Nat) (φ : MvPowerSerie
s σ R) (a : R) : coeff n (φ * C a) = coeff n φ * a
-/
theorem coeff_mul_C (n : ℕ) (φ : R⟦X⟧) (a : R) : coeff n (φ * C a) = coeff n φ * a :=
  MvPowerSeries.coeff_mul_C _ φ a

@[simp]
/-
**PowerSeries.coeff_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_C_mul (n : Nat) (φ : R⟦X⟧) (a : R) : coeff n (C a * φ) = a * coeff n
 φ
参数：n : Nat；φ : R⟦X⟧；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_C_mul`：coeff_C_mul (n : σ ->₀ Nat) (φ : MvPowerSerie
s σ R) (a : R) : coeff n (C a * φ) = a * coeff n φ
-/
theorem coeff_C_mul (n : ℕ) (φ : R⟦X⟧) (a : R) : coeff n (C a * φ) = a * coeff n φ :=
  MvPowerSeries.coeff_C_mul _ φ a

@[simp]
/-
**PowerSeries.coeff_smul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_smul {S : Type*} [Semiring S] [Module R S] (n : Nat) (φ : PowerSerie
s S) (a : R) : coeff n (a • φ) = a • coeff n φ
参数：n : Nat；φ : PowerSeries S；a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_smul {S : Type*} [Semiring S] [Module R S] (n : ℕ) (φ : PowerSeries S) (a : R) :
    coeff n (a • φ) = a • coeff n φ :=
  rfl

@[simp]
/-
**PowerSeries.constantCoeff_smul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_smul {S : Type*} [Semiring S] [Module R S] (φ : PowerSeries 
S) (a : R) : constantCoeff (a • φ) = a • constantCoeff φ
参数：φ : PowerSeries S；a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_smul {S : Type*} [Semiring S] [Module R S] (φ : PowerSeries S) (a : R) :
    constantCoeff (a • φ) = a • constantCoeff φ :=
  rfl
/-
**PowerSeries.smul_eq_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：smul_eq_C_mul (f : R⟦X⟧) (a : R) : a • f = C a * f
参数：f : R⟦X⟧；a : R。
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
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `PowerSeries.coeff_C_mul`：coeff_C_mul (n : Nat) (φ : R⟦X⟧) (a : R) : coef
f n (C a * φ) = a * coeff n φ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_eq_C_mul (f : R⟦X⟧) (a : R) : a • f = C a * f := by
  ext
  simp

@[simp]
/-
**PowerSeries.coeff_succ_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_succ_mul_X (n : Nat) (φ : R⟦X⟧) : coeff (n + 1) (φ * X) = coeff n φ
参数：n : Nat；φ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MvPowerSeries.coeff_add_mul_monomial`：coeff_add_mul_monomial (a : R) : c
oeff (m + n) (φ * monomial n a) = coeff m φ * a
-/
theorem coeff_succ_mul_X (n : ℕ) (φ : R⟦X⟧) : coeff (n + 1) (φ * X) = coeff n φ := by
  simp only [coeff, Finsupp.single_add]
  convert! φ.coeff_add_mul_monomial (single () n) (single () 1) _
  rw [mul_one]

@[simp]
/-
**PowerSeries.coeff_succ_X_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_succ_X_mul (n : Nat) (φ : R⟦X⟧) : coeff (n + 1) (X * φ) = coeff n φ
参数：n : Nat；φ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MvPowerSeries.coeff_add_monomial_mul`：coeff_add_monomial_mul (a : R) : c
oeff (m + n) (monomial m a * φ) = a * coeff n φ
-/
theorem coeff_succ_X_mul (n : ℕ) (φ : R⟦X⟧) : coeff (n + 1) (X * φ) = coeff n φ := by
  simp only [coeff, Finsupp.single_add, add_comm n 1]
  convert! φ.coeff_add_monomial_mul (single () 1) (single () n) _
  rw [one_mul]
/-
**PowerSeries.mul_X_cancel** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：mul_X_cancel {φ ψ : R⟦X⟧} (h : φ * X = ψ * X) : φ = ψ
参数：h : φ * X = ψ * X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.ext_iff`：∀ {R : Type u_1} [inst : Semiring R] {φ ψ : PowerSe
ries R},   φ = ψ ↔ ∀ (n : ℕ), (PowerSeries.coeff n) φ = (PowerSeries.coeff n) ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PowerSeries.coeff_succ_mul_X`：coeff_succ_mul_X (n : Nat) (φ : R⟦X⟧) : co
eff (n + 1) (φ * X) = coeff n φ
-/
theorem mul_X_cancel {φ ψ : R⟦X⟧} (h : φ * X = ψ * X) : φ = ψ := by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + 1)
/-
**PowerSeries.mul_X_injective** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：mul_X_injective : Function.Injective (· * X : R⟦X⟧ -> R⟦X⟧)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.mul_X_cancel`：mul_X_cancel {φ ψ : R⟦X⟧} (h : φ * X = ψ * X) 
: φ = ψ
-/
theorem mul_X_injective : Function.Injective (· * X : R⟦X⟧ → R⟦X⟧) :=
  fun _ _ ↦ mul_X_cancel
/-
**PowerSeries.mul_X_inj** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：mul_X_inj {φ ψ : R⟦X⟧} : φ * X = ψ * X ↔ φ = ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `PowerSeries.mul_X_injective`：mul_X_injective : Function.Injective (· * X
 : R⟦X⟧ -> R⟦X⟧)
-/
theorem mul_X_inj {φ ψ : R⟦X⟧} : φ * X = ψ * X ↔ φ = ψ :=
  mul_X_injective.eq_iff
/-
**PowerSeries.X_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_mul_cancel {φ ψ : R⟦X⟧} (h : X * φ = X * ψ) : φ = ψ
参数：h : X * φ = X * ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.ext_iff`：∀ {R : Type u_1} [inst : Semiring R] {φ ψ : PowerSe
ries R},   φ = ψ ↔ ∀ (n : ℕ), (PowerSeries.coeff n) φ = (PowerSeries.coeff n) ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PowerSeries.coeff_succ_X_mul`：coeff_succ_X_mul (n : Nat) (φ : R⟦X⟧) : co
eff (n + 1) (X * φ) = coeff n φ
-/
theorem X_mul_cancel {φ ψ : R⟦X⟧} (h : X * φ = X * ψ) : φ = ψ := by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + 1)
/-
**PowerSeries.X_mul_injective** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_mul_injective : Function.Injective (X * · : R⟦X⟧ -> R⟦X⟧)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.X_mul_cancel`：X_mul_cancel {φ ψ : R⟦X⟧} (h : X * φ = X * ψ) 
: φ = ψ
-/
theorem X_mul_injective : Function.Injective (X * · : R⟦X⟧ → R⟦X⟧) :=
  fun _ _ ↦ X_mul_cancel
/-
**PowerSeries.X_mul_inj** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_mul_inj {φ ψ : R⟦X⟧} : X * φ = X * ψ ↔ φ = ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `PowerSeries.X_mul_injective`：X_mul_injective : Function.Injective (X * ·
 : R⟦X⟧ -> R⟦X⟧)
-/
theorem X_mul_inj {φ ψ : R⟦X⟧} : X * φ = X * ψ ↔ φ = ψ :=
  X_mul_injective.eq_iff

@[simp]
/-
**PowerSeries.constantCoeff_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_C (a : R) : constantCoeff (C a) = a
参数：a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_C (a : R) : constantCoeff (C a) = a :=
  rfl

@[simp]
/-
**PowerSeries.constantCoeff_comp_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_comp_C : constantCoeff.comp C = RingHom.id R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_comp_C : constantCoeff.comp C = RingHom.id R :=
  rfl

@[simp]
/-
**PowerSeries.constantCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_zero : constantCoeff (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_zero : constantCoeff (R := R) 0 = 0 :=
  rfl

@[simp]
/-
**PowerSeries.constantCoeff_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_one : constantCoeff (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_one : constantCoeff (R := R) 1 = 1 :=
  rfl

@[simp]
/-
**PowerSeries.constantCoeff_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_X : constantCoeff (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_zero_X`：coeff_zero_X (s : σ) : coeff (0 : σ ->₀ Nat)
 (X s : MvPowerSeries σ R) = 0
-/
theorem constantCoeff_X : constantCoeff (R := R) X = 0 :=
  MvPowerSeries.coeff_zero_X _

@[simp]
/-
**PowerSeries.constantCoeff_mk** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_mk {f : Nat -> R} : constantCoeff (mk f) = f 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_mk {f : ℕ → R} : constantCoeff (mk f) = f 0 := rfl
/-
**PowerSeries.coeff_zero_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_zero_mul_X (φ : R⟦X⟧) : coeff 0 (φ * X) = 0
参数：φ : R⟦X⟧。
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
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `PowerSeries.constantCoeff_X`：constantCoeff_X : constantCoeff (R
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_zero_mul_X (φ : R⟦X⟧) : coeff 0 (φ * X) = 0 := by simp
/-
**PowerSeries.coeff_zero_X_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_zero_X_mul (φ : R⟦X⟧) : coeff 0 (X * φ) = 0
参数：φ : R⟦X⟧。
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
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `PowerSeries.constantCoeff_X`：constantCoeff_X : constantCoeff (R
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_zero_X_mul (φ : R⟦X⟧) : coeff 0 (X * φ) = 0 := by simp
/-
**PowerSeries.constantCoeff_surj** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_surj : Function.Surjective (constantCoeff (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.constantCoeff_C`：constantCoeff_C (a : R) : constantCoeff (C 
a) = a
-/
theorem constantCoeff_surj : Function.Surjective (constantCoeff (R := R)) :=
  fun r => ⟨C r, constantCoeff_C r⟩

-- The following section duplicates the API of `Mathlib.Data.Polynomial.Coeff` and should attempt
-- to keep up to date with that
section

/-
**PowerSeries.coeff_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_C_mul_X_pow (x : R) (k n : Nat) : coeff n (C x * X ^ k : R⟦X⟧) = if 
n = k then x else 0
参数：x : R；k n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.X_pow_eq`：X_pow_eq (n : Nat) : (X : R⟦X⟧) ^ n = monomial n 1
· 使用定理 `PowerSeries.coeff_C_mul`：coeff_C_mul (n : Nat) (φ : R⟦X⟧) (a : R) : coef
f n (C a * φ) = a * coeff n φ
· 使用定理 `PowerSeries.coeff_monomial`：coeff_monomial (m n : Nat) (a : R) : coeff m
 (monomial n a) = if m = n then a else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_C_mul_X_pow (x : R) (k n : ℕ) :
    coeff n (C x * X ^ k : R⟦X⟧) = if n = k then x else 0 := by
  simp [X_pow_eq, coeff_monomial]

@[simp]
/-
**PowerSeries.coeff_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_mul_X_pow (p : R⟦X⟧) (n d : Nat) : coeff (d + n) (p * X ^ n) = coeff
 d p
参数：p : R⟦X⟧；n d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `PowerSeries.coeff_X_pow`：coeff_X_pow (m n : Nat) : coeff m ((X : R⟦X⟧) ^
 n) = if m = n then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `add_right_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd 
G] {a b c : G}, b + a = c + a ↔ b = c
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
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem coeff_mul_X_pow (p : R⟦X⟧) (n d : ℕ) :
    coeff (d + n) (p * X ^ n) = coeff d p := by
  rw [coeff_mul, Finset.sum_eq_single (d, n), coeff_X_pow, if_pos rfl, mul_one]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow, if_neg, mul_zero]
    rintro rfl
    apply h2
    rw [mem_antidiagonal, add_right_cancel_iff] at h1
    subst h1
    rfl
  · exact fun h1 => (h1 (mem_antidiagonal.2 rfl)).elim

@[simp]
/-
**PowerSeries.coeff_X_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_X_pow_mul (p : R⟦X⟧) (n d : Nat) : coeff (d + n) (X ^ n * p) = coeff
 d p
参数：p : R⟦X⟧；n d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `PowerSeries.coeff_X_pow`：coeff_X_pow (m n : Nat) : coeff m ((X : R⟦X⟧) ^
 n) = if m = n then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `add_right_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd 
G] {a b c : G}, b + a = c + a ↔ b = c
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
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem coeff_X_pow_mul (p : R⟦X⟧) (n d : ℕ) :
    coeff (d + n) (X ^ n * p) = coeff d p := by
  rw [coeff_mul, Finset.sum_eq_single (n, d), coeff_X_pow, if_pos rfl, one_mul]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow, if_neg, zero_mul]
    rintro rfl
    apply h2
    rw [mem_antidiagonal, add_comm, add_right_cancel_iff] at h1
    subst h1
    rfl
  · rw [add_comm]
    exact fun h1 => (h1 (mem_antidiagonal.2 rfl)).elim
/-
**PowerSeries.mul_X_pow_cancel** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：mul_X_pow_cancel {k : Nat} {φ ψ : R⟦X⟧} (h : φ * X ^ k = ψ * X ^ k) : φ = 
ψ
参数：h : φ * X ^ k = ψ * X ^ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.ext_iff`：∀ {R : Type u_1} [inst : Semiring R] {φ ψ : PowerSe
ries R},   φ = ψ ↔ ∀ (n : ℕ), (PowerSeries.coeff n) φ = (PowerSeries.coeff n) ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PowerSeries.coeff_mul_X_pow`：coeff_mul_X_pow (p : R⟦X⟧) (n d : Nat) : co
eff (d + n) (p * X ^ n) = coeff d p
-/
theorem mul_X_pow_cancel {k : ℕ} {φ ψ : R⟦X⟧} (h : φ * X ^ k = ψ * X ^ k) :
    φ = ψ := by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + k)
/-
**PowerSeries.mul_X_pow_injective** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：mul_X_pow_injective {k : Nat} : Function.Injective (· * X ^ k : R⟦X⟧ -> R⟦
X⟧)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.mul_X_pow_cancel`：mul_X_pow_cancel {k : Nat} {φ ψ : R⟦X⟧} (h
 : φ * X ^ k = ψ * X ^ k) : φ = ψ
-/
theorem mul_X_pow_injective {k : ℕ} : Function.Injective (· * X ^ k : R⟦X⟧ → R⟦X⟧) :=
  fun _ _ ↦ mul_X_pow_cancel
/-
**PowerSeries.mul_X_pow_inj** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：mul_X_pow_inj {k : Nat} {φ ψ : R⟦X⟧} : φ * X ^ k = ψ * X ^ k ↔ φ = ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `PowerSeries.mul_X_pow_injective`：mul_X_pow_injective {k : Nat} : Functio
n.Injective (· * X ^ k : R⟦X⟧ -> R⟦X⟧)
-/
theorem mul_X_pow_inj {k : ℕ} {φ ψ : R⟦X⟧} :
    φ * X ^ k = ψ * X ^ k ↔ φ = ψ :=
  mul_X_pow_injective.eq_iff
/-
**PowerSeries.X_pow_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_pow_mul_cancel {k : Nat} {φ ψ : R⟦X⟧} (h : X ^ k * φ = X ^ k * ψ) : φ = 
ψ
参数：h : X ^ k * φ = X ^ k * ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.ext_iff`：∀ {R : Type u_1} [inst : Semiring R] {φ ψ : PowerSe
ries R},   φ = ψ ↔ ∀ (n : ℕ), (PowerSeries.coeff n) φ = (PowerSeries.coeff n) ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PowerSeries.coeff_X_pow_mul`：coeff_X_pow_mul (p : R⟦X⟧) (n d : Nat) : co
eff (d + n) (X ^ n * p) = coeff d p
-/
theorem X_pow_mul_cancel {k : ℕ} {φ ψ : R⟦X⟧} (h : X ^ k * φ = X ^ k * ψ) :
    φ = ψ := by
  rw [PowerSeries.ext_iff] at h ⊢
  intro n
  simpa using h (n + k)
/-
**PowerSeries.X_pow_mul_injective** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_pow_mul_injective {k : Nat} : Function.Injective (X ^ k * · : R⟦X⟧ -> R⟦
X⟧)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.X_pow_mul_cancel`：X_pow_mul_cancel {k : Nat} {φ ψ : R⟦X⟧} (h
 : X ^ k * φ = X ^ k * ψ) : φ = ψ
-/
theorem X_pow_mul_injective {k : ℕ} : Function.Injective (X ^ k * · : R⟦X⟧ → R⟦X⟧) :=
  fun _ _ ↦ X_pow_mul_cancel
/-
**PowerSeries.X_pow_mul_inj** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_pow_mul_inj {k : Nat} {φ ψ : R⟦X⟧} : X ^ k * φ = X ^ k * ψ ↔ φ = ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `PowerSeries.X_pow_mul_injective`：X_pow_mul_injective {k : Nat} : Functio
n.Injective (X ^ k * · : R⟦X⟧ -> R⟦X⟧)
-/
theorem X_pow_mul_inj {k : ℕ} {φ ψ : R⟦X⟧} :
    X ^ k * φ = X ^ k * ψ ↔ φ = ψ :=
  X_pow_mul_injective.eq_iff
/-
**PowerSeries.coeff_mul_X_pow'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_mul_X_pow' (p : R⟦X⟧) (n d : Nat) : coeff d (p * X ^ n) = ite (n <= 
d) (coeff (d - n) p) 0
参数：p : R⟦X⟧；n d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `PowerSeries.coeff_mul_X_pow`：coeff_mul_X_pow (p : R⟦X⟧) (n d : Nat) : co
eff (d + n) (p * X ^ n) = coeff d p
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `PowerSeries.coeff_X_pow`：coeff_X_pow (m n : Nat) : coeff m ((X : R⟦X⟧) ^
 n) = if m = n then 1 else 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_of_add_le_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] 
[CanonicallyOrderedAdd α] {a b c : α}, a + b ≤ c → b ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem coeff_mul_X_pow' (p : R⟦X⟧) (n d : ℕ) :
    coeff d (p * X ^ n) = ite (n ≤ d) (coeff (d - n) p) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow, if_neg, mul_zero]
    exact ((le_of_add_le_right (mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h).ne
/-
**PowerSeries.coeff_X_pow_mul'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_X_pow_mul' (p : R⟦X⟧) (n d : Nat) : coeff d (X ^ n * p) = ite (n <= 
d) (coeff (d - n) p) 0
参数：p : R⟦X⟧；n d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `PowerSeries.coeff_X_pow_mul`：coeff_X_pow_mul (p : R⟦X⟧) (n d : Nat) : co
eff (d + n) (X ^ n * p) = coeff d p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `PowerSeries.coeff_X_pow`：coeff_X_pow (m n : Nat) : coeff m ((X : R⟦X⟧) ^
 n) = if m = n then 1 else 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_of_add_le_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] 
[CanonicallyOrderedAdd α] {a b c : α}, a + b ≤ c → b ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem coeff_X_pow_mul' (p : R⟦X⟧) (n d : ℕ) :
    coeff d (X ^ n * p) = ite (n ≤ d) (coeff (d - n) p) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_X_pow_mul]
    simp
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow, if_neg, zero_mul]
    have := mem_antidiagonal.mp hx
    rw [add_comm] at this
    exact ((le_of_add_le_right this.le).trans_lt <| not_le.mp h).ne

end

/-- If a formal power series is invertible, then so is its constant coefficient. -/
/-
**PowerSeries.isUnit_constantCoeff** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：isUnit_constantCoeff (φ : R⟦X⟧) (h : IsUnit φ) : IsUnit (constantCoeff φ)
参数：φ : R⟦X⟧；h : IsUnit φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.isUnit_constantCoeff`：isUnit_constantCoeff (φ : MvPowerSer
ies σ R) (h : IsUnit φ) : IsUnit (constantCoeff φ)

--- 原说明 ---
If a formal power series is invertible, then so is its constant coefficient.
-/
theorem isUnit_constantCoeff (φ : R⟦X⟧) (h : IsUnit φ) : IsUnit (constantCoeff φ) :=
  MvPowerSeries.isUnit_constantCoeff φ h

/-- Split off the constant coefficient. -/
/-
**PowerSeries.eq_shift_mul_X_add_const** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：eq_shift_mul_X_add_const (φ : R⟦X⟧) : φ = (mk fun p => coeff (p + 1) φ) * 
X + C (constantCoeff φ)
参数：φ : R⟦X⟧。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `PowerSeries.constantCoeff_X`：constantCoeff_X : constantCoeff (R
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `PowerSeries.coeff_succ_mul_X`：coeff_succ_mul_X (n : Nat) (φ : R⟦X⟧) : co
eff (n + 1) (φ * X) = coeff n φ
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `PowerSeries.coeff_C`：coeff_C (n : Nat) (a : R) : coeff n (C a : R⟦X⟧) = 
if n = 0 then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
Split off the constant coefficient.
-/
theorem eq_shift_mul_X_add_const (φ : R⟦X⟧) :
    φ = (mk fun p => coeff (p + 1) φ) * X + C (constantCoeff φ) := by
  ext (_ | n)
  · simp
  · simp only [coeff_succ_mul_X, coeff_mk, map_add, coeff_C, n.succ_ne_zero,
      if_false, add_zero]

/-- Split off the constant coefficient. -/
/-
**PowerSeries.eq_X_mul_shift_add_const** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：eq_X_mul_shift_add_const (φ : R⟦X⟧) : φ = (X * mk fun p => coeff (p + 1) φ
) + C (constantCoeff φ)
参数：φ : R⟦X⟧。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `PowerSeries.constantCoeff_X`：constantCoeff_X : constantCoeff (R
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `PowerSeries.coeff_succ_X_mul`：coeff_succ_X_mul (n : Nat) (φ : R⟦X⟧) : co
eff (n + 1) (X * φ) = coeff n φ
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `PowerSeries.coeff_C`：coeff_C (n : Nat) (a : R) : coeff n (C a : R⟦X⟧) = 
if n = 0 then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
Split off the constant coefficient.
-/
theorem eq_X_mul_shift_add_const (φ : R⟦X⟧) :
    φ = (X * mk fun p => coeff (p + 1) φ) + C (constantCoeff φ) := by
  ext (_ | n)
  · simp
  · simp only [coeff_succ_X_mul, coeff_mk, map_add, coeff_C, n.succ_ne_zero,
      if_false, add_zero]

section Map

variable {S : Type*} {T : Type*} [Semiring S] [Semiring T]
variable (f : R →+* S) (g : S →+* T)

/-- The map between formal power series induced by a map on the coefficients. -/
/-
**PowerSeries.map** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：map : R⟦X⟧ ->+* S⟦X⟧
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map between formal power series induced by a map on the coefficients.
-/
def map : R⟦X⟧ →+* S⟦X⟧ :=
  MvPowerSeries.map f

@[simp]
/-
**PowerSeries.map_id** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_id : (map (RingHom.id R) : R⟦X⟧ -> R⟦X⟧) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_id : (map (RingHom.id R) : R⟦X⟧ → R⟦X⟧) = id :=
  rfl
/-
**PowerSeries.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_comp : map (g.comp f) = (map g).comp (map f)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp : map (g.comp f) = (map g).comp (map f) :=
  rfl

@[simp]
/-
**PowerSeries.coeff_map** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_map (n : Nat) (φ : R⟦X⟧) : coeff n (map f φ) = f (coeff n φ)
参数：n : Nat；φ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_map (n : ℕ) (φ : R⟦X⟧) : coeff n (map f φ) = f (coeff n φ) :=
  rfl

@[simp]
/-
**PowerSeries.map_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_C (r : R) : map f (C r) = C (f r)
参数：r : R。
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
· 使用定理 `PowerSeries.coeff_C`：coeff_C (n : Nat) (a : R) : coeff n (C a : R⟦X⟧) = 
if n = 0 then a else 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_C (r : R) : map f (C r) = C (f r) := by
  ext
  simp [coeff_C, apply_ite f]

@[simp]
/-
**PowerSeries.map_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_X : map f X = X
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
· 使用定理 `PowerSeries.coeff_X`：coeff_X (n : Nat) : coeff n (X : R⟦X⟧) = if n = 1 t
hen 1 else 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
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
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_X : map f X = X := by
  ext
  simp [coeff_X, apply_ite f]
/-
**PowerSeries.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_surjective (f : S ->+* T) (hf : Function.Surjective f) : Function.Surj
ective (PowerSeries.map f)
参数：f : S ->+* T；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem map_surjective (f : S →+* T) (hf : Function.Surjective f) :
    Function.Surjective (PowerSeries.map f) := by
  intro g
  use PowerSeries.mk fun k ↦ Function.surjInv hf (PowerSeries.coeff k g)
  ext k
  simp only [Function.surjInv, coeff_map, coeff_mk]
  exact Classical.choose_spec (hf (coeff k g))
/-
**PowerSeries.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_injective (f : S ->+* T) (hf : Function.Injective ⇑f) : Function.Injec
tive (PowerSeries.map f)
参数：f : S ->+* T；hf : Function.Injective ⇑f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coeff_map`：coeff_map (n : Nat) (φ : R⟦X⟧) : coeff n (map f φ
) = f (coeff n φ)
-/
theorem map_injective (f : S →+* T) (hf : Function.Injective ⇑f) :
    Function.Injective (PowerSeries.map f) := by
  intro u v huv
  ext k
  apply hf
  rw [← PowerSeries.coeff_map, ← PowerSeries.coeff_map, huv]

end Map

@[simp]
/-
**PowerSeries.map_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_eq_zero {R S : Type*} [DivisionSemiring R] [Semiring S] [Nontrivial S]
 (φ : R⟦X⟧) (f : R ->+* S) : φ.map f = 0 ↔ φ = 0
参数：φ : R⟦X⟧；f : R ->+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.map_eq_zero`：map_eq_zero {S : Type*} [DivisionSemiring R] 
[Semiring S] [Nontrivial S] (φ : MvPowerSeries σ R) (f : R ->+* S) : φ.map f = 0
 ↔ φ = 0
-/
theorem map_eq_zero {R S : Type*} [DivisionSemiring R] [Semiring S] [Nontrivial S] (φ : R⟦X⟧)
    (f : R →+* S) : φ.map f = 0 ↔ φ = 0 :=
  MvPowerSeries.map_eq_zero _ _
/-
**PowerSeries.X_pow_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_pow_dvd_iff {n : Nat} {φ : R⟦X⟧} : (X : R⟦X⟧) ^ n ∣ φ ↔ forall m, m < n 
-> coeff m φ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.unique_single`：unique_single [Unique α] (x : α ->₀ M) : x = sing
le default (x default)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `MvPowerSeries.X_pow_dvd_iff`：X_pow_dvd_iff {s : σ} {n : Nat} {φ : MvPowe
rSeries σ R} : (X s : MvPowerSeries σ R) ^ n ∣ φ ↔ forall m : σ ->₀ Nat, m s < n
 -> coeff m φ = 0
-/
theorem X_pow_dvd_iff {n : ℕ} {φ : R⟦X⟧} :
    (X : R⟦X⟧) ^ n ∣ φ ↔ ∀ m, m < n → coeff m φ = 0 := by
  convert! @MvPowerSeries.X_pow_dvd_iff Unit R _ () n φ
  constructor <;> intro h m hm
  · rw [Finsupp.unique_single m]
    convert! h _ hm
  · apply h
    simpa only [Finsupp.single_eq_same] using hm
/-
**PowerSeries.X_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_dvd_iff {φ : R⟦X⟧} : (X : R⟦X⟧) ∣ φ ↔ constantCoeff φ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `PowerSeries.X_pow_dvd_iff`：X_pow_dvd_iff {n : Nat} {φ : R⟦X⟧} : (X : R⟦X
⟧) ^ n ∣ φ ↔ forall m, m < n -> coeff m φ = 0
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff_apply`：coeff_zero_eq_constantCoe
ff_apply (φ : R⟦X⟧) : coeff 0 φ = constantCoeff φ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `Nat.le_of_succ_le_succ`：∀ {n m : ℕ}, n.succ ≤ m.succ → n ≤ m
-/
theorem X_dvd_iff {φ : R⟦X⟧} : (X : R⟦X⟧) ∣ φ ↔ constantCoeff φ = 0 := by
  rw [← pow_one (X : R⟦X⟧), X_pow_dvd_iff, ← coeff_zero_eq_constantCoeff_apply]
  constructor <;> intro h
  · exact h 0 zero_lt_one
  · intro m hm
    rwa [Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hm)]

end Semiring

section toSubring

variable [Ring R] (p : PowerSeries R) (T : Subring R) (hp : ∀ n, p.coeff n ∈ T)

/-- Given a formal power series `p` and a subring `T` that contains the
coefficients of `p`, return the corresponding formal power series
whose coefficients are in `T`. -/
/-
**PowerSeries.toSubring** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：toSubring : PowerSeries T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a formal power series `p` and a subring `T` that contains the
coefficients of `p`, return the corresponding formal power series
whose coefficients are in `T`.
-/
def toSubring : PowerSeries T := mk fun n => ⟨p.coeff n, hp n⟩

@[simp]
/-
**PowerSeries.coeff_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_toSubring {n : Nat} : (p.toSubring T hp).coeff n = p.coeff n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.toSubring.eq_1`：∀ {R : Type u_1} [inst : Ring R] (p : PowerS
eries R) (T : Subring R) (hp : ∀ (n : ℕ), (PowerSeries.coeff n) p ∈ T),   p.toSu
bring T hp = Pow…
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
-/
theorem coeff_toSubring {n : ℕ} : (p.toSubring T hp).coeff n = p.coeff n := by
  rw [toSubring, coeff_mk]

@[simp]
/-
**PowerSeries.constantCoeff_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_toSubring : (p.toSubring T hp).constantCoeff = p.constantCoe
ff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff_apply`：coeff_zero_eq_constantCoe
ff_apply (φ : R⟦X⟧) : coeff 0 φ = constantCoeff φ
-/
theorem constantCoeff_toSubring : (p.toSubring T hp).constantCoeff = p.constantCoeff :=
  coeff_zero_eq_constantCoeff_apply p

@[simp]
/-
**PowerSeries.map_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_toSubring : (p.toSubring T hp).map T.subtype = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_toSubring`：coeff_toSubring {n : Nat} : (p.toSubring T 
hp).coeff n = p.coeff n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_toSubring : (p.toSubring T hp).map T.subtype = p := ext fun n => by simp

end toSubring

section CommSemiring

variable [CommSemiring R]

open Finset Nat

/-- The ring homomorphism taking a power series `f(X)` to `f(aX)`. -/
/-
**PowerSeries.rescale** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：rescale (a : R) : R⟦X⟧ ->+* R⟦X⟧ where toFun f
参数：a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism taking a power series `f(X)` to `f(aX)`.
-/
noncomputable def rescale (a : R) : R⟦X⟧ →+* R⟦X⟧ where
  toFun f := PowerSeries.mk fun n => a ^ n * PowerSeries.coeff n f
  map_zero' := by
    ext
    simp only [map_zero, PowerSeries.coeff_mk, mul_zero]
  map_one' := by
    ext1
    simp only [mul_boole, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with h
    · rw [h, pow_zero a]
    rfl
  map_add' := by
    intros
    ext
    exact mul_add _ _ _
  map_mul' f g := by
    ext
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mul, Finset.mul_sum]
    apply sum_congr rfl
    simp only [coeff_mk, Prod.forall, mem_antidiagonal]
    intro b c H
    rw [← H, pow_add, mul_mul_mul_comm]

@[simp]
/-
**PowerSeries.coeff_rescale** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_rescale (f : R⟦X⟧) (a : R) (n : Nat) : coeff n (rescale a f) = a ^ n
 * coeff n f
参数：f : R⟦X⟧；a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
-/
theorem coeff_rescale (f : R⟦X⟧) (a : R) (n : ℕ) :
    coeff n (rescale a f) = a ^ n * coeff n f :=
  coeff_mk n (fun n ↦ a ^ n * coeff n f)

@[simp]
/-
**PowerSeries.rescale_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：rescale_zero : rescale 0 = (C (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_C`：coeff_C (n : Nat) (a : R) : coeff n (C a : R⟦X⟧) = 
if n = 0 then a else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem rescale_zero : rescale 0 = (C (R := R)).comp constantCoeff := by
  ext x n
  simp only [Function.comp_apply, RingHom.coe_comp, rescale, RingHom.coe_mk,
    coeff_C]
  split_ifs with h <;> simp [h]
/-
**PowerSeries.rescale_zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：rescale_zero_apply (f : R⟦X⟧) : rescale 0 f = C (constantCoeff f)
参数：f : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.rescale_zero`：rescale_zero : rescale 0 = (C (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rescale_zero_apply (f : R⟦X⟧) : rescale 0 f = C (constantCoeff f) := by simp

@[simp]
/-
**PowerSeries.rescale_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：rescale_one : rescale 1 = RingHom.id R⟦X⟧
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_rescale`：coeff_rescale (f : R⟦X⟧) (a : R) (n : Nat) : 
coeff n (rescale a f) = a ^ n * coeff n f
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rescale_one : rescale 1 = RingHom.id R⟦X⟧ := by
  ext
  simp [coeff_rescale]
/-
**PowerSeries.rescale_mk** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：rescale_mk (f : Nat -> R) (a : R) : rescale a (mk f) = mk fun n : Nat => a
 ^ n * f n
参数：f : Nat -> R；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_rescale`：coeff_rescale (f : R⟦X⟧) (a : R) (n : Nat) : 
coeff n (rescale a f) = a ^ n * coeff n f
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
-/
theorem rescale_mk (f : ℕ → R) (a : R) : rescale a (mk f) = mk fun n : ℕ => a ^ n * f n := by
  ext
  rw [coeff_rescale, coeff_mk, coeff_mk]
/-
**PowerSeries.rescale_rescale** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：rescale_rescale (f : R⟦X⟧) (a b : R) : rescale b (rescale a f) = rescale (
a * b) f
参数：f : R⟦X⟧；a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PowerSeries.coeff_rescale`：coeff_rescale (f : R⟦X⟧) (a : R) (n : Nat) : 
coeff n (rescale a f) = a ^ n * coeff n f
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem rescale_rescale (f : R⟦X⟧) (a b : R) :
    rescale b (rescale a f) = rescale (a * b) f := by
  ext n
  simp_rw [coeff_rescale]
  rw [mul_pow, mul_comm _ (b ^ n), mul_assoc]
/-
**PowerSeries.rescale_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：rescale_mul (a b : R) : rescale (a * b) = (rescale b).comp (rescale a)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_rescale`：coeff_rescale (f : R⟦X⟧) (a : R) (n : Nat) : 
coeff n (rescale a f) = a ^ n * coeff n f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rescale_mul (a b : R) : rescale (a * b) = (rescale b).comp (rescale a) := by
  ext
  simp [← rescale_rescale]
/-
**PowerSeries.rescale_map** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：rescale_map {S : Type*} [CommSemiring S] (φ : R ->+* S) (r : R) (f : R⟦X⟧)
 : rescale (φ r) (f.map φ) = (rescale r f).map (φ : R ->+* S)
参数：φ : R ->+* S；r : R；f : R⟦X⟧。
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
· 使用定理 `PowerSeries.coeff_rescale`：coeff_rescale (f : R⟦X⟧) (a : R) (n : Nat) : 
coeff n (rescale a f) = a ^ n * coeff n f
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rescale_map {S : Type*} [CommSemiring S] (φ : R →+* S) (r : R) (f : R⟦X⟧) :
    rescale (φ r) (f.map φ) = (rescale r f).map (φ : R →+* S) := by
  ext n
  simp [coeff_rescale, coeff_map, map_mul, map_pow]
/-
**PowerSeries.rescale_algebraMap_map** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：rescale_algebraMap_map {A S : Type*} [CommSemiring A] [Algebra A R] [CommS
emiring S] [Algebra A S] (φ : R ->ₐ[A] S) (a : A) (f : R⟦X⟧) : rescale (algebraM
ap A S a) (f.map φ) = (rescale (algebraMap A R a) f).map φ
参数：φ : R ->ₐ[A] S；a : A；f : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PowerSeries.rescale_map`：rescale_map {S : Type*} [CommSemiring S] (φ : R
 ->+* S) (r : R) (f : R⟦X⟧) : rescale (φ r) (f.map φ) = (rescale r f).map (φ : R
 ->+* S)
-/
theorem rescale_algebraMap_map {A S : Type*} [CommSemiring A] [Algebra A R] [CommSemiring S]
    [Algebra A S] (φ : R →ₐ[A] S) (a : A) (f : R⟦X⟧) :
    rescale (algebraMap A S a) (f.map φ) = (rescale (algebraMap A R a) f).map φ := by
  convert! rescale_map (φ : R →+* S) _ _
  simp

end CommSemiring

section CommSemiring

open Finset.HasAntidiagonal Finset

variable {R : Type*} [CommSemiring R] {ι : Type*}

/-- Coefficients of a product of power series -/
/-
**PowerSeries.coeff_prod** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_prod [DecidableEq ι] (f : ι -> PowerSeries R) (d : Nat) (s : Finset 
ι) : coeff d (∏ j in s, f j) = ∑ l in finsuppAntidiag s d, ∏ i in s, coeff (l i)
 (f i)
参数：f : ι -> PowerSeries R；d : Nat；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_prod`：coeff_prod [DecidableEq ι] [DecidableEq σ] (f 
: ι -> MvPowerSeries σ R) (d : σ ->₀ Nat) (s : Finset ι) : coeff d (∏ j in s, f 
j) = ∑ l in fi…
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.uniqueAddEquiv_symm_apply`：∀ {ι : Type u_1} {M : Type u_3} [inst
 : AddZeroClass M] (i : ι) [inst_1 : Subsingleton ι] (b : M),   (Finsupp.uniqueA
ddEquiv i).symm b = fun…
· 使用引理 `Finset.mapRange_finsuppAntidiag_eq`：mapRange_finsuppAntidiag_eq {e : μ ≃
+ μ'} {s : Finset ι} {n : μ} : (finsuppAntidiag s n).map (mapRange.addEquiv e).t
oEmbedding = finsuppAnti…
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …

--- 原说明 ---
Coefficients of a product of power series
-/
theorem coeff_prod [DecidableEq ι] (f : ι → PowerSeries R) (d : ℕ) (s : Finset ι) :
    coeff d (∏ j ∈ s, f j) = ∑ l ∈ finsuppAntidiag s d, ∏ i ∈ s, coeff (l i) (f i) := by
  simp only [coeff]
  rw [MvPowerSeries.coeff_prod, ← Finsupp.uniqueAddEquiv_symm_apply _ d,
    ← mapRange_finsuppAntidiag_eq, sum_map]
  rfl
/-
**PowerSeries.prod_monomial** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：prod_monomial (f : ι -> Nat) (g : ι -> R) (s : Finset ι) : ∏ i in s, monom
ial (f i) (g i) = monomial (∑ i in s, f i) (∏ i in s, g i)
参数：f : ι -> Nat；g : ι -> R；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_finsetSum`：single_finsetSum [AddCommMonoid M] (s : Finset
 ι) (f : ι -> M) (a : α) : single a (∑ b in s, f b) = ∑ b in s, single a (f b)
· 使用定理 `MvPowerSeries.prod_monomial`：prod_monomial (f : ι -> σ ->₀ Nat) (g : ι -
> R) (s : Finset ι) : ∏ i in s, monomial (f i) (g i) = monomial (∑ i in s, f i) 
(∏ i in s, g i)
-/
theorem prod_monomial (f : ι → ℕ) (g : ι → R) (s : Finset ι) :
    ∏ i ∈ s, monomial (f i) (g i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, g i) := by
  simpa [monomial, Finsupp.single_finsetSum] using
    MvPowerSeries.prod_monomial (fun i ↦ Finsupp.single () (f i)) g s
/-
**PowerSeries.monomial_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：monomial_pow (m : Nat) (a : R) (n : Nat) : (monomial m a) ^ n = monomial (
n * m) (a ^ n)
参数：m : Nat；a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `MvPowerSeries.monomial_pow`：monomial_pow (m : σ ->₀ Nat) (a : R) (n : Na
t) : (monomial m a) ^ n = monomial (n • m) (a ^ n)
-/
theorem monomial_pow (m : ℕ) (a : R) (n : ℕ) : (monomial m a) ^ n = monomial (n * m) (a ^ n) := by
  simpa [monomial] using MvPowerSeries.monomial_pow (Finsupp.single () m) a n

/-- The `n`-th coefficient of the `k`-th power of a power series. -/
/-
**PowerSeries.coeff_pow** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_pow (k n : Nat) (φ : R⟦X⟧) : coeff n (φ ^ k) = ∑ l in finsuppAntidia
g (range k) n, ∏ i in range k, coeff (l i) φ
参数：k n : Nat；φ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_range_induction`：prod_range_induction (f s : Nat -> M) (base
 : s 0 = 1) (n : Nat) (step : forall k < n, s (k + 1) = s k * f k) : ∏ k in Fins
et.range n, f k =…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coeff_prod`：coeff_prod [DecidableEq ι] (f : ι -> PowerSeries
 R) (d : Nat) (s : Finset ι) : coeff d (∏ j in s, f j) = ∑ l in finsuppAntidiag 
s d, ∏ i in …

--- 原说明 ---
The `n`-th coefficient of the `k`-th power of a power series.
-/
lemma coeff_pow (k n : ℕ) (φ : R⟦X⟧) :
    coeff n (φ ^ k) = ∑ l ∈ finsuppAntidiag (range k) n, ∏ i ∈ range k, coeff (l i) φ := by
  have h₁ (i : ℕ) : Function.const ℕ φ i = φ := rfl
  have h₂ (i : ℕ) : ∏ j ∈ range i, Function.const ℕ φ j = φ ^ i := by
    apply prod_range_induction (fun _ => φ) (fun i => φ ^ i) rfl i (fun _ => congrFun rfl)
  rw [← h₂, ← h₁ k]
  apply coeff_prod (f := Function.const ℕ φ) (d := n) (s := range k)

/-- First coefficient of the product of two power series. -/
/-
**PowerSeries.coeff_one_mul** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_one_mul (φ ψ : R⟦X⟧) : coeff 1 (φ * ψ) = coeff 1 φ * constantCoeff ψ
 + coeff 1 ψ * constantCoeff φ
参数：φ ψ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
First coefficient of the product of two power series.
-/
lemma coeff_one_mul (φ ψ : R⟦X⟧) : coeff 1 (φ * ψ) =
    coeff 1 φ * constantCoeff ψ + coeff 1 ψ * constantCoeff φ := by
  have : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by exact rfl
  rw [coeff_mul, this, Finset.sum_insert, Finset.sum_singleton, coeff_zero_eq_constantCoeff,
    mul_comm, add_comm]
  simp

/-- First coefficient of the `n`-th power of a power series. -/
/-
**PowerSeries.coeff_one_pow** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_one_pow (n : Nat) (φ : R⟦X⟧) : coeff 1 (φ ^ n) = n * coeff 1 φ * (co
nstantCoeff φ) ^ (n - 1)
参数：n : Nat；φ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `PowerSeries.coeff_one`：coeff_one (n : Nat) : coeff n (1 : R⟦X⟧) = if n =
 0 then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
First coefficient of the `n`-th power of a power series.
-/
lemma coeff_one_pow (n : ℕ) (φ : R⟦X⟧) :
    coeff 1 (φ ^ n) = n * coeff 1 φ * (constantCoeff φ) ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with (rfl | hn)
  · simp
  induction n with
  | zero => lia
  | succ n' ih =>
      have h₁ (m : ℕ) : φ ^ (m + 1) = φ ^ m * φ := by exact rfl
      have h₂ : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by exact rfl
      rw [h₁, coeff_mul, h₂, Finset.sum_insert, Finset.sum_singleton]
      · simp only [coeff_zero_eq_constantCoeff, map_pow, Nat.cast_add, Nat.cast_one,
          add_tsub_cancel_right]
        have h₀ : n' = 0 ∨ 1 ≤ n' := by lia
        rcases h₀ with h' | h'
        · by_contra h''
          rw [h'] at h''
          simp only [pow_zero, one_mul, coeff_one, one_ne_zero, ↓reduceIte, zero_mul, add_zero,
            mul_one] at h''
          norm_num at h''
        · rw [ih]
          · conv => lhs; arg 2; rw [mul_comm, ← mul_assoc]
            move_mul [← constantCoeff φ ^ (n' - 1)]
            conv => enter [1, 2, 1, 1, 2]; rw [← pow_one (a := constantCoeff φ)]
            rw [← pow_add (a := constantCoeff φ)]
            conv => enter [1, 2, 1, 1]; rw [Nat.sub_add_cancel h']
            ring
          exact h'
      · decide

end CommSemiring

section CommRing

variable {A : Type*} [CommRing A]

/-
**PowerSeries.not_isField** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：not_isField : ¬IsField A⟦X⟧
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isField_of_subsingleton`：not_isField_of_subsingleton (R : Type u) [S
emiring R] [Subsingleton R] : ¬IsField R
· 使用定理 `PowerSeries.instSubsingleton`：∀ {R : Type u_1} [Semiring R] [Subsingleto
n R], Subsingleton (PowerSeries R)
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top`：not_isField_iff_exi
sts_ideal_bot_lt_and_lt_top [Nontrivial R] : ¬IsField R ↔ exists I : Ideal R, ⊥ 
< I ∧ I < ⊤
· 使用定理 `MvPowerSeries.instNontrivial`：∀ {σ : Type u_1} {R : Type u_2} [Nontrivia
l R], Nontrivial (MvPowerSeries σ R)
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `PowerSeries.X_ne_zero`：X_ne_zero [Nontrivial R] : (X : R⟦X⟧) != 0
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `PowerSeries.X_dvd_iff`：X_dvd_iff {φ : R⟦X⟧} : (X : R⟦X⟧) ∣ φ ↔ constantC
oeff φ = 0
· 使用定理 `PowerSeries.constantCoeff_one`：constantCoeff_one : constantCoeff (R
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem not_isField : ¬IsField A⟦X⟧ := by
  by_cases hA : Subsingleton A
  · exact not_isField_of_subsingleton _
  · nontriviality A
    rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
    use Ideal.span {X}
    constructor
    · rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      exact X_ne_zero
    · rw [lt_top_iff_ne_top, Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton,
        X_dvd_iff, constantCoeff_one]
      exact one_ne_zero

@[simp]
/-
**PowerSeries.rescale_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：rescale_X (a : A) : rescale a X = C a * X
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PowerSeries.coeff_rescale`：coeff_rescale (f : R⟦X⟧) (a : R) (n : Nat) : 
coeff n (rescale a f) = a ^ n * coeff n f
· 使用定理 `PowerSeries.coeff_X`：coeff_X (n : Nat) : coeff n (X : R⟦X⟧) = if n = 1 t
hen 1 else 0
· 使用定理 `PowerSeries.coeff_C_mul`：coeff_C_mul (n : Nat) (φ : R⟦X⟧) (a : R) : coef
f n (C a * φ) = a * coeff n φ
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem rescale_X (a : A) : rescale a X = C a * X := by
  ext
  simp only [coeff_rescale, coeff_C_mul, coeff_X]
  split_ifs with h <;> simp [h]
/-
**PowerSeries.rescale_neg_one_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：rescale_neg_one_X : rescale (-1 : A) X = -X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.rescale_X`：rescale_X (a : A) : rescale a X = C a * X
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
-/
theorem rescale_neg_one_X : rescale (-1 : A) X = -X := by
  rw [rescale_X, map_neg, map_one, neg_one_mul]

/-- The ring homomorphism taking a power series `f(X)` to `f(-X)`. -/
/-
**PowerSeries.evalNegHom** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：evalNegHom : A⟦X⟧ ->+* A⟦X⟧
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism taking a power series `f(X)` to `f(-X)`.
-/
noncomputable def evalNegHom : A⟦X⟧ →+* A⟦X⟧ :=
  rescale (-1 : A)

@[simp]
/-
**PowerSeries.evalNegHom_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：evalNegHom_X : evalNegHom (X : A⟦X⟧) = -X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.rescale_neg_one_X`：rescale_neg_one_X : rescale (-1 : A) X = 
-X
-/
theorem evalNegHom_X : evalNegHom (X : A⟦X⟧) = -X :=
  rescale_neg_one_X

end CommRing

section Algebra

variable {A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-
**PowerSeries.C_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：C_eq_algebraMap {r : R} : C r = (algebraMap R R⟦X⟧) r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_eq_algebraMap {r : R} : C r = (algebraMap R R⟦X⟧) r :=
  rfl
/-
**PowerSeries.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：algebraMap_apply {r : R} : algebraMap R A⟦X⟧ r = C (algebraMap R A r)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.algebraMap_apply`：algebraMap_apply {r : R} : algebraMap R 
(MvPowerSeries σ A) r = C (algebraMap R A r)
-/
theorem algebraMap_apply {r : R} : algebraMap R A⟦X⟧ r = C (algebraMap R A r) :=
  MvPowerSeries.algebraMap_apply
/-
**PowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Nontrivial (Subalgebra R R⟦X⟧) :=
  { (inferInstance : Nontrivial <| Subalgebra R <| MvPowerSeries Unit R) with }

/-- Change of coefficients in power series, as an `AlgHom` -/
/-
**PowerSeries.mapAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：mapAlgHom (φ : A ->ₐ[R] B) : PowerSeries A ->ₐ[R] PowerSeries B
参数：φ : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change of coefficients in power series, as an `AlgHom`
-/
def mapAlgHom (φ : A →ₐ[R] B) :
    PowerSeries A →ₐ[R] PowerSeries B :=
  MvPowerSeries.mapAlgHom φ
/-
**PowerSeries.mapAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：mapAlgHom_apply (φ : A ->ₐ[R] B) (f : A⟦X⟧) : mapAlgHom φ f = f.map φ
参数：φ : A ->ₐ[R] B；f : A⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.mapAlgHom_apply`：mapAlgHom_apply (φ : A ->ₐ[R] B) (f : MvP
owerSeries σ A) : mapAlgHom (σ
-/
theorem mapAlgHom_apply (φ : A →ₐ[R] B) (f : A⟦X⟧) :
    mapAlgHom φ f = f.map φ :=
  MvPowerSeries.mapAlgHom_apply φ f

end Algebra

end PowerSeries

namespace Polynomial

open Finsupp Polynomial

section Semiring
variable {R : Type*} [Semiring R] (φ ψ : R[X])

/-- The natural inclusion from polynomials into formal power series. -/
@[coe]
/-
**Polynomial.toPowerSeries** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：toPowerSeries : R[X] -> PowerSeries R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion from polynomials into formal power series.
-/
def toPowerSeries : R[X] → PowerSeries R := fun φ =>
  PowerSeries.mk fun n => coeff φ n

/-- The natural inclusion from polynomials into formal power series. -/
/-
**Polynomial.coeToPowerSeries** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：coeToPowerSeries : Coe R[X] (PowerSeries R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion from polynomials into formal power series.
-/
instance coeToPowerSeries : Coe R[X] (PowerSeries R) :=
  ⟨toPowerSeries⟩
/-
**Polynomial.coe_def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_def : (φ : PowerSeries R) = PowerSeries.mk (coeff φ)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_def : (φ : PowerSeries R) = PowerSeries.mk (coeff φ) :=
  rfl

@[simp, norm_cast]
/-
**Polynomial.coeff_coe** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
theorem coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n :=
  congr_arg (coeff φ) Finsupp.single_eq_same

@[simp, norm_cast]
/-
**Polynomial.coe_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_monomial (n : Nat) (a : R) : (monomial n a : PowerSeries R) = PowerSer
ies.monomial n a
参数：n : Nat；a : R。
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
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `PowerSeries.coeff_monomial`：coeff_monomial (m n : Nat) (a : R) : coeff m
 (monomial n a) = if m = n then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_monomial (n : ℕ) (a : R) :
    (monomial n a : PowerSeries R) = PowerSeries.monomial n a := by
  ext
  simp [coeff_coe, PowerSeries.coeff_monomial, Polynomial.coeff_monomial, eq_comm]

@[simp, norm_cast]
/-
**Polynomial.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_zero : ((0 : R[X]) : PowerSeries R) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : R[X]) : PowerSeries R) = 0 :=
  rfl

@[simp, norm_cast]
/-
**Polynomial.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_one : ((1 : R[X]) : PowerSeries R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coe_monomial`：coe_monomial (n : Nat) (a : R) : (monomial n a 
: PowerSeries R) = PowerSeries.monomial n a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.monomial_zero_eq_C_apply`：monomial_zero_eq_C_apply (a : R) :
 monomial 0 a = C a
-/
theorem coe_one : ((1 : R[X]) : PowerSeries R) = 1 := by
  have := coe_monomial 0 (1 : R)
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]
/-
**Polynomial.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_add : ((φ + ψ : R[X]) : PowerSeries R) = φ + ψ
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
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_add : ((φ + ψ : R[X]) : PowerSeries R) = φ + ψ := by
  ext
  simp

@[simp, norm_cast]
/-
**Polynomial.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_mul : ((φ * ψ : R[X]) : PowerSeries R) = φ * ψ
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
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_mul : ((φ * ψ : R[X]) : PowerSeries R) = φ * ψ :=
  PowerSeries.ext fun n => by simp only [coeff_coe, PowerSeries.coeff_mul, coeff_mul]

@[simp, norm_cast]
/-
**Polynomial.coe_smul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：coe_smul (φ : R[X]) (r : R) : (r • φ : Polynomial R) = r • (φ : PowerSerie
s R)
参数：φ : R[X]；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_smul (φ : R[X]) (r : R) :
    (r • φ : Polynomial R) = r • (φ : PowerSeries R) := rfl

@[simp, norm_cast]
/-
**Polynomial.coe_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_C (a : R) : ((C a : R[X]) : PowerSeries R) = PowerSeries.C a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coe_monomial`：coe_monomial (n : Nat) (a : R) : (monomial n a 
: PowerSeries R) = PowerSeries.monomial n a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.monomial_zero_eq_C_apply`：monomial_zero_eq_C_apply (a : R) :
 monomial 0 a = C a
-/
theorem coe_C (a : R) : ((C a : R[X]) : PowerSeries R) = PowerSeries.C a := by
  have := coe_monomial 0 a
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]
/-
**Polynomial.coe_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coe_monomial`：coe_monomial (n : Nat) (a : R) : (monomial n a 
: PowerSeries R) = PowerSeries.monomial n a
-/
theorem coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X :=
  coe_monomial _ _

@[simp]
/-
**Polynomial.polynomial_map_coe** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：polynomial_map_coe {U V : Type*} [CommSemiring U] [CommSemiring V] {φ : U 
->+* V} {f : Polynomial U} : Polynomial.map φ f = PowerSeries.map φ f
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
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma polynomial_map_coe {U V : Type*} [CommSemiring U] [CommSemiring V] {φ : U →+* V}
    {f : Polynomial U} : Polynomial.map φ f = PowerSeries.map φ f := by
  ext
  simp

@[simp]
/-
**Polynomial.constantCoeff_coe** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：constantCoeff_coe : PowerSeries.constantCoeff φ = φ.coeff 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantCoeff_coe : PowerSeries.constantCoeff φ = φ.coeff 0 :=
  rfl

variable (R)
/-
**Polynomial.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_injective : Function.Injective ((↑) : R[X] -> PowerSeries R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_injective : Function.Injective ((↑) : R[X] → PowerSeries R) := fun x y h => by
  ext
  simp_rw [← coeff_coe, h]

variable {R φ ψ}

@[simp, norm_cast]
/-
**Polynomial.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_inj : (φ : PowerSeries R) = ψ ↔ φ = ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Polynomial.coe_injective`：coe_injective : Function.Injective ((↑) : R[X]
 -> PowerSeries R)
-/
theorem coe_inj : (φ : PowerSeries R) = ψ ↔ φ = ψ :=
  (coe_injective R).eq_iff

@[simp]
/-
**Polynomial.coe_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_eq_zero_iff : (φ : PowerSeries R) = 0 ↔ φ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coe_zero`：coe_zero : ((0 : R[X]) : PowerSeries R) = 0
· 使用定理 `Polynomial.coe_inj`：coe_inj : (φ : PowerSeries R) = ψ ↔ φ = ψ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_zero_iff : (φ : PowerSeries R) = 0 ↔ φ = 0 := by rw [← coe_zero, coe_inj]

@[simp]
/-
**Polynomial.coe_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_eq_one_iff : (φ : PowerSeries R) = 1 ↔ φ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coe_one`：coe_one : ((1 : R[X]) : PowerSeries R) = 1
· 使用定理 `Polynomial.coe_inj`：coe_inj : (φ : PowerSeries R) = ψ ↔ φ = ψ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_one_iff : (φ : PowerSeries R) = 1 ↔ φ = 1 := by rw [← coe_one, coe_inj]

/-- The coercion from polynomials to power series
as a ring homomorphism.
-/
/-
**Polynomial.coeToPowerSeries.ringHom** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.coeT
oPowerSeries`。
形式化陈述：{R : Type u_1} → [inst : Semiring R] → Polynomial R →+* PowerSeries R
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coe_one`：coe_one : ((1 : R[X]) : PowerSeries R) = 1
· 使用定理 `Polynomial.coe_mul`：coe_mul : ((φ * ψ : R[X]) : PowerSeries R) = φ * ψ
· 使用定理 `Polynomial.coe_zero`：coe_zero : ((0 : R[X]) : PowerSeries R) = 0
· 使用定理 `Polynomial.coe_add`：coe_add : ((φ + ψ : R[X]) : PowerSeries R) = φ + ψ

--- 原说明 ---
The coercion from polynomials to power series
as a ring homomorphism.
-/
def coeToPowerSeries.ringHom : R[X] →+* PowerSeries R where
  toFun := (↑)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul

@[simp]
/-
**Polynomial.coeToPowerSeries.ringHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l.coeToPowerSeries`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {φ : Polynomial R}, Polynomial.coeToP
owerSeries.ringHom φ = ↑φ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeToPowerSeries.ringHom_apply : coeToPowerSeries.ringHom φ = φ :=
  rfl

@[simp, norm_cast]
/-
**Polynomial.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_pow (n : Nat) : ((φ ^ n : R[X]) : PowerSeries R) = (φ : PowerSeries R)
 ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
-/
theorem coe_pow (n : ℕ) : ((φ ^ n : R[X]) : PowerSeries R) = (φ : PowerSeries R) ^ n :=
  coeToPowerSeries.ringHom.map_pow _ _
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_C_X_eq_coe : φ.eval₂ PowerSeries.C PowerSeries.X = ↑φ := by
  nth_rw 2 [← eval₂_C_X (p := φ)]
  rw [← coeToPowerSeries.ringHom_apply, eval₂_eq_sum_range, eval₂_eq_sum_range, map_sum]
  apply Finset.sum_congr rfl
  intros
  rw [map_mul, map_pow, coeToPowerSeries.ringHom_apply,
    coeToPowerSeries.ringHom_apply, coe_C, coe_X]

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R] (φ ψ : R[X])

/-
**Polynomial._root_.MvPolynomial.toMvPowerSeries_pUnitAlgEquiv** 是 Mathlib 中的一个定
理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MvPolynomial.toMvPowerSeries_pUnitAlgEquiv {f : MvPolynomial PUnit R} :
    (f.toMvPowerSeries : PowerSeries R) =
      (MvPolynomial.uniqueAlgEquiv R PUnit f).toPowerSeries := by
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    --Note: this `have` should be a generic `simp` lemma for a `Unique` type with `()` replaced
    --by any element.
    have : single () (d ()) = d := by ext; simp
    simp only [MvPolynomial.coe_monomial, MvPolynomial.uniqueAlgEquiv_monomial,
      Polynomial.coe_monomial, PowerSeries.monomial, this]
  | add f g hf hg => simp [hf, hg]
/-
**Polynomial.pUnitAlgEquiv_symm_toPowerSeries** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：pUnitAlgEquiv_symm_toPowerSeries {f : Polynomial R} : ((f.toPowerSeries) :
 MvPowerSeries PUnit R) = ((MvPolynomial.uniqueAlgEquiv R PUnit).symm f).toMvPow
erSeries
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.toMvPowerSeries_pUnitAlgEquiv`：∀ {R : Type u_1} [inst : Com
mSemiring R] {f : MvPolynomial PUnit.{1} R},   ↑f = ↑((MvPolynomial.uniqueAlgEqu
iv R PUnit.{1}) f)
-/
theorem pUnitAlgEquiv_symm_toPowerSeries {f : Polynomial R} :
    ((f.toPowerSeries) : MvPowerSeries PUnit R)
      = ((MvPolynomial.uniqueAlgEquiv R PUnit).symm f).toMvPowerSeries := by
  set g := (MvPolynomial.uniqueAlgEquiv R PUnit).symm f
  have : f = MvPolynomial.uniqueAlgEquiv R PUnit g := by simp only [g, AlgEquiv.apply_symm_apply]
  rw [this, MvPolynomial.toMvPowerSeries_pUnitAlgEquiv]

variable (A : Type*) [Semiring A] [Algebra R A]

/-- The coercion from polynomials to power series
as an algebra homomorphism.
-/
/-
**Polynomial.coeToPowerSeries.algHom** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.coeTo
PowerSeries`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     (A : Type u_2) → [inst_1 
: Semiring A] → [inst_2 : Algebra R A] → Polynomial R →ₐ[R] PowerSeries A
参数：A : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from polynomials to power series
as an algebra homomorphism.
-/
def coeToPowerSeries.algHom : R[X] →ₐ[R] PowerSeries A :=
  { (PowerSeries.map (algebraMap R A)).comp coeToPowerSeries.ringHom with
    commutes' := fun r => by simp [PowerSeries.algebraMap_apply] }

@[simp]
/-
**Polynomial.coeToPowerSeries.algHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.coeToPowerSeries`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (φ : Polynomial R) (A : Type u_2)
 [inst_1 : Semiring A] [inst_2 : Algebra R A],   (Polynomial.coeToPowerSeries.al
gHom A) φ = (PowerSeries.map (algebraMap R A)) ↑φ
参数：φ : Polynomial R；A : Type u_2；Polynomial.coeToPowerSeries.algHom A；PowerSerie
s.map (algebraMap R A)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeToPowerSeries.algHom_apply :
    coeToPowerSeries.algHom A φ = PowerSeries.map (algebraMap R A) ↑φ :=
  rfl

end CommSemiring

section CommRing
variable {R : Type*} [CommRing R]

@[simp, norm_cast]
/-
**Polynomial.coe_neg** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：coe_neg (p : R[X]) : ((-p : R[X]) : PowerSeries R) = -p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x : α), f (-x) = -f x
-/
lemma coe_neg (p : R[X]) : ((-p : R[X]) : PowerSeries R) = -p :=
  coeToPowerSeries.ringHom.map_neg p

@[simp, norm_cast]
/-
**Polynomial.coe_sub** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：coe_sub (p q : R[X]) : ((p - q : R[X]) : PowerSeries R) = p - q
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x y : α),   f (x - y) = f x - f y
-/
lemma coe_sub (p q : R[X]) : ((p - q : R[X]) : PowerSeries R) = p - q :=
  coeToPowerSeries.ringHom.map_sub p q

end CommRing

end Polynomial

namespace PowerSeries

section Algebra

open Polynomial

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (f : R⟦X⟧)

/-
**PowerSeries.algebraPolynomial** 是 Mathlib 中的一个实例，位于命名空间 `PowerSeries`。
形式化陈述：algebraPolynomial : Algebra R[X] A⟦X⟧
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebraPolynomial : Algebra R[X] A⟦X⟧ :=
  RingHom.toAlgebra (Polynomial.coeToPowerSeries.algHom A).toRingHom
/-
**PowerSeries.algebraPowerSeries** 是 Mathlib 中的一个实例，位于命名空间 `PowerSeries`。
形式化陈述：algebraPowerSeries : Algebra R⟦X⟧ A⟦X⟧
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebraPowerSeries : Algebra R⟦X⟧ A⟦X⟧ :=
  (map (algebraMap R A)).toAlgebra

-- see Note [lower instance priority]
/-
**PowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) algebraPolynomial' {A : Type*} [CommSemiring A] [Algebra R A[X]] :
    Algebra R A⟦X⟧ :=
  RingHom.toAlgebra <| Polynomial.coeToPowerSeries.ringHom.comp (algebraMap R A[X])

variable (A)
/-
**PowerSeries.algebraMap_apply'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：algebraMap_apply' (p : R[X]) : algebraMap R[X] A⟦X⟧ p = map (algebraMap R 
A) p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply' (p : R[X]) : algebraMap R[X] A⟦X⟧ p = map (algebraMap R A) p :=
  rfl
/-
**PowerSeries.algebraMap_apply''** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：algebraMap_apply'' : algebraMap R⟦X⟧ A⟦X⟧ f = map (algebraMap R A) f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply'' :
    algebraMap R⟦X⟧ A⟦X⟧ f = map (algebraMap R A) f :=
  rfl

end Algebra

end PowerSeries

end

