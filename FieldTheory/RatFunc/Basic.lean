/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.RatFunc.Defs
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# The field structure of rational functions

## Main definitions
Working with rational functions as polynomials:
- `RatFunc.instField` provides a field structure

You can use `IsFractionRing` API to treat `RatFunc` as the field of fractions of polynomials:
* `algebraMap K[X] K⟮X⟯` maps polynomials to rational functions
* `IsFractionRing.algEquiv` maps other fields of fractions of `K[X]` to `K⟮X⟯`.

In particular:
* `FractionRing.algEquiv K[X] K⟮X⟯` maps the generic field of
  fraction construction to `K⟮X⟯`. Combine this with `AlgEquiv.restrictScalars` to change
  the `FractionRing K[X] ≃ₐ[K[X]] K⟮X⟯` to `FractionRing K[X] ≃ₐ[K] K⟮X⟯`.

Working with rational functions as fractions:
- `RatFunc.num` and `RatFunc.denom` give the numerator and denominator.
  These values are chosen to be coprime and such that `RatFunc.denom` is monic.

Lifting homomorphisms of polynomials to other types, by mapping and dividing, as long
as the homomorphism retains the non-zero-divisor property:
- `RatFunc.liftMonoidWithZeroHom` lifts a `K[X] →*₀ G₀` to
  a `K⟮X⟯ →*₀ G₀`, where `[CommRing K] [CommGroupWithZero G₀]`
- `RatFunc.liftRingHom` lifts a `K[X] →+* L` to a `K⟮X⟯ →+* L`,
  where `[CommRing K] [Field L]`
- `RatFunc.liftAlgHom` lifts a `K[X] →ₐ[S] L` to a `K⟮X⟯ →ₐ[S] L`,
  where `[CommRing K] [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]`

This is satisfied by injective homs.

We also have lifting homomorphisms of polynomials to other polynomials,
with the same condition on retaining the non-zero-divisor property across the map:
- `RatFunc.map` lifts `K[X] →* R[X]` when `[CommRing K] [CommRing R]`
- `RatFunc.mapRingHom` lifts `K[X] →+* R[X]` when `[CommRing K] [CommRing R]`
- `RatFunc.mapAlgHom` lifts `K[X] →ₐ[S] R[X]` when
  `[CommRing K] [IsDomain K] [CommRing R] [IsDomain R]`
-/

@[expose] public section

universe u v

noncomputable section

open scoped nonZeroDivisors Polynomial

variable {K : Type u}

namespace RatFunc

section Field

variable [CommRing K]

/-- The zero rational function. -/
protected irreducible_def zero : K⟮X⟯ :=
  ⟨0⟩

/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero K⟮X⟯ :=
  ⟨RatFunc.zero⟩
/-
**RatFunc.ofFractionRing_zero** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_zero : (ofFractionRing 0 : K⟮X⟯) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.zero_def`：∀ {K : Type u_1} [inst : CommRing K], RatFunc.zero = {
 toFractionRing := 0 }
-/
theorem ofFractionRing_zero : (ofFractionRing 0 : K⟮X⟯) = 0 :=
  zero_def.symm

/-- Addition of rational functions. -/
protected irreducible_def add : K⟮X⟯ → K⟮X⟯ → K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p + q⟩

/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add K⟮X⟯ :=
  ⟨RatFunc.add⟩
/-
**RatFunc.ofFractionRing_add** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_add (p q : FractionRing K[X]) : ofFractionRing (p + q) = of
FractionRing p + ofFractionRing q
参数：p q : FractionRing K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.add_def`：∀ {K : Type u_1} [inst : CommRing K] (x x_1 : RatFunc K
),   x.add x_1 =     match x, x_1 with     | { toFractionRing := p }, { toFracti
onRin…
-/
theorem ofFractionRing_add (p q : FractionRing K[X]) :
    ofFractionRing (p + q) = ofFractionRing p + ofFractionRing q :=
  (add_def _ _).symm

/-- Subtraction of rational functions. -/
protected irreducible_def sub : K⟮X⟯ → K⟮X⟯ → K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p - q⟩

/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub K⟮X⟯ :=
  ⟨RatFunc.sub⟩
/-
**RatFunc.ofFractionRing_sub** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_sub (p q : FractionRing K[X]) : ofFractionRing (p - q) = of
FractionRing p - ofFractionRing q
参数：p q : FractionRing K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.sub_def`：∀ {K : Type u_1} [inst : CommRing K] (x x_1 : RatFunc K
),   x.sub x_1 =     match x, x_1 with     | { toFractionRing := p }, { toFracti
onRin…
-/
theorem ofFractionRing_sub (p q : FractionRing K[X]) :
    ofFractionRing (p - q) = ofFractionRing p - ofFractionRing q :=
  (sub_def _ _).symm

/-- Additive inverse of a rational function. -/
protected irreducible_def neg : K⟮X⟯ → K⟮X⟯
  | ⟨p⟩ => ⟨-p⟩

/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg K⟮X⟯ :=
  ⟨RatFunc.neg⟩
/-
**RatFunc.ofFractionRing_neg** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_neg (p : FractionRing K[X]) : ofFractionRing (-p) = -ofFrac
tionRing p
参数：p : FractionRing K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.neg_def`：∀ {K : Type u_1} [inst : CommRing K] (x : RatFunc K),  
 x.neg =     match x with     | { toFractionRing := p } => { toFractionRing := -
p }
-/
theorem ofFractionRing_neg (p : FractionRing K[X]) :
    ofFractionRing (-p) = -ofFractionRing p :=
  (neg_def _).symm

/-- The multiplicative unit of rational functions. -/
protected irreducible_def one : K⟮X⟯ :=
  ⟨1⟩

/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One K⟮X⟯ :=
  ⟨RatFunc.one⟩
/-
**RatFunc.ofFractionRing_one** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_one : (ofFractionRing 1 : K⟮X⟯) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.one_def`：∀ {K : Type u_1} [inst : CommRing K], RatFunc.one = { t
oFractionRing := 1 }
-/
theorem ofFractionRing_one : (ofFractionRing 1 : K⟮X⟯) = 1 :=
  one_def.symm

/-- Multiplication of rational functions. -/
protected irreducible_def mul : K⟮X⟯ → K⟮X⟯ → K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p * q⟩

/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul K⟮X⟯ :=
  ⟨RatFunc.mul⟩
/-
**RatFunc.ofFractionRing_mul** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_mul (p q : FractionRing K[X]) : ofFractionRing (p * q) = of
FractionRing p * ofFractionRing q
参数：p q : FractionRing K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.mul_def`：∀ {K : Type u_1} [inst : CommRing K] (x x_1 : RatFunc K
),   x.mul x_1 =     match x, x_1 with     | { toFractionRing := p }, { toFracti
onRin…
-/
theorem ofFractionRing_mul (p q : FractionRing K[X]) :
    ofFractionRing (p * q) = ofFractionRing p * ofFractionRing q :=
  (mul_def _ _).symm

section IsDomain

variable [IsDomain K]

/-- Division of rational functions. -/
protected irreducible_def div : K⟮X⟯ → K⟮X⟯ → K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p / q⟩

/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div K⟮X⟯ :=
  ⟨RatFunc.div⟩
/-
**RatFunc.ofFractionRing_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_div (p q : FractionRing K[X]) : ofFractionRing (p / q) = of
FractionRing p / ofFractionRing q
参数：p q : FractionRing K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.div_def`：∀ {K : Type u_1} [inst : CommRing K] [inst_1 : IsDomain
 K] (x x_1 : RatFunc K),   x.div x_1 =     match x, x_1 with     | { toFractionR
ing :…
-/
theorem ofFractionRing_div (p q : FractionRing K[X]) :
    ofFractionRing (p / q) = ofFractionRing p / ofFractionRing q :=
  (div_def _ _).symm

/-- Multiplicative inverse of a rational function. -/
protected irreducible_def inv : K⟮X⟯ → K⟮X⟯
  | ⟨p⟩ => ⟨p⁻¹⟩

/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv K⟮X⟯ :=
  ⟨RatFunc.inv⟩
/-
**RatFunc.ofFractionRing_inv** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_inv (p : FractionRing K[X]) : ofFractionRing p⁻¹ = (ofFract
ionRing p)⁻¹
参数：p : FractionRing K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.inv_def`：∀ {K : Type u_1} [inst : CommRing K] [inst_1 : IsDomain
 K] (x : RatFunc K),   x.inv =     match x with     | { toFractionRing := p } =>
 { to…
-/
theorem ofFractionRing_inv (p : FractionRing K[X]) :
    ofFractionRing p⁻¹ = (ofFractionRing p)⁻¹ :=
  (inv_def _).symm

-- Auxiliary lemma for the `Field` instance
/-
**RatFunc.mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：mul_inv_cancel : forall {p : K⟮X⟯}, p != 0 -> p * p⁻¹ = 1 | ⟨p⟩, h => by h
ave : p != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.ofFractionRing_zero`：ofFractionRing_zero : (ofFractionRing 0 : K
⟮X⟯) = 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RatFunc.ofFractionRing.injEq`：∀ {K : Type u} [inst : CommRing K] (toFrac
tionRing toFractionRing_1 : FractionRing (Polynomial K)),   ({ toFractionRing :=
 toFractionRing } …
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
-/
theorem mul_inv_cancel : ∀ {p : K⟮X⟯}, p ≠ 0 → p * p⁻¹ = 1
  | ⟨p⟩, h => by
    have : p ≠ 0 := fun hp => h <| by rw [hp, ofFractionRing_zero]
    simpa only [← ofFractionRing_inv, ← ofFractionRing_mul, ← ofFractionRing_one,
        ofFractionRing.injEq] using
      mul_inv_cancel₀ this

end IsDomain

section SMul

variable {R : Type*}

/-- Scalar multiplication of rational functions. -/
protected irreducible_def smul [SMul R (FractionRing K[X])] : R → K⟮X⟯ → K⟮X⟯
  | r, ⟨p⟩ => ⟨r • p⟩

/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R (FractionRing K[X])] : SMul R K⟮X⟯ :=
  ⟨RatFunc.smul⟩
/-
**RatFunc.ofFractionRing_smul** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : FractionRing
 K[X]) : ofFractionRing (c • p) = c • ofFractionRing p
参数：FractionRing K[X]；c : R；p : FractionRing K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.smul_def`：∀ {K : Type u_2} [inst : CommRing K] {R : Type u_3} [i
nst_1 : SMul R (FractionRing (Polynomial K))] (x : R)   (x_1 : RatFunc K),   Rat
Func.s…
-/
theorem ofFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : FractionRing K[X]) :
    ofFractionRing (c • p) = c • ofFractionRing p :=
  (smul_def _ _).symm
/-
**RatFunc.toFractionRing_smul** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：toFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : K⟮X⟯) : toFr
actionRing (c • p) = c • toFractionRing p
参数：FractionRing K[X]；c : R；p : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.ofFractionRing_smul`：ofFractionRing_smul [SMul R (FractionRing K
[X])] (c : R) (p : FractionRing K[X]) : ofFractionRing (c • p) = c • ofFractionR
ing p
-/
theorem toFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : K⟮X⟯) :
    toFractionRing (c • p) = c • toFractionRing p := by
  cases p
  rw [← ofFractionRing_smul]
/-
**RatFunc.smul_eq_C_smul** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：smul_eq_C_smul (x : K⟮X⟯) (r : K) : r • x = Polynomial.C r • x
参数：x : K⟮X⟯；r : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Localization.induction_on`：induction_on {p : Localization S -> Prop} (x)
 (H : forall y : M × S, p (mk y.1 y.2)) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.ofFractionRing_smul`：ofFractionRing_smul [SMul R (FractionRing K
[X])] (c : R) (p : FractionRing K[X]) : ofFractionRing (c • p) = c • ofFractionR
ing p
· 使用定理 `Localization.smul_mk`：smul_mk [SMul R M] [IsScalarTower R M M] (c : R) (
a b) : c • (mk a b : Localization S) = mk (c • a) b
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Polynomial.smul_eq_C_mul`：smul_eq_C_mul (a : R) : a • p = C a * p
-/
theorem smul_eq_C_smul (x : K⟮X⟯) (r : K) : r • x = Polynomial.C r • x := by
  obtain ⟨x⟩ := x
  induction x using Localization.induction_on
  rw [← ofFractionRing_smul, ← ofFractionRing_smul, Localization.smul_mk,
    Localization.smul_mk, smul_eq_mul, Polynomial.smul_eq_C_mul]

section IsDomain

variable [IsDomain K]
variable [Monoid R] [DistribMulAction R K[X]]
variable [IsScalarTower R K[X] K[X]]

/-
**RatFunc.mk_smul** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：mk_smul (c : R) (p q : K[X]) : RatFunc.mk (c • p) q = c • RatFunc.mk p q
参数：c : R；p q : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.mk_zero`：mk_zero (p : K[X]) : RatFunc.mk p 0 = ofFractionRing (0
 : FractionRing K[X])
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.ofFractionRing_smul`：ofFractionRing_smul [SMul R (FractionRing K
[X])] (c : R) (p : FractionRing K[X]) : ofFractionRing (c • p) = c • ofFractionR
ing p
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
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
· 使用定理 `RatFunc.mk_eq_localization_mk`：mk_eq_localization_mk (p : K[X]) {q : K[X
]} (hq : q != 0) : RatFunc.mk p q = ofFractionRing (Localization.mk p ⟨q, mem_no
nZeroDivisors_iff_n…
· 使用定理 `Localization.smul_mk`：smul_mk [SMul R M] [IsScalarTower R M M] (c : R) (
a b) : c • (mk a b : Localization S) = mk (c • a) b
-/
theorem mk_smul (c : R) (p q : K[X]) : RatFunc.mk (c • p) q = c • RatFunc.mk p q := by
  let : SMulZeroClass R (FractionRing K[X]) := inferInstance
  by_cases hq : q = 0
  · rw [hq, mk_zero, mk_zero, ← ofFractionRing_smul, smul_zero]
  · rw [mk_eq_localization_mk _ hq, mk_eq_localization_mk _ hq, ← Localization.smul_mk, ←
      ofFractionRing_smul]
/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R K[X] K⟮X⟯ :=
  ⟨fun c p q => q.induction_on' fun q r _ => by rw [← mk_smul, smul_assoc, mk_smul, mk_smul]⟩

end IsDomain

end SMul

variable (K)

/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton K] : Subsingleton K⟮X⟯ :=
  toFractionRing_injective.subsingleton
/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited K⟮X⟯ :=
  ⟨0⟩
/-
**RatFunc.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
形式化陈述：instNontrivial [Nontrivial K] : Nontrivial K⟮X⟯
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `RatFunc.ofFractionRing_injective`：ofFractionRing_injective : Function.In
jective (ofFractionRing : _ -> K⟮X⟯)
-/
instance instNontrivial [Nontrivial K] : Nontrivial K⟮X⟯ :=
  ofFractionRing_injective.nontrivial

/-- `K⟮X⟯` is isomorphic to the field of fractions of `K[X]`, as rings.

This is an auxiliary definition; `simp`-normal form is `IsLocalization.algEquiv`.
-/
@[simps apply]
/-
**RatFunc.toFractionRingRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：toFractionRingRingEquiv : K⟮X⟯ ≃+* FractionRing K[X] where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`K⟮X⟯` is isomorphic to the field of fractions of `K[X]`, as rings.

This is an auxiliary definition; `simp`-normal form is `IsLocalization.algEquiv`
.
-/
def toFractionRingRingEquiv : K⟮X⟯ ≃+* FractionRing K[X] where
  toFun := toFractionRing
  invFun := ofFractionRing
  map_add' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_add]
  map_mul' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_mul]

end Field

section TacticInterlude

/-- Solve equations for `K⟮X⟯` by working in `FractionRing K[X]`. -/
macro "frac_tac" : tactic => `(tactic|
  · repeat (rintro (⟨⟩ : _⟮X⟯))
    try simp only [← ofFractionRing_zero, ← ofFractionRing_add, ← ofFractionRing_sub,
      ← ofFractionRing_neg, ← ofFractionRing_one, ← ofFractionRing_mul, ← ofFractionRing_div,
      ← ofFractionRing_inv,
      add_assoc, zero_add, add_zero, mul_assoc, mul_zero, mul_one, mul_add, inv_zero,
      add_comm, add_left_comm, mul_comm, mul_left_comm, sub_eq_add_neg, div_eq_mul_inv,
      add_mul, zero_mul, one_mul, neg_mul, mul_neg, add_neg_cancel])

/-- Solve equations for `K⟮X⟯` by applying `RatFunc.induction_on`. -/
macro "smul_tac" : tactic => `(tactic|
    repeat
      (first
        | rintro (⟨⟩ : _⟮X⟯)
        | intro) <;>
    simp_rw [← ofFractionRing_smul] <;>
    simp only [add_comm, mul_comm, zero_smul, succ_nsmul, zsmul_eq_mul, mul_add, mul_one, mul_zero,
      neg_add, mul_neg,
      Int.cast_zero, Int.cast_add, Int.cast_one,
      Int.cast_negSucc, Int.cast_natCast, Nat.cast_succ,
      Localization.mk_zero, Localization.add_mk_self, Localization.neg_mk,
      ofFractionRing_zero, ← ofFractionRing_add, ← ofFractionRing_neg])

end TacticInterlude

section CommRing

variable (K) [CommRing K]
/-- `K⟮X⟯` is a commutative monoid.

This is an intermediate step on the way to the full instance `RatFunc.instCommRing`.
-/
@[instance_reducible]
/-
**RatFunc.instCommMonoid** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：instCommMonoid : CommMonoid K⟮X⟯ where mul_assoc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`K⟮X⟯` is a commutative monoid.

This is an intermediate step on the way to the full instance `RatFunc.instCommRi
ng`.
-/
def instCommMonoid : CommMonoid K⟮X⟯ where
  mul_assoc := by frac_tac
  mul_comm := by frac_tac
  one_mul := by frac_tac
  mul_one := by frac_tac
  npow := npowRec

/-- `K⟮X⟯` is an additive commutative group.

This is an intermediate step on the way to the full instance `RatFunc.instCommRing`.
-/
@[instance_reducible]
/-
**RatFunc.instAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：instAddCommGroup : AddCommGroup K⟮X⟯ where add_assoc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`K⟮X⟯` is an additive commutative group.

This is an intermediate step on the way to the full instance `RatFunc.instCommRi
ng`.
-/
def instAddCommGroup : AddCommGroup K⟮X⟯ where
  add_assoc := by frac_tac
  add_comm := by frac_tac
  zero_add := by frac_tac
  add_zero := by frac_tac
  neg_add_cancel := by frac_tac
  sub_eq_add_neg := by frac_tac
  nsmul_zero := by smul_tac
  nsmul_succ _ := by smul_tac
  zsmul_zero' := by smul_tac
  zsmul_succ' _ := by smul_tac
  zsmul_neg' _ := by smul_tac
/-
**RatFunc.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
形式化陈述：instCommRing : CommRing K⟮X⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRing : CommRing K⟮X⟯ :=
  { instCommMonoid K, instAddCommGroup K with
    zero_mul := by frac_tac
    mul_zero := by frac_tac
    left_distrib := by frac_tac
    right_distrib := by frac_tac
    npow := npowRec }

variable {K}

section LiftHom

open RatFunc

variable {G₀ L R S F : Type*} [CommGroupWithZero G₀] [Field L] [CommRing R] [CommRing S]
variable [FunLike F R[X] S[X]]

open scoped Classical in
/-- Lift a monoid homomorphism that maps polynomials `φ : R[X] →* S[X]`
to a `R⟮X⟯ →* S⟮X⟯`,
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them. -/
/-
**RatFunc.map** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：map [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ) : R
⟮X⟯ ->* S⟮X⟯ where toFun f
参数：φ : F；hφ : R[X]⁰ <= S[X]⁰.comap φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a monoid homomorphism that maps polynomials `φ : R[X] →* S[X]`
to a `R⟮X⟯ →* S⟮X⟯`,
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them.
-/
def map [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    R⟮X⟯ →* S⟮X⟯ where
  toFun f :=
    RatFunc.liftOn f
      (fun n d => if h : φ d ∈ S[X]⁰ then ofFractionRing (Localization.mk (φ n) ⟨φ d, h⟩) else 0)
      fun {p q p' q'} hq hq' h => by
      simp only [Submonoid.mem_comap.mp (hφ hq), Submonoid.mem_comap.mp (hφ hq'),
        dif_pos, ofFractionRing.injEq, Localization.mk_eq_mk_iff]
      refine Localization.r_of_eq ?_
      simpa only [map_mul] using congr_arg φ h
  map_one' := by
    simp_rw [← ofFractionRing_one, ← Localization.mk_one, liftOn_ofFractionRing_mk,
      OneMemClass.coe_one, map_one, OneMemClass.one_mem, dite_true, ofFractionRing.injEq,
      Localization.mk_one, Localization.mk_eq_monoidOf_mk', Submonoid.LocalizationMap.mk'_self]
  map_mul' x y := by
    obtain ⟨x⟩ := x; obtain ⟨y⟩ := y
    cases x using Localization.induction_on with | _ pq
    cases y using Localization.induction_on with | _ p'q'
    obtain ⟨p, q⟩ := pq
    obtain ⟨p', q'⟩ := p'q'
    have hq : φ q ∈ S[X]⁰ := hφ q.prop
    have hq' : φ q' ∈ S[X]⁰ := hφ q'.prop
    have hqq' : φ ↑(q * q') ∈ S[X]⁰ := by simpa using Submonoid.mul_mem _ hq hq'
    simp_rw [← ofFractionRing_mul, Localization.mk_mul, liftOn_ofFractionRing_mk, dif_pos hq,
      dif_pos hq', dif_pos hqq', ← ofFractionRing_mul, Submonoid.coe_mul, map_mul,
      Localization.mk_mul, Submonoid.mk_mul_mk]
/-
**RatFunc.map_apply_ofFractionRing_mk** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：map_apply_ofFractionRing_mk [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X
]⁰ <= S[X]⁰.comap φ) (n : R[X]) (d : R[X]⁰) : map φ hφ (ofFractionRing (Localiza
tion.mk n d)) = ofFractionRing (Localization.mk (φ n) ⟨φ d, hφ d.prop⟩)
参数：φ : F；hφ : R[X]⁰ <= S[X]⁰.comap φ；n : R[X]；d : R[X]⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.mem_comap`：mem_comap {S : Submonoid N} {f : F} {x : M} : x in 
S.comap f ↔ f x in S
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.liftOn_ofFractionRing_mk`：liftOn_ofFractionRing_mk {P : Sort v} 
(n : K[X]) (d : K[X]⁰) (f : K[X] -> K[X] -> P) (H : forall {p q p' q'} (_hq : q 
in K[X]⁰) (_hq' : q' i…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_apply_ofFractionRing_mk [MonoidHomClass F R[X] S[X]] (φ : F)
    (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) (n : R[X]) (d : R[X]⁰) :
    map φ hφ (ofFractionRing (Localization.mk n d)) =
      ofFractionRing (Localization.mk (φ n) ⟨φ d, hφ d.prop⟩) := by
  simp only [map, MonoidHom.coe_mk, OneHom.coe_mk, liftOn_ofFractionRing_mk,
    Submonoid.mem_comap.mp (hφ d.2), ↓reduceDIte]
/-
**RatFunc.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：map_injective [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.co
map φ) (hf : Function.Injective φ) : Function.Injective (map φ hφ)
参数：φ : F；hφ : R[X]⁰ <= S[X]⁰.comap φ；hf : Function.Injective φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.induction_on`：induction_on {p : Localization S -> Prop} (x)
 (H : forall y : M × S, p (mk y.1 y.2)) : p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `RatFunc.ofFractionRing_injective`：ofFractionRing_injective : Function.In
jective (ofFractionRing : _ -> K⟮X⟯)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RatFunc.map_apply_ofFractionRing_mk`：map_apply_ofFractionRing_mk [Monoid
HomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ) (n : R[X]) (d : R[X]
⁰) : map φ hφ (ofFraction…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem map_injective [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ)
    (hf : Function.Injective φ) : Function.Injective (map φ hφ) := by
  rintro ⟨x⟩ ⟨y⟩ h
  induction x using Localization.induction_on
  induction y using Localization.induction_on
  simpa only [map_apply_ofFractionRing_mk, ofFractionRing_injective.eq_iff,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists, mul_cancel_left_coe_nonZeroDivisors,
    exists_const, ← map_mul, hf.eq_iff] using h

set_option backward.isDefEq.respectTransparency.types false in
/-- Lift a ring homomorphism that maps polynomials `φ : R[X] →+* S[X]`
to a `R⟮X⟯ →+* S⟮X⟯`,
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them. -/
/-
**RatFunc.mapRingHom** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：mapRingHom [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ
) : R⟮X⟯ ->+* S⟮X⟯
参数：φ : F；hφ : R[X]⁰ <= S[X]⁰.comap φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a ring homomorphism that maps polynomials `φ : R[X] →+* S[X]`
to a `R⟮X⟯ →+* S⟮X⟯`,
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them.
-/
def mapRingHom [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    R⟮X⟯ →+* S⟮X⟯ :=
  { map φ hφ with
    map_zero' := by
      simp_rw [MonoidHom.toFun_eq_coe, ← ofFractionRing_zero, ← Localization.mk_zero (1 : R[X]⁰),
        ← Localization.mk_zero (1 : S[X]⁰), map_apply_ofFractionRing_mk, map_zero,
        Localization.mk_eq_mk', IsLocalization.mk'_zero]
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      induction x using Localization.induction_on
      induction y using Localization.induction_on
      · simp only [← ofFractionRing_add, Localization.add_mk, map_add, map_mul,
          MonoidHom.toFun_eq_coe, map_apply_ofFractionRing_mk, Submonoid.coe_mul,
          -- We have to specify `S[X]⁰` to `mk_mul_mk`, otherwise it will try to rewrite
          -- the wrong occurrence.
          Submonoid.mk_mul_mk S[X]⁰] }
/-
**RatFunc.coe_mapRingHom_eq_coe_map** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：coe_mapRingHom_eq_coe_map [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <
= S[X]⁰.comap φ) : (mapRingHom φ hφ : R⟮X⟯ -> S⟮X⟯) = map φ hφ
参数：φ : F；hφ : R[X]⁰ <= S[X]⁰.comap φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_mapRingHom_eq_coe_map [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    (mapRingHom φ hφ : R⟮X⟯ → S⟮X⟯) = map φ hφ :=
  rfl

-- TODO: Generalize to `FunLike` classes,
/-- Lift a monoid with zero homomorphism `R[X] →*₀ G₀` to a `R⟮X⟯ →*₀ G₀`
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them. -/
/-
**RatFunc.liftMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：liftMonoidWithZeroHom (φ : R[X] ->*₀ G₀) (hφ : R[X]⁰ <= G₀⁰.comap φ) : R⟮X
⟯ ->*₀ G₀ where toFun f
参数：φ : R[X] ->*₀ G₀；hφ : R[X]⁰ <= G₀⁰.comap φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a monoid with zero homomorphism `R[X] →*₀ G₀` to a `R⟮X⟯ →*₀ G₀`
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them.
-/
def liftMonoidWithZeroHom (φ : R[X] →*₀ G₀) (hφ : R[X]⁰ ≤ G₀⁰.comap φ) : R⟮X⟯ →*₀ G₀ where
  toFun f :=
    RatFunc.liftOn f (fun p q => φ p / φ q) fun {p q p' q'} hq hq' h => by
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim p q, Subsingleton.elim p' q, Subsingleton.elim q' q]
      rw [div_eq_div_iff, ← map_mul, mul_comm p, h, map_mul, mul_comm] <;>
        exact nonZeroDivisors.ne_zero (hφ ‹_›)
  map_one' := by
    simp_rw [← ofFractionRing_one, ← Localization.mk_one, liftOn_ofFractionRing_mk,
      OneMemClass.coe_one, map_one, div_one]
  map_mul' x y := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    cases x using Localization.induction_on
    cases y using Localization.induction_on
    rw [← ofFractionRing_mul, Localization.mk_mul]
    simp only [liftOn_ofFractionRing_mk, div_mul_div_comm, map_mul, Submonoid.coe_mul]
  map_zero' := by
    simp_rw [← ofFractionRing_zero, ← Localization.mk_zero (1 : R[X]⁰), liftOn_ofFractionRing_mk,
      map_zero, zero_div]
/-
**RatFunc.liftMonoidWithZeroHom_apply_ofFractionRing_mk** 是 Mathlib 中的一个定理，位于命名空
间 `RatFunc`。
形式化陈述：liftMonoidWithZeroHom_apply_ofFractionRing_mk (φ : R[X] ->*₀ G₀) (hφ : R[X
]⁰ <= G₀⁰.comap φ) (n : R[X]) (d : R[X]⁰) : liftMonoidWithZeroHom φ hφ (ofFracti
onRing (Localization.mk n d)) = φ n / φ d
参数：φ : R[X] ->*₀ G₀；hφ : R[X]⁰ <= G₀⁰.comap φ；n : R[X]；d : R[X]⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RatFunc.liftOn_ofFractionRing_mk`：liftOn_ofFractionRing_mk {P : Sort v} 
(n : K[X]) (d : K[X]⁰) (f : K[X] -> K[X] -> P) (H : forall {p q p' q'} (_hq : q 
in K[X]⁰) (_hq' : q' i…
-/
theorem liftMonoidWithZeroHom_apply_ofFractionRing_mk (φ : R[X] →*₀ G₀) (hφ : R[X]⁰ ≤ G₀⁰.comap φ)
    (n : R[X]) (d : R[X]⁰) :
    liftMonoidWithZeroHom φ hφ (ofFractionRing (Localization.mk n d)) = φ n / φ d :=
  liftOn_ofFractionRing_mk _ _ _ _
/-
**RatFunc.liftMonoidWithZeroHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftMonoidWithZeroHom_injective [Nontrivial R] (φ : R[X] ->*₀ G₀) (hφ : Fu
nction.Injective φ) (hφ' : R[X]⁰ <= G₀⁰.comap φ
参数：φ : R[X] ->*₀ G₀；hφ : Function.Injective φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Localization.induction_on`：induction_on {p : Localization S -> Prop} (x)
 (H : forall y : M × S, p (mk y.1 y.2)) : p x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.liftMonoidWithZeroHom_apply_ofFractionRing_mk`：liftMonoidWithZer
oHom_apply_ofFractionRing_mk (φ : R[X] ->*₀ G₀) (hφ : R[X]⁰ <= G₀⁰.comap φ) (n :
 R[X]) (d : R[X]⁰) : liftMonoidWithZeroHom …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Localization.mk_eq_mk_iff`：mk_eq_mk_iff {a c : M} {b d : S} : mk a b = m
k c d ↔ r S ⟨a, b⟩ ⟨c, d⟩
· 使用定理 `Localization.r_of_eq`：r_of_eq {x y : M × S} (h : ↑y.2 * x.1 = ↑x.2 * y.1
) : r S x y
· 使用引理 `mul_eq_mul_of_div_eq_div`：mul_eq_mul_of_div_eq_div (a c : G₀) (hb : b !=
 0) (hd : d != 0) (h : a / b = c / d) : a * d = c * b
· 使用定理 `map_ne_zero_of_mem_nonZeroDivisors`：map_ne_zero_of_mem_nonZeroDivisors [
Nontrivial M₀] [ZeroHomClass F M₀ M₀'] (g : F) (hg : Injective (g : M₀ -> M₀')) 
{x : M₀} (h : x in M₀⁰) …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem liftMonoidWithZeroHom_injective [Nontrivial R] (φ : R[X] →*₀ G₀) (hφ : Function.Injective φ)
    (hφ' : R[X]⁰ ≤ G₀⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftMonoidWithZeroHom φ hφ') := by
  rintro ⟨x⟩ ⟨y⟩
  cases x using Localization.induction_on
  cases y using Localization.induction_on with | _ a'
  simp_rw [liftMonoidWithZeroHom_apply_ofFractionRing_mk]
  intro h
  congr 1
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (M := R[X]) ?_)
  have := mul_eq_mul_of_div_eq_div _ _ ?_ ?_ h
  · rwa [← map_mul, ← map_mul, hφ.eq_iff, mul_comm, mul_comm a'.fst] at this
  all_goals exact map_ne_zero_of_mem_nonZeroDivisors _ hφ (SetLike.coe_mem _)

set_option backward.isDefEq.respectTransparency.types false in
/-- Lift an injective ring homomorphism `R[X] →+* L` to a `R⟮X⟯ →+* L`
by mapping both the numerator and denominator and quotienting them. -/
/-
**RatFunc.liftRingHom** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：liftRingHom (φ : R[X] ->+* L) (hφ : R[X]⁰ <= L⁰.comap φ) : R⟮X⟯ ->+* L
参数：φ : R[X] ->+* L；hφ : R[X]⁰ <= L⁰.comap φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift an injective ring homomorphism `R[X] →+* L` to a `R⟮X⟯ →+* L`
by mapping both the numerator and denominator and quotienting them.
-/
def liftRingHom (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) : R⟮X⟯ →+* L :=
  { liftMonoidWithZeroHom φ.toMonoidWithZeroHom hφ with
    map_add' := fun x y => by
      simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe]
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim (x + y) y, Subsingleton.elim x 0, map_zero, zero_add]
      obtain ⟨x⟩ := x
      obtain ⟨y⟩ := y
      cases x using Localization.induction_on with | _ pq
      cases y using Localization.induction_on with | _ p'q'
      obtain ⟨p, q⟩ := pq
      obtain ⟨p', q'⟩ := p'q'
      rw [← ofFractionRing_add, Localization.add_mk]
      simp only [RingHom.toMonoidWithZeroHom_eq_coe,
        liftMonoidWithZeroHom_apply_ofFractionRing_mk]
      rw [div_add_div, div_eq_div_iff]
      · rw [mul_comm _ p, mul_comm _ p', mul_comm _ (φ p'), add_comm]
        simp only [map_add, map_mul, Submonoid.coe_mul]
      all_goals
        try simp only [← map_mul, ← Submonoid.coe_mul]
        exact nonZeroDivisors.ne_zero (hφ (SetLike.coe_mem _)) }

set_option backward.isDefEq.respectTransparency.types false in
/-
**RatFunc.liftRingHom_apply_ofFractionRing_mk** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc
`。
形式化陈述：liftRingHom_apply_ofFractionRing_mk (φ : R[X] ->+* L) (hφ : R[X]⁰ <= L⁰.co
map φ) (n : R[X]) (d : R[X]⁰) : liftRingHom φ hφ (ofFractionRing (Localization.m
k n d)) = φ n / φ d
参数：φ : R[X] ->+* L；hφ : R[X]⁰ <= L⁰.comap φ；n : R[X]；d : R[X]⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RatFunc.liftMonoidWithZeroHom_apply_ofFractionRing_mk`：liftMonoidWithZer
oHom_apply_ofFractionRing_mk (φ : R[X] ->*₀ G₀) (hφ : R[X]⁰ <= G₀⁰.comap φ) (n :
 R[X]) (d : R[X]⁰) : liftMonoidWithZeroHom …
-/
theorem liftRingHom_apply_ofFractionRing_mk (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) (n : R[X])
    (d : R[X]⁰) : liftRingHom φ hφ (ofFractionRing (Localization.mk n d)) = φ n / φ d :=
  liftMonoidWithZeroHom_apply_ofFractionRing_mk _ hφ _ _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**RatFunc.liftRingHom_ofFractionRing_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RatFu
nc`。
形式化陈述：liftRingHom_ofFractionRing_algebraMap (φ : R[X] ->+* L) (hφ : R[X]⁰ <= L⁰.
comap φ) (x : R[X]) : RatFunc.liftRingHom φ hφ (ofFractionRing <| algebraMap R[X
] _ x) = φ x
参数：φ : R[X] ->+* L；hφ : R[X]⁰ <= L⁰.comap φ；x : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Localization.mk_one_eq_algebraMap`：mk_one_eq_algebraMap (x) : mk x 1 = a
lgebraMap R (Localization M) x
· 使用定理 `RatFunc.liftRingHom_apply_ofFractionRing_mk`：liftRingHom_apply_ofFractio
nRing_mk (φ : R[X] ->+* L) (hφ : R[X]⁰ <= L⁰.comap φ) (n : R[X]) (d : R[X]⁰) : l
iftRingHom φ hφ (ofFractionRing (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftRingHom_ofFractionRing_algebraMap
    (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) (x : R[X]) :
    RatFunc.liftRingHom φ hφ (ofFractionRing <| algebraMap R[X] _ x) = φ x := by
  rw [← Localization.mk_one_eq_algebraMap, liftRingHom_apply_ofFractionRing_mk]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**RatFunc.liftRingHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftRingHom_injective [Nontrivial R] (φ : R[X] ->+* L) (hφ : Function.Inje
ctive φ) (hφ' : R[X]⁰ <= L⁰.comap φ
参数：φ : R[X] ->+* L；hφ : Function.Injective φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RatFunc.liftMonoidWithZeroHom_injective`：liftMonoidWithZeroHom_injective
 [Nontrivial R] (φ : R[X] ->*₀ G₀) (hφ : Function.Injective φ) (hφ' : R[X]⁰ <= G
₀⁰.comap φ
· 使用定理 `nonZeroDivisors_le_comap_nonZeroDivisors_of_injective`：nonZeroDivisors_l
e_comap_nonZeroDivisors_of_injective [NoZeroDivisors M₀'] [MonoidWithZeroHomClas
s F M₀ M₀'] (f : F) (hf : Injective f) : M₀…
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
-/
theorem liftRingHom_injective [Nontrivial R] (φ : R[X] →+* L) (hφ : Function.Injective φ)
    (hφ' : R[X]⁰ ≤ L⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftRingHom φ hφ') :=
  liftMonoidWithZeroHom_injective _ hφ

end LiftHom

variable (K)

@[stacks 09FK]
/-
**RatFunc.instField** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
形式化陈述：instField [IsDomain K] : Field K⟮X⟯ where inv_zero
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.mul_inv_cancel`：mul_inv_cancel : forall {p : K⟮X⟯}, p != 0 -> p 
* p⁻¹ = 1 | ⟨p⟩, h => by have : p != 0
-/
instance instField [IsDomain K] : Field K⟮X⟯ where
  inv_zero := by frac_tac
  div_eq_mul_inv := by frac_tac
  mul_inv_cancel _ := mul_inv_cancel
  zpow := zpowRec
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

section IsFractionRing

/-! ### `RatFunc` as field of fractions of `Polynomial` -/

section IsDomain

variable [IsDomain K]

/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type*) [CommSemiring R] [Algebra R K[X]] : Algebra R K⟮X⟯ where
  algebraMap :=
  { toFun x := RatFunc.mk (algebraMap _ _ x) 1
    map_add' x y := by simp only [mk_one', map_add, ofFractionRing_add]
    map_mul' x y := by simp only [mk_one', map_mul, ofFractionRing_mul]
    map_one' := by simp only [mk_one', map_one, ofFractionRing_one]
    map_zero' := by simp only [mk_one', map_zero, ofFractionRing_zero] }
  smul_def' c x := by
    induction x using RatFunc.induction_on' with | _ p q hq
    rw [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, mk_one', ← mk_smul,
      mk_def_of_ne (c • p) hq, mk_def_of_ne p hq, ← ofFractionRing_mul,
      IsLocalization.mul_mk'_eq_mk'_of_mul, Algebra.smul_def]
  commutes' _ _ := mul_comm _ _

variable {K}

/-- The coercion from polynomials to rational functions, implemented as the algebra map from a
domain to its field of fractions -/
@[coe]
/-
**RatFunc.coePolynomial** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：coePolynomial (P : Polynomial K) : K⟮X⟯
参数：P : Polynomial K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from polynomials to rational functions, implemented as the algebra 
map from a
domain to its field of fractions
-/
def coePolynomial (P : Polynomial K) : K⟮X⟯ := algebraMap _ _ P
/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (Polynomial K) K⟮X⟯ := ⟨coePolynomial⟩
/-
**RatFunc.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：mk_one (x : K[X]) : RatFunc.mk x 1 = algebraMap _ _ x
参数：x : K[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_one (x : K[X]) : RatFunc.mk x 1 = algebraMap _ _ x :=
  rfl
/-
**RatFunc.ofFractionRing_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_algebraMap (x : K[X]) : ofFractionRing (algebraMap _ (Fract
ionRing K[X]) x) = algebraMap _ _ x
参数：x : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.mk_one`：mk_one (x : K[X]) : RatFunc.mk x 1 = algebraMap _ _ x
· 使用定理 `RatFunc.mk_one'`：mk_one' (p : K[X]) : RatFunc.mk p 1 = ofFractionRing (a
lgebraMap _ _ p)
-/
theorem ofFractionRing_algebraMap (x : K[X]) :
    ofFractionRing (algebraMap _ (FractionRing K[X]) x) = algebraMap _ _ x := by
  rw [← mk_one, mk_one']

variable (K) in
/--
The equivalence between `K⟮X⟯` and the field of fractions of `K[X]`
-/
@[simps! apply]
/-
**RatFunc.toFractionRingAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：toFractionRingAlgEquiv (R : Type*) [CommSemiring R] [Algebra R K[X]] : K⟮X
⟯ ≃ₐ[R] FractionRing K[X] where __
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `K⟮X⟯` and the field of fractions of `K[X]`
-/
def toFractionRingAlgEquiv (R : Type*) [CommSemiring R] [Algebra R K[X]] :
    K⟮X⟯ ≃ₐ[R] FractionRing K[X] where
  __ := RatFunc.toFractionRingRingEquiv K
  commutes' r := by
    change (RatFunc.mk (algebraMap R K[X] r) 1).toFractionRing = _
    rw [mk_one']; rfl

@[simp]
/-
**RatFunc.mk_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：mk_eq_div (p q : K[X]) : RatFunc.mk p q = algebraMap _ _ p / algebraMap _ 
_ q
参数：p q : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `RatFunc.mk_eq_div'`：mk_eq_div' (p q : K[X]) : RatFunc.mk p q = ofFractio
nRing (algebraMap _ _ p / algebraMap _ _ q)
· 使用定理 `RatFunc.ofFractionRing_div`：ofFractionRing_div (p q : FractionRing K[X])
 : ofFractionRing (p / q) = ofFractionRing p / ofFractionRing q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RatFunc.ofFractionRing_algebraMap`：ofFractionRing_algebraMap (x : K[X]) 
: ofFractionRing (algebraMap _ (FractionRing K[X]) x) = algebraMap _ _ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_eq_div (p q : K[X]) : RatFunc.mk p q = algebraMap _ _ p / algebraMap _ _ q := by
  simp only [mk_eq_div', ofFractionRing_div, ofFractionRing_algebraMap]

@[simp]
/-
**RatFunc.div_smul** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：div_smul {R} [Monoid R] [DistribMulAction R K[X]] [IsScalarTower R K[X] K[
X]] (c : R) (p q : K[X]) : algebraMap _ K⟮X⟯ (c • p) / algebraMap _ _ q = c • (a
lgebraMap _ _ p / algebraMap _ _ q)
参数：c : R；p q : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.mk_eq_div`：mk_eq_div (p q : K[X]) : RatFunc.mk p q = algebraMap 
_ _ p / algebraMap _ _ q
· 使用定理 `RatFunc.mk_smul`：mk_smul (c : R) (p q : K[X]) : RatFunc.mk (c • p) q = c
 • RatFunc.mk p q
-/
theorem div_smul {R} [Monoid R] [DistribMulAction R K[X]] [IsScalarTower R K[X] K[X]] (c : R)
    (p q : K[X]) :
    algebraMap _ K⟮X⟯ (c • p) / algebraMap _ _ q =
      c • (algebraMap _ _ p / algebraMap _ _ q) := by
  rw [← mk_eq_div, mk_smul, mk_eq_div]
/-
**RatFunc.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：algebraMap_apply {R : Type*} [CommSemiring R] [Algebra R K[X]] (x : R) : a
lgebraMap R K⟮X⟯ x = algebraMap _ _ (algebraMap R K[X] x) / algebraMap K[X] _ 1
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.mk_eq_div`：mk_eq_div (p q : K[X]) : RatFunc.mk p q = algebraMap 
_ _ p / algebraMap _ _ q
-/
theorem algebraMap_apply {R : Type*} [CommSemiring R] [Algebra R K[X]] (x : R) :
    algebraMap R K⟮X⟯ x = algebraMap _ _ (algebraMap R K[X] x) / algebraMap K[X] _ 1 := by
  rw [← mk_eq_div]
  rfl
/-
**RatFunc.map_apply_div_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：map_apply_div_ne_zero {R F : Type*} [CommRing R] [IsDomain R] [FunLike F K
[X] R[X]] [MonoidHomClass F K[X] R[X]] (φ : F) (hφ : K[X]⁰ <= R[X]⁰.comap φ) (p 
q : K[X]) (hq : q != 0) : map φ hφ (algebraMap _ _ p / algebraMap _ _ q) = algeb
raMap _ _ (φ p) / algebraMap _ _ (φ q)
参数：φ : F；hφ : K[X]⁰ <= R[X]⁰.comap φ；p q : K[X]；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.mk_eq_localization_mk`：mk_eq_localization_mk (p : K[X]) {q : K[X
]} (hq : q != 0) : RatFunc.mk p q = ofFractionRing (Localization.mk p ⟨q, mem_no
nZeroDivisors_iff_n…
· 使用定理 `RatFunc.map_apply_ofFractionRing_mk`：map_apply_ofFractionRing_mk [Monoid
HomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ) (n : R[X]) (d : R[X]
⁰) : map φ hφ (ofFraction…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_apply_div_ne_zero {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p q : K[X]) (hq : q ≠ 0) :
    map φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (φ p) / algebraMap _ _ (φ q) := by
  have hq' : φ q ≠ 0 := nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_iff_ne_zero.mpr hq))
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq, map_apply_ofFractionRing_mk,
    mk_eq_localization_mk _ hq']

@[simp]
/-
**RatFunc.map_apply_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：map_apply_div {R F : Type*} [CommRing R] [IsDomain R] [FunLike F K[X] R[X]
] [MonoidWithZeroHomClass F K[X] R[X]] (φ : F) (hφ : K[X]⁰ <= R[X]⁰.comap φ) (p 
q : K[X]) : map φ hφ (algebraMap _ _ p / algebraMap _ _ q) = algebraMap _ _ (φ p
) / algebraMap _ _ (φ q)
参数：φ : F；hφ : K[X]⁰ <= R[X]⁰.comap φ；p q : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `RatFunc.map_apply_div_ne_zero`：map_apply_div_ne_zero {R F : Type*} [Comm
Ring R] [IsDomain R] [FunLike F K[X] R[X]] [MonoidHomClass F K[X] R[X]] (φ : F) 
(hφ : K[X]⁰ <= R[X]…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_apply_div {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidWithZeroHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p q : K[X]) :
    map φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (φ p) / algebraMap _ _ (φ q) := by
  rcases eq_or_ne q 0 with (rfl | hq)
  · have : (0 : K⟮X⟯) = algebraMap K[X] _ 0 / algebraMap K[X] _ 1 := by simp
    rw [map_zero, map_zero, map_zero, div_zero, div_zero, this, map_apply_div_ne_zero, map_one,
      map_one, div_one, map_zero, map_zero]
    exact one_ne_zero
  exact map_apply_div_ne_zero _ _ _ _ hq
/-
**RatFunc.liftMonoidWithZeroHom_apply_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftMonoidWithZeroHom_apply_div {L : Type*} [CommGroupWithZero L] (φ : Mon
oidWithZeroHom K[X] L) (hφ : K[X]⁰ <= L⁰.comap φ) (p q : K[X]) : liftMonoidWithZ
eroHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q
参数：φ : MonoidWithZeroHom K[X] L；hφ : K[X]⁰ <= L⁰.comap φ；p q : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
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
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `RatFunc.mk_eq_localization_mk`：mk_eq_localization_mk (p : K[X]) {q : K[X
]} (hq : q != 0) : RatFunc.mk p q = ofFractionRing (Localization.mk p ⟨q, mem_no
nZeroDivisors_iff_n…
· 使用定理 `RatFunc.liftMonoidWithZeroHom_apply_ofFractionRing_mk`：liftMonoidWithZer
oHom_apply_ofFractionRing_mk (φ : R[X] ->*₀ G₀) (hφ : R[X]⁰ <= G₀⁰.comap φ) (n :
 R[X]) (d : R[X]⁰) : liftMonoidWithZeroHom …
-/
theorem liftMonoidWithZeroHom_apply_div {L : Type*} [CommGroupWithZero L]
    (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (p q : K[X]) :
    liftMonoidWithZeroHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q := by
  rcases eq_or_ne q 0 with (rfl | hq)
  · simp only [div_zero, map_zero]
  simp only [← mk_eq_div, mk_eq_localization_mk _ hq,
    liftMonoidWithZeroHom_apply_ofFractionRing_mk]

@[simp]
/-
**RatFunc.liftMonoidWithZeroHom_apply_div'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftMonoidWithZeroHom_apply_div' {L : Type*} [CommGroupWithZero L] (φ : Mo
noidWithZeroHom K[X] L) (hφ : K[X]⁰ <= L⁰.comap φ) (p q : K[X]) : liftMonoidWith
ZeroHom φ hφ (algebraMap _ _ p) / liftMonoidWithZeroHom φ hφ (algebraMap _ _ q) 
= φ p / φ q
参数：φ : MonoidWithZeroHom K[X] L；hφ : K[X]⁰ <= L⁰.comap φ；p q : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RatFunc.liftMonoidWithZeroHom_apply_div`：liftMonoidWithZeroHom_apply_div
 {L : Type*} [CommGroupWithZero L] (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ <=
 L⁰.comap φ) (p q : K[X]) : l…
-/
theorem liftMonoidWithZeroHom_apply_div' {L : Type*} [CommGroupWithZero L]
    (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (p q : K[X]) :
    liftMonoidWithZeroHom φ hφ (algebraMap _ _ p) / liftMonoidWithZeroHom φ hφ (algebraMap _ _ q) =
      φ p / φ q := by
  rw [← map_div₀, liftMonoidWithZeroHom_apply_div]

set_option backward.isDefEq.respectTransparency.types false in
/-
**RatFunc.liftRingHom_apply_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftRingHom_apply_div {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰ 
<= L⁰.comap φ) (p q : K[X]) : liftRingHom φ hφ (algebraMap _ _ p / algebraMap _ 
_ q) = φ p / φ q
参数：φ : K[X] ->+* L；hφ : K[X]⁰ <= L⁰.comap φ；p q : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RatFunc.liftMonoidWithZeroHom_apply_div`：liftMonoidWithZeroHom_apply_div
 {L : Type*} [CommGroupWithZero L] (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ <=
 L⁰.comap φ) (p q : K[X]) : l…
-/
theorem liftRingHom_apply_div {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (p q : K[X]) : liftRingHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div _ hφ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**RatFunc.liftRingHom_apply_div'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftRingHom_apply_div' {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰
 <= L⁰.comap φ) (p q : K[X]) : liftRingHom φ hφ (algebraMap _ _ p) / liftRingHom
 φ hφ (algebraMap _ _ q) = φ p / φ q
参数：φ : K[X] ->+* L；hφ : K[X]⁰ <= L⁰.comap φ；p q : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RatFunc.liftMonoidWithZeroHom_apply_div'`：liftMonoidWithZeroHom_apply_di
v' {L : Type*} [CommGroupWithZero L] (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ 
<= L⁰.comap φ) (p q : K[X]) : …
-/
theorem liftRingHom_apply_div' {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (p q : K[X]) : liftRingHom φ hφ (algebraMap _ _ p) / liftRingHom φ hφ (algebraMap _ _ q) =
      φ p / φ q :=
  liftMonoidWithZeroHom_apply_div' _ hφ _ _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**RatFunc.liftRingHom_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RatFunc`。
形式化陈述：liftRingHom_algebraMap {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰
 <= L⁰.comap φ) (x : K[X]) : liftRingHom φ hφ (algebraMap K[X] _ x) = φ x
参数：φ : K[X] ->+* L；hφ : K[X]⁰ <= L⁰.comap φ；x : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `RatFunc.liftRingHom_apply_div'`：liftRingHom_apply_div' {L : Type*} [Fiel
d L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ) (p q : K[X]) : liftRingHom φ h
φ (algebraMap _ _ p)…
-/
lemma liftRingHom_algebraMap {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (x : K[X]) : liftRingHom φ hφ (algebraMap K[X] _ x) = φ x := by
  simpa using liftRingHom_apply_div' φ hφ x 1

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**RatFunc.liftRingHom_comp_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RatFunc`。
形式化陈述：liftRingHom_comp_algebraMap {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : 
K[X]⁰ <= L⁰.comap φ) : (liftRingHom φ hφ).comp (algebraMap K[X] _) = φ
参数：φ : K[X] ->+* L；hφ : K[X]⁰ <= L⁰.comap φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用引理 `RatFunc.liftRingHom_algebraMap`：liftRingHom_algebraMap {L : Type*} [Fiel
d L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L⁰.comap φ) (x : K[X]) : liftRingHom φ hφ 
(algebraMap K[X] _ x…
-/
lemma liftRingHom_comp_algebraMap {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ) :
    (liftRingHom φ hφ).comp (algebraMap K[X] _) = φ :=
  RingHom.ext fun _ ↦ liftRingHom_algebraMap _ hφ _

variable (K)
/-
**RatFunc.ofFractionRing_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_comp_algebraMap : ofFractionRing ∘ algebraMap K[X] (Fractio
nRing K[X]) = algebraMap _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RatFunc.ofFractionRing_algebraMap`：ofFractionRing_algebraMap (x : K[X]) 
: ofFractionRing (algebraMap _ (FractionRing K[X]) x) = algebraMap _ _ x
-/
theorem ofFractionRing_comp_algebraMap :
    ofFractionRing ∘ algebraMap K[X] (FractionRing K[X]) = algebraMap _ _ :=
  funext ofFractionRing_algebraMap
/-
**RatFunc.algebraMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：algebraMap_injective : Function.Injective (algebraMap K[X] K⟮X⟯)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.ofFractionRing_comp_algebraMap`：ofFractionRing_comp_algebraMap :
 ofFractionRing ∘ algebraMap K[X] (FractionRing K[X]) = algebraMap _ _
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RatFunc.ofFractionRing_injective`：ofFractionRing_injective : Function.In
jective (ofFractionRing : _ -> K⟮X⟯)
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
-/
theorem algebraMap_injective : Function.Injective (algebraMap K[X] K⟮X⟯) := by
  rw [← ofFractionRing_comp_algebraMap]
  exact ofFractionRing_injective.comp (IsFractionRing.injective _ _)

variable {K}

section LiftAlgHom

variable {L R S : Type*} [Field L] [CommRing R] [IsDomain R] [CommSemiring S] [Algebra S K[X]]
  [Algebra S L] [Algebra S R[X]] (φ : K[X] →ₐ[S] L) (hφ : K[X]⁰ ≤ L⁰.comap φ)

/-- Lift an algebra homomorphism that maps polynomials `φ : K[X] →ₐ[S] R[X]`
to a `K⟮X⟯ →ₐ[S] R⟮X⟯`,
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them. -/
/-
**RatFunc.mapAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：mapAlgHom (φ : K[X] ->ₐ[S] R[X]) (hφ : K[X]⁰ <= R[X]⁰.comap φ) : K⟮X⟯ ->ₐ[
S] R⟮X⟯
参数：φ : K[X] ->ₐ[S] R[X]；hφ : K[X]⁰ <= R[X]⁰.comap φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift an algebra homomorphism that maps polynomials `φ : K[X] →ₐ[S] R[X]`
to a `K⟮X⟯ →ₐ[S] R⟮X⟯`,
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them.
-/
def mapAlgHom (φ : K[X] →ₐ[S] R[X]) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) : K⟮X⟯ →ₐ[S] R⟮X⟯ :=
  { mapRingHom φ hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, coe_mapRingHom_eq_coe_map, algebraMap_apply r, map_apply_div,
        map_one, AlgHom.commutes] }
/-
**RatFunc.coe_mapAlgHom_eq_coe_map** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：coe_mapAlgHom_eq_coe_map (φ : K[X] ->ₐ[S] R[X]) (hφ : K[X]⁰ <= R[X]⁰.comap
 φ) : (mapAlgHom φ hφ : K⟮X⟯ -> R⟮X⟯) = map φ hφ
参数：φ : K[X] ->ₐ[S] R[X]；hφ : K[X]⁰ <= R[X]⁰.comap φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem coe_mapAlgHom_eq_coe_map (φ : K[X] →ₐ[S] R[X]) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) :
    (mapAlgHom φ hφ : K⟮X⟯ → R⟮X⟯) = map φ hφ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Lift an injective algebra homomorphism `K[X] →ₐ[S] L` to a `K⟮X⟯ →ₐ[S] L`
by mapping both the numerator and denominator and quotienting them. -/
/-
**RatFunc.liftAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：liftAlgHom : K⟮X⟯ ->ₐ[S] L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift an injective algebra homomorphism `K[X] →ₐ[S] L` to a `K⟮X⟯ →ₐ[S] L`
by mapping both the numerator and denominator and quotienting them.
-/
def liftAlgHom : K⟮X⟯ →ₐ[S] L :=
  { liftRingHom φ.toRingHom hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, AlgHom.toRingHom_eq_coe, algebraMap_apply r,
        liftRingHom_apply_div, AlgHom.coe_toRingHom, map_one, div_one, AlgHom.commutes] }

set_option backward.isDefEq.respectTransparency.types false in
/-
**RatFunc.liftAlgHom_apply_ofFractionRing_mk** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`
。
形式化陈述：liftAlgHom_apply_ofFractionRing_mk (n : K[X]) (d : K[X]⁰) : liftAlgHom φ h
φ (ofFractionRing (Localization.mk n d)) = φ n / φ d
参数：n : K[X]；d : K[X]⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RatFunc.liftMonoidWithZeroHom_apply_ofFractionRing_mk`：liftMonoidWithZer
oHom_apply_ofFractionRing_mk (φ : R[X] ->*₀ G₀) (hφ : R[X]⁰ <= G₀⁰.comap φ) (n :
 R[X]) (d : R[X]⁰) : liftMonoidWithZeroHom …
-/
theorem liftAlgHom_apply_ofFractionRing_mk (n : K[X]) (d : K[X]⁰) :
    liftAlgHom φ hφ (ofFractionRing (Localization.mk n d)) = φ n / φ d :=
  liftMonoidWithZeroHom_apply_ofFractionRing_mk _ hφ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**RatFunc.liftAlgHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftAlgHom_injective (φ : K[X] ->ₐ[S] L) (hφ : Function.Injective φ) (hφ' 
: K[X]⁰ <= L⁰.comap φ
参数：φ : K[X] ->ₐ[S] L；hφ : Function.Injective φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RatFunc.liftMonoidWithZeroHom_injective`：liftMonoidWithZeroHom_injective
 [Nontrivial R] (φ : R[X] ->*₀ G₀) (hφ : Function.Injective φ) (hφ' : R[X]⁰ <= G
₀⁰.comap φ
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `nonZeroDivisors_le_comap_nonZeroDivisors_of_injective`：nonZeroDivisors_l
e_comap_nonZeroDivisors_of_injective [NoZeroDivisors M₀'] [MonoidWithZeroHomClas
s F M₀ M₀'] (f : F) (hf : Injective f) : M₀…
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
-/
theorem liftAlgHom_injective (φ : K[X] →ₐ[S] L) (hφ : Function.Injective φ)
    (hφ' : K[X]⁰ ≤ L⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftAlgHom φ hφ') :=
  liftMonoidWithZeroHom_injective _ hφ

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**RatFunc.liftAlgHom_apply_div'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftAlgHom_apply_div' (p q : K[X]) : liftAlgHom φ hφ (algebraMap _ _ p) / 
liftAlgHom φ hφ (algebraMap _ _ q) = φ p / φ q
参数：p q : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RatFunc.liftMonoidWithZeroHom_apply_div'`：liftMonoidWithZeroHom_apply_di
v' {L : Type*} [CommGroupWithZero L] (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ 
<= L⁰.comap φ) (p q : K[X]) : …
-/
theorem liftAlgHom_apply_div' (p q : K[X]) :
    liftAlgHom φ hφ (algebraMap _ _ p) / liftAlgHom φ hφ (algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div' _ hφ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**RatFunc.liftAlgHom_apply_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftAlgHom_apply_div (p q : K[X]) : liftAlgHom φ hφ (algebraMap _ _ p / al
gebraMap _ _ q) = φ p / φ q
参数：p q : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RatFunc.liftMonoidWithZeroHom_apply_div`：liftMonoidWithZeroHom_apply_div
 {L : Type*} [CommGroupWithZero L] (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ <=
 L⁰.comap φ) (p q : K[X]) : l…
-/
theorem liftAlgHom_apply_div (p q : K[X]) :
    liftAlgHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) = φ p / φ q :=
  liftMonoidWithZeroHom_apply_div _ hφ _ _

end LiftAlgHom

variable (K)

/-- `K⟮X⟯` is the field of fractions of the polynomials over `K`. -/
/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`K⟮X⟯` is the field of fractions of the polynomials over `K`.
-/
instance : IsFractionRing K[X] K⟮X⟯ where
  map_units y := by
    rw [← ofFractionRing_algebraMap]
    exact (toFractionRingRingEquiv K).symm.toRingHom.isUnit_map (IsLocalization.map_units _ y)
  exists_of_eq {x y} := by
    rw [← ofFractionRing_algebraMap, ← ofFractionRing_algebraMap]
    exact fun h ↦ IsLocalization.exists_of_eq ((toFractionRingRingEquiv K).symm.injective h)
  surj := by
    rintro ⟨z⟩
    convert! IsLocalization.surj K[X]⁰ z
    simp only [← ofFractionRing_algebraMap, ← ofFractionRing_mul,
      ofFractionRing.injEq]

variable {K}
/-
**RatFunc.algebraMap_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：algebraMap_ne_zero {x : K[X]} (hx : x != 0) : algebraMap K[X] K⟮X⟯ x != 0
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `Polynomial.instIsCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : Semi
ring R] [IsCancelAdd R] [IsCancelMulZero R], IsCancelMulZero (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem algebraMap_ne_zero {x : K[X]} (hx : x ≠ 0) : algebraMap K[X] K⟮X⟯ x ≠ 0 := by
  simpa

@[simp]
/-
**RatFunc.liftOn_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftOn_div {P : Sort v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : forall 
p, f p 0 = f 0 1) (H' : forall {p q p' q'} (_hq : q != 0) (_hq' : q' != 0), q' *
 p = q * p' -> f p q = f p' q') (H : forall {p q p' q'} (_hq : q in K[X]⁰) (_hq'
 : q' in K[X]⁰), q' * p = q * p' -> f p q = f p' q'
参数：p q : K[X]；f : K[X] -> K[X] -> P；f0 : forall p, f p 0 = f 0 1；H' : forall {p 
q p' q'} (_hq : q != 0) (_hq' : q' != 0), q' * p = q * p' -> f p q = f p' q'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.mk_eq_div`：mk_eq_div (p q : K[X]) : RatFunc.mk p q = algebraMap 
_ _ p / algebraMap _ _ q
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `RatFunc.liftOn_mk`：liftOn_mk {P : Sort v} (p q : K[X]) (f : K[X] -> K[X]
 -> P) (f0 : forall p, f p 0 = f 0 1) (H' : forall {p q p' q'} (_hq : q != 0) (_
hq' : q…
-/
theorem liftOn_div {P : Sort v} (p q : K[X]) (f : K[X] → K[X] → P) (f0 : ∀ p, f p 0 = f 0 1)
    (H' : ∀ {p q p' q'} (_hq : q ≠ 0) (_hq' : q' ≠ 0), q' * p = q * p' → f p q = f p' q')
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q' :=
      fun {_ _ _ _} hq hq' h => H' (nonZeroDivisors.ne_zero hq) (nonZeroDivisors.ne_zero hq') h) :
    (RatFunc.liftOn (algebraMap _ K⟮X⟯ p / algebraMap _ _ q)) f @H = f p q := by
  rw [← mk_eq_div, liftOn_mk _ _ f f0 @H']

@[simp]
/-
**RatFunc.liftOn'_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDomain K] {P : Sort v} (p q
 : Polynomial K)   (f : Polynomial K → Polynomial K → P),   (∀ (p : Polynomial K
), f p 0 = f 0 1) →     ∀ (H : ∀ {p q a : Polynomial K}, q ≠ 0 → a ≠ 0 → f (a * 
p) (a * q) = f p q),       ((algebraMap (Polynomial K) (RatFunc K)) p / (algebra
Map (Polynomial K) (RatFunc K)) q).liftOn' f H = f p q
参数：p q : Polynomial K；f : Polynomial K → Polynomial K → P；∀ (p : Polynomial K), 
f p 0 = f 0 1；H : ∀ {p q a : Polynomial K}, q ≠ 0 → a ≠ 0 → f (a * p) (a * q) = 
f p q；(algebraMap (Polynomial K) (RatFunc K)) p / (algebraMap (Polynomial K) (Ra
tFunc K)) q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.liftOn'`：liftOn'_div {P : Sort v} (p q : K[X]) (f : K[X] -> K[X]
 -> P) (f0 : forall p, f p 0 = f 0 1) (H) : (RatFunc.liftOn' (algebraMap _ K⟮X⟯ 
p / a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.liftOn'_def`：∀ {K : Type u_1} [inst : CommRing K] [inst_1 : IsDo
main K] {P : Sort u_2} (x : RatFunc K)   (f : Polynomial K → Polynomial K → P) (
H : ∀ {p …
· 使用定理 `RatFunc.liftOn_condition_of_liftOn'_condition`：∀ {K : Type u} [inst : Co
mmRing K] {P : Sort v} {f : Polynomial K → Polynomial K → P},   (∀ {p q a : Poly
nomial K}, q ≠ 0 → a ≠ 0 → f (a * p…
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `RatFunc.liftOn_div`：liftOn_div {P : Sort v} (p q : K[X]) (f : K[X] -> K[
X] -> P) (f0 : forall p, f p 0 = f 0 1) (H' : forall {p q p' q'} (_hq : q != 0) 
(_hq' : …
-/
theorem liftOn'_div {P : Sort v} (p q : K[X]) (f : K[X] → K[X] → P) (f0 : ∀ p, f p 0 = f 0 1)
    (H) :
    (RatFunc.liftOn' (algebraMap _ K⟮X⟯ p / algebraMap _ _ q)) f @H = f p q := by
  rw [RatFunc.liftOn', liftOn_div _ _ _ f0]
  apply liftOn_condition_of_liftOn'_condition H

/-- Induction principle for `K⟮X⟯`: if `f p q : P (p / q)` for all `p q : K[X]`,
then `P` holds on all elements of `K⟮X⟯`.

See also `induction_on'`, which is a recursion principle defined in terms of `RatFunc.mk`.
-/
/-
**RatFunc.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDomain K] {P : RatFunc K → 
Prop} (x : RatFunc K),   (∀ (p q : Polynomial K),       q ≠ 0 → P ((algebraMap (
Polynomial K) (RatFunc K)) p / (algebraMap (Polynomial K) (RatFunc K)) q)) →    
 P x
参数：x : RatFunc K；∀ (p q : Polynomial K),       q ≠ 0 → P ((algebraMap (Polynomia
l K) (RatFunc K)) p / (algebraMap (Polynomial K) (RatFunc K)) q)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.induction_on'`：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDo
main K] {P : RatFunc K → Prop} (x : RatFunc K),   (∀ (p q : Polynomial K), q ≠ 0
 → P (RatFu…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.mk_eq_div`：mk_eq_div (p q : K[X]) : RatFunc.mk p q = algebraMap 
_ _ p / algebraMap _ _ q

--- 原说明 ---
Induction principle for `K⟮X⟯`: if `f p q : P (p / q)` for all `p q : K[X]`,
then `P` holds on all elements of `K⟮X⟯`.

See also `induction_on'`, which is a recursion principle defined in terms of `Ra
tFunc.mk`.
-/
protected theorem induction_on {P : K⟮X⟯ → Prop} (x : K⟮X⟯)
    (f : ∀ (p q : K[X]) (_ : q ≠ 0), P (algebraMap _ K⟮X⟯ p / algebraMap _ _ q)) : P x :=
  x.induction_on' fun p q hq => by simpa using f p q hq
/-
**RatFunc.ofFractionRing_mk'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_mk' (x : K[X]) (y : K[X]⁰) : ofFractionRing (IsLocalization
.mk' _ x y) = IsLocalization.mk' K⟮X⟯ x y
参数：x : K[X]；y : K[X]⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.mk_eq_div'`：mk_eq_div' (p q : K[X]) : RatFunc.mk p q = ofFractio
nRing (algebraMap _ _ p / algebraMap _ _ q)
· 使用定理 `RatFunc.mk_eq_div`：mk_eq_div (p q : K[X]) : RatFunc.mk p q = algebraMap 
_ _ p / algebraMap _ _ q
-/
theorem ofFractionRing_mk' (x : K[X]) (y : K[X]⁰) :
    ofFractionRing (IsLocalization.mk' _ x y) =
      IsLocalization.mk' K⟮X⟯ x y := by
  rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, ← mk_eq_div', ← mk_eq_div]
/-
**RatFunc.mk_eq_mk'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：mk_eq_mk' (f : Polynomial K) {g : Polynomial K} (hg : g != 0) : RatFunc.mk
 f g = IsLocalization.mk' K⟮X⟯ f ⟨g, mem_nonZeroDivisors_iff_ne_zero.2 hg⟩
参数：f : Polynomial K；hg : g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.mk_eq_div`：mk_eq_div (p q : K[X]) : RatFunc.mk p q = algebraMap 
_ _ p / algebraMap _ _ q
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_eq_mk' (f : Polynomial K) {g : Polynomial K} (hg : g ≠ 0) :
    RatFunc.mk f g = IsLocalization.mk' K⟮X⟯ f
      ⟨g, mem_nonZeroDivisors_iff_ne_zero.2 hg⟩ := by
  simp only [mk_eq_div, IsFractionRing.mk'_eq_div]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**RatFunc.ofFractionRing_eq** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_eq : (ofFractionRing : FractionRing K[X] -> K⟮X⟯) = IsLocal
ization.algEquiv K[X]⁰ _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `Localization.induction_on`：induction_on {p : Localization S -> Prop} (x)
 (H : forall y : M × S, p (mk y.1 y.2)) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_eq_mk'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} (x : R) (y : ↥M),   Localization.mk x y = IsLocalization.mk' (L
ocalization M) x y
· 使用定理 `RatFunc.ofFractionRing_mk'`：ofFractionRing_mk' (x : K[X]) (y : K[X]⁰) : 
ofFractionRing (IsLocalization.mk' _ x y) = IsLocalization.mk' K⟮X⟯ x y
· 使用定理 `IsLocalization.algEquiv_apply`：∀ {R : Type u_1} [inst : CommSemiring R] 
(M : Submonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFractionRing_eq :
    (ofFractionRing : FractionRing K[X] → K⟮X⟯) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun x =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.map_mk', RingHom.id_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**RatFunc.toFractionRing_eq** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：toFractionRing_eq : (toFractionRing : K⟮X⟯ -> FractionRing K[X]) = IsLocal
ization.algEquiv K[X]⁰ _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `Localization.induction_on`：induction_on {p : Localization S -> Prop} (x)
 (H : forall y : M × S, p (mk y.1 y.2)) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_eq_mk'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} (x : R) (y : ↥M),   Localization.mk x y = IsLocalization.mk' (L
ocalization M) x y
· 使用定理 `RatFunc.ofFractionRing_mk'`：ofFractionRing_mk' (x : K[X]) (y : K[X]⁰) : 
ofFractionRing (IsLocalization.mk' _ x y) = IsLocalization.mk' K⟮X⟯ x y
· 使用定理 `IsLocalization.algEquiv_apply`：∀ {R : Type u_1} [inst : CommSemiring R] 
(M : Submonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFractionRing_eq :
    (toFractionRing : K⟮X⟯ → FractionRing K[X]) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun ⟨x⟩ =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.map_mk', RingHom.id_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**RatFunc.toFractionRingRingEquiv_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：toFractionRingRingEquiv_symm_eq : (toFractionRingRingEquiv K).symm = (IsLo
calization.algEquiv K[X]⁰ _ _).toRingEquiv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.ofFractionRing_eq`：ofFractionRing_eq : (ofFractionRing : Fractio
nRing K[X] -> K⟮X⟯) = IsLocalization.algEquiv K[X]⁰ _ _
· 使用定理 `RatFunc.toFractionRing_eq`：toFractionRing_eq : (toFractionRing : K⟮X⟯ ->
 FractionRing K[X]) = IsLocalization.algEquiv K[X]⁰ _ _
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingEquiv.mk.congr_simp`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] 
[inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S]   (toEquiv toEquiv_1 : R ≃ S)
 (e_toEquiv :…
· 使用定理 `IsLocalization.algEquiv_apply`：∀ {R : Type u_1} [inst : CommSemiring R] 
(M : Submonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFractionRingRingEquiv_symm_eq :
    (toFractionRingRingEquiv K).symm = (IsLocalization.algEquiv K[X]⁰ _ _).toRingEquiv := by
  ext x
  simp [toFractionRingRingEquiv, ofFractionRing_eq]

section lift

/-
As `R⟮X⟯` is a one-field-struct, we need to specialize the following instances of
`FractionRing`.
-/

variable (R L : Type*) [CommRing R] [Field L] [IsDomain R] [Algebra R[X] L] [FaithfulSMul R[X] L]

/-- `FractionRing.liftAlgebra` specialized to `R⟮X⟯`.

This is a scoped instance because it creates a diamond when `L = R⟮X⟯`. -/
/-
**RatFunc.liftAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：(R : Type u_1) →   (L : Type u_2) →     [inst : CommRing R] →       [inst_
1 : Field L] →         [inst_2 : IsDomain R] →           [inst_3 : Algebra (Poly
nomial R) L] → [FaithfulSMul (Polynomial R) L] → Algebra (RatFunc R) L
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)

--- 原说明 ---
`FractionRing.liftAlgebra` specialized to `R⟮X⟯`.

This is a scoped instance because it creates a diamond when `L = R⟮X⟯`.
-/
scoped instance liftAlgebra : Algebra R⟮X⟯ L :=
  RingHom.toAlgebra (IsFractionRing.lift (FaithfulSMul.algebraMap_injective R[X] _))

/-- `FractionRing.isScalarTower_liftAlgebra` specialized to `R⟮X⟯`. -/
/-
**RatFunc.isScalarTower_liftAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
形式化陈述：isScalarTower_liftAlgebra : IsScalarTower R[X] R⟮X⟯ L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.lift_algebraMap`：lift_algebraMap (hg : Injective g) (x) :
 lift hg (algebraMap A K x) = g x

--- 原说明 ---
`FractionRing.isScalarTower_liftAlgebra` specialized to `R⟮X⟯`.
-/
instance isScalarTower_liftAlgebra :
    IsScalarTower R[X] R⟮X⟯ L :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R[X] L) x).symm

attribute [local instance] Polynomial.algebra

/-- `FractionRing.instFaithfulSMul` specialized to `R⟮X⟯`. -/
/-
**RatFunc.faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
形式化陈述：faithfulSMul (K E : Type*) [Field K] [Field E] [Algebra K E] [FaithfulSMul
 K E] : FaithfulSMul K[X] E⟮X⟯
参数：K E : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)

--- 原说明 ---
`FractionRing.instFaithfulSMul` specialized to `R⟮X⟯`.
-/
instance faithfulSMul (K E : Type*) [Field K] [Field E] [Algebra K E]
    [FaithfulSMul K E] : FaithfulSMul K[X] E⟮X⟯ :=
  (faithfulSMul_iff_algebraMap_injective ..).mpr <|
    (IsFractionRing.injective E[X] _).comp
      (Polynomial.map_injective _ <| FaithfulSMul.algebraMap_injective K E)

section rank

attribute [local instance] Polynomial.algebra

variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

/-
**RatFunc.rank_ratFunc_ratFunc** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：rank_ratFunc_ratFunc : Module.rank k⟮X⟯ K⟮X⟯ = Module.rank k K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.IsAlgebraic.rank_of_isFractionRing`：rank_of_isFractionRing (S' :
 Type u) [CommRing S'] [Algebra R S'] [Algebra S S'] [Module R' S'] [IsScalarTow
er R R' S'] [IsScalarTower R S S…
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `instFaithfulSMulPolynomial`：∀ (R : Type u_1) (A : Type u_3) [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A],   F
aithfulSMul (Pol…
· 使用定理 `instIsAlgebraicPolynomialOfNoZeroDivisors_1`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [alg : A
lgebra.IsAlgebraic R S] [NoZeroDi…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `RatFunc.instIsScalarTowerPolynomial`：∀ {K : Type u} [inst : CommRing K] 
{R : Type u_1} [IsDomain K] [inst_2 : Monoid R]   [inst_3 : DistribMulAction R (
Polynomial K)] [inst_4 : …
· 使用定理 `rank_polynomial_polynomial`：rank_polynomial_polynomial : Module.rank R[X
] S[X] = Module.rank R S
-/
theorem rank_ratFunc_ratFunc : Module.rank k⟮X⟯ K⟮X⟯ = Module.rank k K := by
  rw [Algebra.IsAlgebraic.rank_of_isFractionRing k[X] k⟮X⟯ K[X] K⟮X⟯,
    rank_polynomial_polynomial]
/-
**RatFunc.finrank_ratFunc_ratFunc** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：finrank_ratFunc_ratFunc : Module.finrank k⟮X⟯ K⟮X⟯ = Module.finrank k K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `RatFunc.rank_ratFunc_ratFunc`：rank_ratFunc_ratFunc : Module.rank k⟮X⟯ K⟮
X⟯ = Module.rank k K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_of_rank_eq`：finrank_eq_of_rank_eq {n : Nat} (h : Modul
e.rank R M = ↑n) : finrank R M = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用引理 `Module.rank_lt_aleph0_iff`：rank_lt_aleph0_iff : Module.rank R M < ℵ₀ ↔ M
odule.Finite R M
· 使用定理 `Module.finrank_of_not_finite`：finrank_of_not_finite (h : ¬Module.Finite 
R M) : finrank R M = 0
-/
theorem finrank_ratFunc_ratFunc : Module.finrank k⟮X⟯ K⟮X⟯ = Module.finrank k K := by
  by_cases hf : Module.Finite k⟮X⟯ K⟮X⟯
  · have hrank := rank_ratFunc_ratFunc k K
    rw [← Module.finrank_eq_rank] at hrank
    exact (Module.finrank_eq_of_rank_eq hrank.symm).symm
  · have hf' : ¬ Module.Finite k K := by
      rwa [← Module.rank_lt_aleph0_iff, ← rank_ratFunc_ratFunc, Module.rank_lt_aleph0_iff]
    rw [Module.finrank_of_not_finite hf, Module.finrank_of_not_finite hf']

end rank

end lift

section IsScalarTower

/-- Let `A⟮X⟯ / A[X] / R / R₀` be a tower. If `A[X] / R / R₀` is a scalar tower
then so is `A⟮X⟯ / R / R₀`. -/
/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `A⟮X⟯ / A[X] / R / R₀` be a tower. If `A[X] / R / R₀` is a scalar tower
then so is `A⟮X⟯ / R / R₀`.
-/
instance (R₀ R A : Type*) [CommSemiring R₀] [CommSemiring R] [CommRing A] [IsDomain A]
    [Algebra R₀ A[X]] [SMul R₀ R] [Algebra R A[X]] [IsScalarTower R₀ R A[X]] :
    IsScalarTower R₀ R A⟮X⟯ := IsScalarTower.to₁₂₄ _ _ A[X] _

/-- Let `K / A⟮X⟯ / A[X] / R` be a tower. If `K / A[X] / R` is a scalar tower
then so is `K / A⟮X⟯ / R`. -/
/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `K / A⟮X⟯ / A[X] / R` be a tower. If `K / A[X] / R` is a scalar tower
then so is `K / A⟮X⟯ / R`.
-/
instance (R A K : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A[X] K]
    [FaithfulSMul A[X] K] [CommSemiring R] [Algebra R A[X]] [SMul R K] [IsScalarTower R A[X] K] :
    IsScalarTower R A⟮X⟯ K :=
  IsScalarTower.to₁₃₄ _ A[X] _ _

/-- Let `K / k / A⟮X⟯ / A[X]` be a tower. If `K / k / A[X]` is a scalar tower
then so is `K / k / A⟮X⟯`. -/
/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `K / k / A⟮X⟯ / A[X]` be a tower. If `K / k / A[X]` is a scalar tower
then so is `K / k / A⟮X⟯`.
-/
instance (A k K : Type*) [CommRing A] [IsDomain A] [Field k] [Field K] [Algebra A[X] k]
    [Algebra A[X] K] [SMul k K] [FaithfulSMul A[X] k] [FaithfulSMul A[X] K]
    [IsScalarTower A[X] k K] : IsScalarTower A⟮X⟯ k K where
  smul_assoc a b c := by
    induction a using RatFunc.induction_on with | f p q hq =>
    rw [← smul_right_inj hq]
    simp_rw [← smul_assoc, Algebra.smul_def q]
    field_simp [hq]
    simp

end IsScalarTower

end IsDomain

end IsFractionRing

end CommRing

section NumDenom

/-! ### Numerator and denominator -/

open GCDMonoid Polynomial

variable [Field K]

open scoped Classical in
/-- `RatFunc.numDenom` are numerator and denominator of a rational function over a field,
normalized such that the denominator is monic. -/
/-
**RatFunc.numDenom** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：numDenom (x : K⟮X⟯) : K[X] × K[X]
参数：x : K⟮X⟯。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.liftOn'`：liftOn'_div {P : Sort v} (p q : K[X]) (f : K[X] -> K[X]
 -> P) (f0 : forall p, f p 0 = f 0 1) (H) : (RatFunc.liftOn' (algebraMap _ K⟮X⟯ 
p / a…

--- 原说明 ---
`RatFunc.numDenom` are numerator and denominator of a rational function over a f
ield,
normalized such that the denominator is monic.
-/
def numDenom (x : K⟮X⟯) : K[X] × K[X] :=
  x.liftOn'
    (fun p q =>
      if q = 0 then ⟨0, 1⟩
      else
        let r := gcd p q
        ⟨Polynomial.C (q / r).leadingCoeff⁻¹ * (p / r),
          Polynomial.C (q / r).leadingCoeff⁻¹ * (q / r)⟩)
  (by
      intro p q a hq ha
      dsimp
      rw [if_neg hq, if_neg (mul_ne_zero ha hq)]
      have ha' : a.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha
      have hainv : a.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero ha'
      simp only [Prod.ext_iff, gcd_mul_left, normalize_apply a, Polynomial.coe_normUnit, mul_assoc,
        CommGroupWithZero.coe_normUnit _ ha']
      have hdeg : (gcd p q).degree ≤ q.degree := degree_gcd_le_right _ hq
      have hdeg' : (Polynomial.C a.leadingCoeff⁻¹ * gcd p q).degree ≤ q.degree := by
        rw [Polynomial.degree_mul, Polynomial.degree_C hainv, zero_add]
        exact hdeg
      have hdivp : Polynomial.C a.leadingCoeff⁻¹ * gcd p q ∣ p :=
        (C_mul_dvd hainv).mpr (gcd_dvd_left p q)
      have hdivq : Polynomial.C a.leadingCoeff⁻¹ * gcd p q ∣ q :=
        (C_mul_dvd hainv).mpr (gcd_dvd_right p q)
      rw [EuclideanDomain.mul_div_mul_cancel ha hdivp, EuclideanDomain.mul_div_mul_cancel ha hdivq,
        leadingCoeff_div hdeg, leadingCoeff_div hdeg', Polynomial.leadingCoeff_mul,
        Polynomial.leadingCoeff_C, div_C_mul, div_C_mul, ← mul_assoc, ← Polynomial.C_mul, ←
        mul_assoc, ← Polynomial.C_mul]
      constructor <;> congr <;>
        rw [inv_div, mul_comm, mul_div_assoc, ← mul_assoc, inv_inv, mul_inv_cancel₀ ha',
          one_mul, inv_div])

open scoped Classical in
@[simp]
/-
**RatFunc.numDenom_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：numDenom_div (p : K[X]) {q : K[X]} (hq : q != 0) : numDenom (algebraMap _ 
_ p / algebraMap _ _ q) = (Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd 
p q), Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q))
参数：p : K[X]；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.liftOn'`：liftOn'_div {P : Sort v} (p q : K[X]) (f : K[X] -> K[X]
 -> P) (f0 : forall p, f p 0 = f 0 1) (H) : (RatFunc.liftOn' (algebraMap _ K⟮X⟯ 
p / a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.numDenom.eq_1`：∀ {K : Type u} [inst : Field K] (x : RatFunc K), 
  x.numDenom =     x.liftOn'       (fun p q =>         if q = 0 then (0, 1)     
    else   …
· 使用定理 `RatFunc.liftOn'_div`：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDoma
in K] {P : Sort v} (p q : Polynomial K)   (f : Polynomial K → Polynomial K → P),
   (∀ (p …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `gcd_one_right`：gcd_one_right [NormalizedGCDMonoid α] (a : α) : gcd a 1 =
 1
· 使用定理 `EuclideanDomain.div_self`：div_self {a : R} (a0 : a != 0) : a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
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
· 使用定理 `EuclideanDomain.div_one`：div_one (p : R) : p / 1 = p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem numDenom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    numDenom (algebraMap _ _ p / algebraMap _ _ q) =
      (Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q),
        Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q)) := by
  rw [numDenom, liftOn'_div, if_neg hq]
  intro p
  rw [if_pos rfl, if_neg (one_ne_zero' K[X])]
  simp

/-- `RatFunc.num` is the numerator of a rational function,
normalized such that the denominator is monic. -/
/-
**RatFunc.num** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：num (x : K⟮X⟯) : K[X]
参数：x : K⟮X⟯。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RatFunc.num` is the numerator of a rational function,
normalized such that the denominator is monic.
-/
def num (x : K⟮X⟯) : K[X] :=
  x.numDenom.1

open scoped Classical in
/-
**RatFunc.num_div'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem num_div' (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    num (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) := by
  rw [num, numDenom_div _ hq]

@[simp]
/-
**RatFunc.num_zero** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_zero : num (0 : K⟮X⟯) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `gcd_one_right`：gcd_one_right [NormalizedGCDMonoid α] (a : α) : gcd a 1 =
 1
· 使用定理 `EuclideanDomain.div_self`：div_self {a : R} (a0 : a != 0) : a / a = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `EuclideanDomain.div_one`：div_one (p : R) : p / 1 = p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `_private.Mathlib.FieldTheory.RatFunc.Basic.0.RatFunc.num_div'`：∀ {K : Ty
pe u} [inst : Field K] (p : Polynomial K) {q : Polynomial K},   q ≠ 0 →     ((al
gebraMap (Polynomial K) (RatFunc K)) p / (algebraMa…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem num_zero : num (0 : K⟮X⟯) = 0 := by convert! num_div' (0 : K[X]) one_ne_zero <;> simp

open scoped Classical in
@[simp]
/-
**RatFunc.num_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_div (p q : K[X]) : num (algebraMap _ _ p / algebraMap _ _ q) = Polynom
ial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q)
参数：p q : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
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
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `RatFunc.num_zero`：num_zero : num (0 : K⟮X⟯) = 0
· 使用定理 `gcd_zero_right`：gcd_zero_right [NormalizedGCDMonoid α] (a : α) : gcd a 0
 = normalize a
· 使用定理 `EuclideanDomain.zero_div`：zero_div {a : R} : 0 / a = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.FieldTheory.RatFunc.Basic.0.RatFunc.num_div'`：∀ {K : Ty
pe u} [inst : Field K] (p : Polynomial K) {q : Polynomial K},   q ≠ 0 →     ((al
gebraMap (Polynomial K) (RatFunc K)) p / (algebraMa…
-/
theorem num_div (p q : K[X]) :
    num (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) := by
  by_cases hq : q = 0
  · simp [hq]
  · exact num_div' p hq

@[simp]
/-
**RatFunc.num_one** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_one : num (1 : K⟮X⟯) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `gcd_same`：gcd_same [NormalizedGCDMonoid α] (a : α) : gcd a a = normalize
 a
· 使用定理 `normalize_one`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Norm
alizationMonoid α], normalize 1 = 1
· 使用定理 `EuclideanDomain.div_self`：div_self {a : R} (a0 : a != 0) : a / a = 1
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `RatFunc.num_div`：num_div (p q : K[X]) : num (algebraMap _ _ p / algebraM
ap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q)
-/
theorem num_one : num (1 : K⟮X⟯) = 1 := by convert! num_div (1 : K[X]) 1 <;> simp

@[simp]
/-
**RatFunc.num_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_algebraMap (p : K[X]) : num (algebraMap _ _ p) = p
参数：p : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `gcd_one_right`：gcd_one_right [NormalizedGCDMonoid α] (a : α) : gcd a 1 =
 1
· 使用定理 `EuclideanDomain.div_self`：div_self {a : R} (a0 : a != 0) : a / a = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `EuclideanDomain.div_one`：div_one (p : R) : p / 1 = p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `RatFunc.num_div`：num_div (p q : K[X]) : num (algebraMap _ _ p / algebraM
ap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q)
-/
theorem num_algebraMap (p : K[X]) : num (algebraMap _ _ p) = p := by convert! num_div p 1 <;> simp
/-
**RatFunc.num_div_dvd** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_div_dvd (p : K[X]) {q : K[X]} (hq : q != 0) : num (algebraMap _ _ p / 
algebraMap _ _ q) ∣ p
参数：p : K[X]；hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.num_div`：num_div (p q : K[X]) : num (algebraMap _ _ p / algebraM
ap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q)
· 使用定理 `Polynomial.C_mul_dvd`：C_mul_dvd (ha : a != 0) : C a * p ∣ q ↔ p ∣ q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `right_div_gcd_ne_zero`：right_div_gcd_ne_zero {p q : R} (hq : q != 0) : q
 / GCDMonoid.gcd p q != 0
· 使用定理 `EuclideanDomain.div_dvd_of_dvd`：div_dvd_of_dvd {p q : R} (hpq : q ∣ p) :
 p / q ∣ p
· 使用定理 `GCDMonoid.gcd_dvd_left`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [
self : GCDMonoid α] (a b : α), gcd a b ∣ a
-/
theorem num_div_dvd (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    num (algebraMap _ _ p / algebraMap _ _ q) ∣ p := by
  classical
  rw [num_div _ q, C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_left p q)
  · simpa only [Ne, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq

open scoped Classical in
/-- A version of `num_div_dvd` with the LHS in simp normal form -/
@[simp]
/-
**RatFunc.num_div_dvd'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_div_dvd' (p : K[X]) {q : K[X]} (hq : q != 0) : C (q / gcd p q).leading
Coeff⁻¹ * (p / gcd p q) ∣ p
参数：p : K[X]；hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.num_div`：num_div (p q : K[X]) : num (algebraMap _ _ p / algebraM
ap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q)
· 使用定理 `RatFunc.num_div_dvd`：num_div_dvd (p : K[X]) {q : K[X]} (hq : q != 0) : n
um (algebraMap _ _ p / algebraMap _ _ q) ∣ p

--- 原说明 ---
A version of `num_div_dvd` with the LHS in simp normal form
-/
theorem num_div_dvd' (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q) ∣ p := by simpa using num_div_dvd p hq

/-- `RatFunc.denom` is the denominator of a rational function,
normalized such that it is monic. -/
/-
**RatFunc.denom** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：denom (x : K⟮X⟯) : K[X]
参数：x : K⟮X⟯。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RatFunc.denom` is the denominator of a rational function,
normalized such that it is monic.
-/
def denom (x : K⟮X⟯) : K[X] :=
  x.numDenom.2

open scoped Classical in
@[simp]
/-
**RatFunc.denom_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：denom_div (p : K[X]) {q : K[X]} (hq : q != 0) : denom (algebraMap _ _ p / 
algebraMap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q)
参数：p : K[X]；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.denom.eq_1`：∀ {K : Type u} [inst : Field K] (x : RatFunc K), x.d
enom = x.numDenom.2
· 使用定理 `RatFunc.numDenom_div`：numDenom_div (p : K[X]) {q : K[X]} (hq : q != 0) :
 numDenom (algebraMap _ _ p / algebraMap _ _ q) = (Polynomial.C (q / gcd p q).le
adingCoeff…
-/
theorem denom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    denom (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (q / gcd p q) := by
  rw [denom, numDenom_div _ hq]
/-
**RatFunc.monic_denom** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：monic_denom (x : K⟮X⟯) : (denom x).Monic
参数：x : K⟮X⟯。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.induction_on`：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDom
ain K] {P : RatFunc K → Prop} (x : RatFunc K),   (∀ (p q : Polynomial K),       
q ≠ 0 → P …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.denom_div`：denom_div (p : K[X]) {q : K[X]} (hq : q != 0) : denom
 (algebraMap _ _ p / algebraMap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff
⁻¹ * (q…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用定理 `right_div_gcd_ne_zero`：right_div_gcd_ne_zero {p q : R} (hq : q != 0) : q
 / GCDMonoid.gcd p q != 0
-/
theorem monic_denom (x : K⟮X⟯) : (denom x).Monic := by
  classical
  induction x using RatFunc.induction_on with
  | f p q hq =>
    rw [denom_div p hq, mul_comm]
    exact Polynomial.monic_mul_leadingCoeff_inv (right_div_gcd_ne_zero hq)
/-
**RatFunc.denom_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：denom_ne_zero (x : K⟮X⟯) : denom x != 0
参数：x : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `RatFunc.monic_denom`：monic_denom (x : K⟮X⟯) : (denom x).Monic
-/
theorem denom_ne_zero (x : K⟮X⟯) : denom x ≠ 0 :=
  (monic_denom x).ne_zero

@[simp]
/-
**RatFunc.denom_zero** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：denom_zero : denom (0 : K⟮X⟯) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `gcd_one_right`：gcd_one_right [NormalizedGCDMonoid α] (a : α) : gcd a 1 =
 1
· 使用定理 `EuclideanDomain.div_self`：div_self {a : R} (a0 : a != 0) : a / a = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `RatFunc.denom_div`：denom_div (p : K[X]) {q : K[X]} (hq : q != 0) : denom
 (algebraMap _ _ p / algebraMap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff
⁻¹ * (q…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem denom_zero : denom (0 : K⟮X⟯) = 1 := by
  convert! denom_div (0 : K[X]) one_ne_zero <;> simp

@[simp]
/-
**RatFunc.denom_one** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：denom_one : denom (1 : K⟮X⟯) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `gcd_same`：gcd_same [NormalizedGCDMonoid α] (a : α) : gcd a a = normalize
 a
· 使用定理 `normalize_one`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Norm
alizationMonoid α], normalize 1 = 1
· 使用定理 `EuclideanDomain.div_self`：div_self {a : R} (a0 : a != 0) : a / a = 1
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `RatFunc.denom_div`：denom_div (p : K[X]) {q : K[X]} (hq : q != 0) : denom
 (algebraMap _ _ p / algebraMap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff
⁻¹ * (q…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem denom_one : denom (1 : K⟮X⟯) = 1 := by
  convert! denom_div (1 : K[X]) one_ne_zero <;> simp

@[simp]
/-
**RatFunc.denom_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：denom_algebraMap (p : K[X]) : denom (algebraMap _ K⟮X⟯ p) = 1
参数：p : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `gcd_one_right`：gcd_one_right [NormalizedGCDMonoid α] (a : α) : gcd a 1 =
 1
· 使用定理 `EuclideanDomain.div_self`：div_self {a : R} (a0 : a != 0) : a / a = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `RatFunc.denom_div`：denom_div (p : K[X]) {q : K[X]} (hq : q != 0) : denom
 (algebraMap _ _ p / algebraMap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff
⁻¹ * (q…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem denom_algebraMap (p : K[X]) : denom (algebraMap _ K⟮X⟯ p) = 1 := by
  convert! denom_div p one_ne_zero <;> simp

@[simp]
/-
**RatFunc.denom_div_dvd** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：denom_div_dvd (p q : K[X]) : denom (algebraMap _ _ p / algebraMap _ _ q) ∣
 q
参数：p q : K[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
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
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `RatFunc.denom_zero`：denom_zero : denom (0 : K⟮X⟯) = 1
· 使用定理 `RatFunc.denom_div`：denom_div (p : K[X]) {q : K[X]} (hq : q != 0) : denom
 (algebraMap _ _ p / algebraMap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff
⁻¹ * (q…
· 使用定理 `Polynomial.C_mul_dvd`：C_mul_dvd (ha : a != 0) : C a * p ∣ q ↔ p ∣ q
· 使用定理 `right_div_gcd_ne_zero`：right_div_gcd_ne_zero {p q : R} (hq : q != 0) : q
 / GCDMonoid.gcd p q != 0
· 使用定理 `EuclideanDomain.div_dvd_of_dvd`：div_dvd_of_dvd {p q : R} (hpq : q ∣ p) :
 p / q ∣ p
· 使用定理 `GCDMonoid.gcd_dvd_right`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} 
[self : GCDMonoid α] (a b : α), gcd a b ∣ b
-/
theorem denom_div_dvd (p q : K[X]) : denom (algebraMap _ _ p / algebraMap _ _ q) ∣ q := by
  classical
  by_cases hq : q = 0
  · simp [hq]
  rw [denom_div _ hq, C_mul_dvd]
  · exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_right p q)
  · simpa only [Ne, inv_eq_zero, Polynomial.leadingCoeff_eq_zero] using right_div_gcd_ne_zero hq

@[simp]
/-
**RatFunc.num_div_denom** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x) / algebraMap _ _ (denom 
x) = x
参数：x : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.induction_on`：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDom
ain K] {P : RatFunc K → Prop} (x : RatFunc K),   (∀ (p q : Polynomial K),       
q ≠ 0 → P …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `right_div_gcd_ne_zero`：right_div_gcd_ne_zero {p q : R} (hq : q != 0) : q
 / GCDMonoid.gcd p q != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.num_div`：num_div (p q : K[X]) : num (algebraMap _ _ p / algebraM
ap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q)
· 使用定理 `RatFunc.denom_div`：denom_div (p : K[X]) {q : K[X]} (hq : q != 0) : denom
 (algebraMap _ _ p / algebraMap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff
⁻¹ * (q…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
· 使用定理 `RatFunc.algebraMap_ne_zero`：algebraMap_ne_zero {x : K[X]} (hx : x != 0) 
: algebraMap K[X] K⟮X⟯ x != 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.C_eq_zero`：C_eq_zero : C a = 0 ↔ a = 0
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EuclideanDomain.mul_div_assoc`：mul_div_assoc (x : R) {y z : R} (h : z ∣ 
y) : x * y / z = x * (y / z)
· 使用定理 `GCDMonoid.gcd_dvd_left`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [
self : GCDMonoid α] (a b : α), gcd a b ∣ a
· 使用定理 `GCDMonoid.gcd_dvd_right`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} 
[self : GCDMonoid α] (a b : α), gcd a b ∣ b
-/
theorem num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x) / algebraMap _ _ (denom x) = x := by
  classical
  induction x using RatFunc.induction_on with | _ p q hq
  have q_div_ne_zero : q / gcd p q ≠ 0 := right_div_gcd_ne_zero hq
  rw [num_div p q, denom_div p hq, map_mul, map_mul, mul_div_mul_left,
    div_eq_div_iff, ← map_mul, ← map_mul, mul_comm _ q, ←
    EuclideanDomain.mul_div_assoc, ← EuclideanDomain.mul_div_assoc, mul_comm]
  · apply gcd_dvd_right
  · apply gcd_dvd_left
  · exact algebraMap_ne_zero q_div_ne_zero
  · exact algebraMap_ne_zero hq
  · refine algebraMap_ne_zero (mt Polynomial.C_eq_zero.mp ?_)
    exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr q_div_ne_zero)
/-
**RatFunc.isCoprime_num_denom** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：isCoprime_num_denom (x : K⟮X⟯) : IsCoprime x.num x.denom
参数：x : K⟮X⟯。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.induction_on`：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDom
ain K] {P : RatFunc K → Prop} (x : RatFunc K),   (∀ (p q : Polynomial K),       
q ≠ 0 → P …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.num_div`：num_div (p q : K[X]) : num (algebraMap _ _ p / algebraM
ap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * (p / gcd p q)
· 使用定理 `RatFunc.denom_div`：denom_div (p : K[X]) {q : K[X]} (hq : q != 0) : denom
 (algebraMap _ _ p / algebraMap _ _ q) = Polynomial.C (q / gcd p q).leadingCoeff
⁻¹ * (q…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCoprime_mul_unit_left`：isCoprime_mul_unit_left (hu : IsUnit x) (y z : 
R) : IsCoprime (x * y) (x * z) ↔ IsCoprime y z
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `IsUnit.inv`：inv (h : IsUnit a) : IsUnit a⁻¹
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `right_div_gcd_ne_zero`：right_div_gcd_ne_zero {p q : R} (hq : q != 0) : q
 / GCDMonoid.gcd p q != 0
· 使用定理 `isCoprime_div_gcd_div_gcd`：isCoprime_div_gcd_div_gcd (hq : q != 0) : IsC
oprime (p / GCDMonoid.gcd p q) (q / GCDMonoid.gcd p q)
-/
theorem isCoprime_num_denom (x : K⟮X⟯) : IsCoprime x.num x.denom := by
  classical
  induction x using RatFunc.induction_on with | _ p q hq
  rw [num_div, denom_div _ hq]
  exact (isCoprime_mul_unit_left
    ((leadingCoeff_ne_zero.2 <| right_div_gcd_ne_zero hq).isUnit.inv.map C) _ _).2
      (isCoprime_div_gcd_div_gcd hq)

@[simp]
/-
**RatFunc.num_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_eq_zero_iff {x : K⟮X⟯} : num x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `RatFunc.num_zero`：num_zero : num (0 : K⟮X⟯) = 0
-/
theorem num_eq_zero_iff {x : K⟮X⟯} : num x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← num_div_denom x, h, map_zero, zero_div], fun h => h.symm ▸ num_zero⟩
/-
**RatFunc.num_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_ne_zero {x : K⟮X⟯} (hx : x != 0) : num x != 0
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RatFunc.num_eq_zero_iff`：num_eq_zero_iff {x : K⟮X⟯} : num x = 0 ↔ x = 0
-/
theorem num_ne_zero {x : K⟮X⟯} (hx : x ≠ 0) : num x ≠ 0 :=
  mt num_eq_zero_iff.mp hx
/-
**RatFunc.num_mul_eq_mul_denom_iff** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_mul_eq_mul_denom_iff {x : K⟮X⟯} {p q : K[X]} (hq : q != 0) : x.num * q
 = p * x.denom ↔ x = algebraMap _ _ p / algebraMap _ _ q
参数：hq : q != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `RatFunc.algebraMap_injective`：algebraMap_injective : Function.Injective 
(algebraMap K[X] K⟮X⟯)
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `RatFunc.algebraMap_ne_zero`：algebraMap_ne_zero {x : K[X]} (hx : x != 0) 
: algebraMap K[X] K⟮X⟯ x != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem num_mul_eq_mul_denom_iff {x : K⟮X⟯} {p q : K[X]} (hq : q ≠ 0) :
    x.num * q = p * x.denom ↔ x = algebraMap _ _ p / algebraMap _ _ q := by
  rw [← (algebraMap_injective K).eq_iff, eq_div_iff (algebraMap_ne_zero hq)]
  conv_rhs => rw [← num_div_denom x]
  rw [map_mul, map_mul, div_eq_mul_inv, mul_assoc, mul_comm (Inv.inv _), ←
    mul_assoc, ← div_eq_mul_inv, div_eq_iff]
  exact algebraMap_ne_zero (denom_ne_zero x)
/-
**RatFunc.num_denom_add** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_denom_add (x y : K⟮X⟯) : (x + y).num * (x.denom * y.denom) = (x.num * 
y.denom + x.denom * y.num) * (x + y).denom
参数：x y : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.num_mul_eq_mul_denom_iff`：num_mul_eq_mul_denom_iff {x : K⟮X⟯} {p
 q : K[X]} (hq : q != 0) : x.num * q = p * x.denom ↔ x = algebraMap _ _ p / alge
braMap _ _ q
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
· 使用定理 `div_add_div`：div_add_div (a : K) (c : K) (hb : b != 0) (hd : d != 0) : a
 / b + c / d = (a * d + b * c) / (b * d)
· 使用定理 `RatFunc.algebraMap_ne_zero`：algebraMap_ne_zero {x : K[X]} (hx : x != 0) 
: algebraMap K[X] K⟮X⟯ x != 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem num_denom_add (x y : K⟮X⟯) :
    (x + y).num * (x.denom * y.denom) = (x.num * y.denom + x.denom * y.num) * (x + y).denom :=
  (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr <| by
    conv_lhs => rw [← num_div_denom x, ← num_div_denom y]
    rw [div_add_div, map_mul, map_add, map_mul, map_mul]
    · exact algebraMap_ne_zero (denom_ne_zero x)
    · exact algebraMap_ne_zero (denom_ne_zero y)
/-
**RatFunc.num_denom_neg** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_denom_neg (x : K⟮X⟯) : (-x).num * x.denom = -x.num * (-x).denom
参数：x : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.num_mul_eq_mul_denom_iff`：num_mul_eq_mul_denom_iff {x : K⟮X⟯} {p
 q : K[X]} (hq : q != 0) : x.num * q = p * x.denom ↔ x = algebraMap _ _ p / alge
braMap _ _ q
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
-/
theorem num_denom_neg (x : K⟮X⟯) : (-x).num * x.denom = -x.num * (-x).denom := by
  rw [num_mul_eq_mul_denom_iff (denom_ne_zero x), map_neg, neg_div, num_div_denom]
/-
**RatFunc.num_denom_mul** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_denom_mul (x y : K⟮X⟯) : (x * y).num * (x.denom * y.denom) = x.num * y
.num * (x * y).denom
参数：x y : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.num_mul_eq_mul_denom_iff`：num_mul_eq_mul_denom_iff {x : K⟮X⟯} {p
 q : K[X]} (hq : q != 0) : x.num * q = p * x.denom ↔ x = algebraMap _ _ p / alge
braMap _ _ q
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem num_denom_mul (x y : K⟮X⟯) :
    (x * y).num * (x.denom * y.denom) = x.num * y.num * (x * y).denom :=
  (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr <| by
    conv_lhs =>
      rw [← num_div_denom x, ← num_div_denom y, div_mul_div_comm, ← map_mul, ← map_mul]
/-
**RatFunc.num_dvd** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_dvd {x : K⟮X⟯} {p : K[X]} (hp : p != 0) : num x ∣ p ↔ exists q : K[X],
 q != 0 ∧ x = algebraMap _ _ p / algebraMap _ _ q
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `RatFunc.algebraMap_ne_zero`：algebraMap_ne_zero {x : K[X]} (hx : x != 0) 
: algebraMap K[X] K⟮X⟯ x != 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `RatFunc.num_div_dvd`：num_div_dvd (p : K[X]) {q : K[X]} (hq : q != 0) : n
um (algebraMap _ _ p / algebraMap _ _ q) ∣ p
-/
theorem num_dvd {x : K⟮X⟯} {p : K[X]} (hp : p ≠ 0) :
    num x ∣ p ↔ ∃ q : K[X], q ≠ 0 ∧ x = algebraMap _ _ p / algebraMap _ _ q := by
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨_hx, hq⟩ := mul_ne_zero_iff.mp hp
    use denom x * q
    rw [map_mul, map_mul, ← div_mul_div_comm, div_self, mul_one, num_div_denom]
    · exact ⟨mul_ne_zero (denom_ne_zero x) hq, rfl⟩
    · exact algebraMap_ne_zero hq
  · rintro ⟨q, hq, rfl⟩
    exact num_div_dvd p hq
/-
**RatFunc.denom_dvd** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：denom_dvd {x : K⟮X⟯} {q : K[X]} (hq : q != 0) : denom x ∣ q ↔ exists p : K
[X], x = algebraMap _ _ p / algebraMap _ _ q
参数：hq : q != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `RatFunc.algebraMap_ne_zero`：algebraMap_ne_zero {x : K[X]} (hx : x != 0) 
: algebraMap K[X] K⟮X⟯ x != 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
· 使用定理 `RatFunc.denom_div_dvd`：denom_div_dvd (p q : K[X]) : denom (algebraMap _ 
_ p / algebraMap _ _ q) ∣ q
-/
theorem denom_dvd {x : K⟮X⟯} {q : K[X]} (hq : q ≠ 0) :
    denom x ∣ q ↔ ∃ p : K[X], x = algebraMap _ _ p / algebraMap _ _ q := by
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨_hx, hp⟩ := mul_ne_zero_iff.mp hq
    use num x * p
    rw [map_mul, map_mul, ← div_mul_div_comm, div_self, mul_one, num_div_denom]
    exact algebraMap_ne_zero hp
  · rintro ⟨p, rfl⟩
    exact denom_div_dvd p q
/-
**RatFunc.num_mul_dvd** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_mul_dvd (x y : K⟮X⟯) : num (x * y) ∣ num x * num y
参数：x y : K⟮X⟯。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `RatFunc.num_zero`：num_zero : num (0 : K⟮X⟯) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `RatFunc.num_dvd`：num_dvd {x : K⟮X⟯} {p : K[X]} (hp : p != 0) : num x ∣ p
 ↔ exists q : K[X], q != 0 ∧ x = algebraMap _ _ p / algebraMap _ _ q
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `RatFunc.num_ne_zero`：num_ne_zero {x : K⟮X⟯} (hx : x != 0) : num x != 0
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
-/
theorem num_mul_dvd (x y : K⟮X⟯) : num (x * y) ∣ num x * num y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [num_dvd (mul_ne_zero (num_ne_zero hx) (num_ne_zero hy))]
  refine ⟨x.denom * y.denom, mul_ne_zero (denom_ne_zero x) (denom_ne_zero y), ?_⟩
  rw [map_mul, map_mul, ← div_mul_div_comm, num_div_denom, num_div_denom]
/-
**RatFunc.denom_mul_dvd** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：denom_mul_dvd (x y : K⟮X⟯) : denom (x * y) ∣ denom x * denom y
参数：x y : K⟮X⟯。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.denom_dvd`：denom_dvd {x : K⟮X⟯} {q : K[X]} (hq : q != 0) : denom
 x ∣ q ↔ exists p : K[X], x = algebraMap _ _ p / algebraMap _ _ q
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
-/
theorem denom_mul_dvd (x y : K⟮X⟯) : denom (x * y) ∣ denom x * denom y := by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.num, ?_⟩
  rw [map_mul, map_mul, ← div_mul_div_comm, num_div_denom, num_div_denom]
/-
**RatFunc.denom_add_dvd** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：denom_add_dvd (x y : K⟮X⟯) : denom (x + y) ∣ denom x * denom y
参数：x y : K⟮X⟯。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.denom_dvd`：denom_dvd {x : K⟮X⟯} {q : K[X]} (hq : q != 0) : denom
 x ∣ q ↔ exists p : K[X], x = algebraMap _ _ p / algebraMap _ _ q
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_add_div`：div_add_div (a : K) (c : K) (hb : b != 0) (hd : d != 0) : a
 / b + c / d = (a * d + b * c) / (b * d)
· 使用定理 `RatFunc.algebraMap_ne_zero`：algebraMap_ne_zero {x : K[X]} (hx : x != 0) 
: algebraMap K[X] K⟮X⟯ x != 0
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
-/
theorem denom_add_dvd (x y : K⟮X⟯) : denom (x + y) ∣ denom x * denom y := by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.denom + x.denom * y.num, ?_⟩
  rw [map_mul, map_add, map_mul, map_mul, ← div_add_div, num_div_denom, num_div_denom]
  · exact algebraMap_ne_zero (denom_ne_zero x)
  · exact algebraMap_ne_zero (denom_ne_zero y)
/-
**RatFunc.num_inv_dvd** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：num_inv_dvd {x : K⟮X⟯} (hx : x != 0) : num x⁻¹ ∣ denom x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.num_dvd`：num_dvd {x : K⟮X⟯} {p : K[X]} (hp : p != 0) : num x ∣ p
 ↔ exists q : K[X], q != 0 ∧ x = algebraMap _ _ p / algebraMap _ _ q
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `RatFunc.num_ne_zero`：num_ne_zero {x : K⟮X⟯} (hx : x != 0) : num x != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
-/
theorem num_inv_dvd {x : K⟮X⟯} (hx : x ≠ 0) : num x⁻¹ ∣ denom x := by
  rw [num_dvd x.denom_ne_zero]
  refine ⟨x.num, num_ne_zero hx, ?_⟩
  nth_rw 1 [← x.num_div_denom]
  rw [inv_div]
/-
**RatFunc.denom_inv_dvd** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：denom_inv_dvd {x : K⟮X⟯} (hx : x != 0) : denom x⁻¹ ∣ num x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.denom_dvd`：denom_dvd {x : K⟮X⟯} {q : K[X]} (hq : q != 0) : denom
 x ∣ q ↔ exists p : K[X], x = algebraMap _ _ p / algebraMap _ _ q
· 使用定理 `RatFunc.num_ne_zero`：num_ne_zero {x : K⟮X⟯} (hx : x != 0) : num x != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
-/
theorem denom_inv_dvd {x : K⟮X⟯} (hx : x ≠ 0) : denom x⁻¹ ∣ num x := by
  rw [denom_dvd (num_ne_zero hx)]
  refine ⟨x.denom, ?_⟩
  nth_rw 1 [← x.num_div_denom]
  rw [inv_div]
/-
**RatFunc.associated_num_inv** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：associated_num_inv {x : K⟮X⟯} (hx : x != 0) : Associated (num x⁻¹) (denom 
x)
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `associated_of_dvd_dvd`：associated_of_dvd_dvd [MonoidWithZero M] [IsLeftC
ancelMulZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b
· 使用定理 `Polynomial.instIsLeftCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : 
Semiring R] [IsCancelAdd R] [IsLeftCancelMulZero R], IsLeftCancelMulZero (Polyno
mial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.num_inv_dvd`：num_inv_dvd {x : K⟮X⟯} (hx : x != 0) : num x⁻¹ ∣ de
nom x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `RatFunc.denom_inv_dvd`：denom_inv_dvd {x : K⟮X⟯} (hx : x != 0) : denom x⁻
¹ ∣ num x
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem associated_num_inv {x : K⟮X⟯} (hx : x ≠ 0) : Associated (num x⁻¹) (denom x) := by
  apply associated_of_dvd_dvd (num_inv_dvd hx)
  convert! denom_inv_dvd (inv_ne_zero hx)
  rw [inv_inv]
/-
**RatFunc.associated_denom_inv** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：associated_denom_inv {x : K⟮X⟯} (hx : x != 0) : Associated (denom x⁻¹) (nu
m x)
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `RatFunc.associated_num_inv`：associated_num_inv {x : K⟮X⟯} (hx : x != 0) 
: Associated (num x⁻¹) (denom x)
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem associated_denom_inv {x : K⟮X⟯} (hx : x ≠ 0) : Associated (denom x⁻¹) (num x) := by
  apply Associated.symm
  convert! associated_num_inv (inv_ne_zero hx)
  rw [inv_inv]
/-
**RatFunc.map_denom_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：map_denom_ne_zero {L F : Type*} [Zero L] [FunLike F K[X] L] [ZeroHomClass 
F K[X] L] (φ : F) (hφ : Function.Injective φ) (f : K⟮X⟯) : φ f.denom != 0
参数：φ : F；hφ : Function.Injective φ；f : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
-/
theorem map_denom_ne_zero {L F : Type*} [Zero L] [FunLike F K[X] L] [ZeroHomClass F K[X] L]
    (φ : F) (hφ : Function.Injective φ) (f : K⟮X⟯) : φ f.denom ≠ 0 := fun H =>
  (denom_ne_zero f) ((map_eq_zero_iff φ hφ).mp H)
/-
**RatFunc.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：map_apply {R F : Type*} [CommRing R] [IsDomain R] [FunLike F K[X] R[X]] [M
onoidHomClass F K[X] R[X]] (φ : F) (hφ : K[X]⁰ <= R[X]⁰.comap φ) (f : K⟮X⟯) : ma
p φ hφ f = algebraMap _ _ (φ f.num) / algebraMap _ _ (φ f.denom)
参数：φ : F；hφ : K[X]⁰ <= R[X]⁰.comap φ；f : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
· 使用定理 `RatFunc.map_apply_div_ne_zero`：map_apply_div_ne_zero {R F : Type*} [Comm
Ring R] [IsDomain R] [FunLike F K[X] R[X]] [MonoidHomClass F K[X] R[X]] (φ : F) 
(hφ : K[X]⁰ <= R[X]…
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
-/
theorem map_apply {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidHomClass F K[X] R[X]] (φ : F)
    (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (f : K⟮X⟯) :
    map φ hφ f = algebraMap _ _ (φ f.num) / algebraMap _ _ (φ f.denom) := by
  rw [← num_div_denom f, map_apply_div_ne_zero, num_div_denom f]
  exact denom_ne_zero _
/-
**RatFunc.liftMonoidWithZeroHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftMonoidWithZeroHom_apply {L : Type*} [CommGroupWithZero L] (φ : K[X] ->
*₀ L) (hφ : K[X]⁰ <= L⁰.comap φ) (f : K⟮X⟯) : liftMonoidWithZeroHom φ hφ f = φ f
.num / φ f.denom
参数：φ : K[X] ->*₀ L；hφ : K[X]⁰ <= L⁰.comap φ；f : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
· 使用定理 `RatFunc.liftMonoidWithZeroHom_apply_div`：liftMonoidWithZeroHom_apply_div
 {L : Type*} [CommGroupWithZero L] (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ <=
 L⁰.comap φ) (p q : K[X]) : l…
-/
theorem liftMonoidWithZeroHom_apply {L : Type*} [CommGroupWithZero L] (φ : K[X] →*₀ L)
    (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : K⟮X⟯) :
    liftMonoidWithZeroHom φ hφ f = φ f.num / φ f.denom := by
  rw [← num_div_denom f, liftMonoidWithZeroHom_apply_div, num_div_denom]

set_option backward.isDefEq.respectTransparency.types false in
/-
**RatFunc.liftRingHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftRingHom_apply {L : Type*} [Field L] (φ : K[X] ->+* L) (hφ : K[X]⁰ <= L
⁰.comap φ) (f : K⟮X⟯) : liftRingHom φ hφ f = φ f.num / φ f.denom
参数：φ : K[X] ->+* L；hφ : K[X]⁰ <= L⁰.comap φ；f : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RatFunc.liftMonoidWithZeroHom_apply`：liftMonoidWithZeroHom_apply {L : Ty
pe*} [CommGroupWithZero L] (φ : K[X] ->*₀ L) (hφ : K[X]⁰ <= L⁰.comap φ) (f : K⟮X
⟯) : liftMonoidWithZeroHo…
-/
theorem liftRingHom_apply {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (f : K⟮X⟯) : liftRingHom φ hφ f = φ f.num / φ f.denom :=
  liftMonoidWithZeroHom_apply _ hφ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**RatFunc.liftAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftAlgHom_apply {L S : Type*} [Field L] [CommSemiring S] [Algebra S K[X]]
 [Algebra S L] (φ : K[X] ->ₐ[S] L) (hφ : K[X]⁰ <= L⁰.comap φ) (f : K⟮X⟯) : liftA
lgHom φ hφ f = φ f.num / φ f.denom
参数：φ : K[X] ->ₐ[S] L；hφ : K[X]⁰ <= L⁰.comap φ；f : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RatFunc.liftMonoidWithZeroHom_apply`：liftMonoidWithZeroHom_apply {L : Ty
pe*} [CommGroupWithZero L] (φ : K[X] ->*₀ L) (hφ : K[X]⁰ <= L⁰.comap φ) (f : K⟮X
⟯) : liftMonoidWithZeroHo…
-/
theorem liftAlgHom_apply {L S : Type*} [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]
    (φ : K[X] →ₐ[S] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : K⟮X⟯) :
    liftAlgHom φ hφ f = φ f.num / φ f.denom :=
  liftMonoidWithZeroHom_apply _ hφ _
/-
**RatFunc.num_mul_denom_add_denom_mul_num_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat
Func`。
形式化陈述：num_mul_denom_add_denom_mul_num_ne_zero {x y : K⟮X⟯} (hxy : x + y != 0) : 
x.num * y.denom + x.denom * y.num != 0
参数：hxy : x + y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.num_denom_add`：num_denom_add (x y : K⟮X⟯) : (x + y).num * (x.den
om * y.denom) = (x.num * y.denom + x.denom * y.num) * (x + y).denom
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.num_ne_zero`：num_ne_zero {x : K⟮X⟯} (hx : x != 0) : num x != 0
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem num_mul_denom_add_denom_mul_num_ne_zero {x y : K⟮X⟯} (hxy : x + y ≠ 0) :
    x.num * y.denom + x.denom * y.num ≠ 0 := by
  intro h_zero
  have h := num_denom_add x y
  rw [h_zero, zero_mul] at h
  exact (mul_ne_zero (num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)) h

end NumDenom

section Char

/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Field K] {p : ℕ} [CharP K p] : CharP K⟮X⟯ p :=
  charP_of_injective_algebraMap' K p
/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Field K] {p : ℕ} [ExpChar K p] : ExpChar K⟮X⟯ p :=
  ExpChar.of_injective_algebraMap' K p
/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Field K] [CharZero K] : CharZero K⟮X⟯ :=
  Algebra.charZero_of_charZero K _

end Char

end RatFunc

