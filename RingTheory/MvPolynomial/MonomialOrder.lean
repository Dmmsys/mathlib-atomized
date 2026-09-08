/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.WellFounded
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Degree, leading coefficient and leading term of polynomials with respect to a monomial order

We consider a type `σ` of indeterminates and a commutative semiring `R`
and a monomial order `m : MonomialOrder σ`.

* `m.degree f` is the degree of `f` for the monomial ordering `m`, where the polynomial `0` has
  degree `0`. For the variant mapping polynomial `0` to `⊥` which is less than `0`, see
  `MonomialOrder.withBotDegree`.

* `m.leadingCoeff f` is the leading coefficient of `f` for the monomial ordering `m`.

* `m.Monic f` asserts that the leading coefficient of `f` is `1`.

* `m.leadingTerm f` is the leading term of `f` for the monomial ordering `m`.

* `m.sPolynomial f g` is S-polynomial of `f` and `g`.

* `m.withBotDegree f` is the degree of `f` for the monomial ordering `m`, where the polynomial `0`
  has degree `⊥`, which is not equal to `0`. `MonomialOrder.withBotDegree` is to
  `MonomialOrder.degree` as `Polynomial.degree` is to `Polynomial.natDegree`.

* `m.leadingCoeff_ne_zero_iff f` asserts that this coefficient is nonzero iff `f ≠ 0`.

* in a field, `m.isUnit_leadingCoeff f` asserts that this coefficient is a unit iff `f ≠ 0`.

* `m.degree_add_le` : the `m.degree` of `f + g` is smaller than or equal to the supremum
  of those of `f` and `g`.

* `m.degree_add_of_lt h` : the `m.degree` of `f + g` is equal to that of `f`
  if the `m.degree` of `g` is strictly smaller than that `f`.

* `m.leadingCoeff_add_of_lt h`: then, the leading coefficient of `f + g` is that of `f`.

* `m.degree_add_of_ne h` : the `m.degree` of `f + g` is equal to that the supremum
  of those of `f` and `g` if they are distinct.

* `m.degree_sub_le` : the `m.degree` of `f - g` is smaller than or equal to the supremum
  of those of `f` and `g`.

* `m.degree_sub_of_lt h` : the `m.degree` of `f - g` is equal to that of `f`
  if the `m.degree` of `g` is strictly smaller than that `f`.

* `m.leadingCoeff_sub_of_lt h`: then, the leading coefficient of `f - g` is that of `f`.

* `m.degree_mul_le`: the `m.degree` of `f * g` is smaller than or equal to the sum of those of
  `f` and `g`.

* `m.degree_mul_of_mul_leadingCoeff_ne_zero` : if the product of the leading coefficients
  is nonzero, then the degree is the sum of the degrees.

* `m.leadingCoeff_mul_of_mul_leadingCoeff_ne_zero` : if the product of the leading coefficients
  is nonzero, then the leading coefficient is that product.

* `m.degree_mul_of_left_mem_nonZeroDivisors`, `m.degree_mul_of_right_mem_nonZeroDivisors` and
  `m.degree_mul` assert the equality when the leading coefficient of `f` or `g` isn't zero divisors,
  or when `R` is a domain and `f` and `g` are nonzero.

* `m.leadingCoeff_mul_of_left_mem_nonZeroDivisors`,
  `m.leadingCoeff_mul_of_right_mem_nonZeroDivisors`
  and `m.leadingCoeff_mul` say that `m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g`

* `m.degree_pow_of_pow_leadingCoeff_ne_zero` : is the `n`th power of the leading coefficient
  of `f` is nonzero, then the degree of `f ^ n` is `n • (m.degree f)`

* `m.leadingCoeff_pow_of_pow_leadingCoeff_ne_zero` : is the `n`th power of the leading coefficient
  of `f` is nonzero, then the leading coefficient of `f ^ n` is that power.

* `m.degree_prod_of_mem_nonZeroDivisors` : the degree of a product of polynomials whose leading
  coefficients aren't zero divisors is the sum of their degrees.

* `m.leadingCoeff_prod_of_mem_nonZeroDivisors` : the leading coefficient of a product of polynomials
  whose leading coefficients aren't zero divisors is the product of their leading coefficients.

* `m.Monic.prod` : a product of monic polynomials is monic.

* `m.degree_sub_leadingTerm_lt_iff` : the degree of `f - m.leadingTerm f` is smaller than the
  degree of `f` if and only if `m.degree f ≠ 0`.

## Reference

[Becker-Weispfenning1993]

-/

@[expose] public section

namespace MonomialOrder

open MvPolynomial

open scoped MonomialOrder nonZeroDivisors

variable {σ : Type*} {m : MonomialOrder σ}

section Semiring

variable {R : Type*} [CommSemiring R]

variable (m) in
/-- the degree of a multivariate polynomial with respect to a monomial ordering, where the
polynomial `0` has degree `0`. For the variant mapping polynomial `0` to `⊥` which is less than
`0`, see `MonomialOrder.withBotDegree`. -/
/-
**MonomialOrder.degree** 是 Mathlib 中的一个定义，位于命名空间 `MonomialOrder`。
形式化陈述：degree (f : MvPolynomial σ R) : σ ->₀ Nat
参数：f : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the degree of a multivariate polynomial with respect to a monomial ordering, whe
re the
polynomial `0` has degree `0`. For the variant mapping polynomial `0` to `⊥` whi
ch is less than
`0`, see `MonomialOrder.withBotDegree`.
-/
noncomputable def degree (f : MvPolynomial σ R) : σ →₀ ℕ :=
  m.toSyn.symm (f.support.sup m.toSyn)

variable (m) in
/-- the leading coefficient of a multivariate polynomial with respect to a monomial ordering -/
/-
**MonomialOrder.leadingCoeff** 是 Mathlib 中的一个定义，位于命名空间 `MonomialOrder`。
形式化陈述：leadingCoeff (f : MvPolynomial σ R) : R
参数：f : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the leading coefficient of a multivariate polynomial with respect to a monomial 
ordering
-/
noncomputable def leadingCoeff (f : MvPolynomial σ R) : R :=
  f.coeff (m.degree f)

variable (m) in
/-- A multivariate polynomial is `Monic` with respect to a monomial order
if its leading coefficient (for that monomial order) is 1. -/
/-
**MonomialOrder.Monic** 是 Mathlib 中的一个定义，位于命名空间 `MonomialOrder`。
形式化陈述：Monic (f : MvPolynomial σ R) : Prop
参数：f : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multivariate polynomial is `Monic` with respect to a monomial order
if its leading coefficient (for that monomial order) is 1.
-/
def Monic (f : MvPolynomial σ R) : Prop :=
  m.leadingCoeff f = 1

variable (m) in
/-- The leading term of a multivariate polynomial with respect to a monomial ordering. -/
/-
**MonomialOrder.leadingTerm** 是 Mathlib 中的一个定义，位于命名空间 `MonomialOrder`。
形式化陈述：leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R
参数：f : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The leading term of a multivariate polynomial with respect to a monomial orderin
g.
-/
noncomputable def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)

@[simp]
/-
**MonomialOrder.C_mul_leadingCoeff_monomial_degree** 是 Mathlib 中的一个引理，位于命名空间 `Mo
nomialOrder`。
形式化陈述：C_mul_leadingCoeff_monomial_degree (p : MvPolynomial σ R) : MvPolynomial.C
 (m.leadingCoeff p : R) * MvPolynomial.monomial (m.degree p) (1 : R) = m.leading
Term p
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.C_mul_monomial`：C_mul_monomial : C a * monomial s a' = mono
mial s (a * a')
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MonomialOrder.leadingTerm.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) {
R : Type u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.leadingTerm f 
= (MvPolynomial.mono…
-/
lemma C_mul_leadingCoeff_monomial_degree (p : MvPolynomial σ R) :
    MvPolynomial.C (m.leadingCoeff p : R) * MvPolynomial.monomial (m.degree p) (1 : R) =
      m.leadingTerm p := by
  rw [MvPolynomial.C_mul_monomial, mul_one, leadingTerm]
/-
**MonomialOrder.Monic.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder.M
onic`。
形式化陈述：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Type u_2} [inst : CommSemiring
 R] [Subsingleton R] {f : MvPolynomial σ R},   m.Monic f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.eq_one`：Subsingleton.eq_one [One α] [Subsingleton α] (a : α
) : a = 1
-/
@[nontriviality] theorem Monic.of_subsingleton [Subsingleton R] {f : MvPolynomial σ R} :
    m.Monic f :=
  Subsingleton.eq_one (m.leadingCoeff f)
/-
**MonomialOrder.Monic.decidable** 是 Mathlib 中的一个定义，位于命名空间 `MonomialOrder.Monic`。
形式化陈述：{σ : Type u_1} →   {m : MonomialOrder σ} →     {R : Type u_2} → [inst : Co
mmSemiring R] → [DecidableEq R] → (f : MvPolynomial σ R) → Decidable (m.Monic f)
参数：f : MvPolynomial σ R；m.Monic f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance Monic.decidable [DecidableEq R] (f : MvPolynomial σ R) :
    Decidable (m.Monic f) :=
  inferInstanceAs <| Decidable (m.leadingCoeff f = 1)

@[simp]
/-
**MonomialOrder.Monic.leadingCoeff_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrd
er.Monic`。
形式化陈述：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Type u_2} [inst : CommSemiring
 R] {f : MvPolynomial σ R},   m.Monic f → m.leadingCoeff f = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monic.leadingCoeff_eq_one {f : MvPolynomial σ R} (hf : m.Monic f) : m.leadingCoeff f = 1 :=
  hf
/-
**MonomialOrder.Monic.coeff_degree** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder.Moni
c`。
形式化陈述：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Type u_2} [inst : CommSemiring
 R] {f : MvPolynomial σ R},   m.Monic f → MvPolynomial.coeff (m.degree f) f = 1
参数：m.degree f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monic.coeff_degree {f : MvPolynomial σ R} (hf : m.Monic f) : f.coeff (m.degree f) = 1 :=
  hf

@[simp]
/-
**MonomialOrder.degree_zero** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_zero : m.degree (0 : MvPolynomial σ R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_zero : m.degree (0 : MvPolynomial σ R) = 0 := by
  simp [degree]
/-
**MonomialOrder.ne_zero_of_degree_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrd
er`。
形式化陈述：ne_zero_of_degree_ne_zero {f : MvPolynomial σ R} (h : m.degree f != 0) : f
 != 0
参数：h : m.degree f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_zero_of_degree_ne_zero {f : MvPolynomial σ R} (h : m.degree f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h m.degree_zero

@[simp, nontriviality]
/-
**MonomialOrder.degree_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_subsingleton [Subsingleton R] {f : MvPolynomial σ R} : m.degree f =
 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
-/
theorem degree_subsingleton [Subsingleton R] {f : MvPolynomial σ R} :
    m.degree f = 0 := by
  rw [Subsingleton.eq_zero f, degree_zero]

@[simp]
/-
**MonomialOrder.leadingCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：leadingCoeff_zero : m.leadingCoeff (0 : MvPolynomial σ R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_zero : m.leadingCoeff (0 : MvPolynomial σ R) = 0 := by
  simp [degree, leadingCoeff]
/-
**MonomialOrder.Monic.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder.Monic`。
形式化陈述：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Type u_2} [inst : CommSemiring
 R] [Nontrivial R] {f : MvPolynomial σ R},   m.Monic f → f ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.leadingCoeff_zero`：leadingCoeff_zero : m.leadingCoeff (0 :
 MvPolynomial σ R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Monic.ne_zero [Nontrivial R] {f : MvPolynomial σ R} (hf : m.Monic f) :
    f ≠ 0 := by
  rintro rfl
  simp [Monic, leadingCoeff_zero] at hf
/-
**MonomialOrder.degree_monomial_le** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_monomial_le {d : σ ->₀ Nat} (c : R) : m.degree (monomial d c) ≼[m] 
d
参数：c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `MvPolynomial.support_monomial_subset`：support_monomial_subset : (monomia
l s a).support subseteq {s}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
-/
theorem degree_monomial_le {d : σ →₀ ℕ} (c : R) :
    m.degree (monomial d c) ≼[m] d := by
  simp only [degree, AddEquiv.apply_symm_apply]
  apply le_trans (Finset.sup_mono support_monomial_subset)
  simp only [Finset.sup_singleton, le_refl]
/-
**MonomialOrder.degree_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_monomial {d : σ ->₀ Nat} (c : R) [Decidable (c = 0)] : m.degree (mo
nomial d c) = if c = 0 then 0 else d
参数：c : R；c = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.support_monomial`：support_monomial [h : Decidable (a = 0)] 
: (monomial s a).support = if a = 0 then ∅ else {s}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `AddEquiv.symm_apply_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (x : M), e.symm (e x) = x
-/
theorem degree_monomial {d : σ →₀ ℕ} (c : R) [Decidable (c = 0)] :
    m.degree (monomial d c) = if c = 0 then 0 else d := by
  simp only [degree, support_monomial]
  split_ifs with hc <;> simp
/-
**MonomialOrder.degree_X_le_single** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_X_le_single {s : σ} : m.degree (X s : MvPolynomial σ R) ≼[m] Finsup
p.single s 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.degree_monomial_le`：degree_monomial_le {d : σ ->₀ Nat} (c 
: R) : m.degree (monomial d c) ≼[m] d
-/
theorem degree_X_le_single {s : σ} : m.degree (X s : MvPolynomial σ R) ≼[m] Finsupp.single s 1 :=
  degree_monomial_le 1
/-
**MonomialOrder.degree_X** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_X [Nontrivial R] {s : σ} : m.degree (X s : MvPolynomial σ R) = Fins
upp.single s 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_monomial`：degree_monomial {d : σ ->₀ Nat} (c : R) [
Decidable (c = 0)] : m.degree (monomial d c) = if c = 0 then 0 else d
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem degree_X [Nontrivial R] {s : σ} :
    m.degree (X s : MvPolynomial σ R) = Finsupp.single s 1 := by
  classical
  change m.degree (monomial (Finsupp.single s 1) (1 : R)) = _
  rw [degree_monomial, if_neg one_ne_zero]
/-
**MonomialOrder.degree_one** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Type u_2} [inst : CommSemiring
 R], m.degree 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_subsingleton`：degree_subsingleton [Subsingleton R] 
{f : MvPolynomial σ R} : m.degree f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.one_def`：one_def : (1 : MvPolynomial σ R) = monomial 0 1
· 使用定理 `MonomialOrder.degree_monomial`：degree_monomial {d : σ ->₀ Nat} (c : R) [
Decidable (c = 0)] : m.degree (monomial d c) = if c = 0 then 0 else d
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
@[simp] theorem degree_one : m.degree (1 : MvPolynomial σ R) = 0 := by
  nontriviality R
  classical rw [MvPolynomial.one_def, degree_monomial]
  simp

@[simp]
/-
**MonomialOrder.leadingCoeff_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：leadingCoeff_monomial {d : σ ->₀ Nat} (c : R) : m.leadingCoeff (monomial d
 c) = c
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_monomial`：degree_monomial {d : σ ->₀ Nat} (c : R) [
Decidable (c = 0)] : m.degree (monomial d c) = if c = 0 then 0 else d
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.monomial_zero`：monomial_zero {s : σ ->₀ Nat} : monomial s (
0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
theorem leadingCoeff_monomial {d : σ →₀ ℕ} (c : R) :
    m.leadingCoeff (monomial d c) = c := by
  classical
  simp only [leadingCoeff, degree_monomial]
  split_ifs with hc <;> simp [hc]
/-
**MonomialOrder.monic_monomial_one** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Type u_2} [inst : CommSemiring
 R] {d : σ →₀ ℕ},   m.Monic ((MvPolynomial.monomial d) 1)
参数：(MvPolynomial.monomial d) 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.leadingCoeff_monomial`：leadingCoeff_monomial {d : σ ->₀ Na
t} (c : R) : m.leadingCoeff (monomial d c) = c
-/
@[simp] theorem monic_monomial_one {d : σ →₀ ℕ} :
    m.Monic (monomial d (1 : R)) :=
  m.leadingCoeff_monomial 1
/-
**MonomialOrder.monic_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：monic_monomial {d : σ ->₀ Nat} {c : R} : m.Monic (monomial d c) ↔ c = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.Monic.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) {R : Ty
pe u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.Monic f = (m.leading
Coeff f = 1)
· 使用定理 `MonomialOrder.leadingCoeff_monomial`：leadingCoeff_monomial {d : σ ->₀ Na
t} (c : R) : m.leadingCoeff (monomial d c) = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem monic_monomial {d : σ →₀ ℕ} {c : R} :
    m.Monic (monomial d c) ↔ c = 1 := by
  rw [Monic, m.leadingCoeff_monomial]
/-
**MonomialOrder.leadingCoeff_X** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：leadingCoeff_X {s : σ} : m.leadingCoeff (X s : MvPolynomial σ R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.leadingCoeff_monomial`：leadingCoeff_monomial {d : σ ->₀ Na
t} (c : R) : m.leadingCoeff (monomial d c) = c
-/
theorem leadingCoeff_X {s : σ} :
    m.leadingCoeff (X s : MvPolynomial σ R) = 1 :=
  m.leadingCoeff_monomial 1
/-
**MonomialOrder.monic_X** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Type u_2} [inst : CommSemiring
 R] {s : σ}, m.Monic (MvPolynomial.X s)
参数：MvPolynomial.X s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.monic_monomial_one`：∀ {σ : Type u_1} {m : MonomialOrder σ}
 {R : Type u_2} [inst : CommSemiring R] {d : σ →₀ ℕ},   m.Monic ((MvPolynomial.m
onomial d) 1)
-/
@[simp] theorem monic_X {s : σ} :
    m.Monic (X s : MvPolynomial σ R) :=
  monic_monomial_one
/-
**MonomialOrder.leadingCoeff_one** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：leadingCoeff_one : m.leadingCoeff (1 : MvPolynomial σ R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.leadingCoeff_monomial`：leadingCoeff_monomial {d : σ ->₀ Na
t} (c : R) : m.leadingCoeff (monomial d c) = c
-/
theorem leadingCoeff_one : m.leadingCoeff (1 : MvPolynomial σ R) = 1 :=
  m.leadingCoeff_monomial 1
/-
**MonomialOrder.monic_C_one** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：monic_C_one : m.Monic (C 1 : MvPolynomial σ R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.monic_monomial_one`：∀ {σ : Type u_1} {m : MonomialOrder σ}
 {R : Type u_2} [inst : CommSemiring R] {d : σ →₀ ℕ},   m.Monic ((MvPolynomial.m
onomial d) 1)
-/
theorem monic_C_one : m.Monic (C 1 : MvPolynomial σ R) :=
  monic_monomial_one

@[simp]
/-
**MonomialOrder.monic_one** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：monic_one : m.Monic (1 : MvPolynomial σ R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.monic_monomial_one`：∀ {σ : Type u_1} {m : MonomialOrder σ}
 {R : Type u_2} [inst : CommSemiring R] {d : σ →₀ ℕ},   m.Monic ((MvPolynomial.m
onomial d) 1)
-/
lemma monic_one : m.Monic (1 : MvPolynomial σ R) := monic_monomial_one
/-
**MonomialOrder.degree_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_le_iff {f : MvPolynomial σ R} {d : σ ->₀ Nat} : m.degree f ≼[m] d ↔
 forall c in f.support, c ≼[m] d
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
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem degree_le_iff {f : MvPolynomial σ R} {d : σ →₀ ℕ} :
    m.degree f ≼[m] d ↔ ∀ c ∈ f.support, c ≼[m] d := by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.sup_le_iff, mem_support_iff, ne_eq]
/-
**MonomialOrder.degree_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_lt_iff {f : MvPolynomial σ R} {d : σ ->₀ Nat} (hd : 0 ≺[m] d) : m.d
egree f ≺[m] d ↔ forall c in f.support, c ≺[m] d
参数：hd : 0 ≺[m] d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem degree_lt_iff {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : 0 ≺[m] d) :
    m.degree f ≺[m] d ↔ ∀ c ∈ f.support, c ≺[m] d := by
  simp only [map_zero] at hd
  unfold degree
  simp only [AddEquiv.apply_symm_apply]
  exact Finset.sup_lt_iff hd
/-
**MonomialOrder.le_degree** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：le_degree {f : MvPolynomial σ R} {d : σ ->₀ Nat} (hd : d in f.support) : d
 ≼[m] m.degree f
参数：hd : d in f.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem le_degree {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    d ≼[m] m.degree f := by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.le_sup hd]
/-
**MonomialOrder.coeff_eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：coeff_eq_zero_of_lt {f : MvPolynomial σ R} {d : σ ->₀ Nat} (hd : m.degree 
f ≺[m] d) : f.coeff d = 0
参数：hd : m.degree f ≺[m] d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `MonomialOrder.le_degree`：le_degree {f : MvPolynomial σ R} {d : σ ->₀ Nat
} (hd : d in f.support) : d ≼[m] m.degree f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
-/
theorem coeff_eq_zero_of_lt {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : m.degree f ≺[m] d) :
    f.coeff d = 0 := by
  rw [← not_le] at hd
  by_contra hf
  apply hd (m.le_degree (mem_support_iff.mpr hf))
/-
**MonomialOrder.leadingCoeff_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrde
r`。
形式化陈述：leadingCoeff_ne_zero_iff {f : MvPolynomial σ R} : m.leadingCoeff f != 0 ↔ 
f != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `MonomialOrder.leadingCoeff_zero`：leadingCoeff_zero : m.leadingCoeff (0 :
 MvPolynomial σ R) = 0
· 使用定理 `MonomialOrder.leadingCoeff.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) 
{R : Type u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.leadingCoeff 
f = MvPolynomial.coef…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `MonomialOrder.degree.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) {R : T
ype u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.degree f = m.toSyn.
symm (f.support…
· 使用定理 `Finset.sup_mem_of_nonempty`：sup_mem_of_nonempty (hs : s.Nonempty) : s.su
p f in f '' s
· 使用引理 `MvPolynomial.support_nonempty`：support_nonempty {p : MvPolynomial σ R} :
 p.support.Nonempty ↔ p != 0
· 使用定理 `AddEquiv.symm_apply_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (x : M), e.symm (e x) = x
-/
theorem leadingCoeff_ne_zero_iff {f : MvPolynomial σ R} :
    m.leadingCoeff f ≠ 0 ↔ f ≠ 0 := by
  constructor
  · rw [not_imp_not]
    intro hf
    rw [hf, leadingCoeff_zero]
  · intro hf
    rw [← support_nonempty] at hf
    rw [leadingCoeff, ← mem_support_iff, degree]
    suffices f.support.sup m.toSyn ∈ m.toSyn '' f.support by
      obtain ⟨d, hd, hd'⟩ := this
      rw [← hd', AddEquiv.symm_apply_apply]
      exact hd
    exact Finset.sup_mem_of_nonempty hf

@[simp]
/-
**MonomialOrder.leadingCoeff_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrde
r`。
形式化陈述：leadingCoeff_eq_zero_iff {f : MvPolynomial σ R} : leadingCoeff m f = 0 ↔ f
 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem leadingCoeff_eq_zero_iff {f : MvPolynomial σ R} :
    leadingCoeff m f = 0 ↔ f = 0 := by
  simp only [← not_iff_not, leadingCoeff_ne_zero_iff]
/-
**MonomialOrder.coeff_degree_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrde
r`。
形式化陈述：coeff_degree_ne_zero_iff {f : MvPolynomial σ R} : f.coeff (m.degree f) != 
0 ↔ f != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.leadingCoeff_ne_zero_iff`：leadingCoeff_ne_zero_iff {f : Mv
Polynomial σ R} : m.leadingCoeff f != 0 ↔ f != 0
-/
theorem coeff_degree_ne_zero_iff {f : MvPolynomial σ R} :
    f.coeff (m.degree f) ≠ 0 ↔ f ≠ 0 :=
  m.leadingCoeff_ne_zero_iff
/-
**MonomialOrder.degree_mem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`
。
形式化陈述：degree_mem_support_iff (f : MvPolynomial σ R) : m.degree f in f.support ↔ 
f != 0
参数：f : MvPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `MonomialOrder.coeff_degree_ne_zero_iff`：coeff_degree_ne_zero_iff {f : Mv
Polynomial σ R} : f.coeff (m.degree f) != 0 ↔ f != 0
-/
theorem degree_mem_support_iff (f : MvPolynomial σ R) : m.degree f ∈ f.support ↔ f ≠ 0 :=
  mem_support_iff.trans coeff_degree_ne_zero_iff

@[simp]
/-
**MonomialOrder.coeff_degree_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrde
r`。
形式化陈述：coeff_degree_eq_zero_iff {f : MvPolynomial σ R} : f.coeff (m.degree f) = 0
 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.leadingCoeff_eq_zero_iff`：leadingCoeff_eq_zero_iff {f : Mv
Polynomial σ R} : leadingCoeff m f = 0 ↔ f = 0
-/
theorem coeff_degree_eq_zero_iff {f : MvPolynomial σ R} :
    f.coeff (m.degree f) = 0 ↔ f = 0 :=
  m.leadingCoeff_eq_zero_iff
/-
**MonomialOrder.degree_mem_support** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_mem_support {p : MvPolynomial σ R} (hp : p != 0) : m.degree p in p.
support
参数：hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `MonomialOrder.coeff_degree_ne_zero_iff`：coeff_degree_ne_zero_iff {f : Mv
Polynomial σ R} : f.coeff (m.degree f) != 0 ↔ f != 0
-/
lemma degree_mem_support {p : MvPolynomial σ R} (hp : p ≠ 0) :
    m.degree p ∈ p.support := by
  rwa [MvPolynomial.mem_support_iff, coeff_degree_ne_zero_iff]
/-
**MonomialOrder.degree_eq_zero_iff_totalDegree_eq_zero** 是 Mathlib 中的一个定理，位于命名空间
 `MonomialOrder`。
形式化陈述：degree_eq_zero_iff_totalDegree_eq_zero {f : MvPolynomial σ R} : m.degree f
 = 0 ↔ f.totalDegree = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `MonomialOrder.bot_eq_zero`：bot_eq_zero : (⊥ : m.syn) = 0
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `AddEquiv.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZeroClass 
M] [inst_1 : AddZeroClass N] (h : M ≃+ N), h 0 = 0
· 使用定理 `MonomialOrder.degree_le_iff`：degree_le_iff {f : MvPolynomial σ R} {d : σ
 ->₀ Nat} : m.degree f ≼[m] d ↔ forall c in f.support, c ≼[m] d
· 使用定理 `MvPolynomial.totalDegree_eq_zero_iff`：totalDegree_eq_zero_iff (p : MvPol
ynomial σ R) : p.totalDegree = 0 ↔ forall (m : σ ->₀ Nat) (_ : m in p.support) (
x : σ), m x = 0
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_congr`：∀ {a b c d : Prop}, (a ↔ c) → (b ↔ d) → (a → b ↔ c → d)
· 使用定理 `Eq.to_iff`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Finsupp.ext_iff`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M] {f g : 
α →₀ M}, f = g ↔ ∀ (a : α), f a = g a
-/
theorem degree_eq_zero_iff_totalDegree_eq_zero {f : MvPolynomial σ R} :
    m.degree f = 0 ↔ f.totalDegree = 0 := by
  rw [← m.toSyn.injective.eq_iff]
  rw [map_zero, ← m.bot_eq_zero, eq_bot_iff, m.bot_eq_zero, ← m.toSyn.map_zero]
  rw [degree_le_iff]
  rw [totalDegree_eq_zero_iff]
  apply forall_congr'
  intro d
  apply imp_congr (rfl.to_iff)
  rw [map_zero, ← m.bot_eq_zero, ← eq_bot_iff, m.bot_eq_zero]
  simp only [EmbeddingLike.map_eq_zero_iff]
  exact Finsupp.ext_iff

@[simp]
/-
**MonomialOrder.degree_C** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_C (r : R) : m.degree (C r) = 0
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_eq_zero_iff_totalDegree_eq_zero`：degree_eq_zero_iff
_totalDegree_eq_zero {f : MvPolynomial σ R} : m.degree f = 0 ↔ f.totalDegree = 0
· 使用定理 `MvPolynomial.totalDegree_C`：totalDegree_C (a : R) : (C a : MvPolynomial 
σ R).totalDegree = 0
-/
theorem degree_C (r : R) :
    m.degree (C r) = 0 := by
  rw [degree_eq_zero_iff_totalDegree_eq_zero, totalDegree_C]

@[simp]
/-
**MonomialOrder.leadingCoeff_C** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：leadingCoeff_C (c : R) : m.leadingCoeff (C c) = c
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_C`：degree_C (r : R) : m.degree (C r) = 0
· 使用定理 `MvPolynomial.coeff_zero_C`：coeff_zero_C (a) : coeff 0 (C a : MvPolynomia
l σ R) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_C (c : R) : m.leadingCoeff (C c) = c := by
  simp [leadingCoeff]
/-
**MonomialOrder.eq_C_of_degree_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`
。
形式化陈述：eq_C_of_degree_eq_zero {f : MvPolynomial σ R} (hf : m.degree f = 0) : f = 
C (m.leadingCoeff f)
参数：hf : m.degree f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MonomialOrder.coeff_eq_zero_of_lt`：coeff_eq_zero_of_lt {f : MvPolynomial
 σ R} {d : σ ->₀ Nat} (hd : m.degree f ≺[m] d) : f.coeff d = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `EmbeddingLike.map_eq_zero_iff`：∀ {F : Type u_1} {M : Type u_4} {N : Type
 u_5} [inst : Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [EmbeddingLik
e F M N] [ZeroHomCl…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem eq_C_of_degree_eq_zero {f : MvPolynomial σ R} (hf : m.degree f = 0) :
    f = C (m.leadingCoeff f) := by
  ext d
  simp only [leadingCoeff, hf]
  classical
  by_cases hd : d = 0
  · simp [hd]
  · rw [coeff_C, if_neg (Ne.symm hd)]
    apply coeff_eq_zero_of_lt (m := m)
    rw [hf, map_zero, lt_iff_le_and_ne, ne_eq, eq_comm, EmbeddingLike.map_eq_zero_iff]
    exact ⟨bot_le, hd⟩
/-
**MonomialOrder.degree_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_eq_zero_iff {f : MvPolynomial σ R} : m.degree f = 0 ↔ f = C (m.lead
ingCoeff f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.eq_C_of_degree_eq_zero`：eq_C_of_degree_eq_zero {f : MvPoly
nomial σ R} (hf : m.degree f = 0) : f = C (m.leadingCoeff f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_C`：degree_C (r : R) : m.degree (C r) = 0
-/
theorem degree_eq_zero_iff {f : MvPolynomial σ R} :
    m.degree f = 0 ↔ f = C (m.leadingCoeff f) :=
  ⟨MonomialOrder.eq_C_of_degree_eq_zero, fun h => by rw [h, MonomialOrder.degree_C]⟩
/-
**MonomialOrder.degree_add_le** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_add_le {f g : MvPolynomial σ R} : m.toSyn (m.degree (f + g)) <= m.t
oSyn (m.degree f) ⊔ m.toSyn (m.degree g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用定理 `MonomialOrder.degree_le_iff`：degree_le_iff {f : MvPolynomial σ R} {d : σ
 ->₀ Nat} : m.degree f ≼[m] d ↔ forall c in f.support, c ≼[m] d
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MonomialOrder.le_degree`：le_degree {f : MvPolynomial σ R} {d : σ ->₀ Nat
} (hd : d in f.support) : d ≼[m] m.degree f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem degree_add_le {f g : MvPolynomial σ R} :
    m.toSyn (m.degree (f + g)) ≤ m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  conv_rhs => rw [← m.toSyn.apply_symm_apply (_ ⊔ _)]
  rw [degree_le_iff]
  simp only [AddEquiv.apply_symm_apply, le_sup_iff]
  intro b hb
  by_cases hf : b ∈ f.support
  · left
    exact m.le_degree hf
  · right
    apply m.le_degree
    simp only [notMem_support_iff] at hf
    simpa only [mem_support_iff, coeff_add, hf, zero_add] using hb
/-
**MonomialOrder.degree_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_sum_le {α : Type*} {s : Finset α} {f : α -> MvPolynomial σ R} : (m.
toSyn <| m.degree <| ∑ x in s, f x) <= s.sup fun x => (m.toSyn <| m.degree <| f 
x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MonomialOrder.degree_add_le`：degree_add_le {f g : MvPolynomial σ R} : m.
toSyn (m.degree (f + g)) <= m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g)
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem degree_sum_le {α : Type*} {s : Finset α} {f : α → MvPolynomial σ R} :
    (m.toSyn <| m.degree <| ∑ x ∈ s, f x) ≤ s.sup fun x ↦ (m.toSyn <| m.degree <| f x) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s haA h =>
    rw [Finset.sum_cons, Finset.sup_cons]
    exact le_trans m.degree_add_le (max_le_max le_rfl h)
/-
**MonomialOrder.degree_add_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_add_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f)
 : m.degree (f + g) = m.degree f
参数：h : m.degree g ≺[m] m.degree f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MonomialOrder.degree_add_le`：degree_add_le {f g : MvPolynomial σ R} : m.
toSyn (m.degree (f + g)) <= m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MonomialOrder.le_degree`：le_degree {f : MvPolynomial σ R} {d : σ ->₀ Nat
} (hd : d in f.support) : d ≼[m] m.degree f
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
· 使用定理 `MonomialOrder.coeff_eq_zero_of_lt`：coeff_eq_zero_of_lt {f : MvPolynomial
 σ R} {d : σ ->₀ Nat} (hd : m.degree f ≺[m] d) : f.coeff d = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonomialOrder.leadingCoeff.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) 
{R : Type u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.leadingCoeff 
f = MvPolynomial.coef…
· 使用定理 `MonomialOrder.leadingCoeff_ne_zero_iff`：leadingCoeff_ne_zero_iff {f : Mv
Polynomial σ R} : m.leadingCoeff f != 0 ↔ f != 0
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem degree_add_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.degree (f + g) = m.degree f := by
  apply m.toSyn.injective
  apply le_antisymm
  · apply le_trans degree_add_le
    simp only [sup_le_iff, le_refl, true_and, le_of_lt h]
  · apply le_degree
    rw [mem_support_iff, coeff_add, m.coeff_eq_zero_of_lt h, add_zero,
      ← leadingCoeff, leadingCoeff_ne_zero_iff]
    intro hf
    rw [← not_le, hf] at h
    apply h
    simp only [degree_zero, map_zero]
    apply bot_le
/-
**MonomialOrder.degree_add_eq_right_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrd
er`。
形式化陈述：degree_add_eq_right_of_lt {f g : MvPolynomial σ R} (h : m.degree f ≺[m] m.
degree g) : m.degree (f + g) = m.degree g
参数：h : m.degree f ≺[m] m.degree g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MonomialOrder.degree_add_of_lt`：degree_add_of_lt {f g : MvPolynomial σ R
} (h : m.degree g ≺[m] m.degree f) : m.degree (f + g) = m.degree f
-/
theorem degree_add_eq_right_of_lt {f g : MvPolynomial σ R} (h : m.degree f ≺[m] m.degree g) :
    m.degree (f + g) = m.degree g := by
  rw [add_comm]
  exact degree_add_of_lt h
/-
**MonomialOrder.leadingCoeff_add_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`
。
形式化陈述：leadingCoeff_add_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.deg
ree f) : m.leadingCoeff (f + g) = m.leadingCoeff f
参数：h : m.degree g ≺[m] m.degree f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_add_of_lt`：degree_add_of_lt {f g : MvPolynomial σ R
} (h : m.degree g ≺[m] m.degree f) : m.degree (f + g) = m.degree f
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
· 使用定理 `MonomialOrder.coeff_eq_zero_of_lt`：coeff_eq_zero_of_lt {f : MvPolynomial
 σ R} {d : σ ->₀ Nat} (hd : m.degree f ≺[m] d) : f.coeff d = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_add_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.leadingCoeff (f + g) = m.leadingCoeff f := by
  simp only [leadingCoeff, m.degree_add_of_lt h, coeff_add, coeff_eq_zero_of_lt h, add_zero]
/-
**MonomialOrder.Monic.add_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder.Monic`。
形式化陈述：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Type u_2} [inst : CommSemiring
 R] {f g : MvPolynomial σ R},   m.Monic f → m.toSyn (m.degree g) < m.toSyn (m.de
gree f) → m.Monic (f + g)
参数：m.degree g；m.degree f；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.leadingCoeff_add_of_lt`：leadingCoeff_add_of_lt {f g : MvPo
lynomial σ R} (h : m.degree g ≺[m] m.degree f) : m.leadingCoeff (f + g) = m.lead
ingCoeff f
· 使用定理 `MonomialOrder.Monic.leadingCoeff_eq_one`：∀ {σ : Type u_1} {m : MonomialO
rder σ} {R : Type u_2} [inst : CommSemiring R] {f : MvPolynomial σ R},   m.Monic
 f → m.leadingCoeff f = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Monic.add_of_lt {f g : MvPolynomial σ R} (hf : m.Monic f) (h : m.degree g ≺[m] m.degree f) :
    m.Monic (f + g) := by
  simp only [Monic, leadingCoeff_add_of_lt h, hf.leadingCoeff_eq_one]
/-
**MonomialOrder.degree_add_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_add_of_ne {f g : MvPolynomial σ R} (h : m.degree f != m.degree g) :
 m.toSyn (m.degree (f + g)) = m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g)
参数：h : m.degree f != m.degree g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_add_of_lt`：degree_add_of_lt {f g : MvPolynomial σ R
} (h : m.degree g ≺[m] m.degree f) : m.degree (f + g) = m.degree f
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `EmbeddingLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : F) {x y : α} : f x =
 f y ↔ x = y
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `right_eq_sup`：right_eq_sup : b = a ⊔ b ↔ a <= b
-/
theorem degree_add_of_ne {f g : MvPolynomial σ R}
    (h : m.degree f ≠ m.degree g) :
    m.toSyn (m.degree (f + g)) = m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  by_cases h' : m.degree g ≺[m] m.degree f
  · simp [degree_add_of_lt h', le_of_lt h']
  · rw [not_lt, le_iff_eq_or_lt, Classical.or_iff_not_imp_left, EmbeddingLike.apply_eq_iff_eq] at h'
    rw [add_comm, degree_add_of_lt (h' h), right_eq_sup]
    simp only [le_of_lt (h' h)]
/-
**MonomialOrder.degree_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_mul_le {f g : MvPolynomial σ R} : m.degree (f * g) ≼[m] m.degree f 
+ m.degree g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_le_iff`：degree_le_iff {f : MvPolynomial σ R} {d : σ
 ->₀ Nat} : m.degree f ≼[m] d ↔ forall c in f.support, c ≼[m] d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `MvPolynomial.coeff_mul`：coeff_mul [DecidableEq σ] (p q : MvPolynomial σ 
R) (n : σ ->₀ Nat) : coeff n (p * q) = ∑ x in Finset.antidiagonal n, coeff x.1 p
 * coeff x.2…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `MonomialOrder.coeff_eq_zero_of_lt`：coeff_eq_zero_of_lt {f : MvPolynomial
 σ R} {d : σ ->₀ Nat} (hd : m.degree f ≺[m] d) : f.coeff d = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `lt_of_add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [
AddLeftReflectLT α] {a b c : α}, a + b < a + c → b < c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MonomialOrder.isOrderedAddMonoid_syn`：∀ {σ : Type u_1} (self : MonomialO
rder σ), IsOrderedAddMonoid self.syn
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem degree_mul_le {f g : MvPolynomial σ R} :
    m.degree (f * g) ≼[m] m.degree f + m.degree g := by
  classical
  rw [degree_le_iff]
  intro c
  rw [← not_lt, mem_support_iff, not_imp_not]
  intro hc
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨d, e⟩ hde
  simp only [Finset.mem_antidiagonal] at hde
  dsimp only
  by_cases hd : m.degree f ≺[m] d
  · rw [m.coeff_eq_zero_of_lt hd, zero_mul]
  · suffices m.degree g ≺[m] e by
      rw [m.coeff_eq_zero_of_lt this, mul_zero]
    simp only [not_lt] at hd
    apply lt_of_add_lt_add_left (a := m.toSyn d)
    grw [← map_add _ _ e, hd, ← map_add, hde]
    exact hc

/-- Multiplicativity of leading coefficients -/
/-
**MonomialOrder.coeff_mul_of_add_of_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `Monomia
lOrder`。
形式化陈述：coeff_mul_of_add_of_degree_le {f g : MvPolynomial σ R} {a b : σ ->₀ Nat} (
ha : m.degree f ≼[m] a) (hb : m.degree g ≼[m] b) : (f * g).coeff (a + b) = f.coe
ff a * g.coeff b
参数：ha : m.degree f ≼[m] a；hb : m.degree g ≼[m] b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_mul`：coeff_mul [DecidableEq σ] (p q : MvPolynomial σ 
R) (n : σ ->₀ Nat) : coeff n (p * q) = ∑ x in Finset.antidiagonal n, coeff x.1 p
 * coeff x.2…
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `MonomialOrder.coeff_eq_zero_of_lt`：coeff_eq_zero_of_lt {f : MvPolynomial
 σ R} {d : σ ->₀ Nat} (hd : m.degree f ≺[m] d) : f.coeff d = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `le_of_add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] 
[AddRightReflectLE α] {a b c : α}, b + a ≤ c + a → b ≤ c
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MonomialOrder.isOrderedAddMonoid_syn`：∀ {σ : Type u_1} (self : MonomialO
rder σ), IsOrderedAddMonoid self.syn
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Multiplicativity of leading coefficients
-/
theorem coeff_mul_of_add_of_degree_le {f g : MvPolynomial σ R} {a b : σ →₀ ℕ}
    (ha : m.degree f ≼[m] a) (hb : m.degree g ≼[m] b) :
    (f * g).coeff (a + b) = f.coeff a * g.coeff b := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (a, b)]
  · rintro ⟨c, d⟩ hcd h
    simp only [Finset.mem_antidiagonal] at hcd
    by_cases hf : m.degree f ≺[m] c
    · rw [m.coeff_eq_zero_of_lt hf, zero_mul]
    · suffices m.degree g ≺[m] d by
        rw [coeff_eq_zero_of_lt this, mul_zero]
      rw [not_lt] at hf
      rw [← not_le]
      intro hf'
      apply h
      suffices c = a by
        simpa [Prod.mk.injEq, this] using hcd
      apply m.toSyn.injective
      apply le_antisymm (le_trans hf ha)
      apply le_of_add_le_add_right (a := m.toSyn b)
      rw [← map_add, ← hcd, map_add]
      simp only [add_le_add_iff_left]
      exact le_trans hf' hb
  · simp

/-- Multiplicativity of leading coefficients -/
/-
**MonomialOrder.coeff_mul_of_degree_add** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder
`。
形式化陈述：coeff_mul_of_degree_add {f g : MvPolynomial σ R} : (f * g).coeff (m.degree
 f + m.degree g) = m.leadingCoeff f * m.leadingCoeff g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.coeff_mul_of_add_of_degree_le`：coeff_mul_of_add_of_degree_
le {f g : MvPolynomial σ R} {a b : σ ->₀ Nat} (ha : m.degree f ≼[m] a) (hb : m.d
egree g ≼[m] b) : (f * g).coeff (…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
Multiplicativity of leading coefficients
-/
theorem coeff_mul_of_degree_add {f g : MvPolynomial σ R} :
    (f * g).coeff (m.degree f + m.degree g) = m.leadingCoeff f * m.leadingCoeff g :=
  coeff_mul_of_add_of_degree_le (le_of_eq rfl) (le_of_eq rfl)

/-- Monomial degree of product -/
/-
**MonomialOrder.degree_mul_of_mul_leadingCoeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间
 `MonomialOrder`。
形式化陈述：degree_mul_of_mul_leadingCoeff_ne_zero {f g : MvPolynomial σ R} (hfg : m.l
eadingCoeff f * m.leadingCoeff g != 0) : m.degree (f * g) = m.degree f + m.degre
e g
参数：hfg : m.leadingCoeff f * m.leadingCoeff g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MonomialOrder.degree_mul_le`：degree_mul_le {f g : MvPolynomial σ R} : m.
degree (f * g) ≼[m] m.degree f + m.degree g
· 使用定理 `MonomialOrder.le_degree`：le_degree {f : MvPolynomial σ R} {d : σ ->₀ Nat
} (hd : d in f.support) : d ≼[m] m.degree f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `MonomialOrder.coeff_mul_of_degree_add`：coeff_mul_of_degree_add {f g : Mv
Polynomial σ R} : (f * g).coeff (m.degree f + m.degree g) = m.leadingCoeff f * m
.leadingCoeff g

--- 原说明 ---
Monomial degree of product
-/
theorem degree_mul_of_mul_leadingCoeff_ne_zero {f g : MvPolynomial σ R}
    (hfg : m.leadingCoeff f * m.leadingCoeff g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply m.toSyn.injective
  apply le_antisymm degree_mul_le
  apply le_degree
  rw [mem_support_iff, coeff_mul_of_degree_add]
  exact hfg

/-- Multiplicativity of leading coefficients -/
/-
**MonomialOrder.leadingCoeff_mul_of_mul_leadingCoeff_ne_zero** 是 Mathlib 中的一个定理，
位于命名空间 `MonomialOrder`。
形式化陈述：leadingCoeff_mul_of_mul_leadingCoeff_ne_zero {f g : MvPolynomial σ R} (hfg
 : m.leadingCoeff f * m.leadingCoeff g != 0) : m.leadingCoeff (f * g) = m.leadin
gCoeff f * m.leadingCoeff g
参数：hfg : m.leadingCoeff f * m.leadingCoeff g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.leadingCoeff.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) 
{R : Type u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.leadingCoeff 
f = MvPolynomial.coef…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonomialOrder.coeff_mul_of_degree_add`：coeff_mul_of_degree_add {f g : Mv
Polynomial σ R} : (f * g).coeff (m.degree f + m.degree g) = m.leadingCoeff f * m
.leadingCoeff g
· 使用定理 `MonomialOrder.degree_mul_of_mul_leadingCoeff_ne_zero`：degree_mul_of_mul_
leadingCoeff_ne_zero {f g : MvPolynomial σ R} (hfg : m.leadingCoeff f * m.leadin
gCoeff g != 0) : m.degree (f * g) = m.degr…

--- 原说明 ---
Multiplicativity of leading coefficients
-/
theorem leadingCoeff_mul_of_mul_leadingCoeff_ne_zero {f g : MvPolynomial σ R}
    (hfg : m.leadingCoeff f * m.leadingCoeff g ≠ 0) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  rw [leadingCoeff, ← coeff_mul_of_degree_add, degree_mul_of_mul_leadingCoeff_ne_zero hfg]
/-
**MonomialOrder.degree_mul_of_left_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间
 `MonomialOrder`。
形式化陈述：degree_mul_of_left_mem_nonZeroDivisors {f g : MvPolynomial σ R} (hf : m.le
adingCoeff f in nonZeroDivisors _) (hg : g != 0) : m.degree (f * g) = m.degree f
 + m.degree g
参数：hf : m.leadingCoeff f in nonZeroDivisors _；hg : g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.degree_mul_of_mul_leadingCoeff_ne_zero`：degree_mul_of_mul_
leadingCoeff_ne_zero {f g : MvPolynomial σ R} (hfg : m.leadingCoeff f * m.leadin
gCoeff g != 0) : m.degree (f * g) = m.degr…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nonZeroDivisors_iff`：mem_nonZeroDivisors_iff : r in M₀⁰ ↔ (forall x,
 r * x = 0 -> x = 0) ∧ forall x, x * r = 0 -> x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem degree_mul_of_left_mem_nonZeroDivisors {f g : MvPolynomial σ R}
    (hf : m.leadingCoeff f ∈ nonZeroDivisors _) (hg : g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply degree_mul_of_mul_leadingCoeff_ne_zero
  apply not_imp_not.mpr (mem_nonZeroDivisors_iff.mp hf |>.1 _)
  simp [hg]
/-
**MonomialOrder.degree_mul_of_right_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空
间 `MonomialOrder`。
形式化陈述：degree_mul_of_right_mem_nonZeroDivisors {f g : MvPolynomial σ R} (hf : f !
= 0) (hg : m.leadingCoeff g in nonZeroDivisors _) : m.degree (f * g) = m.degree 
f + m.degree g
参数：hf : f != 0；hg : m.leadingCoeff g in nonZeroDivisors _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.degree_mul_of_left_mem_nonZeroDivisors`：degree_mul_of_left
_mem_nonZeroDivisors {f g : MvPolynomial σ R} (hf : m.leadingCoeff f in nonZeroD
ivisors _) (hg : g != 0) : m.degree (f * g…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem degree_mul_of_right_mem_nonZeroDivisors {f g : MvPolynomial σ R}
    (hf : f ≠ 0) (hg : m.leadingCoeff g ∈ nonZeroDivisors _) :
    m.degree (f * g) = m.degree f + m.degree g :=
  add_comm (m.degree f) (m.degree g) ▸ mul_comm f g ▸ degree_mul_of_left_mem_nonZeroDivisors hg hf
/-
**MonomialOrder.leadingCoeff_mul_of_left_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，
位于命名空间 `MonomialOrder`。
形式化陈述：leadingCoeff_mul_of_left_mem_nonZeroDivisors {f g : MvPolynomial σ R} (hf 
: m.leadingCoeff f in nonZeroDivisors _) : m.leadingCoeff (f * g) = m.leadingCoe
ff f * m.leadingCoeff g
参数：hf : m.leadingCoeff f in nonZeroDivisors _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MonomialOrder.leadingCoeff_zero`：leadingCoeff_zero : m.leadingCoeff (0 :
 MvPolynomial σ R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_mul_of_left_mem_nonZeroDivisors`：degree_mul_of_left
_mem_nonZeroDivisors {f g : MvPolynomial σ R} (hf : m.leadingCoeff f in nonZeroD
ivisors _) (hg : g != 0) : m.degree (f * g…
· 使用定理 `MonomialOrder.coeff_mul_of_degree_add`：coeff_mul_of_degree_add {f g : Mv
Polynomial σ R} : (f * g).coeff (m.degree f + m.degree g) = m.leadingCoeff f * m
.leadingCoeff g
-/
theorem leadingCoeff_mul_of_left_mem_nonZeroDivisors {f g : MvPolynomial σ R}
    (hf : m.leadingCoeff f ∈ nonZeroDivisors _) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases hg : g = 0
  · simp [hg]
  · simp only [leadingCoeff, degree_mul_of_left_mem_nonZeroDivisors hf hg, coeff_mul_of_degree_add]
/-
**MonomialOrder.leadingCoeff_mul_of_right_mem_nonZeroDivisors** 是 Mathlib 中的一个定理
，位于命名空间 `MonomialOrder`。
形式化陈述：leadingCoeff_mul_of_right_mem_nonZeroDivisors {f g : MvPolynomial σ R} (hg
 : m.leadingCoeff g in nonZeroDivisors _) : m.leadingCoeff (f * g) = m.leadingCo
eff f * m.leadingCoeff g
参数：hg : m.leadingCoeff g in nonZeroDivisors _。
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
· 使用定理 `MonomialOrder.leadingCoeff_zero`：leadingCoeff_zero : m.leadingCoeff (0 :
 MvPolynomial σ R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MonomialOrder.degree_mul_of_right_mem_nonZeroDivisors`：degree_mul_of_rig
ht_mem_nonZeroDivisors {f g : MvPolynomial σ R} (hf : f != 0) (hg : m.leadingCoe
ff g in nonZeroDivisors _) : m.degree (f * …
· 使用定理 `MonomialOrder.coeff_mul_of_degree_add`：coeff_mul_of_degree_add {f g : Mv
Polynomial σ R} : (f * g).coeff (m.degree f + m.degree g) = m.leadingCoeff f * m
.leadingCoeff g
-/
theorem leadingCoeff_mul_of_right_mem_nonZeroDivisors {f g : MvPolynomial σ R}
    (hg : m.leadingCoeff g ∈ nonZeroDivisors _) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases hf : f = 0
  · simp [hf]
  · simp only [leadingCoeff, degree_mul_of_right_mem_nonZeroDivisors hf hg, coeff_mul_of_degree_add]

/-- Monomial degree of product -/
/-
**MonomialOrder.degree_mul_of_isRegular_left** 是 Mathlib 中的一个定理，位于命名空间 `Monomial
Order`。
形式化陈述：degree_mul_of_isRegular_left {f g : MvPolynomial σ R} (hf : IsRegular (m.l
eadingCoeff f)) (hg : g != 0) : m.degree (f * g) = m.degree f + m.degree g
参数：hf : IsRegular (m.leadingCoeff f)；hg : g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.degree_mul_of_mul_leadingCoeff_ne_zero`：degree_mul_of_mul_
leadingCoeff_ne_zero {f g : MvPolynomial σ R} (hfg : m.leadingCoeff f * m.leadin
gCoeff g != 0) : m.degree (f * g) = m.degr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Monomial degree of product
-/
theorem degree_mul_of_isRegular_left {f g : MvPolynomial σ R}
    (hf : IsRegular (m.leadingCoeff f)) (hg : g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply degree_mul_of_mul_leadingCoeff_ne_zero
  simp only [ne_eq, hf, IsRegular.left, IsLeftRegular.mul_left_eq_zero_iff,
    leadingCoeff_eq_zero_iff]
  exact hg

/-- Multiplicativity of leading coefficients -/
/-
**MonomialOrder.leadingCoeff_mul_of_isRegular_left** 是 Mathlib 中的一个定理，位于命名空间 `Mo
nomialOrder`。
形式化陈述：leadingCoeff_mul_of_isRegular_left {f g : MvPolynomial σ R} (hf : IsRegula
r (m.leadingCoeff f)) : m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoe
ff g
参数：hf : IsRegular (m.leadingCoeff f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MonomialOrder.leadingCoeff_zero`：leadingCoeff_zero : m.leadingCoeff (0 :
 MvPolynomial σ R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_mul_of_isRegular_left`：degree_mul_of_isRegular_left
 {f g : MvPolynomial σ R} (hf : IsRegular (m.leadingCoeff f)) (hg : g != 0) : m.
degree (f * g) = m.degree f + m.…
· 使用定理 `MonomialOrder.coeff_mul_of_degree_add`：coeff_mul_of_degree_add {f g : Mv
Polynomial σ R} : (f * g).coeff (m.degree f + m.degree g) = m.leadingCoeff f * m
.leadingCoeff g

--- 原说明 ---
Multiplicativity of leading coefficients
-/
theorem leadingCoeff_mul_of_isRegular_left {f g : MvPolynomial σ R}
    (hf : IsRegular (m.leadingCoeff f)) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases hg : g = 0
  · simp [hg]
  · simp only [leadingCoeff, degree_mul_of_isRegular_left hf hg, coeff_mul_of_degree_add]

/-- Monomial degree of product -/
/-
**MonomialOrder.degree_mul_of_isRegular_right** 是 Mathlib 中的一个定理，位于命名空间 `Monomia
lOrder`。
形式化陈述：degree_mul_of_isRegular_right {f g : MvPolynomial σ R} (hf : f != 0) (hg :
 IsRegular (m.leadingCoeff g)) : m.degree (f * g) = m.degree f + m.degree g
参数：hf : f != 0；hg : IsRegular (m.leadingCoeff g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MonomialOrder.degree_mul_of_isRegular_left`：degree_mul_of_isRegular_left
 {f g : MvPolynomial σ R} (hf : IsRegular (m.leadingCoeff f)) (hg : g != 0) : m.
degree (f * g) = m.degree f + m.…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
Monomial degree of product
-/
theorem degree_mul_of_isRegular_right {f g : MvPolynomial σ R}
    (hf : f ≠ 0) (hg : IsRegular (m.leadingCoeff g)) :
    m.degree (f * g) = m.degree f + m.degree g := by
  rw [mul_comm, m.degree_mul_of_isRegular_left hg hf, add_comm]

/-- Multiplicativity of leading coefficients -/
/-
**MonomialOrder.leadingCoeff_mul_of_isRegular_right** 是 Mathlib 中的一个定理，位于命名空间 `M
onomialOrder`。
形式化陈述：leadingCoeff_mul_of_isRegular_right {f g : MvPolynomial σ R} (hg : IsRegul
ar (m.leadingCoeff g)) : m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCo
eff g
参数：hg : IsRegular (m.leadingCoeff g)。
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
· 使用定理 `MonomialOrder.leadingCoeff_zero`：leadingCoeff_zero : m.leadingCoeff (0 :
 MvPolynomial σ R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MonomialOrder.degree_mul_of_isRegular_right`：degree_mul_of_isRegular_rig
ht {f g : MvPolynomial σ R} (hf : f != 0) (hg : IsRegular (m.leadingCoeff g)) : 
m.degree (f * g) = m.degree f + m…
· 使用定理 `MonomialOrder.coeff_mul_of_degree_add`：coeff_mul_of_degree_add {f g : Mv
Polynomial σ R} : (f * g).coeff (m.degree f + m.degree g) = m.leadingCoeff f * m
.leadingCoeff g

--- 原说明 ---
Multiplicativity of leading coefficients
-/
theorem leadingCoeff_mul_of_isRegular_right {f g : MvPolynomial σ R}
    (hg : IsRegular (m.leadingCoeff g)) :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases hf : f = 0
  · simp [hf]
  · simp only [leadingCoeff, degree_mul_of_isRegular_right hf hg, coeff_mul_of_degree_add]
/-
**MonomialOrder.Monic.mul** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder.Monic`。
形式化陈述：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Type u_2} [inst : CommSemiring
 R] {f g : MvPolynomial σ R},   m.Monic f → m.Monic g → m.Monic (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.Monic.leadingCoeff_eq_one`：∀ {σ : Type u_1} {m : MonomialO
rder σ} {R : Type u_2} [inst : CommSemiring R] {f : MvPolynomial σ R},   m.Monic
 f → m.leadingCoeff f = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MonomialOrder.Monic.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) {R : Ty
pe u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.Monic f = (m.leading
Coeff f = 1)
· 使用定理 `MonomialOrder.leadingCoeff.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) 
{R : Type u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.leadingCoeff 
f = MvPolynomial.coef…
· 使用定理 `MonomialOrder.degree_mul_of_mul_leadingCoeff_ne_zero`：degree_mul_of_mul_
leadingCoeff_ne_zero {f g : MvPolynomial σ R} (hfg : m.leadingCoeff f * m.leadin
gCoeff g != 0) : m.degree (f * g) = m.degr…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `MonomialOrder.coeff_mul_of_degree_add`：coeff_mul_of_degree_add {f g : Mv
Polynomial σ R} : (f * g).coeff (m.degree f + m.degree g) = m.leadingCoeff f * m
.leadingCoeff g
-/
theorem Monic.mul {f g : MvPolynomial σ R} (hf : m.Monic f) (hg : m.Monic g) :
    m.Monic (f * g) := by
  nontriviality R
  suffices m.leadingCoeff f * m.leadingCoeff g = 1 by
    rw [Monic, MonomialOrder.leadingCoeff,
      degree_mul_of_mul_leadingCoeff_ne_zero, coeff_mul_of_degree_add, this]
    rw [this]
    exact one_ne_zero
  rw [hf.leadingCoeff_eq_one, hg.leadingCoeff_eq_one, one_mul]

/-- Monomial degree of product -/
/-
**MonomialOrder.degree_mul** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_mul [NoZeroDivisors R] {f g : MvPolynomial σ R} (hf : f != 0) (hg :
 g != 0) : m.degree (f * g) = m.degree f + m.degree g
参数：hf : f != 0；hg : g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.degree_mul_of_mul_leadingCoeff_ne_zero`：degree_mul_of_mul_
leadingCoeff_ne_zero {f g : MvPolynomial σ R} (hfg : m.leadingCoeff f * m.leadin
gCoeff g != 0) : m.degree (f * g) = m.degr…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
Monomial degree of product
-/
theorem degree_mul [NoZeroDivisors R] {f g : MvPolynomial σ R} (hf : f ≠ 0) (hg : g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply degree_mul_of_mul_leadingCoeff_ne_zero
  simp only [ne_eq, mul_eq_zero, leadingCoeff_eq_zero_iff, not_or]
  tauto

/-- Multiplicativity of leading coefficients -/
/-
**MonomialOrder.leadingCoeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Type u_2} [inst : CommSemiring
 R] [NoZeroDivisors R]   {f g : MvPolynomial σ R}, m.leadingCoeff (f * g) = m.le
adingCoeff f * m.leadingCoeff g
参数：f * g。
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
· 使用定理 `MonomialOrder.leadingCoeff_zero`：leadingCoeff_zero : m.leadingCoeff (0 :
 MvPolynomial σ R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MonomialOrder.leadingCoeff.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) 
{R : Type u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.leadingCoeff 
f = MvPolynomial.coef…
· 使用定理 `MonomialOrder.degree_mul`：degree_mul [NoZeroDivisors R] {f g : MvPolynom
ial σ R} (hf : f != 0) (hg : g != 0) : m.degree (f * g) = m.degree f + m.degree 
g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonomialOrder.coeff_mul_of_degree_add`：coeff_mul_of_degree_add {f g : Mv
Polynomial σ R} : (f * g).coeff (m.degree f + m.degree g) = m.leadingCoeff f * m
.leadingCoeff g

--- 原说明 ---
Multiplicativity of leading coefficients
-/
@[simp] theorem leadingCoeff_mul [NoZeroDivisors R] {f g : MvPolynomial σ R} :
    m.leadingCoeff (f * g) = m.leadingCoeff f * m.leadingCoeff g := by
  by_cases! +distrib h : f = 0 ∨ g = 0
  · cases h <;> simp [*]
  obtain ⟨hf, hg⟩ := h
  rw [leadingCoeff, degree_mul hf hg, ← coeff_mul_of_degree_add]

/-- Monomial degree of powers -/
/-
**MonomialOrder.degree_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_pow_le {f : MvPolynomial σ R} (n : Nat) : m.degree (f ^ n) ≼[m] n •
 (m.degree f)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MonomialOrder.degree_one`：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Ty
pe u_2} [inst : CommSemiring R], m.degree 1 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MonomialOrder.degree_mul_le`：degree_mul_le {f g : MvPolynomial σ R} : m.
degree (f * g) ≼[m] m.degree f + m.degree g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MonomialOrder.isOrderedAddMonoid_syn`：∀ {σ : Type u_1} (self : MonomialO
rder σ), IsOrderedAddMonoid self.syn
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …

--- 原说明 ---
Monomial degree of powers
-/
theorem degree_pow_le {f : MvPolynomial σ R} (n : ℕ) :
    m.degree (f ^ n) ≼[m] n • (m.degree f) := by
  induction n with
  | zero => simp [m.degree_one]
  | succ n hrec =>
      simp only [pow_add, pow_one, add_smul, one_smul]
      apply le_trans m.degree_mul_le
      simp only [map_add, add_le_add_iff_right]
      exact hrec
/-
**MonomialOrder.coeff_pow_nsmul_degree** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`
。
形式化陈述：coeff_pow_nsmul_degree (f : MvPolynomial σ R) (n : Nat) : (f ^ n).coeff (n
 • m.degree f) = m.leadingCoeff f ^ n
参数：f : MvPolynomial σ R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MvPolynomial.coeff_zero_one`：coeff_zero_one : coeff 0 (1 : MvPolynomial 
σ R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `MonomialOrder.coeff_mul_of_add_of_degree_le`：coeff_mul_of_add_of_degree_
le {f g : MvPolynomial σ R} {a b : σ ->₀ Nat} (ha : m.degree f ≼[m] a) (hb : m.d
egree g ≼[m] b) : (f * g).coeff (…
· 使用定理 `MonomialOrder.degree_pow_le`：degree_pow_le {f : MvPolynomial σ R} (n : N
at) : m.degree (f ^ n) ≼[m] n • (m.degree f)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MonomialOrder.leadingCoeff.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) 
{R : Type u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.leadingCoeff 
f = MvPolynomial.coef…
-/
theorem coeff_pow_nsmul_degree (f : MvPolynomial σ R) (n : ℕ) :
    (f ^ n).coeff (n • m.degree f) = m.leadingCoeff f ^ n := by
  induction n with
  | zero => simp
  | succ n hrec =>
    simp only [add_smul, one_smul, pow_add, pow_one]
    rw [m.coeff_mul_of_add_of_degree_le (m.degree_pow_le _) le_rfl, hrec, leadingCoeff]

/-- Monomial degree of powers -/
/-
**MonomialOrder.degree_pow_of_pow_leadingCoeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间
 `MonomialOrder`。
形式化陈述：degree_pow_of_pow_leadingCoeff_ne_zero {f : MvPolynomial σ R} {n : Nat} (h
f : m.leadingCoeff f ^ n != 0) : m.degree (f ^ n) = n • m.degree f
参数：hf : m.leadingCoeff f ^ n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MonomialOrder.degree_pow_le`：degree_pow_le {f : MvPolynomial σ R} (n : N
at) : m.degree (f ^ n) ≼[m] n • (m.degree f)
· 使用定理 `MonomialOrder.le_degree`：le_degree {f : MvPolynomial σ R} {d : σ ->₀ Nat
} (hd : d in f.support) : d ≼[m] m.degree f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `MonomialOrder.coeff_pow_nsmul_degree`：coeff_pow_nsmul_degree (f : MvPoly
nomial σ R) (n : Nat) : (f ^ n).coeff (n • m.degree f) = m.leadingCoeff f ^ n

--- 原说明 ---
Monomial degree of powers
-/
theorem degree_pow_of_pow_leadingCoeff_ne_zero {f : MvPolynomial σ R} {n : ℕ}
    (hf : m.leadingCoeff f ^ n ≠ 0) :
    m.degree (f ^ n) = n • m.degree f := by
  apply m.toSyn.injective
  apply le_antisymm (m.degree_pow_le n)
  apply le_degree
  rw [mem_support_iff, coeff_pow_nsmul_degree]
  exact hf

/-- Leading coefficient of powers -/
/-
**MonomialOrder.leadingCoeff_pow_of_pow_leadingCoeff_ne_zero** 是 Mathlib 中的一个定理，
位于命名空间 `MonomialOrder`。
形式化陈述：leadingCoeff_pow_of_pow_leadingCoeff_ne_zero {f : MvPolynomial σ R} {n : N
at} (hf : m.leadingCoeff f ^ n != 0) : m.leadingCoeff (f ^ n) = m.leadingCoeff f
 ^ n
参数：hf : m.leadingCoeff f ^ n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.leadingCoeff.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) 
{R : Type u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.leadingCoeff 
f = MvPolynomial.coef…
· 使用定理 `MonomialOrder.degree_pow_of_pow_leadingCoeff_ne_zero`：degree_pow_of_pow_
leadingCoeff_ne_zero {f : MvPolynomial σ R} {n : Nat} (hf : m.leadingCoeff f ^ n
 != 0) : m.degree (f ^ n) = n • m.degree f
· 使用定理 `MonomialOrder.coeff_pow_nsmul_degree`：coeff_pow_nsmul_degree (f : MvPoly
nomial σ R) (n : Nat) : (f ^ n).coeff (n • m.degree f) = m.leadingCoeff f ^ n

--- 原说明 ---
Leading coefficient of powers
-/
theorem leadingCoeff_pow_of_pow_leadingCoeff_ne_zero {f : MvPolynomial σ R} {n : ℕ}
    (hf : m.leadingCoeff f ^ n ≠ 0) :
    m.leadingCoeff (f ^ n) = m.leadingCoeff f ^ n := by
  rw [leadingCoeff, degree_pow_of_pow_leadingCoeff_ne_zero hf, coeff_pow_nsmul_degree]
/-
**MonomialOrder.Monic.pow** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder.Monic`。
形式化陈述：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Type u_2} [inst : CommSemiring
 R] {f : MvPolynomial σ R} {n : ℕ},   m.Monic f → m.Monic (f ^ n)
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.Monic.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) {R : Ty
pe u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.Monic f = (m.leading
Coeff f = 1)
· 使用定理 `MonomialOrder.leadingCoeff_pow_of_pow_leadingCoeff_ne_zero`：leadingCoeff
_pow_of_pow_leadingCoeff_ne_zero {f : MvPolynomial σ R} {n : Nat} (hf : m.leadin
gCoeff f ^ n != 0) : m.leadingCoeff (f ^ n) = m.…
· 使用定理 `MonomialOrder.Monic.leadingCoeff_eq_one`：∀ {σ : Type u_1} {m : MonomialO
rder σ} {R : Type u_2} [inst : CommSemiring R] {f : MvPolynomial σ R},   m.Monic
 f → m.leadingCoeff f = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
protected theorem Monic.pow {f : MvPolynomial σ R} {n : ℕ} (hf : m.Monic f) :
    m.Monic (f ^ n) := by
  nontriviality R
  rw [Monic, leadingCoeff_pow_of_pow_leadingCoeff_ne_zero, hf.leadingCoeff_eq_one, one_pow]
  rw [hf.leadingCoeff_eq_one, one_pow]
  exact one_ne_zero

/-- Monomial degree of powers (in a reduced ring) -/
/-
**MonomialOrder.degree_pow** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_pow [IsReduced R] (f : MvPolynomial σ R) (n : Nat) : m.degree (f ^ 
n) = n • m.degree f
参数：f : MvPolynomial σ R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MonomialOrder.degree_one`：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Ty
pe u_2} [inst : CommSemiring R], m.degree 1 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `MonomialOrder.degree_pow_of_pow_leadingCoeff_ne_zero`：degree_pow_of_pow_
leadingCoeff_ne_zero {f : MvPolynomial σ R} {n : Nat} (hf : m.leadingCoeff f ^ n
 != 0) : m.degree (f ^ n) = n • m.degree f
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `MonomialOrder.leadingCoeff_ne_zero_iff`：leadingCoeff_ne_zero_iff {f : Mv
Polynomial σ R} : m.leadingCoeff f != 0 ↔ f != 0

--- 原说明 ---
Monomial degree of powers (in a reduced ring)
-/
theorem degree_pow [IsReduced R] (f : MvPolynomial σ R) (n : ℕ) :
    m.degree (f ^ n) = n • m.degree f := by
  by_cases hf : f = 0
  · rw [hf, degree_zero, smul_zero]
    by_cases hn : n = 0
    · rw [hn, pow_zero, degree_one]
    · rw [zero_pow hn, degree_zero]
  apply degree_pow_of_pow_leadingCoeff_ne_zero
  apply pow_ne_zero
  rw [leadingCoeff_ne_zero_iff]
  exact hf

/-- Leading coefficient of powers (in a reduced ring) -/
/-
**MonomialOrder.leadingCoeff_pow** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：leadingCoeff_pow [IsReduced R] (f : MvPolynomial σ R) (n : Nat) : m.leadin
gCoeff (f ^ n) = m.leadingCoeff f ^ n
参数：f : MvPolynomial σ R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.leadingCoeff.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) 
{R : Type u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.leadingCoeff 
f = MvPolynomial.coef…
· 使用定理 `MonomialOrder.degree_pow`：degree_pow [IsReduced R] (f : MvPolynomial σ R
) (n : Nat) : m.degree (f ^ n) = n • m.degree f
· 使用定理 `MonomialOrder.coeff_pow_nsmul_degree`：coeff_pow_nsmul_degree (f : MvPoly
nomial σ R) (n : Nat) : (f ^ n).coeff (n • m.degree f) = m.leadingCoeff f ^ n

--- 原说明 ---
Leading coefficient of powers (in a reduced ring)
-/
theorem leadingCoeff_pow [IsReduced R] (f : MvPolynomial σ R) (n : ℕ) :
    m.leadingCoeff (f ^ n) = m.leadingCoeff f ^ n := by
  rw [leadingCoeff, degree_pow, coeff_pow_nsmul_degree]
/-
**MonomialOrder.degree_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_smul_le {r : R} {f : MvPolynomial σ R} : m.degree (r • f) ≼[m] m.de
gree f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.smul_eq_C_mul`：smul_eq_C_mul (p : MvPolynomial σ R) (a : R)
 : a • p = C a * p
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MonomialOrder.degree_mul_le`：degree_mul_le {f g : MvPolynomial σ R} : m.
degree (f * g) ≼[m] m.degree f + m.degree g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_C`：degree_C (r : R) : m.degree (C r) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_smul_le {r : R} {f : MvPolynomial σ R} :
    m.degree (r • f) ≼[m] m.degree f := by
  rw [smul_eq_C_mul]
  apply le_of_le_of_eq degree_mul_le
  simp
/-
**MonomialOrder.degree_smul_of_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Mo
nomialOrder`。
形式化陈述：degree_smul_of_mem_nonZeroDivisors {r : R} (hr : r in nonZeroDivisors _) {
f : MvPolynomial σ R} : m.degree (r • f) = m.degree f
参数：hr : r in nonZeroDivisors _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MonomialOrder.degree_smul_le`：degree_smul_le {r : R} {f : MvPolynomial σ
 R} : m.degree (r • f) ≼[m] m.degree f
· 使用定理 `MonomialOrder.le_degree`：le_degree {f : MvPolynomial σ R} {d : σ ->₀ Nat
} (hd : d in f.support) : d ≼[m] m.degree f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.smul_eq_C_mul`：smul_eq_C_mul (p : MvPolynomial σ R) (a : R)
 : a • p = C a * p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MonomialOrder.degree_C`：degree_C (r : R) : m.degree (C r) = 0
· 使用定理 `MonomialOrder.coeff_mul_of_degree_add`：coeff_mul_of_degree_add {f g : Mv
Polynomial σ R} : (f * g).coeff (m.degree f + m.degree g) = m.leadingCoeff f * m
.leadingCoeff g
· 使用定理 `MonomialOrder.leadingCoeff_C`：leadingCoeff_C (c : R) : m.leadingCoeff (C
 c) = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nonZeroDivisors_iff`：mem_nonZeroDivisors_iff : r in M₀⁰ ↔ (forall x,
 r * x = 0 -> x = 0) ∧ forall x, x * r = 0 -> x = 0
· 使用定理 `MonomialOrder.leadingCoeff_ne_zero_iff`：leadingCoeff_ne_zero_iff {f : Mv
Polynomial σ R} : m.leadingCoeff f != 0 ↔ f != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem degree_smul_of_mem_nonZeroDivisors {r : R} (hr : r ∈ nonZeroDivisors _)
    {f : MvPolynomial σ R} :
    m.degree (r • f) = m.degree f := by
  by_cases hf : f = 0
  · simp [hf]
  apply m.toSyn.injective
  apply le_antisymm degree_smul_le
  apply le_degree
  simp only [mem_support_iff, smul_eq_C_mul]
  rw [← zero_add (degree m f), ← degree_C r, coeff_mul_of_degree_add]
  simp [not_imp_not.mpr ((mem_nonZeroDivisors_iff.mp hr).1 _) <| m.leadingCoeff_ne_zero_iff.mpr hf]
/-
**MonomialOrder.degree_smul_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrde
r`。
形式化陈述：degree_smul_of_isRegular {r : R} (hr : IsRegular r) {f : MvPolynomial σ R}
 : m.degree (r • f) = m.degree f
参数：hr : IsRegular r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.degree_smul_of_mem_nonZeroDivisors`：degree_smul_of_mem_non
ZeroDivisors {r : R} (hr : r in nonZeroDivisors _) {f : MvPolynomial σ R} : m.de
gree (r • f) = m.degree f
· 使用引理 `IsRegular.mem_nonZeroDivisors`：IsRegular.mem_nonZeroDivisors (h : IsRegu
lar r) : r in M₀⁰
-/
theorem degree_smul_of_isRegular {r : R} (hr : IsRegular r) {f : MvPolynomial σ R} :
    m.degree (r • f) = m.degree f :=
  m.degree_smul_of_mem_nonZeroDivisors hr.mem_nonZeroDivisors
/-
**MonomialOrder.degree_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_prod_le {ι : Type*} {P : ι -> MvPolynomial σ R} {s : Finset ι} : m.
degree (∏ i in s, P i) ≼[m] ∑ i in s, m.degree (P i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.C_1`：C_1 : C 1 = (1 : MvPolynomial σ R)
· 使用定理 `MonomialOrder.degree_C`：degree_C (r : R) : m.degree (C r) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MonomialOrder.degree_mul_le`：degree_mul_le {f g : MvPolynomial σ R} : m.
degree (f * g) ≼[m] m.degree f + m.degree g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MonomialOrder.isOrderedAddMonoid_syn`：∀ {σ : Type u_1} (self : MonomialO
rder σ), IsOrderedAddMonoid self.syn
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem degree_prod_le {ι : Type*} {P : ι → MvPolynomial σ R} {s : Finset ι} :
    m.degree (∏ i ∈ s, P i) ≼[m] ∑ i ∈ s, m.degree (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [← C_1, m.degree_C, map_zero]
  | insert a s has hrec =>
    rw [Finset.prod_insert has, Finset.sum_insert has]
    apply le_trans degree_mul_le
    simp only [map_add, add_le_add_iff_left, hrec]
/-
**MonomialOrder.coeff_prod_sum_degree** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：coeff_prod_sum_degree {ι : Type*} (P : ι -> MvPolynomial σ R) (s : Finset 
ι) : coeff (∑ i in s, m.degree (P i)) (∏ i in s, P i) = ∏ i in s, m.leadingCoeff
 (P i)
参数：P : ι -> MvPolynomial σ R；s : Finset ι。
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
· 使用定理 `MvPolynomial.coeff_zero_one`：coeff_zero_one : coeff 0 (1 : MvPolynomial 
σ R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `MonomialOrder.coeff_mul_of_add_of_degree_le`：coeff_mul_of_add_of_degree_
le {f g : MvPolynomial σ R} {a b : σ ->₀ Nat} (ha : m.degree f ≼[m] a) (hb : m.d
egree g ≼[m] b) : (f * g).coeff (…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MonomialOrder.degree_prod_le`：degree_prod_le {ι : Type*} {P : ι -> MvPol
ynomial σ R} {s : Finset ι} : m.degree (∏ i in s, P i) ≼[m] ∑ i in s, m.degree (
P i)
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
-/
theorem coeff_prod_sum_degree {ι : Type*} (P : ι → MvPolynomial σ R) (s : Finset ι) :
    coeff (∑ i ∈ s, m.degree (P i)) (∏ i ∈ s, P i) = ∏ i ∈ s, m.leadingCoeff (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has hrec =>
    simp only [Finset.prod_insert has, Finset.sum_insert has]
    rw [coeff_mul_of_add_of_degree_le (le_of_eq rfl) degree_prod_le]
    exact congr_arg₂ _ rfl hrec
/-
**MonomialOrder.degree_prod_of_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Mo
nomialOrder`。
形式化陈述：degree_prod_of_mem_nonZeroDivisors {ι : Type*} {P : ι -> MvPolynomial σ R}
 {s : Finset ι} (H : forall i in s, m.leadingCoeff (P i) in nonZeroDivisors _) :
 m.degree (∏ i in s, P i) = ∑ i in s, m.degree (P i)
参数：H : forall i in s, m.leadingCoeff (P i) in nonZeroDivisors _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MonomialOrder.degree_subsingleton`：degree_subsingleton [Subsingleton R] 
{f : MvPolynomial σ R} : m.degree f = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MonomialOrder.degree_prod_le`：degree_prod_le {ι : Type*} {P : ι -> MvPol
ynomial σ R} {s : Finset ι} : m.degree (∏ i in s, P i) ≼[m] ∑ i in s, m.degree (
P i)
· 使用定理 `MonomialOrder.le_degree`：le_degree {f : MvPolynomial σ R} {d : σ ->₀ Nat
} (hd : d in f.support) : d ≼[m] m.degree f
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `MonomialOrder.coeff_prod_sum_degree`：coeff_prod_sum_degree {ι : Type*} (
P : ι -> MvPolynomial σ R) (s : Finset ι) : coeff (∑ i in s, m.degree (P i)) (∏ 
i in s, P i) = ∏ i in s, …
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用引理 `prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors`：prod_mem_nonZeroDivisor
s_of_mem_nonZeroDivisors {ι : Type*} {s : Finset ι} {f : ι -> M₀} (h : forall i 
in s, f i in M₀⁰) : ∏ i in s, f i in …
-/
theorem degree_prod_of_mem_nonZeroDivisors {ι : Type*}
    {P : ι → MvPolynomial σ R} {s : Finset ι}
    (H : ∀ i ∈ s, m.leadingCoeff (P i) ∈ nonZeroDivisors _) :
    m.degree (∏ i ∈ s, P i) = ∑ i ∈ s, m.degree (P i) := by
  cases subsingleton_or_nontrivial R with
  | inl _ => simp [Subsingleton.elim _ (0 : MvPolynomial σ R)]
  | inr _ =>
    apply m.toSyn.injective
    refine le_antisymm degree_prod_le (m.le_degree ?_)
    rw [mem_support_iff, m.coeff_prod_sum_degree]
    exact nonZeroDivisors.ne_zero (prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors H)

-- TODO : it suffices that all leading coefficients but one are regular
/-
**MonomialOrder.degree_prod_of_regular** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`
。
形式化陈述：degree_prod_of_regular {ι : Type*} {P : ι -> MvPolynomial σ R} {s : Finset
 ι} (H : forall i in s, IsRegular (m.leadingCoeff (P i))) : m.degree (∏ i in s, 
P i) = ∑ i in s, m.degree (P i)
参数：H : forall i in s, IsRegular (m.leadingCoeff (P i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MonomialOrder.degree_subsingleton`：degree_subsingleton [Subsingleton R] 
{f : MvPolynomial σ R} : m.degree f = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MonomialOrder.degree_prod_le`：degree_prod_le {ι : Type*} {P : ι -> MvPol
ynomial σ R} {s : Finset ι} : m.degree (∏ i in s, P i) ≼[m] ∑ i in s, m.degree (
P i)
· 使用定理 `MonomialOrder.le_degree`：le_degree {f : MvPolynomial σ R} {d : σ ->₀ Nat
} (hd : d in f.support) : d ≼[m] m.degree f
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `MonomialOrder.coeff_prod_sum_degree`：coeff_prod_sum_degree {ι : Type*} (
P : ι -> MvPolynomial σ R) (s : Finset ι) : coeff (∑ i in s, m.degree (P i)) (∏ 
i in s, P i) = ∏ i in s, …
· 使用定理 `IsRegular.ne_zero`：IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) :
 a != 0
· 使用引理 `IsRegular.prod`：IsRegular.prod (h : forall i in s, IsRegular (f i)) : Is
Regular (∏ i in s, f i)
-/
theorem degree_prod_of_regular {ι : Type*}
    {P : ι → MvPolynomial σ R} {s : Finset ι} (H : ∀ i ∈ s, IsRegular (m.leadingCoeff (P i))) :
    m.degree (∏ i ∈ s, P i) = ∑ i ∈ s, m.degree (P i) := by
  cases subsingleton_or_nontrivial R with
  | inl _ => simp [Subsingleton.elim _ (0 : MvPolynomial σ R)]
  | inr _ =>
    apply m.toSyn.injective
    refine le_antisymm degree_prod_le (m.le_degree ?_)
    rw [mem_support_iff, m.coeff_prod_sum_degree]
    exact (IsRegular.prod H).ne_zero
/-
**MonomialOrder.degree_prod** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_prod [NoZeroDivisors R] {ι : Type*} {P : ι -> MvPolynomial σ R} {s 
: Finset ι} (H : forall i in s, P i != 0) : m.degree (∏ i in s, P i) = ∑ i in s,
 m.degree (P i)
参数：H : forall i in s, P i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MonomialOrder.degree_subsingleton`：degree_subsingleton [Subsingleton R] 
{f : MvPolynomial σ R} : m.degree f = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MonomialOrder.degree_prod_le`：degree_prod_le {ι : Type*} {P : ι -> MvPol
ynomial σ R} {s : Finset ι} : m.degree (∏ i in s, P i) ≼[m] ∑ i in s, m.degree (
P i)
· 使用定理 `MonomialOrder.le_degree`：le_degree {f : MvPolynomial σ R} {d : σ ->₀ Nat
} (hd : d in f.support) : d ≼[m] m.degree f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.coeff_prod_sum_degree`：coeff_prod_sum_degree {ι : Type*} (
P : ι -> MvPolynomial σ R) (s : Finset ι) : coeff (∑ i in s, m.degree (P i)) (∏ 
i in s, P i) = ∏ i in s, …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem degree_prod [NoZeroDivisors R] {ι : Type*} {P : ι → MvPolynomial σ R} {s : Finset ι}
    (H : ∀ i ∈ s, P i ≠ 0) :
    m.degree (∏ i ∈ s, P i) = ∑ i ∈ s, m.degree (P i) := by
  cases subsingleton_or_nontrivial R with
  | inl _ => simp [Subsingleton.elim _ (0 : MvPolynomial σ R)]
  | inr _ =>
    apply m.toSyn.injective
    refine le_antisymm degree_prod_le (m.le_degree ?_)
    simpa [m.coeff_prod_sum_degree, Finset.prod_eq_zero_iff]
/-
**MonomialOrder.degree_mul'** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_mul' [NoZeroDivisors R] {f g : MvPolynomial σ R} (hf : f * g != 0) 
: m.degree (f * g) = m.degree f + m.degree g
参数：hf : f * g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.degree_mul`：degree_mul [NoZeroDivisors R] {f g : MvPolynom
ial σ R} (hf : f != 0) (hg : g != 0) : m.degree (f * g) = m.degree f + m.degree 
g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ne_zero_and_ne_zero_of_mul`：ne_zero_and_ne_zero_of_mul (h : a * b != 0) 
: a != 0 ∧ b != 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma degree_mul' [NoZeroDivisors R] {f g : MvPolynomial σ R} (hf : f * g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply ne_zero_and_ne_zero_of_mul at hf
  exact m.degree_mul hf.1 hf.2
/-
**MonomialOrder.notMem_support_of_degree_lt** 是 Mathlib 中的一个引理，位于命名空间 `MonomialO
rder`。
形式化陈述：notMem_support_of_degree_lt {f g : MvPolynomial σ R} (h : m.degree f ≺[m] 
m.degree g) : m.degree g ∉ f.support
参数：h : m.degree f ≺[m] m.degree g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.coeff_eq_zero_of_lt`：coeff_eq_zero_of_lt {f : MvPolynomial
 σ R} {d : σ ->₀ Nat} (hd : m.degree f ≺[m] d) : f.coeff d = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma notMem_support_of_degree_lt {f g : MvPolynomial σ R} (h : m.degree f ≺[m] m.degree g) :
    m.degree g ∉ f.support := by
  simp [coeff_eq_zero_of_lt h]
/-
**MonomialOrder.leadingCoeff_prod_of_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名
空间 `MonomialOrder`。
形式化陈述：leadingCoeff_prod_of_mem_nonZeroDivisors {ι : Type*} {P : ι -> MvPolynomia
l σ R} {s : Finset ι} (H : forall i in s, m.leadingCoeff (P i) in nonZeroDivisor
s _) : m.leadingCoeff (∏ i in s, P i) = ∏ i in s, m.leadingCoeff (P i)
参数：H : forall i in s, m.leadingCoeff (P i) in nonZeroDivisors _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_prod_of_mem_nonZeroDivisors`：degree_prod_of_mem_non
ZeroDivisors {ι : Type*} {P : ι -> MvPolynomial σ R} {s : Finset ι} (H : forall 
i in s, m.leadingCoeff (P i) in nonZer…
· 使用定理 `MonomialOrder.coeff_prod_sum_degree`：coeff_prod_sum_degree {ι : Type*} (
P : ι -> MvPolynomial σ R) (s : Finset ι) : coeff (∑ i in s, m.degree (P i)) (∏ 
i in s, P i) = ∏ i in s, …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_prod_of_mem_nonZeroDivisors {ι : Type*}
    {P : ι → MvPolynomial σ R} {s : Finset ι}
    (H : ∀ i ∈ s, m.leadingCoeff (P i) ∈ nonZeroDivisors _) :
    m.leadingCoeff (∏ i ∈ s, P i) = ∏ i ∈ s, m.leadingCoeff (P i) := by
  simp only [leadingCoeff, degree_prod_of_mem_nonZeroDivisors H, coeff_prod_sum_degree]

-- TODO : it suffices that all leading coefficients but one are regular
/-
**MonomialOrder.leadingCoeff_prod_of_regular** 是 Mathlib 中的一个定理，位于命名空间 `Monomial
Order`。
形式化陈述：leadingCoeff_prod_of_regular {ι : Type*} {P : ι -> MvPolynomial σ R} {s : 
Finset ι} (H : forall i in s, IsRegular (m.leadingCoeff (P i))) : m.leadingCoeff
 (∏ i in s, P i) = ∏ i in s, m.leadingCoeff (P i)
参数：H : forall i in s, IsRegular (m.leadingCoeff (P i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_prod_of_regular`：degree_prod_of_regular {ι : Type*}
 {P : ι -> MvPolynomial σ R} {s : Finset ι} (H : forall i in s, IsRegular (m.lea
dingCoeff (P i))) : m.degr…
· 使用定理 `MonomialOrder.coeff_prod_sum_degree`：coeff_prod_sum_degree {ι : Type*} (
P : ι -> MvPolynomial σ R) (s : Finset ι) : coeff (∑ i in s, m.degree (P i)) (∏ 
i in s, P i) = ∏ i in s, …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_prod_of_regular {ι : Type*}
    {P : ι → MvPolynomial σ R} {s : Finset ι} (H : ∀ i ∈ s, IsRegular (m.leadingCoeff (P i))) :
    m.leadingCoeff (∏ i ∈ s, P i) = ∏ i ∈ s, m.leadingCoeff (P i) := by
  simp only [leadingCoeff, degree_prod_of_regular H, coeff_prod_sum_degree]

/-- A product of monic polynomials is monic -/
/-
**MonomialOrder.Monic.prod** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder.Monic`。
形式化陈述：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Type u_2} [inst : CommSemiring
 R] {ι : Type u_3} {P : ι → MvPolynomial σ R}   {s : Finset ι}, (∀ i ∈ s, m.Moni
c (P i)) → m.Monic (∏ i ∈ s, P i)
参数：∀ i ∈ s, m.Monic (P i)；∏ i ∈ s, P i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.Monic.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) {R : Ty
pe u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.Monic f = (m.leading
Coeff f = 1)
· 使用定理 `MonomialOrder.leadingCoeff_prod_of_regular`：leadingCoeff_prod_of_regular
 {ι : Type*} {P : ι -> MvPolynomial σ R} {s : Finset ι} (H : forall i in s, IsRe
gular (m.leadingCoeff (P i))) : …
· 使用定理 `MonomialOrder.Monic.leadingCoeff_eq_one`：∀ {σ : Type u_1} {m : MonomialO
rder σ} {R : Type u_2} [inst : CommSemiring R] {f : MvPolynomial σ R},   m.Monic
 f → m.leadingCoeff f = 1
· 使用定理 `isRegular_one`：isRegular_one : IsRegular (1 : R)
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1

--- 原说明 ---
A product of monic polynomials is monic
-/
protected theorem Monic.prod {ι : Type*} {P : ι → MvPolynomial σ R} {s : Finset ι}
    (H : ∀ i ∈ s, m.Monic (P i)) :
    m.Monic (∏ i ∈ s, P i) := by
  rw [Monic, leadingCoeff_prod_of_regular]
  · exact Finset.prod_eq_one H
  · intro i hi
    rw [(H i hi).leadingCoeff_eq_one]
    exact isRegular_one

/--
The leading term in a multivariate polynomial is zero if and only if this polynomial is zero.
-/
@[simp]
/-
**MonomialOrder.leadingTerm_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder
`。
形式化陈述：leadingTerm_eq_zero_iff (p : MvPolynomial σ R) : m.leadingTerm p = 0 ↔ p =
 0
参数：p : MvPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The leading term in a multivariate polynomial is zero if and only if this polyno
mial is zero.
-/
lemma leadingTerm_eq_zero_iff (p : MvPolynomial σ R) : m.leadingTerm p = 0 ↔ p = 0 := by
  simp only [leadingTerm, monomial_eq_zero, leadingCoeff_eq_zero_iff]

/-- The leading term of the zero polynomial is zero -/
@[simp]
/-
**MonomialOrder.leadingTerm_zero** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：leadingTerm_zero : m.leadingTerm (0 : MvPolynomial σ R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.leadingTerm_eq_zero_iff`：leadingTerm_eq_zero_iff (p : MvPo
lynomial σ R) : m.leadingTerm p = 0 ↔ p = 0

--- 原说明 ---
The leading term of the zero polynomial is zero
-/
lemma leadingTerm_zero : m.leadingTerm (0 : MvPolynomial σ R) = 0 := by
  rw [leadingTerm_eq_zero_iff]

/--
The set of leading terms of non-zero polynomials within a set `B` is equal to the set of
leading terms of all polynomials within `B`, excluding zero.
-/
/-
**MonomialOrder.image_leadingTerm_sdiff_singleton_zero** 是 Mathlib 中的一个引理，位于命名空间
 `MonomialOrder`。
形式化陈述：image_leadingTerm_sdiff_singleton_zero (B : Set (MvPolynomial σ R)) : m.le
adingTerm '' (B \ {0}) = (m.leadingTerm '' B) \ {0}
参数：B : Set (MvPolynomial σ R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The set of leading terms of non-zero polynomials within a set `B` is equal to th
e set of
leading terms of all polynomials within `B`, excluding zero.
-/
lemma image_leadingTerm_sdiff_singleton_zero (B : Set (MvPolynomial σ R)) :
    m.leadingTerm '' (B \ {0}) = (m.leadingTerm '' B) \ {0} := by
  aesop

/--
The set of leading terms of zero and polynomials within a set `B` is equal to the set of
zero and leading terms of polynomials within `B`.
-/
/-
**MonomialOrder.image_leadingTerm_insert_zero** 是 Mathlib 中的一个引理，位于命名空间 `Monomia
lOrder`。
形式化陈述：image_leadingTerm_insert_zero (B : Set (MvPolynomial σ R)) : m.leadingTerm
 '' (insert (0 : MvPolynomial σ R) B) = insert 0 (m.leadingTerm '' B)
参数：B : Set (MvPolynomial σ R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MonomialOrder.leadingTerm_zero`：leadingTerm_zero : m.leadingTerm (0 : Mv
Polynomial σ R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The set of leading terms of zero and polynomials within a set `B` is equal to th
e set of
zero and leading terms of polynomials within `B`.
-/
lemma image_leadingTerm_insert_zero (B : Set (MvPolynomial σ R)) :
    m.leadingTerm '' (insert (0 : MvPolynomial σ R) B) = insert 0 (m.leadingTerm '' B) := by
  aesop

/-- The degree of `f` equals to the degree of `leadingTerm f` -/
@[simp]
/-
**MonomialOrder.degree_leadingTerm** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_leadingTerm (f : MvPolynomial σ R) : m.degree (m.leadingTerm f) = m
.degree f
参数：f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_monomial`：degree_monomial {d : σ ->₀ Nat} (c : R) [
Decidable (c = 0)] : m.degree (monomial d c) = if c = 0 then 0 else d
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The degree of `f` equals to the degree of `leadingTerm f`
-/
lemma degree_leadingTerm (f : MvPolynomial σ R) :
    m.degree (m.leadingTerm f) = m.degree f := by
  classical
  simp only [leadingTerm, degree_monomial, leadingCoeff_eq_zero_iff, ite_eq_right_iff]
  simp_intro h

@[simp]
/-
**MonomialOrder.leadingCoeff_leadingTerm** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrde
r`。
形式化陈述：leadingCoeff_leadingTerm (f : MvPolynomial σ R) : m.leadingCoeff (m.leadin
gTerm f) = m.leadingCoeff f
参数：f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.leadingCoeff_monomial`：leadingCoeff_monomial {d : σ ->₀ Na
t} (c : R) : m.leadingCoeff (monomial d c) = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leadingCoeff_leadingTerm (f : MvPolynomial σ R) :
    m.leadingCoeff (m.leadingTerm f) = m.leadingCoeff f := by
  simp [leadingTerm, leadingCoeff_monomial]

@[simp]
/-
**MonomialOrder.leadingTerm_leadingTerm** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder
`。
形式化陈述：leadingTerm_leadingTerm (f : MvPolynomial σ R) : m.leadingTerm (m.leadingT
erm f) = m.leadingTerm f
参数：f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `MonomialOrder.leadingCoeff_zero`：leadingCoeff_zero : m.leadingCoeff (0 :
 MvPolynomial σ R) = 0
· 使用定理 `MvPolynomial.monomial_zero`：monomial_zero {s : σ ->₀ Nat} : monomial s (
0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_monomial`：degree_monomial {d : σ ->₀ Nat} (c : R) [
Decidable (c = 0)] : m.degree (monomial d c) = if c = 0 then 0 else d
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MonomialOrder.leadingCoeff_monomial`：leadingCoeff_monomial {d : σ ->₀ Na
t} (c : R) : m.leadingCoeff (monomial d c) = c
-/
lemma leadingTerm_leadingTerm (f : MvPolynomial σ R) :
    m.leadingTerm (m.leadingTerm f) = m.leadingTerm f := by
  classical
  by_cases h : f = 0 <;> simp [leadingTerm, h, degree_monomial]

@[simp]
/-
**MonomialOrder.leadingTerm_C** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：leadingTerm_C (c : R) : m.leadingTerm (C c) = C c
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonomialOrder.degree_C`：degree_C (r : R) : m.degree (C r) = 0
· 使用定理 `MonomialOrder.leadingCoeff_C`：leadingCoeff_C (c : R) : m.leadingCoeff (C
 c) = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leadingTerm_C (c : R) : m.leadingTerm (C c) = C c := by
  simp [leadingTerm, leadingCoeff_C]

@[simp]
/-
**MonomialOrder.leadingTerm_monomial** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：leadingTerm_monomial (s : σ ->₀ Nat) (c : R) : m.leadingTerm (monomial s c
) = monomial s c
参数：s : σ ->₀ Nat；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.monomial_zero`：monomial_zero {s : σ ->₀ Nat} : monomial s (
0 : R) = 0
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `MonomialOrder.leadingCoeff_zero`：leadingCoeff_zero : m.leadingCoeff (0 :
 MvPolynomial σ R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_monomial`：degree_monomial {d : σ ->₀ Nat} (c : R) [
Decidable (c = 0)] : m.degree (monomial d c) = if c = 0 then 0 else d
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MonomialOrder.leadingCoeff_monomial`：leadingCoeff_monomial {d : σ ->₀ Na
t} (c : R) : m.leadingCoeff (monomial d c) = c
-/
lemma leadingTerm_monomial (s : σ →₀ ℕ) (c : R) :
    m.leadingTerm (monomial s c) = monomial s c := by
  classical
  by_cases h : c = 0 <;> simp [leadingTerm, degree_monomial, h]

@[simp]
/-
**MonomialOrder.degree_leadingTerm_mul** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`
。
形式化陈述：degree_leadingTerm_mul [NoZeroDivisors R] (p q : MvPolynomial σ R) : m.deg
ree (m.leadingTerm p * q) = m.degree (p * q)
参数：p q : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_mul`：degree_mul [NoZeroDivisors R] {f g : MvPolynom
ial σ R} (hf : f != 0) (hg : g != 0) : m.degree (f * g) = m.degree f + m.degree 
g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_monomial`：degree_monomial {d : σ ->₀ Nat} (c : R) [
Decidable (c = 0)] : m.degree (monomial d c) = if c = 0 then 0 else d
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用引理 `MonomialOrder.leadingTerm_zero`：leadingTerm_zero : m.leadingTerm (0 : Mv
Polynomial σ R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma degree_leadingTerm_mul [NoZeroDivisors R] (p q : MvPolynomial σ R) :
    m.degree (m.leadingTerm p * q) = m.degree (p * q) := by
  wlog! +distrib h : p ≠ 0 ∧ q ≠ 0
  · obtain rfl | rfl := h <;> simp
  classical
  simp [leadingTerm, degree_mul, h, degree_monomial]

@[simp]
/-
**MonomialOrder.degree_mul_leadingTerm** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`
。
形式化陈述：degree_mul_leadingTerm [NoZeroDivisors R] (p q : MvPolynomial σ R) : m.deg
ree (p * m.leadingTerm q) = m.degree (p * q)
参数：p q : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonomialOrder.degree_leadingTerm_mul`：degree_leadingTerm_mul [NoZeroDivi
sors R] (p q : MvPolynomial σ R) : m.degree (m.leadingTerm p * q) = m.degree (p 
* q)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma degree_mul_leadingTerm [NoZeroDivisors R] (p q : MvPolynomial σ R) :
    m.degree (p * m.leadingTerm q) = m.degree (p * q) :=
  mul_comm _ p ▸ mul_comm _ p ▸ m.degree_leadingTerm_mul q p
/-
**MonomialOrder.degree_lt_of_left_ne_zero_of_degree_mul_lt** 是 Mathlib 中的一个引理，位于
命名空间 `MonomialOrder`。
形式化陈述：degree_lt_of_left_ne_zero_of_degree_mul_lt [NoZeroDivisors R] {p p' q : Mv
Polynomial σ R} (hp : p != 0) (h : m.degree (p * q) ≺[m] m.degree (p' * q)) : m.
degree p ≺[m] m.degree p'
参数：hp : p != 0；h : m.degree (p * q) ≺[m] m.degree (p' * q)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_mul`：degree_mul [NoZeroDivisors R] {f g : MvPolynom
ial σ R} (hf : f != 0) (hg : g != 0) : m.degree (f * g) = m.degree f + m.degree 
g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
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
· 使用定理 `MonomialOrder.isOrderedAddMonoid_syn`：∀ {σ : Type u_1} (self : MonomialO
rder σ), IsOrderedAddMonoid self.syn
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `lt_of_le_of_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `MonomialOrder.degree_mul_le`：degree_mul_le {f g : MvPolynomial σ R} : m.
degree (f * g) ≼[m] m.degree f + m.degree g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
-/
lemma degree_lt_of_left_ne_zero_of_degree_mul_lt [NoZeroDivisors R] {p p' q : MvPolynomial σ R}
    (hp : p ≠ 0) (h : m.degree (p * q) ≺[m] m.degree (p' * q)) :
    m.degree p ≺[m] m.degree p' := by
  wlog! hq : q ≠ 0
  · simp [hq] at h
  apply lt_of_le_of_lt' m.degree_mul_le at h
  simpa [m.degree_mul hp hq] using h
/-
**MonomialOrder.degree_mul_lt_iff_left_lt_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `
MonomialOrder`。
形式化陈述：degree_mul_lt_iff_left_lt_of_ne_zero [NoZeroDivisors R] {p p' q : MvPolyno
mial σ R} (hp : p != 0) (hq : q != 0) : m.degree (p * q) ≺[m] m.degree (p' * q) 
↔ m.degree p ≺[m] m.degree p'
参数：hp : p != 0；hq : q != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonomialOrder.degree_lt_of_left_ne_zero_of_degree_mul_lt`：degree_lt_of_l
eft_ne_zero_of_degree_mul_lt [NoZeroDivisors R] {p p' q : MvPolynomial σ R} (hp 
: p != 0) (h : m.degree (p * q) ≺[m] m.degree …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_mul`：degree_mul [NoZeroDivisors R] {f g : MvPolynom
ial σ R} (hf : f != 0) (hg : g != 0) : m.degree (f * g) = m.degree f + m.degree 
g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
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
· 使用定理 `MonomialOrder.isOrderedAddMonoid_syn`：∀ {σ : Type u_1} (self : MonomialO
rder σ), IsOrderedAddMonoid self.syn
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
lemma degree_mul_lt_iff_left_lt_of_ne_zero [NoZeroDivisors R] {p p' q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    m.degree (p * q) ≺[m] m.degree (p' * q) ↔ m.degree p ≺[m] m.degree p' := by
  refine ⟨m.degree_lt_of_left_ne_zero_of_degree_mul_lt hp, ?_⟩
  intro h
  simpa [m.degree_mul hp hq, m.degree_mul (show p' ≠ 0 by contrapose! h; simp [h]) hq] using h

@[simp]
/-
**MonomialOrder.monic_leadingTerm** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：monic_leadingTerm (p : MvPolynomial σ R) : m.Monic (m.leadingTerm p) ↔ m.M
onic p
参数：p : MvPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.leadingCoeff_monomial`：leadingCoeff_monomial {d : σ ->₀ Na
t} (c : R) : m.leadingCoeff (monomial d c) = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monic_leadingTerm (p : MvPolynomial σ R) :
    m.Monic (m.leadingTerm p) ↔ m.Monic p := by simp [leadingTerm, Monic]
/-
**MonomialOrder.support_leadingTerm** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：support_leadingTerm (p : MvPolynomial σ R) [Decidable (p = 0)] : support (
m.leadingTerm p) = if p = 0 then ∅ else {m.degree p}
参数：p : MvPolynomial σ R；p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.support_monomial`：support_monomial [h : Decidable (a = 0)] 
: (monomial s a).support = if a = 0 then ∅ else {s}
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma support_leadingTerm (p : MvPolynomial σ R) [Decidable (p = 0)] :
    support (m.leadingTerm p) = if p = 0 then ∅ else {m.degree p} := by
  classical
  simp [leadingTerm, support_monomial]
/-
**MonomialOrder.support_leadingTerm'** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：support_leadingTerm' {p : MvPolynomial σ R} (hp : p != 0) : support (m.lea
dingTerm p) = {m.degree p}
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.support_monomial`：support_monomial [h : Decidable (a = 0)] 
: (monomial s a).support = if a = 0 then ∅ else {s}
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma support_leadingTerm' {p : MvPolynomial σ R} (hp : p ≠ 0) :
    support (m.leadingTerm p) = {m.degree p} := by
  classical
  simp [leadingTerm, support_monomial, hp]
/-
**MonomialOrder.le_degree_of_mem_support** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrde
r`。
形式化陈述：le_degree_of_mem_support {p : MvPolynomial σ R} {a : σ ->₀ Nat} (ha : a in
 p.support) : a ≼[m] m.degree p
参数：ha : a in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
lemma le_degree_of_mem_support {p : MvPolynomial σ R} {a : σ →₀ ℕ}
    (ha : a ∈ p.support) : a ≼[m] m.degree p := by
  simp [degree, Finset.le_sup ha]
/-
**MonomialOrder.leadingTerm_eq_leadingTerm_iff** 是 Mathlib 中的一个引理，位于命名空间 `Monomi
alOrder`。
形式化陈述：leadingTerm_eq_leadingTerm_iff {p q : MvPolynomial σ R} : m.leadingTerm p 
= m.leadingTerm q ↔ m.leadingCoeff p = m.leadingCoeff q ∧ m.degree p = m.degree 
q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.leadingTerm.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) {
R : Type u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.leadingTerm f 
= (MvPolynomial.mono…
· 使用定理 `MvPolynomial.monomial_eq_monomial_iff`：monomial_eq_monomial_iff {α : Typ
e*} (a₁ a₂ : α ->₀ Nat) (b₁ b₂ : R) : monomial a₁ b₁ = monomial a₂ b₂ ↔ a₁ = a₂ 
∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `MonomialOrder.leadingCoeff_zero`：leadingCoeff_zero : m.leadingCoeff (0 :
 MvPolynomial σ R) = 0
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma leadingTerm_eq_leadingTerm_iff {p q : MvPolynomial σ R} :
    m.leadingTerm p = m.leadingTerm q ↔
    m.leadingCoeff p = m.leadingCoeff q ∧ m.degree p = m.degree q := by
  rw [leadingTerm, leadingTerm, monomial_eq_monomial_iff]
  aesop

@[simp]
/-
**MonomialOrder.leadingTerm_mul** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：leadingTerm_mul [NoZeroDivisors R] (p q : MvPolynomial σ R) : m.leadingTer
m (p * q) = m.leadingTerm p * m.leadingTerm q
参数：p q : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.leadingTerm_zero`：leadingTerm_zero : m.leadingTerm (0 : Mv
Polynomial σ R) = 0
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_eq_mul`：zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MonomialOrder.degree_mul'`：degree_mul' [NoZeroDivisors R] {f g : MvPolyn
omial σ R} (hf : f * g != 0) : m.degree (f * g) = m.degree f + m.degree g
· 使用定理 `MonomialOrder.leadingCoeff_mul`：∀ {σ : Type u_1} {m : MonomialOrder σ} {
R : Type u_2} [inst : CommSemiring R] [NoZeroDivisors R]   {f g : MvPolynomial σ
 R}, m.leadingCoeff …
· 使用定理 `MvPolynomial.monomial_mul`：monomial_mul {s s' : σ ->₀ Nat} {a b : R} : m
onomial s a * monomial s' b = monomial (s + s') (a * b)
-/
theorem leadingTerm_mul [NoZeroDivisors R] (p q : MvPolynomial σ R) :
    m.leadingTerm (p * q) = m.leadingTerm p * m.leadingTerm q := by
  by_cases! h0 : p * q = 0
  · simp [h0, zero_eq_mul.mp]
  simp [leadingTerm, m.degree_mul' h0]

@[simp, nontriviality]
/-
**MonomialOrder.monic_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：monic_of_subsingleton [Subsingleton R] (p : MvPolynomial σ R) : m.Monic p
参数：p : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.eq_one`：Subsingleton.eq_one [One α] [Subsingleton α] (a : α
) : a = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma monic_of_subsingleton [Subsingleton R] (p : MvPolynomial σ R) :
    m.Monic p := by
  simp [Subsingleton.eq_one (α := MvPolynomial σ R)]
/-
**MonomialOrder.degree_le_degree_of_support_subset** 是 Mathlib 中的一个引理，位于命名空间 `Mo
nomialOrder`。
形式化陈述：degree_le_degree_of_support_subset {p q : MvPolynomial σ R} (h : p.support
 subseteq q.support) : m.degree p ≼[m] m.degree q
参数：h : p.support subseteq q.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
-/
lemma degree_le_degree_of_support_subset {p q : MvPolynomial σ R} (h : p.support ⊆ q.support) :
    m.degree p ≼[m] m.degree q := by
  simp_rw [degree, m.toSyn.apply_symm_apply]
  exact Finset.sup_mono h
/-
**MonomialOrder.toSyn_degree_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：toSyn_degree_mul_le {f g : MvPolynomial σ R} : m.toSyn (m.degree (f * g)) 
<= m.toSyn (m.degree f) + m.toSyn (m.degree g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.degree_mul_le`：degree_mul_le {f g : MvPolynomial σ R} : m.
degree (f * g) ≼[m] m.degree f + m.degree g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem toSyn_degree_mul_le {f g : MvPolynomial σ R} :
    m.toSyn (m.degree (f * g)) ≤ m.toSyn (m.degree f) + m.toSyn (m.degree g) :=
  map_add m.toSyn _ _ ▸ degree_mul_le
/-
**MonomialOrder.mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors** 是 Math
lib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors {f : MvPolynomial 
σ R} (hf : m.leadingCoeff f in R⁰) : f in (MvPolynomial σ R)⁰
参数：hf : m.leadingCoeff f in R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `nonZeroDivisorsLeft_eq_nonZeroDivisors`：nonZeroDivisorsLeft_eq_nonZeroDi
visors : nonZeroDivisorsLeft M₀ = nonZeroDivisors M₀
· 使用引理 `mem_nonZeroDivisorsLeft_iff`：mem_nonZeroDivisorsLeft_iff : x in nonZeroD
ivisorsLeft M₀ ↔ forall y, x * y = 0 -> y = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MonomialOrder.leadingCoeff_eq_zero_iff`：leadingCoeff_eq_zero_iff {f : Mv
Polynomial σ R} : leadingCoeff m f = 0 ↔ f = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.leadingCoeff_mul_of_left_mem_nonZeroDivisors`：leadingCoeff
_mul_of_left_mem_nonZeroDivisors {f g : MvPolynomial σ R} (hf : m.leadingCoeff f
 in nonZeroDivisors _) : m.leadingCoeff (f * g) …
· 使用引理 `mul_left_mem_nonZeroDivisors_eq_zero_iff`：mul_left_mem_nonZeroDivisors_e
q_zero_iff (hr : r in M₀⁰) : r * x = 0 ↔ x = 0
-/
lemma mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors
    {f : MvPolynomial σ R} (hf : m.leadingCoeff f ∈ R⁰) : f ∈ (MvPolynomial σ R)⁰ := by
  rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors, mem_nonZeroDivisorsLeft_iff]
  intro g
  simp [← m.leadingCoeff_eq_zero_iff (f := f * g),
    m.leadingCoeff_mul_of_left_mem_nonZeroDivisors hf, mul_left_mem_nonZeroDivisors_eq_zero_iff hf]

section withBotDegree

variable (f g : MvPolynomial σ R)

variable (m) in
/-- the degree of a multivariate polynomial with respect to a monomial ordering, where polynomial
`0` has degree `⊥`, which is not equal to `0`. `MonomialOrder.withBotDegree` is to
`MonomialOrder.degree` as `Polynomial.degree` is to `Polynomial.natDegree`. -/
/-
**MonomialOrder.withBotDegree** 是 Mathlib 中的一个定义，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree : WithBot (σ ->₀ Nat)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the degree of a multivariate polynomial with respect to a monomial ordering, whe
re polynomial
`0` has degree `⊥`, which is not equal to `0`. `MonomialOrder.withBotDegree` is 
to
`MonomialOrder.degree` as `Polynomial.degree` is to `Polynomial.natDegree`.
-/
noncomputable def withBotDegree : WithBot (σ →₀ ℕ) :=
  f.support.image m.toSyn |>.max.map m.toSyn.symm
/-
**MonomialOrder.withBotDegree_eq** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_eq [Decidable (f = 0)] : m.withBotDegree f = if f = 0 then ⊥
 else ↑(m.degree f)
参数：f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_sup_of_nonempty`：coe_sup_of_nonempty (h : s.Nonempty) (f : β 
-> α) : (↑(s.sup f) : WithBot α) = s.sup ((↑) ∘ f)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
lemma withBotDegree_eq [Decidable (f = 0)] :
    m.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f) := by
  simp [withBotDegree, degree]
  by_cases hf : f = 0
  · simp [hf]
  · simp [hf, Finset.max_eq_sup_coe, ← Finset.coe_sup_of_nonempty _ (⇑m.toSyn)]

@[simp]
/-
**MonomialOrder.withBotDegree_eq_coe_degree_iff** 是 Mathlib 中的一个引理，位于命名空间 `Monom
ialOrder`。
形式化陈述：withBotDegree_eq_coe_degree_iff : m.withBotDegree f = m.degree f ↔ f != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.withBotDegree_eq`：withBotDegree_eq [Decidable (f = 0)] : m
.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma withBotDegree_eq_coe_degree_iff : m.withBotDegree f = m.degree f ↔ f ≠ 0 := by
  classical
  simp [withBotDegree_eq]

@[simp]
/-
**MonomialOrder.withBotDegree_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrde
r`。
形式化陈述：withBotDegree_eq_bot_iff : m.withBotDegree f = ⊥ ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.withBotDegree_eq`：withBotDegree_eq [Decidable (f = 0)] : m
.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma withBotDegree_eq_bot_iff : m.withBotDegree f = ⊥ ↔ f = 0 := by
  classical
  simp [withBotDegree_eq]
/-
**MonomialOrder.degree_eq_unbotD_withBotDegree** 是 Mathlib 中的一个引理，位于命名空间 `Monomi
alOrder`。
形式化陈述：degree_eq_unbotD_withBotDegree : m.degree f = (m.withBotDegree f).unbotD 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用引理 `MonomialOrder.withBotDegree_eq`：withBotDegree_eq [Decidable (f = 0)] : m
.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma degree_eq_unbotD_withBotDegree : m.degree f = (m.withBotDegree f).unbotD 0 := by
  classical
  by_cases h : f = 0 <;> simp [withBotDegree_eq, h]

@[simp]
/-
**MonomialOrder.withBotDegree_zero** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_zero : m.withBotDegree (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma withBotDegree_zero : m.withBotDegree (R := R) 0 = ⊥ := rfl
/-
**MonomialOrder.withBotDegree_monomial** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`
。
形式化陈述：withBotDegree_monomial (d) (c) [Decidable (c = 0)] : m.withBotDegree (R
参数：d；c；c = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.monomial_zero`：monomial_zero {s : σ ->₀ Nat} : monomial s (
0 : R) = 0
· 使用引理 `MonomialOrder.withBotDegree_eq`：withBotDegree_eq [Decidable (f = 0)] : m
.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MonomialOrder.degree_monomial`：degree_monomial {d : σ ->₀ Nat} (c : R) [
Decidable (c = 0)] : m.degree (monomial d c) = if c = 0 then 0 else d
-/
lemma withBotDegree_monomial (d) (c) [Decidable (c = 0)] :
    m.withBotDegree (R := R) (monomial d c) = if c = 0 then ⊥ else ↑d := by
  classical
  split_ifs <;> simp [withBotDegree_eq, *, m.degree_monomial]
/-
**MonomialOrder.withBotDegree_C** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_C (c) [Decidable (c = 0)] : m.withBotDegree (R
参数：c；c = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.withBotDegree_monomial`：withBotDegree_monomial (d) (c) [De
cidable (c = 0)] : m.withBotDegree (R
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma withBotDegree_C (c) [Decidable (c = 0)] :
    m.withBotDegree (R := R) (C c) = if c = 0 then ⊥ else 0 := by
  simp [← monomial_zero', withBotDegree_monomial]

@[simp]
/-
**MonomialOrder.withBotDegree_leadingTerm** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrd
er`。
形式化陈述：withBotDegree_leadingTerm : m.withBotDegree (m.leadingTerm f) = m.withBotD
egree f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.withBotDegree_eq`：withBotDegree_eq [Decidable (f = 0)] : m
.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `MonomialOrder.degree_leadingTerm`：degree_leadingTerm (f : MvPolynomial σ
 R) : m.degree (m.leadingTerm f) = m.degree f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma withBotDegree_leadingTerm : m.withBotDegree (m.leadingTerm f) = m.withBotDegree f := by
  classical
  simp [withBotDegree_eq]

@[simp]
/-
**MonomialOrder.withBotDegree_one** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_one [Nontrivial R] : m.withBotDegree (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.withBotDegree_eq`：withBotDegree_eq [Decidable (f = 0)] : m
.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `MonomialOrder.degree_one`：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Ty
pe u_2} [inst : CommSemiring R], m.degree 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma withBotDegree_one [Nontrivial R] : m.withBotDegree (R := R) 1 = 0 := by
  classical
  simp [withBotDegree_eq]

variable {f g} in
/-
**MonomialOrder.withBotDegree_mul_of_left_mem_nonZeroDivisors** 是 Mathlib 中的一个引理
，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_mul_of_left_mem_nonZeroDivisors (hf : m.leadingCoeff f in no
nZeroDivisors _) : m.withBotDegree (f * g) = m.withBotDegree f + m.withBotDegree
 g
参数：hf : m.leadingCoeff f in nonZeroDivisors _。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `mem_nonZeroDivisors_iff_left`：mem_nonZeroDivisors_iff_left : r in M₀⁰ ↔ 
forall x, r * x = 0 -> x = 0
· 使用引理 `MonomialOrder.mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors`：m
em_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors {f : MvPolynomial σ R} (h
f : m.leadingCoeff f in R⁰) : f in (MvPolynomial σ R)⁰
· 使用引理 `MonomialOrder.withBotDegree_eq`：withBotDegree_eq [Decidable (f = 0)] : m
.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MonomialOrder.degree_mul_of_left_mem_nonZeroDivisors`：degree_mul_of_left
_mem_nonZeroDivisors {f g : MvPolynomial σ R} (hf : m.leadingCoeff f in nonZeroD
ivisors _) (hg : g != 0) : m.degree (f * g…
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma withBotDegree_mul_of_left_mem_nonZeroDivisors (hf : m.leadingCoeff f ∈ nonZeroDivisors _) :
    m.withBotDegree (f * g) = m.withBotDegree f + m.withBotDegree g := by
  classical
  by_cases! h0 : f = 0 ∨ g = 0
  · rcases h0 with h0 | h0 <;> simp [h0]
  suffices f * g ≠ 0 by simp [withBotDegree_eq, m.degree_mul_of_left_mem_nonZeroDivisors hf, *]
  apply mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors at hf
  rw [mem_nonZeroDivisors_iff_left] at hf
  tauto

variable {f g} in
/-
**MonomialOrder.withBotDegree_mul_of_right_mem_nonZeroDivisors** 是 Mathlib 中的一个引
理，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_mul_of_right_mem_nonZeroDivisors (hf : m.leadingCoeff g in n
onZeroDivisors _) : m.withBotDegree (f * g) = m.withBotDegree f + m.withBotDegre
e g
参数：hf : m.leadingCoeff g in nonZeroDivisors _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `MonomialOrder.withBotDegree_mul_of_left_mem_nonZeroDivisors`：withBotDegr
ee_mul_of_left_mem_nonZeroDivisors (hf : m.leadingCoeff f in nonZeroDivisors _) 
: m.withBotDegree (f * g) = m.withBotDegree f + m…
-/
lemma withBotDegree_mul_of_right_mem_nonZeroDivisors (hf : m.leadingCoeff g ∈ nonZeroDivisors _) :
    m.withBotDegree (f * g) = m.withBotDegree f + m.withBotDegree g := by
  rw [mul_comm, add_comm, withBotDegree_mul_of_left_mem_nonZeroDivisors (hf := hf)]

@[simp]
/-
**MonomialOrder.withBotDegree_mul** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_mul [NoZeroDivisors R] : m.withBotDegree (f * g) = m.withBot
Degree f + m.withBotDegree g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `MonomialOrder.withBotDegree_mul_of_left_mem_nonZeroDivisors`：withBotDegr
ee_mul_of_left_mem_nonZeroDivisors (hf : m.leadingCoeff f in nonZeroDivisors _) 
: m.withBotDegree (f * g) = m.withBotDegree f + m…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `MonomialOrder.leadingCoeff_ne_zero_iff`：leadingCoeff_ne_zero_iff {f : Mv
Polynomial σ R} : m.leadingCoeff f != 0 ↔ f != 0
-/
lemma withBotDegree_mul [NoZeroDivisors R] :
    m.withBotDegree (f * g) = m.withBotDegree f + m.withBotDegree g := by
  nontriviality R using Subsingleton.eq_zero (α := MvPolynomial σ R)
  by_cases! hf : f = 0
  · simp [hf]
  rw [← m.leadingCoeff_ne_zero_iff, ← mem_nonZeroDivisors_iff_ne_zero] at hf
  exact m.withBotDegree_mul_of_left_mem_nonZeroDivisors hf
/-
**MonomialOrder.withBotDegree_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_mul_le : m.withBotDegree (f * g) ≼'[m] m.withBotDegree f + m
.withBotDegree g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MonomialOrder.withBotDegree_eq_coe_degree_iff`：withBotDegree_eq_coe_degr
ee_iff : m.withBotDegree f = m.degree f ↔ f != 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MonomialOrder.degree_mul_le`：degree_mul_le {f g : MvPolynomial σ R} : m.
degree (f * g) ≼[m] m.degree f + m.degree g
-/
lemma withBotDegree_mul_le :
    m.withBotDegree (f * g) ≼'[m] m.withBotDegree f + m.withBotDegree g := by
  by_cases! h0 : f * g = 0
  · simp [h0]
  simp [-map_add, m.withBotDegree_eq_coe_degree_iff _ |>.mpr h0,
    m.withBotDegree_eq_coe_degree_iff f |>.mpr (by grind),
    m.withBotDegree_eq_coe_degree_iff g |>.mpr (by grind), ← WithBot.coe_add, m.degree_mul_le]
/-
**MonomialOrder.toWithBotSyn_withBotDegree_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `Mon
omialOrder`。
形式化陈述：toWithBotSyn_withBotDegree_mul_le : m.toWithBotSyn (m.withBotDegree (f * g
)) <= m.toWithBotSyn (m.withBotDegree f) + m.toWithBotSyn (m.withBotDegree g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MonomialOrder.withBotDegree_eq_coe_degree_iff`：withBotDegree_eq_coe_degr
ee_iff : m.withBotDegree f = m.degree f ↔ f != 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MonomialOrder.toSyn_degree_mul_le`：toSyn_degree_mul_le {f g : MvPolynomi
al σ R} : m.toSyn (m.degree (f * g)) <= m.toSyn (m.degree f) + m.toSyn (m.degree
 g)
-/
lemma toWithBotSyn_withBotDegree_mul_le :
    m.toWithBotSyn (m.withBotDegree (f * g)) ≤
      m.toWithBotSyn (m.withBotDegree f) + m.toWithBotSyn (m.withBotDegree g) := by
  by_cases h0 : f * g = 0
  · simp [h0]
  simp [m.withBotDegree_eq_coe_degree_iff f |>.mpr (by grind),
    m.withBotDegree_eq_coe_degree_iff g |>.mpr (by grind),
    m.withBotDegree_eq_coe_degree_iff _ |>.mpr h0, ← WithBot.coe_add,
    m.toSyn_degree_mul_le]
/-
**MonomialOrder.withBotDegree_le_withBotDegree_iff** 是 Mathlib 中的一个引理，位于命名空间 `Mo
nomialOrder`。
形式化陈述：withBotDegree_le_withBotDegree_iff : m.withBotDegree f ≼'[m] m.withBotDegr
ee g ↔ (m.degree f ≼[m] m.degree g ∧ (g = 0 -> f = 0))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.withBotDegree_eq`：withBotDegree_eq [Decidable (f = 0)] : m
.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma withBotDegree_le_withBotDegree_iff :
    m.withBotDegree f ≼'[m] m.withBotDegree g ↔
      (m.degree f ≼[m] m.degree g ∧ (g = 0 → f = 0)) := by
  classical
  by_cases! +distrib h : f ≠ 0 ∧ g ≠ 0
  · simp [m.withBotDegree_eq, h, m.toWithBotSyn_apply]
  rcases h with h | _
  · simp [h]
  · aesop

variable {g} in
/-
**MonomialOrder.withBotDegree_le_withBotDegree_iff_of_ne_zero** 是 Mathlib 中的一个引理
，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_le_withBotDegree_iff_of_ne_zero (hg : g != 0) : m.withBotDeg
ree f ≼'[m] m.withBotDegree g ↔ m.degree f ≼[m] m.degree g
参数：hg : g != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma withBotDegree_le_withBotDegree_iff_of_ne_zero (hg : g ≠ 0) :
    m.withBotDegree f ≼'[m] m.withBotDegree g ↔ m.degree f ≼[m] m.degree g := by
  simp [withBotDegree_le_withBotDegree_iff, hg]
/-
**MonomialOrder.withBotDegree_lt_withBotDegree_iff** 是 Mathlib 中的一个引理，位于命名空间 `Mo
nomialOrder`。
形式化陈述：withBotDegree_lt_withBotDegree_iff : m.withBotDegree f ≺'[m] m.withBotDegr
ee g ↔ (m.degree f ≺[m] m.degree g ∨ (f = 0 ∧ g != 0))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `MonomialOrder.withBotDegree_eq`：withBotDegree_eq [Decidable (f = 0)] : m
.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma withBotDegree_lt_withBotDegree_iff :
    m.withBotDegree f ≺'[m] m.withBotDegree g ↔
      (m.degree f ≺[m] m.degree g ∨ (f = 0 ∧ g ≠ 0)) := by
  classical
  by_cases! hg : g = 0
  · simp_rw [toWithBotSyn_apply]
    aesop
  by_cases! hf : f = 0
  · simp [hg, hf, bot_lt_iff_ne_bot, toWithBotSyn_apply]
  simp [withBotDegree_eq, hf, hg, toWithBotSyn_apply]

variable {f} in
/-
**MonomialOrder.withBotDegree_lt_withBotDegree_iff_of_ne_zero** 是 Mathlib 中的一个引理
，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_lt_withBotDegree_iff_of_ne_zero (hf : f != 0) : m.withBotDeg
ree f ≺'[m] m.withBotDegree g ↔ m.degree f ≺[m] m.degree g
参数：hf : f != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma withBotDegree_lt_withBotDegree_iff_of_ne_zero (hf : f ≠ 0) :
    m.withBotDegree f ≺'[m] m.withBotDegree g ↔ m.degree f ≺[m] m.degree g := by
  simp [withBotDegree_lt_withBotDegree_iff, hf]
/-
**MonomialOrder.withBotDegree_eq_withBotDegree_iff** 是 Mathlib 中的一个引理，位于命名空间 `Mo
nomialOrder`。
形式化陈述：withBotDegree_eq_withBotDegree_iff : m.withBotDegree f = m.withBotDegree g
 ↔ (m.degree f = m.degree g ∧ (f = 0 ↔ g = 0))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.withBotDegree_eq`：withBotDegree_eq [Decidable (f = 0)] : m
.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
lemma withBotDegree_eq_withBotDegree_iff :
    m.withBotDegree f = m.withBotDegree g ↔ (m.degree f = m.degree g ∧ (f = 0 ↔ g = 0)) := by
  classical
  by_cases! +distrib h : f ≠ 0 ∧ g ≠ 0
  · simp [h, m.withBotDegree_eq]
  rcases h with h | h
  all_goals
    simp_rw [h]
    revert f g
    simp [m.withBotDegree_eq, m.degree_zero]
/-
**MonomialOrder.withBotDegree_add_le** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_add_le : (m.toWithBotSyn <| m.withBotDegree (f + g)) <= (m.t
oWithBotSyn <| m.withBotDegree f) ⊔ (m.toWithBotSyn <| m.withBotDegree g)
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `MonomialOrder.degree_add_le`：degree_add_le {f g : MvPolynomial σ R} : m.
toSyn (m.degree (f + g)) <= m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g)
-/
lemma withBotDegree_add_le :
    (m.toWithBotSyn <| m.withBotDegree (f + g)) ≤
      (m.toWithBotSyn <| m.withBotDegree f) ⊔ (m.toWithBotSyn <| m.withBotDegree g) := by
  by_cases! h : f = 0 ∨ g = 0
  · rcases h with h | h <;> simp [h, m.toWithBotSyn_apply]
  simpa [withBotDegree_le_withBotDegree_iff, h] using degree_add_le (R := R)

variable {f g} in
/-
**MonomialOrder.withBotDegree_add_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder
`。
形式化陈述：withBotDegree_add_of_lt (h : m.withBotDegree g ≺'[m] m.withBotDegree f) : 
m.withBotDegree (f + g) = m.withBotDegree f
参数：h : m.withBotDegree g ≺'[m] m.withBotDegree f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `MonomialOrder.degree_add_of_lt`：degree_add_of_lt {f g : MvPolynomial σ R
} (h : m.degree g ≺[m] m.degree f) : m.degree (f + g) = m.degree f
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma withBotDegree_add_of_lt (h : m.withBotDegree g ≺'[m] m.withBotDegree f) :
    m.withBotDegree (f + g) = m.withBotDegree f := by
  by_cases hg : g = 0
  · simp [hg]
  simp only [withBotDegree_lt_withBotDegree_iff, hg, ne_eq, false_and, or_false] at h
  simp only [withBotDegree_eq_withBotDegree_iff, show f ≠ 0 by contrapose h; simp [h], iff_false]
  apply (show ∀ {p q}, p → (p → q) → (p ∧ q) by tauto) (m.degree_add_of_lt h)
  intro h'
  contrapose! h
  simp [← h', h]

variable {f g} in
/-
**MonomialOrder.withBotDegree_add_of_right_lt** 是 Mathlib 中的一个引理，位于命名空间 `Monomia
lOrder`。
形式化陈述：withBotDegree_add_of_right_lt (h : m.withBotDegree f ≺'[m] m.withBotDegree
 g) : m.withBotDegree (f + g) = m.withBotDegree g
参数：h : m.withBotDegree f ≺'[m] m.withBotDegree g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `MonomialOrder.withBotDegree_add_of_lt`：withBotDegree_add_of_lt (h : m.wi
thBotDegree g ≺'[m] m.withBotDegree f) : m.withBotDegree (f + g) = m.withBotDegr
ee f
-/
lemma withBotDegree_add_of_right_lt (h : m.withBotDegree f ≺'[m] m.withBotDegree g) :
    m.withBotDegree (f + g) = m.withBotDegree g := by
  rw [add_comm, withBotDegree_add_of_lt h]
/-
**MonomialOrder.withBotDegree_sum_le** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_sum_le {α : Type*} {s : Finset α} {f : α -> MvPolynomial σ R
} : (m.toWithBotSyn <| m.withBotDegree <| ∑ x in s, f x) <= s.sup fun x => (m.to
WithBotSyn <| m.withBotDegree <| f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `MonomialOrder.withBotDegree_add_le`：withBotDegree_add_le : (m.toWithBotS
yn <| m.withBotDegree (f + g)) <= (m.toWithBotSyn <| m.withBotDegree f) ⊔ (m.toW
ithBotSyn <| m.withBotDe…
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma withBotDegree_sum_le {α : Type*} {s : Finset α} {f : α → MvPolynomial σ R} :
    (m.toWithBotSyn <| m.withBotDegree <| ∑ x ∈ s, f x) ≤
      s.sup fun x ↦ (m.toWithBotSyn <| m.withBotDegree <| f x) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s haA h =>
    rw [Finset.sum_cons, Finset.sup_cons]
    exact le_trans (m.withBotDegree_add_le _ _) (max_le_max le_rfl h)

variable {f} in
/-
**MonomialOrder.le_withBotDegree** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：le_withBotDegree {d : σ ->₀ Nat} (hd : d in f.support) : d ≼'[m] m.withBot
Degree f
参数：hd : d in f.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.withBotDegree_eq`：withBotDegree_eq [Decidable (f = 0)] : m
.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPolynomial.ne_zero_iff`：ne_zero_iff {p : MvPolynomial σ R} : p != 0 ↔ 
exists d, coeff d p != 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MonomialOrder.le_degree`：le_degree {f : MvPolynomial σ R} {d : σ ->₀ Nat
} (hd : d in f.support) : d ≼[m] m.degree f
-/
lemma le_withBotDegree {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    d ≼'[m] m.withBotDegree f := by
  classical
  simp [withBotDegree_eq, toWithBotSyn_apply, ne_zero_iff.mpr ⟨d, by simpa using hd⟩, le_degree hd]

variable {f g} in
/-
**MonomialOrder.withBotDegree_le_withBotDegree_of_support_subset** 是 Mathlib 中的一
个引理，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_le_withBotDegree_of_support_subset (h : f.support subseteq g
.support) : m.withBotDegree f ≼'[m] m.withBotDegree g
参数：h : f.support subseteq g.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.withBotDegree_le_withBotDegree_iff_of_ne_zero`：withBotDegr
ee_le_withBotDegree_iff_of_ne_zero (hg : g != 0) : m.withBotDegree f ≼'[m] m.wit
hBotDegree g ↔ m.degree f ≼[m] m.degree g
· 使用引理 `MonomialOrder.degree_le_degree_of_support_subset`：degree_le_degree_of_su
pport_subset {p q : MvPolynomial σ R} (h : p.support subseteq q.support) : m.deg
ree p ≼[m] m.degree q
-/
lemma withBotDegree_le_withBotDegree_of_support_subset
    (h : f.support ⊆ g.support) :
    m.withBotDegree f ≼'[m] m.withBotDegree g := by
  by_cases hg : g = 0
  · simpa [hg] using h
  rw [m.withBotDegree_le_withBotDegree_iff_of_ne_zero _ hg]
  exact m.degree_le_degree_of_support_subset h

end withBotDegree

end Semiring

section Ring

variable {R : Type*} [CommRing R]

variable (m) in
/-- The S-polynomial of two polynomials.

Denoting

- the leading monomial of polynomial $f$ and $g$ as $lm(f)$ and $lm(g)$,
- the leading coefficient of $f$ and $g$ as $lc(f)$ and $lc(g)$
  (formalized as `m.leadingCoeff f` and `m.leadingCoeff g`), and
- the least common multiple of $lm(f)$ and $lm(g)$ as $lcm(lm(f),lm(g))$,

the S-polynomial of $f$ and $g$ is defined as
$$sPoly(f,g) := (lcm(lm(f),lm(g)) / lm(f)) * lc(g) * f - (lcm(lm(f),lm(g)) / lm(g)) * lc(f) * g.$$

$(lcm(lm(f),lm(g)) / lm(f))$ and $lcm(lm(f),lm(g)) / lm(g)$ is formalized as
`monomial (m.degree g - m.degree f) 1` and `monomial (m.degree g - m.degree f) 1`, while there is
also another more direct formalization in `sPolynomial_def`.

Notice that, when the polynomial ring is over a field, S-polynomial is usually defined as
$$sPoly'(f,g) :=
  (lcm(lm(f),lm(g)) / (lm(f) * lc(f))) * f - (lcm(lm(f),lm(g)) / (lm(g) * lc(g))) * g,$$
while we avoid inverting $lc(f)$ and $lc(g)$ in this formalization so that it doesn't require a
field or units (`IsUnit`) over ring.

An equality between these two versions holds: $$sPoly(f,g) = lc(f) * lc(g) * sPoly'(f,g).$$
-/
/-
**MonomialOrder.sPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `MonomialOrder`。
形式化陈述：sPolynomial (f g : MvPolynomial σ R) : MvPolynomial σ R
参数：f g : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The S-polynomial of two polynomials.

Denoting

- the leading monomial of polynomial $f$ and $g$ as $lm(f)$ and $lm(g)$,
- the leading coefficient of $f$ and $g$ as $lc(f)$ and $lc(g)$
  (formalized as `m.leadingCoeff f` and `m.leadingCoeff g`), and
- the least common multiple of $lm(f)$ and $lm(g)$ as $lcm(lm(f),lm(g))$,

the S-polynomial of $f$ and $g$ is defined as
$$sPoly(f,g) := (lcm(lm(f),lm(g)) / lm(f)) * lc(g) * f - (lcm(lm(f),lm(g)) / lm(
g)) * lc(f) * g.$$

$(lcm(lm(f),lm(g)) / lm(f))$ and $lcm(lm(f),lm(g)) / lm(g)$ is formalized as
`monomial (m.degree g - m.degree f) 1` and `monomial (m.degree g - m.degree f) 1
`, while there is
also another more direct formalization in `sPolynomial_def`.

Notice that, when the polynomial ring is over a field, S-polynomial is usually d
efined as
$$sPoly'(f,g) :=
  (lcm(lm(f),lm(g)) / (lm(f) * lc(f))) * f - (lcm(lm(f),lm(g)) / (lm(g) * lc(g))
) * g,$$
while we avoid inverting $lc(f)$ and $lc(g)$ in this formalization so that it do
esn't require a
field or units (`IsUnit`) over ring.

An equality between these two versions holds: $$sPoly(f,g) = lc(f) * lc(g) * sPo
ly'(f,g).$$
-/
noncomputable def sPolynomial (f g : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree g - m.degree f) (m.leadingCoeff g) * f -
  monomial (m.degree f - m.degree g) (m.leadingCoeff f) * g
/-
**MonomialOrder.sPolynomial_def** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：sPolynomial_def (f g : MvPolynomial σ R) : m.sPolynomial f g = monomial (m
.degree f ⊔ m.degree g - m.degree f) (m.leadingCoeff g) * f - monomial (m.degree
 f ⊔ m.degree g - m.degree g) (m.leadingCoeff f) * g
参数：f g : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `MonomialOrder.sPolynomial.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) {
R : Type u_2} [inst : CommRing R] (f g : MvPolynomial σ R),   m.sPolynomial f g 
=     (MvPolynomial.…
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
lemma sPolynomial_def (f g : MvPolynomial σ R) :
    m.sPolynomial f g =
      monomial (m.degree f ⊔ m.degree g - m.degree f) (m.leadingCoeff g) * f -
      monomial (m.degree f ⊔ m.degree g - m.degree g) (m.leadingCoeff f) * g := by
  suffices ∀ f g, m.degree g - m.degree f = m.degree f ⊔ m.degree g - m.degree f by
    rw [sPolynomial, this, this, sup_comm]
  intro f g
  ext a
  obtain (h | h) := le_total (m.degree f a) (m.degree g a) <;> simp [h]
/-
**MonomialOrder.degree_ne_zero_of_sub_leadingTerm_ne_zero** 是 Mathlib 中的一个引理，位于命
名空间 `MonomialOrder`。
形式化陈述：degree_ne_zero_of_sub_leadingTerm_ne_zero {f : MvPolynomial σ R} (h : f - 
m.leadingTerm f != 0) : m.degree f != 0
参数：h : f - m.leadingTerm f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonomialOrder.degree_eq_zero_iff`：degree_eq_zero_iff {f : MvPolynomial σ
 R} : m.degree f = 0 ↔ f = C (m.leadingCoeff f)
· 使用引理 `MonomialOrder.leadingTerm_C`：leadingTerm_C (c : R) : m.leadingTerm (C c)
 = C c
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
-/
lemma degree_ne_zero_of_sub_leadingTerm_ne_zero {f : MvPolynomial σ R}
    (h : f - m.leadingTerm f ≠ 0) : m.degree f ≠ 0 := by
  contrapose h
  rw [m.degree_eq_zero_iff.mp h, leadingTerm_C, sub_eq_zero]

@[simp]
/-
**MonomialOrder.degree_neg** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_neg {f : MvPolynomial σ R} : m.degree (-f) = m.degree f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.support_neg`：∀ {R : Type u} (σ : Type u_1) [inst : CommRing
 R] {p : MvPolynomial σ R}, (-p).support = p.support
-/
theorem degree_neg {f : MvPolynomial σ R} :
    m.degree (-f) = m.degree f := by
  unfold degree
  rw [support_neg]

@[simp]
/-
**MonomialOrder.leadingCoeff_neg** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：leadingCoeff_neg {f : MvPolynomial σ R} : m.leadingCoeff (-f) = - m.leadin
gCoeff f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_neg`：degree_neg {f : MvPolynomial σ R} : m.degree (
-f) = m.degree f
· 使用定理 `MvPolynomial.coeff_neg`：coeff_neg (m : σ ->₀ Nat) (p : MvPolynomial σ R)
 : coeff m (-p) = -coeff m p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_neg {f : MvPolynomial σ R} :
    m.leadingCoeff (-f) = - m.leadingCoeff f := by
  simp only [leadingCoeff, degree_neg, coeff_neg]
/-
**MonomialOrder.degree_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_sub_le {f g : MvPolynomial σ R} : m.toSyn (m.degree (f - g)) <= m.t
oSyn (m.degree f) ⊔ m.toSyn (m.degree g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MonomialOrder.degree_add_le`：degree_add_le {f g : MvPolynomial σ R} : m.
toSyn (m.degree (f + g)) <= m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g)
· 使用定理 `MonomialOrder.degree_neg`：degree_neg {f : MvPolynomial σ R} : m.degree (
-f) = m.degree f
-/
theorem degree_sub_le {f g : MvPolynomial σ R} :
    m.toSyn (m.degree (f - g)) ≤ m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  rw [sub_eq_add_neg]
  apply le_of_le_of_eq m.degree_add_le
  rw [degree_neg]
/-
**MonomialOrder.degree_sub_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_sub_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f)
 : m.degree (f - g) = m.degree f
参数：h : m.degree g ≺[m] m.degree f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MonomialOrder.degree_add_of_lt`：degree_add_of_lt {f g : MvPolynomial σ R
} (h : m.degree g ≺[m] m.degree f) : m.degree (f + g) = m.degree f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_neg`：degree_neg {f : MvPolynomial σ R} : m.degree (
-f) = m.degree f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem degree_sub_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.degree (f - g) = m.degree f := by
  rw [sub_eq_add_neg]
  apply degree_add_of_lt
  simp only [degree_neg, h]
/-
**MonomialOrder.leadingCoeff_sub_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`
。
形式化陈述：leadingCoeff_sub_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.deg
ree f) : m.leadingCoeff (f - g) = m.leadingCoeff f
参数：h : m.degree g ≺[m] m.degree f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MonomialOrder.leadingCoeff_add_of_lt`：leadingCoeff_add_of_lt {f g : MvPo
lynomial σ R} (h : m.degree g ≺[m] m.degree f) : m.leadingCoeff (f + g) = m.lead
ingCoeff f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_neg`：degree_neg {f : MvPolynomial σ R} : m.degree (
-f) = m.degree f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem leadingCoeff_sub_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.leadingCoeff (f - g) = m.leadingCoeff f := by
  rw [sub_eq_add_neg]
  apply leadingCoeff_add_of_lt
  simp only [degree_neg, h]
/-
**MonomialOrder.degree_sub_leadingTerm_le** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrd
er`。
形式化陈述：degree_sub_leadingTerm_le (f : MvPolynomial σ R) : m.degree (f - m.leading
Term f) ≼[m] m.degree f
参数：f : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MonomialOrder.degree_sub_le`：degree_sub_le {f g : MvPolynomial σ R} : m.
toSyn (m.degree (f - g)) <= m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.degree_leadingTerm`：degree_leadingTerm (f : MvPolynomial σ
 R) : m.degree (m.leadingTerm f) = m.degree f
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
-/
theorem degree_sub_leadingTerm_le (f : MvPolynomial σ R) :
    m.degree (f - m.leadingTerm f) ≼[m] m.degree f := by
  apply le_trans degree_sub_le
  simp [degree_leadingTerm]
/-
**MonomialOrder.degree_sub_leadingTerm_lt_degree** 是 Mathlib 中的一个定理，位于命名空间 `Mono
mialOrder`。
形式化陈述：degree_sub_leadingTerm_lt_degree {f : MvPolynomial σ R} (h : m.degree f !=
 0) : m.degree (f - m.leadingTerm f) ≺[m] m.degree f
参数：h : m.degree f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `MonomialOrder.degree_sub_leadingTerm_le`：degree_sub_leadingTerm_le (f : 
MvPolynomial σ R) : m.degree (f - m.leadingTerm f) ≼[m] m.degree f
· 使用定理 `MvPolynomial.coeff_sub`：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p - q) = coeff m p - coeff m q
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用引理 `MonomialOrder.degree_mem_support`：degree_mem_support {p : MvPolynomial σ
 R} (hp : p != 0) : m.degree p in p.support
-/
theorem degree_sub_leadingTerm_lt_degree {f : MvPolynomial σ R} (h : m.degree f ≠ 0) :
    m.degree (f - m.leadingTerm f) ≺[m] m.degree f := by
  classical
  by_cases hl : f - m.leadingTerm f = 0
  · simpa [hl, toSyn_lt_iff_ne_zero]
  · apply lt_of_le_of_ne (m.degree_sub_leadingTerm_le f)
    by_contra! h'
    simp only [EmbeddingLike.apply_eq_iff_eq] at h'
    apply m.degree_mem_support at hl
    rw [h', mem_support_iff] at hl
    simp [leadingTerm, leadingCoeff] at hl
/-
**MonomialOrder.degree_sub_leadingTerm_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Monomia
lOrder`。
形式化陈述：degree_sub_leadingTerm_lt_iff {f : MvPolynomial σ R} : m.degree (f - m.lea
dingTerm f) ≺[m] m.degree f ↔ m.degree f != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `MonomialOrder.degree_sub_leadingTerm_lt_degree`：degree_sub_leadingTerm_l
t_degree {f : MvPolynomial σ R} (h : m.degree f != 0) : m.degree (f - m.leadingT
erm f) ≺[m] m.degree f
-/
theorem degree_sub_leadingTerm_lt_iff {f : MvPolynomial σ R} :
    m.degree (f - m.leadingTerm f) ≺[m] m.degree f ↔ m.degree f ≠ 0 := by
  refine ⟨?_, degree_sub_leadingTerm_lt_degree⟩
  intro h h'
  simp only [h', map_zero] at h
  exact not_lt_bot h
/-
**MonomialOrder.sPolynomial_antisymm** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：sPolynomial_antisymm (f g : MvPolynomial σ R) : m.sPolynomial f g = - m.sP
olynomial g f
参数：f g : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
lemma sPolynomial_antisymm (f g : MvPolynomial σ R) :
    m.sPolynomial f g = - m.sPolynomial g f :=
  (neg_sub (_ * g) (_ * f)).symm

@[simp]
/-
**MonomialOrder.sPolynomial_left_zero** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：sPolynomial_left_zero (g : MvPolynomial σ R) : m.sPolynomial 0 g = 0
参数：g : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MonomialOrder.leadingCoeff_zero`：leadingCoeff_zero : m.leadingCoeff (0 :
 MvPolynomial σ R) = 0
· 使用定理 `MvPolynomial.monomial_zero`：monomial_zero {s : σ ->₀ Nat} : monomial s (
0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sPolynomial_left_zero (g : MvPolynomial σ R) :
    m.sPolynomial 0 g = 0 := by
  simp [sPolynomial]

@[simp]
/-
**MonomialOrder.sPolynomial_right_zero** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`
。
形式化陈述：sPolynomial_right_zero (f : MvPolynomial σ R) : m.sPolynomial f 0 = 0
参数：f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.sPolynomial_antisymm`：sPolynomial_antisymm (f g : MvPolyno
mial σ R) : m.sPolynomial f g = - m.sPolynomial g f
· 使用引理 `MonomialOrder.sPolynomial_left_zero`：sPolynomial_left_zero (g : MvPolyno
mial σ R) : m.sPolynomial 0 g = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
lemma sPolynomial_right_zero (f : MvPolynomial σ R) :
    m.sPolynomial f 0 = 0 := by
  rw [sPolynomial_antisymm, sPolynomial_left_zero, neg_zero]

@[simp]
/-
**MonomialOrder.sPolynomial_self** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：sPolynomial_self (f : MvPolynomial σ R) : m.sPolynomial f f = 0
参数：f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma sPolynomial_self (f : MvPolynomial σ R) : m.sPolynomial f f = 0 := sub_self _
/-
**MonomialOrder.degree_sPolynomial_le** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_sPolynomial_le (f g : MvPolynomial σ R) : ((m.degree <| m.sPolynomi
al f g) ≼[m] m.degree f ⊔ m.degree g)
参数：f g : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.sPolynomial_def`：sPolynomial_def (f g : MvPolynomial σ R) 
: m.sPolynomial f g = monomial (m.degree f ⊔ m.degree g - m.degree f) (m.leading
Coeff g) * f - mono…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MonomialOrder.degree_sub_le`：degree_sub_le {f g : MvPolynomial σ R} : m.
toSyn (m.degree (f - g)) <= m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g)
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `MonomialOrder.degree_mul_le`：degree_mul_le {f g : MvPolynomial σ R} : m.
degree (f * g) ≼[m] m.degree f + m.degree g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonomialOrder.degree_monomial`：degree_monomial {d : σ ->₀ Nat} (c : R) [
Decidable (c = 0)] : m.degree (monomial d c) = if c = 0 then 0 else d
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用引理 `MonomialOrder.sPolynomial_left_zero`：sPolynomial_left_zero (g : MvPolyno
mial σ R) : m.sPolynomial 0 g = 0
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
（共 34 条，此处仅展示前 30 条）
-/
lemma degree_sPolynomial_le (f g : MvPolynomial σ R) :
    ((m.degree <| m.sPolynomial f g) ≼[m] m.degree f ⊔ m.degree g) := by
  classical
  wlog! +distrib h0 : f ≠ 0 ∧ g ≠ 0
  · (obtain rfl | rfl := h0) <;> simp
  simp only [sPolynomial_def]
  apply degree_sub_le.trans
  apply (sup_le_sup degree_mul_le degree_mul_le).trans
  simp [degree_monomial, h0.1, h0.2, tsub_add_cancel_of_le, le_sup_left, le_sup_right]
/-
**MonomialOrder.coeff_sPolynomial_sup_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Monomia
lOrder`。
形式化陈述：coeff_sPolynomial_sup_eq_zero (f g : MvPolynomial σ R) : (m.sPolynomial f 
g).coeff (m.degree f ⊔ m.degree g) = 0
参数：f g : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.sPolynomial_def`：sPolynomial_def (f g : MvPolynomial σ R) 
: m.sPolynomial f g = monomial (m.degree f ⊔ m.degree g - m.degree f) (m.leading
Coeff g) * f - mono…
· 使用定理 `MvPolynomial.coeff_sub`：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p - q) = coeff m p - coeff m q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `MvPolynomial.coeff_monomial_mul`：coeff_monomial_mul (m) (s : σ ->₀ Nat) 
(r : R) (p : MvPolynomial σ R) : coeff (s + m) (monomial s r * p) = r * coeff m 
p
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 41 条，此处仅展示前 30 条）
-/
lemma coeff_sPolynomial_sup_eq_zero (f g : MvPolynomial σ R) :
    (m.sPolynomial f g).coeff (m.degree f ⊔ m.degree g) = 0 := by
  rw [sPolynomial_def, coeff_sub]
  nth_rewrite 1 [← tsub_add_cancel_of_le le_sup_left, coeff_monomial_mul]
  nth_rewrite 1 [← tsub_add_cancel_of_le le_sup_right, coeff_monomial_mul]
  unfold leadingCoeff
  ring
/-
**MonomialOrder.degree_sPolynomial** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_sPolynomial (f g : MvPolynomial σ R) : (m.degree <| m.sPolynomial f
 g) ≺[m] m.degree f ⊔ m.degree g ∨ m.sPolynomial f g = 0
参数：f g : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonomialOrder.degree_eq_zero_iff`：degree_eq_zero_iff {f : MvPolynomial σ
 R} : m.degree f = 0 ↔ f = C (m.leadingCoeff f)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 52 条，此处仅展示前 30 条）
-/
lemma degree_sPolynomial (f g : MvPolynomial σ R) :
    (m.degree <| m.sPolynomial f g) ≺[m] m.degree f ⊔ m.degree g ∨ m.sPolynomial f g = 0 := by
  by_cases hf : m.degree f = 0 ∧ m.degree g = 0
  · rcases hf with ⟨h₁, h₂⟩
    right
    suffices C (m.leadingCoeff g) * f - C (m.leadingCoeff f) * g = 0 by simp_all [sPolynomial_def]
    nth_rewrite 1 [degree_eq_zero_iff.mp h₁]
    nth_rewrite 2 [degree_eq_zero_iff.mp h₂]
    ring
  · rw [or_iff_not_imp_right]
    intro hs
    apply (m.degree_sPolynomial_le f g).lt_of_ne
    apply m.toSyn.injective.ne
    contrapose hs
    rw [← m.coeff_degree_eq_zero_iff, hs, m.coeff_sPolynomial_sup_eq_zero]
/-
**MonomialOrder.degree_sPolynomial_lt_sup_degree** 是 Mathlib 中的一个引理，位于命名空间 `Mono
mialOrder`。
形式化陈述：degree_sPolynomial_lt_sup_degree {f g : MvPolynomial σ R} (h : m.sPolynomi
al f g != 0) : (m.degree <| m.sPolynomial f g) ≺[m] m.degree f ⊔ m.degree g
参数：h : m.sPolynomial f g != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用引理 `MonomialOrder.degree_sPolynomial`：degree_sPolynomial (f g : MvPolynomial
 σ R) : (m.degree <| m.sPolynomial f g) ≺[m] m.degree f ⊔ m.degree g ∨ m.sPolyno
mial f g = 0
-/
lemma degree_sPolynomial_lt_sup_degree {f g : MvPolynomial σ R} (h : m.sPolynomial f g ≠ 0) :
    (m.degree <| m.sPolynomial f g) ≺[m] m.degree f ⊔ m.degree g :=
  (or_iff_left h).mp <| m.degree_sPolynomial f g
/-
**MonomialOrder.sPolynomial_lt_of_degree_ne_zero_of_degree_eq** 是 Mathlib 中的一个引理
，位于命名空间 `MonomialOrder`。
形式化陈述：sPolynomial_lt_of_degree_ne_zero_of_degree_eq {f g : MvPolynomial σ R} (h 
: m.degree f = m.degree g) (hs : m.sPolynomial f g != 0) : m.degree (m.sPolynomi
al f g) ≺[m] m.degree f
参数：h : m.degree f = m.degree g；hs : m.sPolynomial f g != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `MonomialOrder.degree_sPolynomial_lt_sup_degree`：degree_sPolynomial_lt_su
p_degree {f g : MvPolynomial σ R} (h : m.sPolynomial f g != 0) : (m.degree <| m.
sPolynomial f g) ≺[m] m.degree f ⊔ m…
-/
lemma sPolynomial_lt_of_degree_ne_zero_of_degree_eq {f g : MvPolynomial σ R}
    (h : m.degree f = m.degree g) (hs : m.sPolynomial f g ≠ 0) :
    m.degree (m.sPolynomial f g) ≺[m] m.degree f := by
  simpa [h] using m.degree_sPolynomial_lt_sup_degree hs
/-
**MonomialOrder.sPolynomial_monomial_mul** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrde
r`。
形式化陈述：sPolynomial_monomial_mul [NoZeroDivisors R] (p₁ p₂ : MvPolynomial σ R) (d₁
 d₂ : σ ->₀ Nat) (c₁ c₂ : R) : m.sPolynomial ((monomial d₁ c₁) * p₁) ((monomial 
d₂ c₂) * p₂) = monomial ((d₁ + m.degree p₁) ⊔ (d₂ + m.degree p₂) - m.degree p₁ ⊔
 m.degree p₂) (c₁ * c₂) * m.sPolynomial p₁ p₂
参数：p₁ p₂ : MvPolynomial σ R；d₁ d₂ : σ ->₀ Nat；c₁ c₂ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.sPolynomial_def`：sPolynomial_def (f g : MvPolynomial σ R) 
: m.sPolynomial f g = monomial (m.degree f ⊔ m.degree g - m.degree f) (m.leading
Coeff g) * f - mono…
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MvPolynomial.monomial_eq_zero`：monomial_eq_zero {s : σ ->₀ Nat} {b : R} 
: monomial s b = 0 ↔ b = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_mul`：degree_mul [NoZeroDivisors R] {f g : MvPolynom
ial σ R} (hf : f != 0) (hg : g != 0) : m.degree (f * g) = m.degree f + m.degree 
g
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MvPolynomial.monomial_mul`：monomial_mul {s s' : σ ->₀ Nat} {a b : R} : m
onomial s a * monomial s' b = monomial (s + s') (a * b)
· 使用定理 `MonomialOrder.leadingCoeff_mul`：∀ {σ : Type u_1} {m : MonomialOrder σ} {
R : Type u_2} [inst : CommSemiring R] [NoZeroDivisors R]   {f g : MvPolynomial σ
 R}, m.leadingCoeff …
· 使用定理 `MonomialOrder.leadingCoeff_monomial`：leadingCoeff_monomial {d : σ ->₀ Na
t} (c : R) : m.leadingCoeff (monomial d c) = c
· 使用定理 `MonomialOrder.degree_monomial`：degree_monomial {d : σ ->₀ Nat} (c : R) [
Decidable (c = 0)] : m.degree (monomial d c) = if c = 0 then 0 else d
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `tsub_add_tsub_cancel`：tsub_add_tsub_cancel (hab : b <= a) (hcb : c <= b)
 : a - b + (b - c) = a - c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `tsub_add_eq_add_tsub`：tsub_add_eq_add_tsub (h : b <= a) : a - b + c = a 
+ c - b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 52 条，此处仅展示前 30 条）
-/
lemma sPolynomial_monomial_mul [NoZeroDivisors R] (p₁ p₂ : MvPolynomial σ R) (d₁ d₂ : σ →₀ ℕ)
    (c₁ c₂ : R) :
    m.sPolynomial ((monomial d₁ c₁) * p₁) ((monomial d₂ c₂) * p₂) =
      monomial ((d₁ + m.degree p₁) ⊔ (d₂ + m.degree p₂) - m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) *
      m.sPolynomial p₁ p₂ := by
  classical
  simp only [sPolynomial_def]
  wlog! +distrib H : c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ p₁ ≠ 0 ∧ p₂ ≠ 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  rcases H with ⟨hc1, hc2, hp1, hp2⟩
  have hm1 := (monomial_eq_zero (s := d₁)).not.mpr hc1
  have hm2 := (monomial_eq_zero (s := d₂)).not.mpr hc2
  simp_rw [m.degree_mul hm1 hp1, m.degree_mul hm2 hp2,
    mul_sub, ← mul_assoc _ _ p₁, ← mul_assoc _ _ p₂, monomial_mul,
    m.leadingCoeff_mul, m.leadingCoeff_monomial,
    degree_monomial, hc1, hc2, reduceIte, mul_right_comm, mul_comm c₂ c₁]
  rw [tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp),
    tsub_add_tsub_cancel (sup_le_sup (self_le_add_left _ _) (self_le_add_left _ _)) (by simp),
    tsub_add_eq_add_tsub le_sup_left, tsub_add_eq_add_tsub le_sup_right,
    add_comm d₁, add_comm d₂, add_tsub_add_eq_tsub_right, add_tsub_add_eq_tsub_right]
/-
**MonomialOrder.sPolynomial_monomial_mul'** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrd
er`。
形式化陈述：sPolynomial_monomial_mul' [NoZeroDivisors R] (p₁ p₂ : MvPolynomial σ R) (d
₁ d₂ : σ ->₀ Nat) (c₁ c₂ : R) : m.sPolynomial (monomial d₁ c₁ * p₁) (monomial d₂
 c₂ * p₂) = monomial (m.degree (monomial d₁ c₁ * p₁) ⊔ m.degree (monomial d₂ c₂ 
* p₂) - m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) * m.sPolynomial p₁ p₂
参数：p₁ p₂ : MvPolynomial σ R；d₁ d₂ : σ ->₀ Nat；c₁ c₂ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.sPolynomial_monomial_mul`：sPolynomial_monomial_mul [NoZero
Divisors R] (p₁ p₂ : MvPolynomial σ R) (d₁ d₂ : σ ->₀ Nat) (c₁ c₂ : R) : m.sPoly
nomial ((monomial d₁ c₁) * p…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_mul`：degree_mul [NoZeroDivisors R] {f g : MvPolynom
ial σ R} (hf : f != 0) (hg : g != 0) : m.degree (f * g) = m.degree f + m.degree 
g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MonomialOrder.degree_monomial`：degree_monomial {d : σ ->₀ Nat} (c : R) [
Decidable (c = 0)] : m.degree (monomial d c) = if c = 0 then 0 else d
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `MvPolynomial.monomial_zero`：monomial_zero {s : σ ->₀ Nat} : monomial s (
0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `MonomialOrder.sPolynomial_left_zero`：sPolynomial_left_zero (g : MvPolyno
mial σ R) : m.sPolynomial 0 g = 0
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonomialOrder.sPolynomial_right_zero`：sPolynomial_right_zero (f : MvPoly
nomial σ R) : m.sPolynomial f 0 = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma sPolynomial_monomial_mul' [NoZeroDivisors R] (p₁ p₂ : MvPolynomial σ R) (d₁ d₂ : σ →₀ ℕ)
    (c₁ c₂ : R) :
    m.sPolynomial (monomial d₁ c₁ * p₁) (monomial d₂ c₂ * p₂) =
      monomial (m.degree (monomial d₁ c₁ * p₁) ⊔ m.degree (monomial d₂ c₂ * p₂) -
          m.degree p₁ ⊔ m.degree p₂) (c₁ * c₂) *
      m.sPolynomial p₁ p₂ := by
  classical
  wlog! +distrib H : c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ p₁ ≠ 0 ∧ p₂ ≠ 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  simp [H, degree_mul, sPolynomial_monomial_mul, degree_monomial]
/-
**MonomialOrder.sPolynomial_leadingTerm_mul** 是 Mathlib 中的一个引理，位于命名空间 `MonomialO
rder`。
形式化陈述：sPolynomial_leadingTerm_mul [NoZeroDivisors R] (p₁ p₂ q₁ q₂ : MvPolynomial
 σ R) : m.sPolynomial (m.leadingTerm p₁ * q₁) (m.leadingTerm p₂ * q₂) = monomial
 ((m.degree p₁ + m.degree q₁) ⊔ (m.degree p₂ + m.degree q₂) - m.degree q₁ ⊔ m.de
gree q₂) (m.leadingCoeff p₁ * m.leadingCoeff p₂) * m.sPolynomial q₁ q₂
参数：p₁ p₂ q₁ q₂ : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.sPolynomial_monomial_mul`：sPolynomial_monomial_mul [NoZero
Divisors R] (p₁ p₂ : MvPolynomial σ R) (d₁ d₂ : σ ->₀ Nat) (c₁ c₂ : R) : m.sPoly
nomial ((monomial d₁ c₁) * p…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sPolynomial_leadingTerm_mul [NoZeroDivisors R] (p₁ p₂ q₁ q₂ : MvPolynomial σ R) :
    m.sPolynomial (m.leadingTerm p₁ * q₁) (m.leadingTerm p₂ * q₂) =
    monomial
        ((m.degree p₁ + m.degree q₁) ⊔ (m.degree p₂ + m.degree q₂) - m.degree q₁ ⊔ m.degree q₂)
        (m.leadingCoeff p₁ * m.leadingCoeff p₂) *
      m.sPolynomial q₁ q₂ := by
  simp [sPolynomial_monomial_mul, leadingTerm]
/-
**MonomialOrder.sPolynomial_leadingTerm_mul'** 是 Mathlib 中的一个引理，位于命名空间 `Monomial
Order`。
形式化陈述：sPolynomial_leadingTerm_mul' [NoZeroDivisors R] (p₁ p₂ q₁ q₂ : MvPolynomia
l σ R) : m.sPolynomial (m.leadingTerm p₁ * q₁) (m.leadingTerm p₂ * q₂) = monomia
l ((m.degree (p₁ * q₁)) ⊔ (m.degree (p₂ * q₂)) - m.degree q₁ ⊔ m.degree q₂) (m.l
eadingCoeff p₁ * m.leadingCoeff p₂) * m.sPolynomial q₁ q₂
参数：p₁ p₂ q₁ q₂ : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.sPolynomial_monomial_mul`：sPolynomial_monomial_mul [NoZero
Divisors R] (p₁ p₂ : MvPolynomial σ R) (d₁ d₂ : σ ->₀ Nat) (c₁ c₂ : R) : m.sPoly
nomial ((monomial d₁ c₁) * p…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_mul`：degree_mul [NoZeroDivisors R] {f g : MvPolynom
ial σ R} (hf : f != 0) (hg : g != 0) : m.degree (f * g) = m.degree f + m.degree 
g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用引理 `MonomialOrder.leadingTerm_zero`：leadingTerm_zero : m.leadingTerm (0 : Mv
Polynomial σ R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `MonomialOrder.sPolynomial_left_zero`：sPolynomial_left_zero (g : MvPolyno
mial σ R) : m.sPolynomial 0 g = 0
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `MonomialOrder.leadingCoeff_zero`：leadingCoeff_zero : m.leadingCoeff (0 :
 MvPolynomial σ R) = 0
· 使用定理 `MvPolynomial.monomial_zero`：monomial_zero {s : σ ->₀ Nat} : monomial s (
0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonomialOrder.sPolynomial_right_zero`：sPolynomial_right_zero (f : MvPoly
nomial σ R) : m.sPolynomial f 0 = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma sPolynomial_leadingTerm_mul' [NoZeroDivisors R] (p₁ p₂ q₁ q₂ : MvPolynomial σ R) :
    m.sPolynomial (m.leadingTerm p₁ * q₁) (m.leadingTerm p₂ * q₂) =
    monomial
        ((m.degree (p₁ * q₁)) ⊔ (m.degree (p₂ * q₂)) - m.degree q₁ ⊔ m.degree q₂)
        (m.leadingCoeff p₁ * m.leadingCoeff p₂) *
      m.sPolynomial q₁ q₂ := by
  wlog! +distrib H : p₁ ≠ 0 ∧ p₂ ≠ 0 ∧ q₁ ≠ 0 ∧ q₂ ≠ 0
  · (obtain rfl | rfl | rfl | rfl := H) <;> simp
  simp [H, leadingTerm, sPolynomial_monomial_mul, degree_mul]
/-
**MonomialOrder.sPolynomial_decomposition** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrd
er`。
形式化陈述：sPolynomial_decomposition {d : m.syn} {ι : Type*} {B : Finset ι} {g : ι ->
 MvPolynomial σ R} (hd : forall b in B, (m.toSyn <| m.degree <| g b) = d ∧ IsUni
t (m.leadingCoeff <| g b) ∨ g b = 0) (hfd : (m.toSyn <| m.degree <| ∑ b in B, g 
b) < d) : exists (c : ι -> ι -> R), ∑ b in B, g b = ∑ b₁ in B, ∑ b₂ in B, (c b₁ 
b₂) • m.sPolynomial (g b₁) (g b₂)
参数：hd : forall b in B, (m.toSyn <| m.degree <| g b) = d ∧ IsUnit (m.leadingCoeff
 <| g b) ∨ g b = 0；hfd : (m.toSyn <| m.degree <| ∑ b in B, g b) < d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `MonomialOrder.sPolynomial_right_zero`：sPolynomial_right_zero (f : MvPoly
nomial σ R) : m.sPolynomial f 0 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `MonomialOrder.sPolynomial_left_zero`：sPolynomial_left_zero (g : MvPolyno
mial σ R) : m.sPolynomial 0 g = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
（共 67 条，此处仅展示前 30 条）
-/
lemma sPolynomial_decomposition {d : m.syn} {ι : Type*}
    {B : Finset ι} {g : ι → MvPolynomial σ R}
    (hd : ∀ b ∈ B,
      (m.toSyn <| m.degree <| g b) = d ∧ IsUnit (m.leadingCoeff <| g b) ∨ g b = 0)
    (hfd : (m.toSyn <| m.degree <| ∑ b ∈ B, g b) < d) :
    ∃ (c : ι → ι → R),
      ∑ b ∈ B, g b = ∑ b₁ ∈ B, ∑ b₂ ∈ B, (c b₁ b₂) • m.sPolynomial (g b₁) (g b₂) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb h =>
    by_cases hb0 : g b = 0
    · simp_all
    simp? [Finset.sum_insert hb, hb0] at hfd hd says
      simp only [Finset.sum_insert hb, Finset.mem_insert, forall_eq_or_imp, hb0, or_false]
        at hfd hd
    obtain ⟨⟨rfl, isunit_gb⟩, hd⟩ := hd
    use fun b₁ b₂ ↦ if b₂ = b then ↑isunit_gb.unit⁻¹ else 0
    simp? [Finset.sum_insert hb, hb] says
      simp only [Finset.sum_insert hb, ite_smul, zero_smul, ↓reduceIte, Finset.sum_ite_eq', hb,
        add_zero, sPolynomial_self, smul_zero, zero_add]
    simp only [m.toSyn.injective.eq_iff] at *
    trans ∑ b' ∈ B, (g b' - (m.leadingCoeff (g b') * ↑isunit_gb.unit⁻¹) • g b)
    · suffices (-(∑ i ∈ B, m.leadingCoeff (g i))) = m.leadingCoeff (g b) by
        rw [add_comm, Finset.sum_sub_distrib, sub_eq_add_neg, ← Finset.sum_smul, ← Finset.sum_mul,
          ← neg_smul, ← neg_mul, this, isunit_gb.mul_val_inv, one_smul]
      rw [← add_eq_zero_iff_neg_eq']
      trans (g b).coeff (m.degree <| g b) + ∑ i ∈ B, (g i).coeff (m.degree <| g b)
      · unfold leadingCoeff
        congr 1
        apply Finset.sum_congr rfl
        intro b' hb'
        rcases hd b' hb' with h | h <;> simp [h]
      · rw [← coeff_sum, ← coeff_add, ← notMem_support_iff]
        exact m.notMem_support_of_degree_lt hfd
    · apply Finset.sum_congr rfl
      intro b' hb'
      rw [sPolynomial]
      obtain (⟨h, -⟩ | h) := hd b' hb' <;>
        simp [h, ← smul_eq_C_mul, smul_sub, ← mul_smul, mul_comm (m.leadingCoeff (g b'))]

@[simp]
/-
**MonomialOrder.withBotDegree_neg** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：withBotDegree_neg (f : MvPolynomial σ R) : m.withBotDegree (-f) = m.withBo
tDegree f
参数：f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonomialOrder.withBotDegree_eq`：withBotDegree_eq [Decidable (f = 0)] : m
.withBotDegree f = if f = 0 then ⊥ else ↑(m.degree f)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MonomialOrder.degree_neg`：degree_neg {f : MvPolynomial σ R} : m.degree (
-f) = m.degree f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma withBotDegree_neg (f : MvPolynomial σ R) :
    m.withBotDegree (-f) = m.withBotDegree f := by
  classical
  simp [m.withBotDegree_eq]

end Ring

section Field

variable {R : Type*} [Field R]

/-
**MonomialOrder.isUnit_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：isUnit_leadingCoeff {f : MvPolynomial σ R} : IsUnit (m.leadingCoeff f) ↔ f
 != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUnit_leadingCoeff {f : MvPolynomial σ R} :
    IsUnit (m.leadingCoeff f) ↔ f ≠ 0 := by
  simp only [isUnit_iff_ne_zero, ne_eq, leadingCoeff_eq_zero_iff]
/-
**MonomialOrder.sPolynomial_decomposition'** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOr
der`。
形式化陈述：sPolynomial_decomposition' {d : m.syn} {ι : Type*} {B : Finset ι} (g : ι -
> MvPolynomial σ R) (hd : forall b in B, (m.toSyn <| m.degree <| g b) = d ∨ g b 
= 0) (hfd : (m.toSyn <| m.degree <| ∑ b in B, g b) < d) : exists (c : ι -> ι -> 
R), ∑ b in B, g b = ∑ b₁ in B, ∑ b₂ in B, (c b₁ b₂) • m.sPolynomial (g b₁) (g b₂
)
参数：g : ι -> MvPolynomial σ R；hd : forall b in B, (m.toSyn <| m.degree <| g b) = 
d ∨ g b = 0；hfd : (m.toSyn <| m.degree <| ∑ b in B, g b) < d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonomialOrder.sPolynomial_decomposition`：sPolynomial_decomposition {d : 
m.syn} {ι : Type*} {B : Finset ι} {g : ι -> MvPolynomial σ R} (hd : forall b in 
B, (m.toSyn <| m.degree <| g …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma sPolynomial_decomposition' {d : m.syn} {ι : Type*}
    {B : Finset ι} (g : ι → MvPolynomial σ R)
    (hd : ∀ b ∈ B, (m.toSyn <| m.degree <| g b) = d ∨ g b = 0)
    (hfd : (m.toSyn <| m.degree <| ∑ b ∈ B, g b) < d) :
    ∃ (c : ι → ι → R),
      ∑ b ∈ B, g b = ∑ b₁ ∈ B, ∑ b₂ ∈ B, (c b₁ b₂) • m.sPolynomial (g b₁) (g b₂) := by
  refine m.sPolynomial_decomposition ?_ hfd
  simpa [and_or_right, em']

end Field

section Binomial

variable {R : Type*} [CommRing R]

open Finsupp MvPolynomial

/-
**MonomialOrder.degree_X_add_C** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_X_add_C [Nontrivial R] {ι : Type*} (m : MonomialOrder ι) (i : ι) (r
 : R) : m.degree (X i + C r) = single i 1
参数：m : MonomialOrder ι；i : ι；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_add_of_lt`：degree_add_of_lt {f g : MvPolynomial σ R
} (h : m.degree g ≺[m] m.degree f) : m.degree (f + g) = m.degree f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonomialOrder.degree_C`：degree_C (r : R) : m.degree (C r) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `MonomialOrder.degree_X`：degree_X [Nontrivial R] {s : σ} : m.degree (X s 
: MvPolynomial σ R) = Finsupp.single s 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonomialOrder.bot_eq_zero`：bot_eq_zero : (⊥ : m.syn) = 0
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma degree_X_add_C [Nontrivial R]
    {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.degree (X i + C r) = single i 1 := by
  rw [degree_add_of_lt, degree_X]
  simp only [degree_C, map_zero, degree_X]
  rw [← bot_eq_zero, bot_lt_iff_ne_bot, bot_eq_zero, ← map_zero m.toSyn]
  simp
/-
**MonomialOrder.degree_X_sub_C** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_X_sub_C [Nontrivial R] {ι : Type*} (m : MonomialOrder ι) (i : ι) (r
 : R) : m.degree (X i - C r) = single i 1
参数：m : MonomialOrder ι；i : ι；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `MonomialOrder.degree_X_add_C`：degree_X_add_C [Nontrivial R] {ι : Type*} 
(m : MonomialOrder ι) (i : ι) (r : R) : m.degree (X i + C r) = single i 1
-/
lemma degree_X_sub_C [Nontrivial R]
    {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.degree (X i - C r) = single i 1 := by
  rw [sub_eq_add_neg, ← map_neg, degree_X_add_C]
/-
**MonomialOrder.monic_X_add_C** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：monic_X_add_C {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) : m.Monic 
(X i + C r)
参数：m : MonomialOrder ι；i : ι；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MonomialOrder.Monic.add_of_lt`：∀ {σ : Type u_1} {m : MonomialOrder σ} {R
 : Type u_2} [inst : CommSemiring R] {f g : MvPolynomial σ R},   m.Monic f → m.t
oSyn (m.degree g) <…
· 使用定理 `MonomialOrder.monic_X`：∀ {σ : Type u_1} {m : MonomialOrder σ} {R : Type 
u_2} [inst : CommSemiring R] {s : σ}, m.Monic (MvPolynomial.X s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_C`：degree_C (r : R) : m.degree (C r) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `MonomialOrder.degree_X`：degree_X [Nontrivial R] {s : σ} : m.degree (X s 
: MvPolynomial σ R) = Finsupp.single s 1
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma monic_X_add_C {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.Monic (X i + C r) := by
  nontriviality R
  apply monic_X.add_of_lt
  simp [degree_C, degree_X, ← not_le, ← eq_zero_iff]
/-
**MonomialOrder.monic_X_sub_C** 是 Mathlib 中的一个引理，位于命名空间 `MonomialOrder`。
形式化陈述：monic_X_sub_C {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) : m.Monic 
(X i - C r)
参数：m : MonomialOrder ι；i : ι；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `MonomialOrder.monic_X_add_C`：monic_X_add_C {ι : Type*} (m : MonomialOrde
r ι) (i : ι) (r : R) : m.Monic (X i + C r)
-/
lemma monic_X_sub_C {ι : Type*} (m : MonomialOrder ι) (i : ι) (r : R) :
    m.Monic (X i - C r) := by
  rw [sub_eq_add_neg, ← map_neg]
  apply monic_X_add_C

end Binomial

end MonomialOrder

