/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Monomial.Predicates

/-!

# Computing limits of monomials

In this file we define the `Monomial` structure, representing monomials in a basis, i.e.
`coef * b₁ ^ e₁ * ... * bₙ ^ eₙ` where `[b₁, ..., bₙ]` is a well-formed basis.

In the tactic implementation, we use `Monomial` to connect multiseries with real functions.
In this file we show how to find a limit of `Monomial` and how to asymptotically compare two
`Monomial`s.

## Main definitions

* `Monomial`: type to represent monomials.
* `UnitMonomial.toFun`/`Monomial.toFun`: converts structures to real functions.
* `UnitMonomial.toLogFun_isEquivalent_of_nonzero_head`: `log m.toFun` is asymptotically equivalent
  to its first summand - `m[0] • log basis[0]` if `m[0] ≠ 0`. Using this theorem we can prove that
  the asymptotic behaviour of the monomials is determined by its first non-zero exponent.
* `toFun_tendsto_top_of_FirstNonzeroIsPos` and its variants are used to infer the limit of
  `t.toFun` from `FirstNonzeroIsPos`/`FirstNonzeroIsNeg`/`AllZero`.
* `IsLittleO_of_lt_exps` and its variants are used to asymptotically compare two monomials.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Asymptotics Filter Topology Real

/-- Structure for representing monomials with coefficients. -/
/-
**Tactic.ComputeAsymptotics.Monomial** 是 Mathlib 中的一个归纳类型，位于命名空间 `Tactic.Compute
Asymptotics`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure for representing monomials with coefficients.
-/
structure Monomial where
  /-- Real coefficient of the monomial. -/
  coef : ℝ
  /-- Unit part of the monomial. -/
  unit : UnitMonomial

namespace UnitMonomial

/-- Function corresponding to a monomial. -/
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toFun** 是 Mathlib 中的一个定义，位于命名空间 `Tactic
.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toFun (m : UnitMonomial) (basis : Basis) : Real -> Real
参数：m : UnitMonomial；basis : Basis。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Function corresponding to a monomial.
-/
noncomputable def toFun (m : UnitMonomial) (basis : Basis) : ℝ → ℝ :=
  fun x ↦ (m.zipWith (fun exp b ↦ (b x)^exp) basis).prod

/-- Logarithm of function represented by a monomial, i.e.
`m[0] * log basis[0] + ... + m[n] * log basis[n]`. -/
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toLogFun** 是 Mathlib 中的一个定义，位于命名空间 `Tac
tic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toLogFun (m : UnitMonomial) (basis : Basis) : Real -> Real
参数：m : UnitMonomial；basis : Basis。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Logarithm of function represented by a monomial, i.e.
`m[0] * log basis[0] + ... + m[n] * log basis[n]`.
-/
noncomputable def toLogFun (m : UnitMonomial) (basis : Basis) : ℝ → ℝ :=
  fun x ↦ (m.zipWith (fun exp b ↦ exp * log (b x)) basis).sum

@[simp]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toFun_nil** 是 Mathlib 中的一个定理，位于命名空间 `Ta
ctic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toFun_nil (basis : Basis) : (UnitMonomial.toFun [] basis) = 1
参数：basis : Basis。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFun_nil (basis : Basis) : (UnitMonomial.toFun [] basis) = 1 := by
  ext x
  simp [toFun]

@[simp]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toFun_nil_basis** 是 Mathlib 中的一个定理，位于命名
空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toFun_nil_basis (m : UnitMonomial) : (UnitMonomial.toFun m []) = 1
参数：m : UnitMonomial。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.zipWith_nil_right`：∀ {α : Type u} {β : Type v} {γ : Type w} {l : Li
st α} {f : α → β → γ}, List.zipWith f l [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFun_nil_basis (m : UnitMonomial) : (UnitMonomial.toFun m []) = 1 := by
  ext x
  simp [toFun]

@[simp]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toFun_cons** 是 Mathlib 中的一个定理，位于命名空间 `T
actic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toFun_cons (exp : Real) (tl : UnitMonomial) (basis_hd : Real -> Real) (bas
is_tl : Basis) : (UnitMonomial.toFun (exp :: tl) (basis_hd :: basis_tl)) = basis
_hd ^ exp * tl.toFun basis_tl
参数：exp : Real；tl : UnitMonomial；basis_hd : Real -> Real；basis_tl : Basis。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFun_cons (exp : ℝ) (tl : UnitMonomial) (basis_hd : ℝ → ℝ) (basis_tl : Basis) :
    (UnitMonomial.toFun (exp :: tl) (basis_hd :: basis_tl)) =
    basis_hd ^ exp * tl.toFun basis_tl := by
  ext x
  simp [toFun]

@[simp]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toLogFun_nil** 是 Mathlib 中的一个定理，位于命名空间 
`Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toLogFun_nil (basis : Basis) : (UnitMonomial.toLogFun [] basis) = 0
参数：basis : Basis。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toLogFun_nil (basis : Basis) : (UnitMonomial.toLogFun [] basis) = 0 := by
  ext x
  simp [toLogFun]

@[simp]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toLogFun_nil_basis** 是 Mathlib 中的一个定理，位
于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toLogFun_nil_basis (m : UnitMonomial) : (UnitMonomial.toLogFun m []) = 0
参数：m : UnitMonomial。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.zipWith_nil_right`：∀ {α : Type u} {β : Type v} {γ : Type w} {l : Li
st α} {f : α → β → γ}, List.zipWith f l [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toLogFun_nil_basis (m : UnitMonomial) : (UnitMonomial.toLogFun m []) = 0 := by
  ext x
  simp [toLogFun]

@[simp]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toLogFun_cons** 是 Mathlib 中的一个定理，位于命名空间
 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toLogFun_cons (exp : Real) (tl : UnitMonomial) (basis_hd : Real -> Real) (
basis_tl : Basis) : (UnitMonomial.toLogFun (exp :: tl) (basis_hd :: basis_tl)) =
 exp • Real.log ∘ basis_hd + UnitMonomial.toLogFun tl basis_tl
参数：exp : Real；tl : UnitMonomial；basis_hd : Real -> Real；basis_tl : Basis。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toLogFun_cons (exp : ℝ) (tl : UnitMonomial) (basis_hd : ℝ → ℝ) (basis_tl : Basis) :
    (UnitMonomial.toLogFun (exp :: tl) (basis_hd :: basis_tl)) =
    exp • Real.log ∘ basis_hd + UnitMonomial.toLogFun tl basis_tl := by
  ext x
  simp [toLogFun]

/-- Multiplication of unit monomials. -/
/-
**Tactic.ComputeAsymptotics.UnitMonomial.mul** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.C
omputeAsymptotics.UnitMonomial`。
形式化陈述：mul (m1 m2 : UnitMonomial) : UnitMonomial
参数：m1 m2 : UnitMonomial。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of unit monomials.
-/
noncomputable def mul (m1 m2 : UnitMonomial) : UnitMonomial :=
  m1.zipWith (· + ·) m2

/-- Inversion of a unit monomial. -/
/-
**Tactic.ComputeAsymptotics.UnitMonomial.inv** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.C
omputeAsymptotics.UnitMonomial`。
形式化陈述：inv (m : UnitMonomial) : UnitMonomial
参数：m : UnitMonomial。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inversion of a unit monomial.
-/
noncomputable def inv (m : UnitMonomial) : UnitMonomial :=
  m.map (-·)
/-
**Tactic.ComputeAsymptotics.UnitMonomial.mul_length** 是 Mathlib 中的一个定理，位于命名空间 `T
actic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：mul_length {m1 m2 : UnitMonomial} (h : m1.length = m2.length) : (mul m1 m2
).length = m1.length
参数：h : m1.length = m2.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_zipWith`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β → γ} {l₁ : List α} {l₂ : List β},   (List.zipWith f l₁ l₂).length = min l
₁.length …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_length {m1 m2 : UnitMonomial} (h : m1.length = m2.length) :
    (mul m1 m2).length = m1.length := by
  simp [mul, h]

@[simp]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.inv_length** 是 Mathlib 中的一个定理，位于命名空间 `T
actic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：inv_length (m : UnitMonomial) : (inv m).length = m.length
参数：m : UnitMonomial。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_length (m : UnitMonomial) :
    (inv m).length = m.length := by
  simp [inv]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.mul_toFun** 是 Mathlib 中的一个定理，位于命名空间 `Ta
ctic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：mul_toFun {m1 m2 : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasi
s basis) (h_length : m1.length = m2.length) : (m1.mul m2).toFun basis =ᶠ[atTop] 
m1.toFun basis * m2.toFun basis
参数：h_basis : WellFormedBasis basis；h_length : m1.length = m2.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.eventually_pos`：eventually_pos
 {basis : Basis} (h : WellFormedBasis basis) : forallᶠ x in atTop, forall f in b
asis, 0 < f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.zipWith_self`：∀ {α : Type u_1} {δ : Type u_2} {f : α → α → δ} {l : 
List α}, List.zipWith f l l = List.map (fun a => f a a) l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `List.zipWith_nil_right`：∀ {α : Type u} {β : Type v} {γ : Type w} {l : Li
st α} {f : α → β → γ}, List.zipWith f l [] = []
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.tail`：tail {basis_hd : Real ->
 Real} {basis_tl : Basis} (h : WellFormedBasis (basis_hd :: basis_tl)) : WellFor
medBasis basis_tl
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
-/
theorem mul_toFun {m1 m2 : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis)
    (h_length : m1.length = m2.length) :
    (m1.mul m2).toFun basis =ᶠ[atTop] m1.toFun basis * m2.toFun basis := by
  apply h_basis.eventually_pos.mono
  intro x h_pos
  simp only [toFun, mul, Pi.mul_apply]
  induction m1 generalizing m2 basis with
  | nil =>
    symm at h_length
    simp_all
  | cons exp1 exps1 ih =>
    cases m2 with
    | nil => simp at h_length
    | cons exp2 exps2 =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      simp only [List.zipWith_cons_cons, List.prod_cons] at ih ⊢
      have h1 : exps1.length = exps2.length := by grind
      have h2 : ∀ f ∈ basis_tl, 0 < f x := by grind
      have h3 : 0 < basis_hd x := h_pos _ (by simp)
      rw [ih h_basis.tail h1 h2, Real.rpow_add h3]
      grind
/-
**Tactic.ComputeAsymptotics.UnitMonomial.inv_toFun** 是 Mathlib 中的一个定理，位于命名空间 `Ta
ctic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：inv_toFun {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis ba
sis) : m.inv.toFun basis =ᶠ[atTop] (m.toFun basis)⁻¹
参数：h_basis : WellFormedBasis basis。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.zipWith_nil_right`：∀ {α : Type u} {β : Type v} {γ : Type w} {l : Li
st α} {f : α → β → γ}, List.zipWith f l [] = []
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.head_eventually_pos`：head_even
tually_pos {basis_hd : Real -> Real} {basis_tl : Basis} (h : WellFormedBasis (ba
sis_hd :: basis_tl)) : forallᶠ x in atTop, 0 < basi…
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.tail`：tail {basis_hd : Real ->
 Real} {basis_tl : Basis} (h : WellFormedBasis (basis_hd :: basis_tl)) : WellFor
medBasis basis_tl
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
-/
theorem inv_toFun {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis) :
    m.inv.toFun basis =ᶠ[atTop] (m.toFun basis)⁻¹ := by
  eta_expand
  simp only [toFun, inv, Pi.inv_apply]
  induction m generalizing basis with
  | nil => simp
  | cons exp exps ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      apply ((h_basis.head_eventually_pos).and (ih (h_basis.tail))).mono
      intro x ⟨h_pos, ih⟩
      simp only [List.map_cons, List.zipWith_cons_cons, List.prod_cons, mul_inv_rev]
      grind [Real.rpow_neg h_pos.le]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.majorized_tail_toFun_head** 是 Mathlib 中
的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：majorized_tail_toFun_head {m : UnitMonomial} {basis_hd : Real -> Real} {ba
sis_tl : Basis} (h_length : m.length = basis_tl.length) (h_basis : WellFormedBas
is (basis_hd :: basis_tl)) : Majorized (m.toFun basis_tl) basis_hd 0
参数：h_length : m.length = basis_tl.length；h_basis : WellFormedBasis (basis_hd :: 
basis_tl)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_nil`：toFun_nil (basis : Bas
is) : (UnitMonomial.toFun [] basis) = 1
· 使用定理 `Tactic.ComputeAsymptotics.Majorized.const`：const (h_tendsto : Tendsto b 
atTop atTop) {c : Real} : Majorized (fun _ => c) b 0
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.tendsto_atTop`：tendsto_atTop {
basis : Basis} (h : WellFormedBasis basis) {f : Real -> Real} (hf : f in basis) 
: Tendsto f atTop atTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_cons`：toFun_cons (exp : Rea
l) (tl : UnitMonomial) (basis_hd : Real -> Real) (basis_tl : Basis) : (UnitMonom
ial.toFun (exp :: tl) (basis_hd :: basi…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Tactic.ComputeAsymptotics.Majorized.mul`：mul {f_exp g_exp : Real} (hf : 
Majorized f b f_exp) (hg : Majorized g b g_exp) (h_pos : forallᶠ t in atTop, 0 <
 b t) : Majorized (f * g) b (…
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.tail_pow_majorized_head`：tail_
pow_majorized_head {hd f : Real -> Real} {tl : Basis} (h_basis : WellFormedBasis
 (hd :: tl)) (hf : f in tl) (r : Real) : Majorized (f ^…
· 使用定理 `Asymptotics.IsLittleO.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {l : Fi
lter α} {f : α → …
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.tail`：tail {basis_hd : Real ->
 Real} {basis_tl : Basis} (h : WellFormedBasis (basis_hd :: basis_tl)) : WellFor
medBasis basis_tl
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.head_eventually_pos`：head_even
tually_pos {basis_hd : Real -> Real} {basis_tl : Basis} (h : WellFormedBasis (ba
sis_hd :: basis_tl)) : forallᶠ x in atTop, 0 < basi…
-/
theorem majorized_tail_toFun_head {m : UnitMonomial} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h_length : m.length = basis_tl.length)
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    Majorized (m.toFun basis_tl) basis_hd 0 := by
  induction m generalizing basis_hd basis_tl with
  | nil =>
    simp only [toFun_nil]
    exact Majorized.const (h_basis.tendsto_atTop (by simp))
  | cons hd tl ih =>
    cases basis_tl with
    | nil => simp at h_length
    | cons basis_tl_hd basis_tl_tl =>
      simp only [List.length_cons, Nat.add_right_cancel_iff, toFun_cons] at h_length ⊢
      rw [← add_zero 0]
      apply Majorized.mul (h_basis.tail_pow_majorized_head (by simp) _) _
        h_basis.head_eventually_pos
      exact fun exp h_exp ↦
        (ih h_length h_basis.tail 1 (by simp)).trans <|
        h_basis.tail_pow_majorized_head (by simp) 1 exp h_exp
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toFun_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ta
ctic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toFun_pos {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis ba
sis) : forallᶠ x in atTop, 0 < m.toFun basis x
参数：h_basis : WellFormedBasis basis。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.eventually_pos`：eventually_pos
 {basis : Basis} (h : WellFormedBasis basis) : forallᶠ x in atTop, forall f in b
asis, 0 < f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_nil`：toFun_nil (basis : Bas
is) : (UnitMonomial.toFun [] basis) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_nil_basis`：toFun_nil_basis 
(m : UnitMonomial) : (UnitMonomial.toFun m []) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.tail`：tail {basis_hd : Real ->
 Real} {basis_tl : Basis} (h : WellFormedBasis (basis_hd :: basis_tl)) : WellFor
medBasis basis_tl
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem toFun_pos {m : UnitMonomial} {basis : Basis}
    (h_basis : WellFormedBasis basis) :
    ∀ᶠ x in atTop, 0 < m.toFun basis x := by
  apply h_basis.eventually_pos.mono
  intro x hx
  induction m generalizing basis with
  | nil => simp
  | cons exp exps ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      simp only [toFun, List.zipWith_cons_cons, List.prod_cons]
      apply mul_pos (Real.rpow_pos_of_pos (hx basis_hd (by simp)) _)
      exact ih h_basis.tail (hx · <| by simp [·])
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toFun_ne_zero** 是 Mathlib 中的一个定理，位于命名空间
 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toFun_ne_zero {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasi
s basis) : forallᶠ x in atTop, m.toFun basis x != 0
参数：h_basis : WellFormedBasis basis。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_pos`：toFun_pos {m : UnitMon
omial} {basis : Basis} (h_basis : WellFormedBasis basis) : forallᶠ x in atTop, 0
 < m.toFun basis x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem toFun_ne_zero {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis) :
    ∀ᶠ x in atTop, m.toFun basis x ≠ 0 :=
  (toFun_pos h_basis).mono fun _ hx => hx.ne'
/-
**Tactic.ComputeAsymptotics.UnitMonomial.zeros_append_toFun** 是 Mathlib 中的一个定理，位
于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：zeros_append_toFun {m : UnitMonomial} {left right : Basis} : (List.replica
te left.length 0 ++ m : UnitMonomial).toFun (left ++ right) = m.toFun right
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_cons`：toFun_cons (exp : Rea
l) (tl : UnitMonomial) (basis_hd : Real -> Real) (basis_tl : Basis) : (UnitMonom
ial.toFun (exp :: tl) (basis_hd :: basi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.pi_rpow_zero`：pi_rpow_zero {α : Type*} (f : α -> Real) : f ^ (0 : R
eal) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zeros_append_toFun {m : UnitMonomial} {left right : Basis} :
    (List.replicate left.length 0 ++ m : UnitMonomial).toFun (left ++ right) = m.toFun right := by
  induction left with
  | nil => rfl
  | cons left_hd left_tl ih => simp [List.replicate_succ, ih]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.log_toFun_eq_toLogFun** 是 Mathlib 中的一个定
理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：log_toFun_eq_toLogFun {m : UnitMonomial} {basis : Basis} (h_basis : WellFo
rmedBasis basis) : Real.log ∘ m.toFun basis =ᶠ[atTop] m.toLogFun basis
参数：h_basis : WellFormedBasis basis。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.eventually_pos`：eventually_pos
 {basis : Basis} (h : WellFormedBasis basis) : forallᶠ x in atTop, forall f in b
asis, 0 < f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_nil`：toFun_nil (basis : Bas
is) : (UnitMonomial.toFun [] basis) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toLogFun_nil`：toLogFun_nil (basis
 : Basis) : (UnitMonomial.toLogFun [] basis) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_nil_basis`：toFun_nil_basis 
(m : UnitMonomial) : (UnitMonomial.toFun m []) = 1
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toLogFun_nil_basis`：toLogFun_nil_
basis (m : UnitMonomial) : (UnitMonomial.toLogFun m []) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_cons`：toFun_cons (exp : Rea
l) (tl : UnitMonomial) (basis_hd : Real -> Real) (basis_tl : Basis) : (UnitMonom
ial.toFun (exp :: tl) (basis_hd :: basi…
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toLogFun_cons`：toLogFun_cons (exp
 : Real) (tl : UnitMonomial) (basis_hd : Real -> Real) (basis_tl : Basis) : (Uni
tMonomial.toLogFun (exp :: tl) (basis_hd :…
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.tail`：tail {basis_hd : Real ->
 Real} {basis_tl : Basis} (h : WellFormedBasis (basis_hd :: basis_tl)) : WellFor
medBasis basis_tl
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem log_toFun_eq_toLogFun {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis) :
    Real.log ∘ m.toFun basis =ᶠ[atTop] m.toLogFun basis := by
  apply h_basis.eventually_pos.mono
  intro x hx
  suffices h : (0 < m.toFun basis x ∧ (log ∘ m.toFun basis) x = m.toLogFun basis x) from h.2
  induction m generalizing basis with
  | nil => simp
  | cons e es ih =>
    cases basis with
    | nil => simp
    | cons b bs =>
      simp only [toFun_cons, Pi.mul_apply, Pi.pow_apply, Function.comp_apply, toLogFun_cons,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      obtain ⟨hpos, heq⟩ := ih h_basis.tail (hx · <| by simp [·])
      refine ⟨mul_pos (Real.rpow_pos_of_pos (hx b (by simp)) _) hpos, ?_⟩
      rw [Real.log_mul (Real.rpow_pos_of_pos (hx b (by simp)) _).ne' hpos.ne',
            Real.log_rpow (hx b (by simp)), ← heq]
      rfl
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toLogFun_isEquivalent_of_nonzero_head**
 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toLogFun_isEquivalent_of_nonzero_head {exps_hd : Real} {exps_tl : UnitMono
mial} {basis_hd : Real -> Real} {basis_tl : Basis} (h_basis : WellFormedBasis (b
asis_hd :: basis_tl)) (h_nonzero : exps_hd != 0) : UnitMonomial.toLogFun (exps_h
d :: exps_tl) (basis_hd :: basis_tl) ~[atTop] exps_hd • log ∘ basis_hd
参数：h_basis : WellFormedBasis (basis_hd :: basis_tl)；h_nonzero : exps_hd != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toLogFun_cons`：toLogFun_cons (exp
 : Real) (tl : UnitMonomial) (basis_hd : Real -> Real) (basis_tl : Basis) : (Uni
tMonomial.toLogFun (exp :: tl) (basis_hd :…
· 使用定理 `Asymptotics.IsEquivalent.add_isLittleO`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEq
uivalent l u v → w =o[l] v →…
· 使用定理 `Asymptotics.IsEquivalent.refl`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u : α → β} {l : Filter α}, Asymptotics.IsEquivalent l u u
· 使用定理 `Asymptotics.IsLittleO.const_mul_right'`：∀ {α : Type u_1} {E : Type u_3} 
{R : Type u_13} [inst : Norm E] [inst_1 : SeminormedRing R] {f : α → E} {l : Fil
ter α}   {g : α → R} {c : R}…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.tail_isLittleO_head`：tail_isLi
ttleO_head {hd : Real -> Real} {tl : Basis} (h : WellFormedBasis (hd :: tl)) {f 
: Real -> Real} (hf : f in tl) : (Real.log ∘ f) =o[…
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toLogFun_nil`：toLogFun_nil (basis
 : Basis) : (UnitMonomial.toLogFun [] basis) = 0
· 使用定理 `Asymptotics.isLittleO_zero`：isLittleO_zero : (fun _x => (0 : E')) =o[l] 
g'
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toLogFun_nil_basis`：toLogFun_nil_
basis (m : UnitMonomial) : (UnitMonomial.toLogFun m []) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsLittleO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R
 : Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filte
r α}   {f : α → R}, f =o[l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem toLogFun_isEquivalent_of_nonzero_head {exps_hd : ℝ} {exps_tl : UnitMonomial}
    {basis_hd : ℝ → ℝ} {basis_tl : Basis} (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_nonzero : exps_hd ≠ 0) :
    UnitMonomial.toLogFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) ~[atTop]
      exps_hd • log ∘ basis_hd := by
  simp only [toLogFun_cons]
  apply IsEquivalent.refl.add_isLittleO
  apply IsLittleO.const_mul_right' (isUnit_iff_ne_zero.mpr h_nonzero)
  have hlo : ∀ b ∈ basis_tl, (Real.log ∘ b) =o[atTop] (Real.log ∘ basis_hd) :=
    fun b hb => h_basis.tail_isLittleO_head hb
  clear h_basis
  induction exps_tl generalizing basis_tl with
  | nil =>
    simp only [toLogFun_nil]
    exact Asymptotics.isLittleO_zero _ _
  | cons e es ih =>
    cases basis_tl with
    | nil =>
      simp only [toLogFun_nil_basis]
      exact Asymptotics.isLittleO_zero _ _
    | cons b bs =>
      exact (IsLittleO.const_mul_left (hlo b (by simp)) e).add (ih (by grind))
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toFun_tendsto_top_of_head_pos** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toFun_tendsto_top_of_head_pos {exps_hd : Real} {exps_tl : UnitMonomial} {b
asis_hd : Real -> Real} {basis_tl : Basis} (h_basis : WellFormedBasis (basis_hd 
:: basis_tl)) (h_nonzero : 0 < exps_hd) : Tendsto (UnitMonomial.toFun (exps_hd :
: exps_tl) (basis_hd :: basis_tl)) atTop atTop
参数：h_basis : WellFormedBasis (basis_hd :: basis_tl)；h_nonzero : 0 < exps_hd。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.congr_left`：∀ {α : Type u_1} {β : Type u_2} [in
st : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEquiv
alent l u v → u =ᶠ[l] w →…
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toLogFun_isEquivalent_of_nonzero_
head`：toLogFun_isEquivalent_of_nonzero_head {exps_hd : Real} {exps_tl : UnitMono
mial} {basis_hd : Real -> Real} {basis_tl : Basis} (h_basis : Well…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.log_toFun_eq_toLogFun`：log_toFun_
eq_toLogFun {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis)
 : Real.log ∘ m.toFun basis =ᶠ[atTop] m.toLogFun b…
· 使用定理 `Asymptotics.IsEquivalent.tendsto_atTop`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v : α
 → β}   {l : Filter α} [Orde…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.tendsto_atTop`：tendsto_atTop {
basis : Basis} (h : WellFormedBasis basis) {f : Real -> Real} (hf : f in basis) 
: Tendsto f atTop atTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_pos`：toFun_pos {m : UnitMon
omial} {basis : Basis} (h_basis : WellFormedBasis basis) : forallᶠ x in atTop, 0
 < m.toFun basis x
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Real.tendsto_exp_atTop`：tendsto_exp_atTop : Tendsto exp atTop atTop
-/
theorem toFun_tendsto_top_of_head_pos {exps_hd : ℝ} {exps_tl : UnitMonomial} {basis_hd : ℝ → ℝ}
    {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_nonzero : 0 < exps_hd) :
    Tendsto (UnitMonomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl)) atTop atTop := by
  have h_equiv : Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) ~[atTop]
      exps_hd • Real.log ∘ basis_hd :=
    (toLogFun_isEquivalent_of_nonzero_head h_basis h_nonzero.ne').congr_left
      (log_toFun_eq_toLogFun h_basis).symm
  suffices h_log : Tendsto (Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl))
      atTop atTop by
    apply Filter.Tendsto.congr' _ (Real.tendsto_exp_atTop.comp h_log)
    apply (toFun_pos (m := (exps_hd :: exps_tl)) h_basis).mono
    intro x hx
    simp only [Function.comp_apply]
    exact Real.exp_log hx
  apply IsEquivalent.tendsto_atTop h_equiv.symm
  apply Filter.Tendsto.const_mul_atTop h_nonzero
  apply Tendsto.comp Real.tendsto_log_atTop
  exact h_basis.tendsto_atTop (by simp)
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toFun_tendsto_zero_of_head_neg** 是 Math
lib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toFun_tendsto_zero_of_head_neg {exps_hd : Real} {exps_tl : UnitMonomial} {
basis_hd : Real -> Real} {basis_tl : Basis} (h_basis : WellFormedBasis (basis_hd
 :: basis_tl)) (h_nonzero : exps_hd < 0) : Tendsto (UnitMonomial.toFun (exps_hd 
:: exps_tl) (basis_hd :: basis_tl)) atTop (𝓝 0)
参数：h_basis : WellFormedBasis (basis_hd :: basis_tl)；h_nonzero : exps_hd < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.congr_left`：∀ {α : Type u_1} {β : Type u_2} [in
st : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEquiv
alent l u v → u =ᶠ[l] w →…
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toLogFun_isEquivalent_of_nonzero_
head`：toLogFun_isEquivalent_of_nonzero_head {exps_hd : Real} {exps_tl : UnitMono
mial} {basis_hd : Real -> Real} {basis_tl : Basis} (h_basis : Well…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.log_toFun_eq_toLogFun`：log_toFun_
eq_toLogFun {m : UnitMonomial} {basis : Basis} (h_basis : WellFormedBasis basis)
 : Real.log ∘ m.toFun basis =ᶠ[atTop] m.toLogFun b…
· 使用定理 `Asymptotics.IsEquivalent.tendsto_atBot`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v : α
 → β}   {l : Filter α} [Orde…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
· 使用定理 `Tactic.ComputeAsymptotics.WellFormedBasis.tendsto_atTop`：tendsto_atTop {
basis : Basis} (h : WellFormedBasis basis) {f : Real -> Real} (hf : f in basis) 
: Tendsto f atTop atTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Filter.Tendsto.const_mul_atTop_of_neg`：∀ {α : Type u_1} {β : Type u_2} [
inst : Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} 
  {f : β → α} {r : α}, r < …
· 使用定理 `Real.tendsto_exp_atBot`：tendsto_exp_atBot : Tendsto exp atBot (𝓝 0)
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_pos`：toFun_pos {m : UnitMon
omial} {basis : Basis} (h_basis : WellFormedBasis basis) : forallᶠ x in atTop, 0
 < m.toFun basis x
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
-/
theorem toFun_tendsto_zero_of_head_neg {exps_hd : ℝ} {exps_tl : UnitMonomial} {basis_hd : ℝ → ℝ}
    {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_nonzero : exps_hd < 0) :
    Tendsto (UnitMonomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl)) atTop (𝓝 0) := by
  have h_equiv : Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) ~[atTop]
      exps_hd • Real.log ∘ basis_hd :=
    (toLogFun_isEquivalent_of_nonzero_head h_basis h_nonzero.ne).congr_left
      (log_toFun_eq_toLogFun h_basis).symm
  suffices h_log : Tendsto (Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl))
      atTop atBot by
    have hmono := Real.tendsto_exp_atBot.comp h_log
    apply Filter.Tendsto.congr' _ hmono
    apply (toFun_pos (m := (exps_hd :: exps_tl)) h_basis).mono
    intro x hx
    simp only [Function.comp_apply]
    exact Real.exp_log hx
  apply IsEquivalent.tendsto_atBot h_equiv.symm
  have h_log_atTop : Tendsto (Real.log ∘ basis_hd) atTop atTop :=
    Tendsto.comp Real.tendsto_log_atTop (h_basis.tendsto_atTop (by simp))
  exact Filter.Tendsto.const_mul_atTop_of_neg h_nonzero h_log_atTop
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toFun_tendsto_top_of_firstNonzeroIsPos*
* 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toFun_tendsto_top_of_firstNonzeroIsPos {m : UnitMonomial} {basis : Basis} 
(h_basis : WellFormedBasis basis) (h_length : m.length = basis.length) (h_firstI
sPos : FirstNonzeroIsPos m) : Tendsto (UnitMonomial.toFun m basis) atTop atTop
参数：h_basis : WellFormedBasis basis；h_length : m.length = basis.length；h_firstIsP
os : FirstNonzeroIsPos m。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_tendsto_top_of_firstNonzeroIsPos {m : UnitMonomial} {basis : Basis}
    (h_basis : WellFormedBasis basis) (h_length : m.length = basis.length)
    (h_firstIsPos : FirstNonzeroIsPos m) :
    Tendsto (UnitMonomial.toFun m basis) atTop atTop := by
  cases m with
  | nil => simp at h_firstIsPos
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [FirstNonzeroIsPos.cons_iff] at h_firstIsPos
      obtain h | h := h_firstIsPos
      · exact toFun_tendsto_top_of_head_pos h_basis h
      · have h_eq : UnitMonomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) =
                    UnitMonomial.toFun exps_tl basis_tl := by
          ext x; simp [UnitMonomial.toFun, h.left]
        rw [h_eq]
        exact toFun_tendsto_top_of_firstNonzeroIsPos h_basis.tail (by simpa using h_length) h.right
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toFun_tendsto_zero_of_firstNonzeroIsNeg
** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toFun_tendsto_zero_of_firstNonzeroIsNeg {m : UnitMonomial} {basis : Basis}
 (h_basis : WellFormedBasis basis) (h_length : m.length = basis.length) (h_first
IsNeg : FirstNonzeroIsNeg m) : Tendsto (UnitMonomial.toFun m basis) atTop (𝓝 0)
参数：h_basis : WellFormedBasis basis；h_length : m.length = basis.length；h_firstIsN
eg : FirstNonzeroIsNeg m。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_tendsto_zero_of_firstNonzeroIsNeg {m : UnitMonomial} {basis : Basis}
    (h_basis : WellFormedBasis basis) (h_length : m.length = basis.length)
    (h_firstIsNeg : FirstNonzeroIsNeg m) :
    Tendsto (UnitMonomial.toFun m basis) atTop (𝓝 0) := by
  cases m with
  | nil => simp at h_firstIsNeg
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [FirstNonzeroIsNeg.cons_iff] at h_firstIsNeg
      obtain h | h := h_firstIsNeg
      · exact toFun_tendsto_zero_of_head_neg h_basis h
      · have h_eq : UnitMonomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) =
                    UnitMonomial.toFun exps_tl basis_tl := by
          ext x; simp [UnitMonomial.toFun, h.left]
        rw [h_eq]
        exact toFun_tendsto_zero_of_firstNonzeroIsNeg h_basis.tail (by simpa using h_length) h.right
/-
**Tactic.ComputeAsymptotics.UnitMonomial.toFun_tendsto_one_of_allZero** 是 Mathli
b 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：toFun_tendsto_one_of_allZero {m : UnitMonomial} {basis : Basis} (h_allZero
 : AllZero m) : Tendsto (UnitMonomial.toFun m basis) atTop (𝓝 1)
参数：h_allZero : AllZero m。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_tendsto_one_of_allZero {m : UnitMonomial} {basis : Basis}
    (h_allZero : AllZero m) :
    Tendsto (UnitMonomial.toFun m basis) atTop (𝓝 1) := by
  cases m with
  | nil =>
    exact tendsto_const_nhds
  | cons exps_hd exps_tl =>
    cases basis with
    | nil =>
      eta_expand
      simp [toFun]
    | cons basis_hd basis_tl =>
      simp at h_allZero
      have h_eq : UnitMonomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) =
                  UnitMonomial.toFun exps_tl basis_tl := by
        ext x; simp [UnitMonomial.toFun, h_allZero.left]
      rw [h_eq]
      apply toFun_tendsto_one_of_allZero h_allZero.right
/-
**Tactic.ComputeAsymptotics.UnitMonomial.isLittleO_of_lt** 是 Mathlib 中的一个引理，位于命名
空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：isLittleO_of_lt {basis : Basis} {m1 m2 : UnitMonomial} (h_basis : WellForm
edBasis basis) (h1 : m1.length = basis.length) (h2 : m2.length = basis.length) (
h_lt : m1 < m2) : m1.toFun basis =o[atTop] m2.toFun basis
参数：h_basis : WellFormedBasis basis；h1 : m1.length = basis.length；h2 : m2.length 
= basis.length；h_lt : m1 < m2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isLittleO_of_lt {basis : Basis} {m1 m2 : UnitMonomial}
    (h_basis : WellFormedBasis basis)
    (h1 : m1.length = basis.length)
    (h2 : m2.length = basis.length)
    (h_lt : m1 < m2) :
    m1.toFun basis =o[atTop] m2.toFun basis := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp only [List.length_nil, List.length_eq_zero_iff] at h1 h2
    simp [h1, h2] at h_lt
  obtain _ | ⟨exp1, m1⟩ := m1
  · simp at h1
  obtain _ | ⟨exp2, m2⟩ := m2
  · simp at h2
  cases h_lt with
  | cons h =>
    simp only [toFun_cons]
    apply IsBigO.mul_isLittleO (isBigO_refl _ _)
    exact isLittleO_of_lt h_basis.tail (by simpa using h1) (by simpa using h2) h
  | rel h =>
    simp only [List.length_cons, Nat.add_right_cancel_iff, toFun_cons] at h1 h2 ⊢
    apply IsLittleO.of_tendsto_div_atTop
    apply Filter.Tendsto.congr' (f₁ := UnitMonomial.toFun ((exp2 - exp1) ::
      UnitMonomial.mul m2 (UnitMonomial.inv m1)) (basis_hd :: basis_tl))
    · simp only [toFun_cons, Pi.mul_apply, Pi.pow_apply]
      grw [mul_toFun h_basis.tail (by grind [inv_length]), inv_toFun h_basis.tail]
      apply h_basis.head_eventually_pos.mono
      intro x hx
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, Real.rpow_sub hx]
      field
    · apply toFun_tendsto_top_of_firstNonzeroIsPos h_basis
      · grind [inv_length, mul_length]
      · apply FirstNonzeroIsPos.of_head
        grind

end UnitMonomial

namespace Monomial

/-- Converts `t : Monomial` to real function represented by the corresponding monomial, i.e.
`t.coef * basis[0]^t.exps[0] * basis[1]^t.exps[1] * ...`. It is always assumed that
`t.exps.length = basis.length`, but some theorems below do not require this assumption. -/
/-
**Tactic.ComputeAsymptotics.Monomial.toFun** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.Com
puteAsymptotics.Monomial`。
形式化陈述：toFun (t : Monomial) (basis : Basis) : Real -> Real
参数：t : Monomial；basis : Basis。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts `t : Monomial` to real function represented by the corresponding monomi
al, i.e.
`t.coef * basis[0]^t.exps[0] * basis[1]^t.exps[1] * ...`. It is always assumed t
hat
`t.exps.length = basis.length`, but some theorems below do not require this assu
mption.
-/
noncomputable def toFun (t : Monomial) (basis : Basis) : ℝ → ℝ :=
  t.coef • t.unit.toFun basis

@[simp]
/-
**Tactic.ComputeAsymptotics.Monomial.nil_toFun** 是 Mathlib 中的一个定理，位于命名空间 `Tactic
.ComputeAsymptotics.Monomial`。
形式化陈述：nil_toFun {coef : Real} {basis : Basis} : Monomial.toFun ⟨coef, []⟩ basis 
= fun _ => coef
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_nil`：toFun_nil (basis : Bas
is) : (UnitMonomial.toFun [] basis) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nil_toFun {coef : ℝ} {basis : Basis} :
    Monomial.toFun ⟨coef, []⟩ basis = fun _ ↦ coef := by
  ext x
  simp [toFun]

@[simp]
/-
**Tactic.ComputeAsymptotics.Monomial.cons_toFun** 是 Mathlib 中的一个定理，位于命名空间 `Tacti
c.ComputeAsymptotics.Monomial`。
形式化陈述：cons_toFun {coef exp : Real} {m : UnitMonomial} {basis_hd : Real -> Real} 
{basis_tl : Basis} : Monomial.toFun ⟨coef, exp :: m⟩ (basis_hd :: basis_tl) = ba
sis_hd ^ exp * Monomial.toFun ⟨coef, m⟩ basis_tl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_cons`：toFun_cons (exp : Rea
l) (tl : UnitMonomial) (basis_hd : Real -> Real) (basis_tl : Basis) : (UnitMonom
ial.toFun (exp :: tl) (basis_hd :: basi…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
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
-/
theorem cons_toFun {coef exp : ℝ} {m : UnitMonomial} {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    Monomial.toFun ⟨coef, exp :: m⟩ (basis_hd :: basis_tl) =
    basis_hd ^ exp * Monomial.toFun ⟨coef, m⟩ basis_tl := by
  ext x
  simp [toFun]
  ring

/-- If `t.coef = 0`, then `t.toFun` is zero. -/
/-
**Tactic.ComputeAsymptotics.Monomial.zero_coef_toFun** 是 Mathlib 中的一个定理，位于命名空间 `
Tactic.ComputeAsymptotics.Monomial`。
形式化陈述：zero_coef_toFun {t : Monomial} (basis : Basis) (h_coef : t.coef = 0) : t.t
oFun basis = 0
参数：basis : Basis；h_coef : t.coef = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `t.coef = 0`, then `t.toFun` is zero.
-/
theorem zero_coef_toFun {t : Monomial} (basis : Basis) (h_coef : t.coef = 0) :
    t.toFun basis = 0 := by
  simp [toFun, h_coef]

/-- If `t.coef = 0`, then `t.toFun` is zero. -/
/-
**Tactic.ComputeAsymptotics.Monomial.zero_coef_toFun'** 是 Mathlib 中的一个定理，位于命名空间 
`Tactic.ComputeAsymptotics.Monomial`。
形式化陈述：zero_coef_toFun' (basis : Basis) (exps : UnitMonomial) : Monomial.toFun ⟨0
, exps⟩ basis = 0
参数：basis : Basis；exps : UnitMonomial。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Monomial.zero_coef_toFun`：zero_coef_toFun {t :
 Monomial} (basis : Basis) (h_coef : t.coef = 0) : t.toFun basis = 0

--- 原说明 ---
If `t.coef = 0`, then `t.toFun` is zero.
-/
theorem zero_coef_toFun' (basis : Basis) (exps : UnitMonomial) :
    Monomial.toFun ⟨0, exps⟩ basis = 0 := zero_coef_toFun _ rfl

/-- Negation of a monomial. -/
/-
**Tactic.ComputeAsymptotics.Monomial.neg** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.Compu
teAsymptotics.Monomial`。
形式化陈述：neg (t : Monomial) : Monomial
参数：t : Monomial。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negation of a monomial.
-/
noncomputable def neg (t : Monomial) : Monomial :=
  ⟨-t.coef, t.unit⟩

/-- Multiplication of monomials. -/
/-
**Tactic.ComputeAsymptotics.Monomial.mul** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.Compu
teAsymptotics.Monomial`。
形式化陈述：mul (t1 t2 : Monomial) : Monomial
参数：t1 t2 : Monomial。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of monomials.
-/
noncomputable def mul (t1 t2 : Monomial) : Monomial :=
  ⟨t1.coef * t2.coef, t1.unit.mul t2.unit⟩

/-- Scales a monomial by a real factor `c`. -/
/-
**Tactic.ComputeAsymptotics.Monomial.smul** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.Comp
uteAsymptotics.Monomial`。
形式化陈述：smul (t : Monomial) (c : Real) : Monomial
参数：t : Monomial；c : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scales a monomial by a real factor `c`.
-/
noncomputable def smul (t : Monomial) (c : ℝ) : Monomial :=
  ⟨c * t.coef, t.unit⟩

/-- Inversion operation for monomials. -/
/-
**Tactic.ComputeAsymptotics.Monomial.inv** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.Compu
teAsymptotics.Monomial`。
形式化陈述：inv (t : Monomial) : Monomial
参数：t : Monomial。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inversion operation for monomials.
-/
noncomputable def inv (t : Monomial) : Monomial :=
  ⟨t.coef⁻¹, t.unit.inv⟩

/-- Flipping the sign of `coef` flips the sign of `toFun`. The theorem is stated in this form,
because it allows one to rewrite the `t.toFun basis` expression. It is used below in cases where we
want to reduce the case of `t.coef < 0` to `t.coef > 0`. -/
/-
**Tactic.ComputeAsymptotics.Monomial.neg_toFun** 是 Mathlib 中的一个定理，位于命名空间 `Tactic
.ComputeAsymptotics.Monomial`。
形式化陈述：neg_toFun {t : Monomial} {basis : Basis} : t.toFun basis = -t.neg.toFun ba
sis
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Flipping the sign of `coef` flips the sign of `toFun`. The theorem is stated in 
this form,
because it allows one to rewrite the `t.toFun basis` expression. It is used belo
w in cases where we
want to reduce the case of `t.coef < 0` to `t.coef > 0`.
-/
theorem neg_toFun {t : Monomial} {basis : Basis} :
    t.toFun basis = -t.neg.toFun basis := by
  ext x
  simp [neg, toFun]
/-
**Tactic.ComputeAsymptotics.Monomial.mul_toFun** 是 Mathlib 中的一个定理，位于命名空间 `Tactic
.ComputeAsymptotics.Monomial`。
形式化陈述：mul_toFun {t1 t2 : Monomial} {basis : Basis} (h_basis : WellFormedBasis ba
sis) (h_length : t1.unit.length = t2.unit.length) : (mul t1 t2).toFun basis =ᶠ[a
tTop] t1.toFun basis * t2.toFun basis
参数：h_basis : WellFormedBasis basis；h_length : t1.unit.length = t2.unit.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.const_smul`：∀ {α : Type u} {β : Type v} {γ : Type u_
2} [inst : SMul γ β] {f g : α → β} {l : Filter α},   f =ᶠ[l] g → ∀ (c : γ), c • 
f =ᶠ[l] c • g
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.mul_toFun`：mul_toFun {m1 m2 : Uni
tMonomial} {basis : Basis} (h_basis : WellFormedBasis basis) (h_length : m1.leng
th = m2.length) : (m1.mul m2).toFun ba…
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
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
-/
theorem mul_toFun {t1 t2 : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis)
    (h_length : t1.unit.length = t2.unit.length) :
    (mul t1 t2).toFun basis =ᶠ[atTop] t1.toFun basis * t2.toFun basis := by
  simp only [toFun, mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  grw [UnitMonomial.mul_toFun h_basis h_length]
  filter_upwards [] with t
  simp [Pi.smul_apply, Pi.mul_apply]
  ring
/-
**Tactic.ComputeAsymptotics.Monomial.smul_toFun** 是 Mathlib 中的一个定理，位于命名空间 `Tacti
c.ComputeAsymptotics.Monomial`。
形式化陈述：smul_toFun {t : Monomial} {basis : Basis} (c : Real) : (smul t c).toFun ba
sis = c • t.toFun basis
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
-/
theorem smul_toFun {t : Monomial} {basis : Basis} (c : ℝ) :
    (smul t c).toFun basis = c • t.toFun basis := by
  ext x
  simp [smul, toFun]
  ring
/-
**Tactic.ComputeAsymptotics.Monomial.inv_toFun** 是 Mathlib 中的一个定理，位于命名空间 `Tactic
.ComputeAsymptotics.Monomial`。
形式化陈述：inv_toFun {t : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis)
 : t.inv.toFun basis =ᶠ[atTop] (t.toFun basis)⁻¹
参数：h_basis : WellFormedBasis basis。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.const_smul`：∀ {α : Type u} {β : Type v} {γ : Type u_
2} [inst : SMul γ β] {f g : α → β} {l : Filter α},   f =ᶠ[l] g → ∀ (c : γ), c • 
f =ᶠ[l] c • g
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.inv_toFun`：inv_toFun {m : UnitMon
omial} {basis : Basis} (h_basis : WellFormedBasis basis) : m.inv.toFun basis =ᶠ[
atTop] (m.toFun basis)⁻¹
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
-/
theorem inv_toFun {t : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis) :
    t.inv.toFun basis =ᶠ[atTop] (t.toFun basis)⁻¹ := by
  simp only [toFun, inv]
  grw [UnitMonomial.inv_toFun h_basis]
  filter_upwards [] with x
  simp [Pi.smul_apply, Pi.inv_apply]
  ring

@[simp]
/-
**Tactic.ComputeAsymptotics.Monomial.inv_length** 是 Mathlib 中的一个定理，位于命名空间 `Tacti
c.ComputeAsymptotics.Monomial`。
形式化陈述：inv_length (t : Monomial) : t.inv.unit.length = t.unit.length
参数：t : Monomial。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.inv_length`：inv_length (m : UnitM
onomial) : (inv m).length = m.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_length (t : Monomial) :
    t.inv.unit.length = t.unit.length := by
  simp [inv]

/-- If `t.coef > 0` then `t.toFun` is eventually positive. -/
/-
**Tactic.ComputeAsymptotics.Monomial.toFun_pos** 是 Mathlib 中的一个定理，位于命名空间 `Tactic
.ComputeAsymptotics.Monomial`。
形式化陈述：toFun_pos {t : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis)
 (h_coef : 0 < t.coef) : forallᶠ x in atTop, 0 < t.toFun basis x
参数：h_basis : WellFormedBasis basis；h_coef : 0 < t.coef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_pos`：toFun_pos {m : UnitMon
omial} {basis : Basis} (h_basis : WellFormedBasis basis) : forallᶠ x in atTop, 0
 < m.toFun basis x
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R

--- 原说明 ---
If `t.coef > 0` then `t.toFun` is eventually positive.
-/
theorem toFun_pos {t : Monomial} {basis : Basis}
    (h_basis : WellFormedBasis basis) (h_coef : 0 < t.coef) :
    ∀ᶠ x in atTop, 0 < t.toFun basis x := by
  simp only [Monomial.toFun]
  apply (t.unit.toFun_pos h_basis).mono
  intro x hx
  simp only [Pi.smul_apply, smul_eq_mul]
  positivity
/-
**Tactic.ComputeAsymptotics.Monomial.zeros_append_toFun** 是 Mathlib 中的一个定理，位于命名空
间 `Tactic.ComputeAsymptotics.Monomial`。
形式化陈述：zeros_append_toFun (coef : Real) {exps : UnitMonomial} {left right : Basis
} : let t : Monomial
参数：coef : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.zeros_append_toFun`：zeros_append_
toFun {m : UnitMonomial} {left right : Basis} : (List.replicate left.length 0 ++
 m : UnitMonomial).toFun (left ++ right) = m.to…
-/
theorem zeros_append_toFun (coef : ℝ) {exps : UnitMonomial} {left right : Basis} :
    let t : Monomial := ⟨coef, List.replicate left.length 0 ++ exps⟩;
    t.toFun (left ++ right) = (mk coef exps).toFun right := by
  exact congrArg (coef • ·) UnitMonomial.zeros_append_toFun

/-- `t.toFun` tends to `𝓝 0` when `t.coef = 0`. -/
/-
**Tactic.ComputeAsymptotics.Monomial.tendsto_zero_of_coef_zero** 是 Mathlib 中的一个定
理，位于命名空间 `Tactic.ComputeAsymptotics.Monomial`。
形式化陈述：tendsto_zero_of_coef_zero {coef : Real} {exps : UnitMonomial} (basis : Bas
is) (h_coef : coef = 0) : let t : Monomial
参数：basis : Basis；h_coef : coef = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.Monomial.zero_coef_toFun`：zero_coef_toFun {t :
 Monomial} (basis : Basis) (h_coef : t.coef = 0) : t.toFun basis = 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)

--- 原说明 ---
`t.toFun` tends to `𝓝 0` when `t.coef = 0`.
-/
theorem tendsto_zero_of_coef_zero {coef : ℝ} {exps : UnitMonomial} (basis : Basis)
    (h_coef : coef = 0) :
    let t : Monomial := ⟨coef, exps⟩;
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  intro t
  rw [zero_coef_toFun _ (by simpa [t])]
  exact tendsto_const_nhds
/-
**Tactic.ComputeAsymptotics.Monomial.toFun_tendsto_zero_of_firstNonzeroIsNeg** 是
 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Monomial`。
形式化陈述：toFun_tendsto_zero_of_firstNonzeroIsNeg {coef : Real} {exps : UnitMonomial
} {basis : Basis} (h_basis : WellFormedBasis basis) (h_length : exps.length = ba
sis.length) (h_exps : exps.FirstNonzeroIsNeg) : let t : Monomial
参数：h_basis : WellFormedBasis basis；h_length : exps.length = basis.length；h_exps 
: exps.FirstNonzeroIsNeg。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_tendsto_zero_of_firstNonzer
oIsNeg`：toFun_tendsto_zero_of_firstNonzeroIsNeg {m : UnitMonomial} {basis : Basi
s} (h_basis : WellFormedBasis basis) (h_length : m.length = basis.le…
-/
theorem toFun_tendsto_zero_of_firstNonzeroIsNeg {coef : ℝ} {exps : UnitMonomial} {basis : Basis}
    (h_basis : WellFormedBasis basis)
    (h_length : exps.length = basis.length)
    (h_exps : exps.FirstNonzeroIsNeg) :
    let t : Monomial := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul _
    (UnitMonomial.toFun_tendsto_zero_of_firstNonzeroIsNeg h_basis h_length h_exps)
  simp
/-
**Tactic.ComputeAsymptotics.Monomial.toFun_tendsto_top_of_firstNonzeroIsPos** 是 
Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Monomial`。
形式化陈述：toFun_tendsto_top_of_firstNonzeroIsPos {coef : Real} {exps : UnitMonomial}
 {basis : Basis} (h_basis : WellFormedBasis basis) (h_length : exps.length = bas
is.length) (h_coef : 0 < coef) (h_exps : exps.FirstNonzeroIsPos) : let t : Monom
ial
参数：h_basis : WellFormedBasis basis；h_length : exps.length = basis.length；h_coef 
: 0 < coef；h_exps : exps.FirstNonzeroIsPos。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_tendsto_top_of_firstNonzero
IsPos`：toFun_tendsto_top_of_firstNonzeroIsPos {m : UnitMonomial} {basis : Basis}
 (h_basis : WellFormedBasis basis) (h_length : m.length = basis.len…
-/
theorem toFun_tendsto_top_of_firstNonzeroIsPos {coef : ℝ} {exps : UnitMonomial} {basis : Basis}
    (h_basis : WellFormedBasis basis)
    (h_length : exps.length = basis.length)
    (h_coef : 0 < coef)
    (h_exps : exps.FirstNonzeroIsPos) :
    let t : Monomial := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop atTop := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul_atTop h_coef
    (UnitMonomial.toFun_tendsto_top_of_firstNonzeroIsPos h_basis h_length h_exps)
/-
**Tactic.ComputeAsymptotics.Monomial.toFun_tendsto_bot_of_firstNonzeroIsPos** 是 
Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Monomial`。
形式化陈述：toFun_tendsto_bot_of_firstNonzeroIsPos {coef : Real} {exps : UnitMonomial}
 {basis : Basis} (h_basis : WellFormedBasis basis) (h_length : exps.length = bas
is.length) (h_coef : coef < 0) (h_exps : exps.FirstNonzeroIsPos) : let t : Monom
ial
参数：h_basis : WellFormedBasis basis；h_length : exps.length = basis.length；h_coef 
: coef < 0；h_exps : exps.FirstNonzeroIsPos。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.const_mul_atTop_of_neg`：∀ {α : Type u_1} {β : Type u_2} [
inst : Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} 
  {f : β → α} {r : α}, r < …
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_tendsto_top_of_firstNonzero
IsPos`：toFun_tendsto_top_of_firstNonzeroIsPos {m : UnitMonomial} {basis : Basis}
 (h_basis : WellFormedBasis basis) (h_length : m.length = basis.len…
-/
theorem toFun_tendsto_bot_of_firstNonzeroIsPos {coef : ℝ} {exps : UnitMonomial} {basis : Basis}
    (h_basis : WellFormedBasis basis)
    (h_length : exps.length = basis.length)
    (h_coef : coef < 0)
    (h_exps : exps.FirstNonzeroIsPos) :
    let t : Monomial := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop atBot := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul_atTop_of_neg h_coef
    (UnitMonomial.toFun_tendsto_top_of_firstNonzeroIsPos h_basis h_length h_exps)
/-
**Tactic.ComputeAsymptotics.Monomial.toFun_tendsto_const_of_allZero** 是 Mathlib 
中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Monomial`。
形式化陈述：toFun_tendsto_const_of_allZero {coef : Real} {exps : UnitMonomial} {basis 
: Basis} (h_exps : exps.AllZero) : let t : Monomial
参数：h_exps : exps.AllZero。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.toFun_tendsto_one_of_allZero`：toF
un_tendsto_one_of_allZero {m : UnitMonomial} {basis : Basis} (h_allZero : AllZer
o m) : Tendsto (UnitMonomial.toFun m basis) atTop (𝓝 1)
-/
theorem toFun_tendsto_const_of_allZero {coef : ℝ} {exps : UnitMonomial} {basis : Basis}
    (h_exps : exps.AllZero) :
    let t : Monomial := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop (𝓝 coef) := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul _ (UnitMonomial.toFun_tendsto_one_of_allZero h_exps)
  simp [t]
/-
**Tactic.ComputeAsymptotics.Monomial.majorized_tail_toFun_head** 是 Mathlib 中的一个定
理，位于命名空间 `Tactic.ComputeAsymptotics.Monomial`。
形式化陈述：majorized_tail_toFun_head {t : Monomial} {basis_hd : Real -> Real} {basis_
tl : Basis} (h_length : t.unit.length = basis_tl.length) (h_basis : WellFormedBa
sis (basis_hd :: basis_tl)) : Majorized (t.toFun basis_tl) basis_hd 0
参数：h_length : t.unit.length = basis_tl.length；h_basis : WellFormedBasis (basis_h
d :: basis_tl)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Majorized.smul`：smul (h : Majorized f b exp) {
c : Real} : Majorized (c • f) b exp
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.majorized_tail_toFun_head`：majori
zed_tail_toFun_head {m : UnitMonomial} {basis_hd : Real -> Real} {basis_tl : Bas
is} (h_length : m.length = basis_tl.length) (h_basis :…
-/
theorem majorized_tail_toFun_head {t : Monomial} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h_length : t.unit.length = basis_tl.length)
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    Majorized (t.toFun basis_tl) basis_hd 0 := by
  exact Majorized.smul (UnitMonomial.majorized_tail_toFun_head h_length h_basis)
/-
**Tactic.ComputeAsymptotics.Monomial.isLittleO_of_lt_exps** 是 Mathlib 中的一个引理，位于命
名空间 `Tactic.ComputeAsymptotics.Monomial`。
形式化陈述：isLittleO_of_lt_exps {basis : Basis} {t1 t2 : Monomial} (h_basis : WellFor
medBasis basis) (h1 : t1.unit.length = basis.length) (h2 : t2.unit.length = basi
s.length) (h_coef2 : t2.coef != 0) (h_lt : t1.unit < t2.unit) : t1.toFun basis =
o[atTop] t2.toFun basis
参数：h_basis : WellFormedBasis basis；h1 : t1.unit.length = basis.length；h2 : t2.un
it.length = basis.length；h_coef2 : t2.coef != 0；h_lt : t1.unit < t2.unit。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.smul_isLittleO`：∀ {α : Type u_1} {E' : Type u_6} {F' 
: Type u_7} {R : Type u_13} {𝕜' : Type u_16} [inst : SeminormedAddCommGroup E'] 
  [inst_1 : SeminormedA…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Tactic.ComputeAsymptotics.UnitMonomial.isLittleO_of_lt`：isLittleO_of_lt 
{basis : Basis} {m1 m2 : UnitMonomial} (h_basis : WellFormedBasis basis) (h1 : m
1.length = basis.length) (h2 : m2.length = b…
-/
lemma isLittleO_of_lt_exps {basis : Basis} {t1 t2 : Monomial}
    (h_basis : WellFormedBasis basis)
    (h1 : t1.unit.length = basis.length)
    (h2 : t2.unit.length = basis.length)
    (h_coef2 : t2.coef ≠ 0)
    (h_lt : t1.unit < t2.unit) :
    t1.toFun basis =o[atTop] t2.toFun basis := by
  simp only [toFun]
  pull fun _ ↦ _
  apply Asymptotics.IsBigO.smul_isLittleO
  · simp at h_coef2
    simp
    grind
  apply UnitMonomial.isLittleO_of_lt h_basis h1 h2 h_lt
/-
**Tactic.ComputeAsymptotics.Monomial.isLittleO_of_lt_exps_left** 是 Mathlib 中的一个定
理，位于命名空间 `Tactic.ComputeAsymptotics.Monomial`。
形式化陈述：isLittleO_of_lt_exps_left {left right : Basis} {t1 t2 : Monomial} (h_basis
 : WellFormedBasis (left ++ right)) (h1 : t1.unit.length = left.length + right.l
ength) (h2 : t2.unit.length = right.length) (h_coef2 : t2.coef != 0) (h_lt : t1.
unit < List.replicate left.length 0 ++ t2.unit) : t1.toFun (left ++ right) =o[at
Top] t2.toFun right
参数：h_basis : WellFormedBasis (left ++ right)；h1 : t1.unit.length = left.length +
 right.length；h2 : t2.unit.length = right.length；h_coef2 : t2.coef != 0；h_lt : t
1.unit < List.replicate left.length 0 ++ t2.unit。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Monomial.zeros_append_toFun`：zeros_append_toFu
n (coef : Real) {exps : UnitMonomial} {left right : Basis} : let t : Monomial
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Tactic.ComputeAsymptotics.Monomial.isLittleO_of_lt_exps`：isLittleO_of_lt
_exps {basis : Basis} {t1 t2 : Monomial} (h_basis : WellFormedBasis basis) (h1 :
 t1.unit.length = basis.length) (h2 : t2.unit…
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
-/
theorem isLittleO_of_lt_exps_left {left right : Basis} {t1 t2 : Monomial}
    (h_basis : WellFormedBasis (left ++ right))
    (h1 : t1.unit.length = left.length + right.length)
    (h2 : t2.unit.length = right.length)
    (h_coef2 : t2.coef ≠ 0)
    (h_lt : t1.unit < List.replicate left.length 0 ++ t2.unit) :
    t1.toFun (left ++ right) =o[atTop] t2.toFun right := by
  obtain ⟨coef2, exps2⟩ := t2
  let t2' : Monomial := ⟨coef2, List.replicate left.length 0 ++ exps2⟩
  have : t2'.toFun (left ++ right) = Monomial.toFun ⟨coef2, exps2⟩ right :=
    Monomial.zeros_append_toFun _
  rw [← this]
  apply isLittleO_of_lt_exps h_basis <;> simpa [t2']
/-
**Tactic.ComputeAsymptotics.Monomial.isLittleO_of_lt_exps_right** 是 Mathlib 中的一个
定理，位于命名空间 `Tactic.ComputeAsymptotics.Monomial`。
形式化陈述：isLittleO_of_lt_exps_right {left right : Basis} {t1 t2 : Monomial} (h_basi
s : WellFormedBasis (left ++ right)) (h1 : t1.unit.length = left.length + right.
length) (h2 : t2.unit.length = right.length) (h_coef1 : t1.coef != 0) (h_lt : Li
st.replicate left.length 0 ++ t2.unit < t1.unit) : t2.toFun right =o[atTop] t1.t
oFun (left ++ right)
参数：h_basis : WellFormedBasis (left ++ right)；h1 : t1.unit.length = left.length +
 right.length；h2 : t2.unit.length = right.length；h_coef1 : t1.coef != 0；h_lt : L
ist.replicate left.length 0 ++ t2.unit < t1.unit。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Monomial.zeros_append_toFun`：zeros_append_toFu
n (coef : Real) {exps : UnitMonomial} {left right : Basis} : let t : Monomial
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Tactic.ComputeAsymptotics.Monomial.isLittleO_of_lt_exps`：isLittleO_of_lt
_exps {basis : Basis} {t1 t2 : Monomial} (h_basis : WellFormedBasis basis) (h1 :
 t1.unit.length = basis.length) (h2 : t2.unit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
-/
theorem isLittleO_of_lt_exps_right {left right : Basis} {t1 t2 : Monomial}
    (h_basis : WellFormedBasis (left ++ right))
    (h1 : t1.unit.length = left.length + right.length)
    (h2 : t2.unit.length = right.length)
    (h_coef1 : t1.coef ≠ 0)
    (h_lt : List.replicate left.length 0 ++ t2.unit < t1.unit) :
    t2.toFun right =o[atTop] t1.toFun (left ++ right) := by
  obtain ⟨coef2, exps2⟩ := t2
  let t2' : Monomial := ⟨coef2, List.replicate left.length 0 ++ exps2⟩
  have : t2'.toFun (left ++ right) = Monomial.toFun ⟨coef2, exps2⟩ right :=
    Monomial.zeros_append_toFun _
  rw [← this]
  apply isLittleO_of_lt_exps h_basis <;> simpa [t2']

end Monomial

end Tactic.ComputeAsymptotics

