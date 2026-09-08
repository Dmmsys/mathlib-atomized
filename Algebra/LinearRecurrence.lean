/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear recurrence

Informally, a "linear recurrence" is an assertion of the form
`∀ n : ℕ, u (n + d) = a 0 * u n + a 1 * u (n+1) + ... + a (d-1) * u (n+d-1)`,
where `u` is a sequence, `d` is the *order* of the recurrence and the `a i`
are its *coefficients*.

In this file, we define the structure `LinearRecurrence` so that
`LinearRecurrence.mk d a` represents the above relation, and we call
a sequence `u` which verifies it a *solution* of the linear recurrence.

We prove a few basic lemmas about this concept, such as :

* the space of solutions is a submodule of `(ℕ → α)` (i.e a vector space if `α`
  is a field)
* the function that maps a solution `u` to its first `d` terms builds a `LinearEquiv`
  between the solution space and `Fin d → α`, aka `α ^ d`. As a consequence, two
  solutions are equal if and only if their first `d` terms are equal.
* a geometric sequence `q ^ n` is solution iff `q` is a root of a particular polynomial,
  which we call the *characteristic polynomial* of the recurrence

Of course, although we can inductively generate solutions (cf `mkSol`), the
interesting part would be to determine closed-forms for the solutions.
This is currently *not implemented*, as we are waiting for definition and
properties of eigenvalues and eigenvectors.

-/

@[expose] public section

noncomputable section

open Finset

open Polynomial

/-- A "linear recurrence relation" over a commutative semiring is given by its
  order `n` and `n` coefficients. -/
@[wikidata Q364089]
/-
**LinearRecurrence** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [CommSemiring R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A "linear recurrence relation" over a commutative semiring is given by its
  order `n` and `n` coefficients.
-/
structure LinearRecurrence (R : Type*) [CommSemiring R] where
  /-- Order of the linear recurrence -/
  order : ℕ
  /-- Coefficients of the linear recurrence -/
  coeffs : Fin order → R
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type*) [CommSemiring R] : Inhabited (LinearRecurrence R) :=
  ⟨⟨0, default⟩⟩

namespace LinearRecurrence

section CommSemiring

variable {R : Type*} [CommSemiring R] (E : LinearRecurrence R)

/-- We say that a sequence `u` is solution of `LinearRecurrence order coeffs` when we have
  `u (n + order) = ∑ i : Fin order, coeffs i * u (n + i)` for any `n`. -/
/-
**LinearRecurrence.IsSolution** 是 Mathlib 中的一个定义，位于命名空间 `LinearRecurrence`。
形式化陈述：IsSolution (u : Nat -> R)
参数：u : Nat -> R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a sequence `u` is solution of `LinearRecurrence order coeffs` when w
e have
  `u (n + order) = ∑ i : Fin order, coeffs i * u (n + i)` for any `n`.
-/
def IsSolution (u : ℕ → R) :=
  ∀ n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i)

/-- A solution of a `LinearRecurrence` which satisfies certain initial conditions.
  We will prove this is the only such solution. -/
/-
**LinearRecurrence.mkSol** 是 Mathlib 中的一个定义，位于命名空间 `LinearRecurrence`。
形式化陈述：mkSol (init : Fin E.order -> R) : Nat -> R | n => if h : n < E.order then 
init ⟨n, h⟩ else ∑ k : Fin E.order, have _ : n - E.order + k < n
参数：init : Fin E.order -> R。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A solution of a `LinearRecurrence` which satisfies certain initial conditions.
  We will prove this is the only such solution.
-/
def mkSol (init : Fin E.order → R) : ℕ → R
  | n =>
    if h : n < E.order then init ⟨n, h⟩
    else
      ∑ k : Fin E.order,
        have _ : n - E.order + k < n := by lia
        E.coeffs k * mkSol init (n - E.order + k)

/-- `E.mkSol` indeed gives solutions to `E`. -/
/-
**LinearRecurrence.is_sol_mkSol** 是 Mathlib 中的一个定理，位于命名空间 `LinearRecurrence`。
形式化陈述：is_sol_mkSol (init : Fin E.order -> R) : E.IsSolution (E.mkSol init)
参数：init : Fin E.order -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearRecurrence.mkSol.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (E
 : LinearRecurrence R) (init : Fin E.order → R) (x : ℕ),   E.mkSol init x =     
if h : x < E.orde…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`E.mkSol` indeed gives solutions to `E`.
-/
theorem is_sol_mkSol (init : Fin E.order → R) : E.IsSolution (E.mkSol init) := by
  intro n
  rw [mkSol]
  simp

/-- `E.mkSol init`'s first `E.order` terms are `init`. -/
/-
**LinearRecurrence.mkSol_eq_init** 是 Mathlib 中的一个定理，位于命名空间 `LinearRecurrence`。
形式化陈述：mkSol_eq_init (init : Fin E.order -> R) : forall n : Fin E.order, E.mkSol 
init n = init n
参数：init : Fin E.order -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearRecurrence.mkSol.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (E
 : LinearRecurrence R) (init : Fin E.order → R) (x : ℕ),   E.mkSol init x =     
if h : x < E.orde…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Fin.mk_val`：∀ {n : ℕ} (i : Fin n), ⟨↑i, ⋯⟩ = i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`E.mkSol init`'s first `E.order` terms are `init`.
-/
theorem mkSol_eq_init (init : Fin E.order → R) : ∀ n : Fin E.order, E.mkSol init n = init n := by
  intro n
  rw [mkSol]
  simp only [n.is_lt, dif_pos, Fin.mk_val]

/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `∀ n, u n = E.mkSol init n`. -/
/-
**LinearRecurrence.eq_mk_of_is_sol_of_eq_init** 是 Mathlib 中的一个定理，位于命名空间 `LinearR
ecurrence`。
形式化陈述：eq_mk_of_is_sol_of_eq_init {u : Nat -> R} {init : Fin E.order -> R} (h : E
.IsSolution u) (heq : forall n : Fin E.order, u n = init n) : forall n, u n = E.
mkSol init n
参数：h : E.IsSolution u；heq : forall n : Fin E.order, u n = init n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearRecurrence.mkSol.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (E
 : LinearRecurrence R) (init : Fin E.order → R) (x : ℕ),   E.mkSol init x =     
if h : x < E.orde…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Lean.Omega.Int.ofNat_sub_dichotomy`：∀ {a b : ℕ}, b ≤ a ∧ ↑(a - b) = ↑a -
 ↑b ∨ a < b ∧ ↑(a - b) = 0
· 使用定理 `Lean.Omega.Constraint.not_sat'_of_isImpossible`：∀ {c : Omega.Constraint}
, c.isImpossible = true → ∀ {x y : Omega.Coeffs}, ¬c.sat' x y = true
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Lean.Omega.Constraint.combine_sat'`：∀ {s t : Omega.Constraint} {x y : Om
ega.Coeffs}, s.sat' x y = true → t.sat' x y = true → (s.combine t).sat' x y = tr
ue
· 使用定理 `Lean.Omega.Constraint.addInequality_sat`：∀ {c : ℤ} {x y : Omega.Coeffs},
 c + x.dot y ≥ 0 → { lowerBound := some (-c), upperBound := none }.sat' x y = tr
ue
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Int.sub_nonneg_of_le`：∀ {a b : ℤ}, b ≤ a → 0 ≤ a - b
· 使用定理 `Int.add_one_le_of_lt`：∀ {a b : ℤ}, a < b → a + 1 ≤ b
· 使用定理 `Lean.Omega.Int.ofNat_lt_of_lt`：∀ {x y : ℕ}, x < y → ↑x < ↑y
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Lean.Omega.Int.sub_congr`：∀ {a b c d : ℤ}, a = b → c = d → a - c = b - d
· 使用定理 `Lean.Omega.LinearCombo.coordinate_eval_1`：∀ {a0 a1 : ℤ} {t : List ℤ}, (O
mega.LinearCombo.coordinate 1).eval (Omega.Coeffs.ofList (a0 :: a1 :: t)) = a1
· 使用定理 `Lean.Omega.Int.add_congr`：∀ {a b c d : ℤ}, a = b → c = d → a + c = b + d
· 使用定理 `Lean.Omega.LinearCombo.coordinate_eval_3`：∀ {a0 a1 a2 a3 : ℤ} {t : List 
ℤ},   (Omega.LinearCombo.coordinate 3).eval (Omega.Coeffs.ofList (a0 :: a1 :: a2
 :: a3 :: t)) = a3
· 使用定理 `Lean.Omega.LinearCombo.add_eval`：∀ (l₁ l₂ : Omega.LinearCombo) (v : Omeg
a.Coeffs), (l₁ + l₂).eval v = l₁.eval v + l₂.eval v
· 使用定理 `Lean.Omega.LinearCombo.sub_eval`：∀ (l₁ l₂ : Omega.LinearCombo) (v : Omeg
a.Coeffs), (l₁ - l₂).eval v = l₁.eval v - l₂.eval v
· 使用定理 `Lean.Omega.combo_sat'`：∀ (s t : Omega.Constraint) (a : ℤ) (x : Omega.Coe
ffs) (b : ℤ) (y v : Omega.Coeffs),   s.sat' x v = true → t.sat' y v = true → (Om
ega.Constra…
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `∀ n, u n = E.mkSol init n`.
-/
theorem eq_mk_of_is_sol_of_eq_init {u : ℕ → R} {init : Fin E.order → R} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : ∀ n, u n = E.mkSol init n := by
  intro n
  rw [mkSol]
  split_ifs with h'
  · exact mod_cast heq ⟨n, h'⟩
  · dsimp only
    rw [← tsub_add_cancel_of_le (le_of_not_gt h'), h (n - E.order)]
    congr with k
    rw [eq_mk_of_is_sol_of_eq_init h heq (n - E.order + k)]
    simp

/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `u = E.mkSol init`. This proves that `E.mkSol init` is the only solution
  of `E` whose first `E.order` values are given by `init`. -/
/-
**LinearRecurrence.eq_mk_of_is_sol_of_eq_init'** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Recurrence`。
形式化陈述：eq_mk_of_is_sol_of_eq_init' {u : Nat -> R} {init : Fin E.order -> R} (h : 
E.IsSolution u) (heq : forall n : Fin E.order, u n = init n) : u = E.mkSol init
参数：h : E.IsSolution u；heq : forall n : Fin E.order, u n = init n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearRecurrence.eq_mk_of_is_sol_of_eq_init`：eq_mk_of_is_sol_of_eq_init 
{u : Nat -> R} {init : Fin E.order -> R} (h : E.IsSolution u) (heq : forall n : 
Fin E.order, u n = init n) : fora…

--- 原说明 ---
If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `u = E.mkSol init`. This proves that `E.mkSol init` is the only solution
  of `E` whose first `E.order` values are given by `init`.
-/
theorem eq_mk_of_is_sol_of_eq_init' {u : ℕ → R} {init : Fin E.order → R} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : u = E.mkSol init :=
  funext (E.eq_mk_of_is_sol_of_eq_init h heq)

/-- The space of solutions of `E`, as a `Submodule` over `R` of the module `ℕ → R`. -/
/-
**LinearRecurrence.solSpace** 是 Mathlib 中的一个定义，位于命名空间 `LinearRecurrence`。
形式化陈述：solSpace : Submodule R (Nat -> R) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of solutions of `E`, as a `Submodule` over `R` of the module `ℕ → R`.
-/
def solSpace : Submodule R (ℕ → R) where
  carrier := { u | E.IsSolution u }
  zero_mem' n := by simp
  add_mem' {u v} hu hv n := by simp [mul_add, sum_add_distrib, hu n, hv n]
  smul_mem' a u hu n := by simp [hu n, mul_sum]; ac_rfl

/-- Defining property of the solution space : `u` is a solution
  iff it belongs to the solution space. -/
/-
**LinearRecurrence.is_sol_iff_mem_solSpace** 是 Mathlib 中的一个定理，位于命名空间 `LinearRecu
rrence`。
形式化陈述：is_sol_iff_mem_solSpace (u : Nat -> R) : E.IsSolution u ↔ u in E.solSpace
参数：u : Nat -> R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Defining property of the solution space : `u` is a solution
  iff it belongs to the solution space.
-/
theorem is_sol_iff_mem_solSpace (u : ℕ → R) : E.IsSolution u ↔ u ∈ E.solSpace :=
  Iff.rfl

/-- The function that maps a solution `u` of `E` to its first
  `E.order` terms as a `LinearEquiv`. -/
/-
**LinearRecurrence.toInit** 是 Mathlib 中的一个定义，位于命名空间 `LinearRecurrence`。
形式化陈述：toInit : E.solSpace ≃ₗ[R] Fin E.order -> R where toFun u x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearRecurrence.is_sol_mkSol`：is_sol_mkSol (init : Fin E.order -> R) : 
E.IsSolution (E.mkSol init)

--- 原说明 ---
The function that maps a solution `u` of `E` to its first
  `E.order` terms as a `LinearEquiv`.
-/
def toInit : E.solSpace ≃ₗ[R] Fin E.order → R where
  toFun u x := (u : ℕ → R) x
  map_add' u v := by
    ext
    simp
  map_smul' a u := by
    ext
    simp
  invFun u := ⟨E.mkSol u, E.is_sol_mkSol u⟩
  left_inv u := by ext n; symm; apply E.eq_mk_of_is_sol_of_eq_init u.2; intro k; rfl
  right_inv u := funext_iff.mpr fun n ↦ E.mkSol_eq_init u n
/-
**LinearRecurrence.mkSol_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearRecurrence`。
形式化陈述：mkSol_injective : E.mkSol.Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem mkSol_injective : E.mkSol.Injective :=
  Subtype.val_injective.comp E.toInit.symm.injective

/-- A basis of the solution space given by solutions whose initial conditions are the standard basis
vectors -/
/-
**LinearRecurrence.basis** 是 Mathlib 中的一个定义，位于命名空间 `LinearRecurrence`。
形式化陈述：basis : Module.Basis (Fin E.order) R E.solSpace
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A basis of the solution space given by solutions whose initial conditions are th
e standard basis
vectors
-/
def basis : Module.Basis (Fin E.order) R E.solSpace :=
  .ofEquivFun E.toInit

/-- The coordinates of a solution in the basis are its first `E.order` values -/
/-
**LinearRecurrence.repr_basis_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearRecurrence`。
形式化陈述：repr_basis_eq (u : E.solSpace) : E.basis.repr u = .ofSupportFinite (u ∘ Fi
n.val) (Set.toFinite _)
参数：u : E.solSpace。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coordinates of a solution in the basis are its first `E.order` values
-/
theorem repr_basis_eq (u : E.solSpace) :
    E.basis.repr u = .ofSupportFinite (u ∘ Fin.val) (Set.toFinite _) :=
  rfl

/-- The nth coordinate of a solution in the basis equals its nth value -/
@[simp]
/-
**LinearRecurrence.repr_basis_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearRecurrence`
。
形式化陈述：repr_basis_apply (u : E.solSpace) (n : Fin E.order) : E.basis.repr u n = u
.val n
参数：u : E.solSpace；n : Fin E.order。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nth coordinate of a solution in the basis equals its nth value
-/
theorem repr_basis_apply (u : E.solSpace) (n : Fin E.order) : E.basis.repr u n = u.val n :=
  rfl

/-- Two solutions are equal iff their initial conditions are equal. -/
/-
**LinearRecurrence.eq_iff_eqOn_range_order** 是 Mathlib 中的一个定理，位于命名空间 `LinearRecu
rrence`。
形式化陈述：eq_iff_eqOn_range_order (u v : Nat -> R) (hu : E.IsSolution u) (hv : E.IsS
olution v) : u = v ↔ Set.EqOn u v ↑(range E.order)
参数：u v : Nat -> R；hu : E.IsSolution u；hv : E.IsSolution v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearRecurrence.is_sol_iff_mem_solSpace`：is_sol_iff_mem_solSpace (u : N
at -> R) : E.IsSolution u ↔ u in E.solSpace
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.prop`：∀ {n : ℕ} (a : Fin n), ↑a < n

--- 原说明 ---
Two solutions are equal iff their initial conditions are equal.
-/
theorem eq_iff_eqOn_range_order (u v : ℕ → R) (hu : E.IsSolution u) (hv : E.IsSolution v) :
    u = v ↔ Set.EqOn u v ↑(range E.order) := by
  replace hu : u ∈ E.solSpace := (is_sol_iff_mem_solSpace _ _).mp hu
  replace hv : v ∈ E.solSpace := (is_sol_iff_mem_solSpace _ _).mp hv
  rw [← Subtype.mk.injEq u hu v hv, ← E.basis.repr.injective.eq_iff]
  constructor
  · exact fun h n hn ↦ congr($h ⟨n, Finset.mem_range.mp hn⟩)
  · exact fun h ↦ Finsupp.ext fun n ↦ h <| Finset.mem_range.mpr n.prop

@[deprecated (since := "2026-04-16")] alias sol_eq_of_eq_init := eq_iff_eqOn_range_order

/-! `E.tupleSucc` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
where `n := E.order`. This operation is quite useful for determining closed-form
solutions of `E`. -/

/-- `E.tupleSucc` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
where `n := E.order`. -/
/-
**LinearRecurrence.tupleSucc** 是 Mathlib 中的一个定义，位于命名空间 `LinearRecurrence`。
形式化陈述：tupleSucc : (Fin E.order -> R) ->ₗ[R] Fin E.order -> R where toFun X i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`E.tupleSucc` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`
,
where `n := E.order`.
-/
def tupleSucc : (Fin E.order → R) →ₗ[R] Fin E.order → R where
  toFun X i := if h : (i : ℕ) + 1 < E.order then X ⟨i + 1, h⟩ else ∑ i, E.coeffs i * X i
  map_add' x y := by
    ext i
    split_ifs with h <;> simp [h, mul_add, sum_add_distrib]
  map_smul' x y := by
    ext i
    split_ifs with h <;>
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, h, ↓reduceDIte, mul_sum]
    exact sum_congr rfl fun x _ ↦ by ac_rfl

end CommSemiring

section StrongRankCondition

-- note: `StrongRankCondition` is the same as `Nontrivial` on `CommRing`s, but that result,
-- `commRing_strongRankCondition`, is in a much later file.
variable {R : Type*} [CommRing R] [StrongRankCondition R] (E : LinearRecurrence R)

/-- The dimension of `E.solSpace` is `E.order`. -/
/-
**LinearRecurrence.solSpace_rank** 是 Mathlib 中的一个定理，位于命名空间 `LinearRecurrence`。
形式化陈述：solSpace_rank : Module.rank R E.solSpace = E.order
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_eq_card_basis`：rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Bas
is ι R M) : Module.rank R M = Fintype.card ι
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The dimension of `E.solSpace` is `E.order`.
-/
theorem solSpace_rank : Module.rank R E.solSpace = E.order := by
  simp [rank_eq_card_basis E.basis]

end StrongRankCondition

section CommRing

variable {R : Type*} [CommRing R] (E : LinearRecurrence R)

/-- The characteristic polynomial of `E` is
`X ^ E.order - ∑ i : Fin E.order, (E.coeffs i) * X ^ i`. -/
/-
**LinearRecurrence.charPoly** 是 Mathlib 中的一个定义，位于命名空间 `LinearRecurrence`。
形式化陈述：charPoly : R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The characteristic polynomial of `E` is
`X ^ E.order - ∑ i : Fin E.order, (E.coeffs i) * X ^ i`.
-/
def charPoly : R[X] :=
  Polynomial.monomial E.order 1 - ∑ i : Fin E.order, Polynomial.monomial i (E.coeffs i)

@[simp]
/-
**LinearRecurrence.charPoly_degree_eq_order** 是 Mathlib 中的一个定理，位于命名空间 `LinearRec
urrence`。
形式化陈述：charPoly_degree_eq_order [Nontrivial R] : (charPoly E).degree = E.order
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearRecurrence.charPoly.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (E 
: LinearRecurrence R),   E.charPoly = (Polynomial.monomial E.order) 1 - ∑ i, (Po
lynomial.monomial ↑i…
· 使用定理 `Polynomial.degree_sub_eq_left_of_degree_lt`：degree_sub_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p - q) = degree p
· 使用定理 `Polynomial.degree_monomial`：degree_monomial (n : Nat) (ha : a != 0) : de
gree (monomial n a) = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.degree_sum_fin_lt`：degree_sum_fin_lt {n : Nat} (f : Fin n -> 
R) : degree (∑ i : Fin n, C (f i) * X ^ (i : Nat)) < n
-/
theorem charPoly_degree_eq_order [Nontrivial R] : (charPoly E).degree = E.order := by
  rw [charPoly, degree_sub_eq_left_of_degree_lt]
    <;> rw [degree_monomial E.order one_ne_zero]
  simp_rw [← C_mul_X_pow_eq_monomial]
  exact degree_sum_fin_lt E.coeffs
/-
**LinearRecurrence.charPoly_monic** 是 Mathlib 中的一个定理，位于命名空间 `LinearRecurrence`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (E : LinearRecurrence R), E.charPoly.
Monic
参数：E : LinearRecurrence R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `LinearRecurrence.charPoly_degree_eq_order`：charPoly_degree_eq_order [Non
trivial R] : (charPoly E).degree = E.order
· 使用定理 `LinearRecurrence.charPoly.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (E 
: LinearRecurrence R),   E.charPoly = (Polynomial.monomial E.order) 1 - ∑ i, (Po
lynomial.monomial ↑i…
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_monomial_same`：coeff_monomial_same (n : Nat) (c : R) : 
(monomial n c).coeff n = c
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `sub_eq_self`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = a ↔
 b = 0
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `Polynomial.degree_monomial_le`：degree_monomial_le (n : Nat) (a : R) : de
gree (monomial n a) <= n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem charPoly_monic : charPoly E |>.Monic := by
  nontriviality R
  rw [Monic, leadingCoeff, natDegree_eq_of_degree_eq_some <| charPoly_degree_eq_order _, charPoly,
    coeff_sub, coeff_monomial_same, finsetSum_coeff, sub_eq_self]
  refine sum_eq_zero fun _ _ ↦ coeff_eq_zero_of_degree_lt ?_
  grw [degree_monomial_le]
  simp

/-- The geometric sequence `q^n` is a solution of `E` iff
  `q` is a root of `E`'s characteristic polynomial. -/
/-
**LinearRecurrence.geom_sol_iff_root_charPoly** 是 Mathlib 中的一个定理，位于命名空间 `LinearR
ecurrence`。
形式化陈述：geom_sol_iff_root_charPoly (q : R) : (E.IsSolution fun n => q ^ n) ↔ E.cha
rPoly.IsRoot q
参数：q : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearRecurrence.charPoly.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (E 
: LinearRecurrence R),   E.charPoly = (Polynomial.monomial E.order) 1 - ∑ i, (Po
lynomial.monomial ↑i…
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `Polynomial.eval.eq_1`：∀ {R : Type u} [inst : Semiring R] (x : R) (p : Po
lynomial R), Polynomial.eval x p = Polynomial.eval₂ (RingHom.id R) x p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval₂_sub`：eval₂_sub {S} [Ring S] (f : R ->+* S) {x : S} : (p
 - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval₂_monomial`：eval₂_monomial {n : Nat} {r : R} : (monomial 
n r).eval₂ f x = f r * x ^ n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.eval₂_finsetSum`：eval₂_finsetSum (s : Finset ι) (g : ι -> R[X
]) (x : S) : (∑ i in s, g i).eval₂ f x = ∑ i in s, (g i).eval₂ f x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
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
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The geometric sequence `q^n` is a solution of `E` iff
  `q` is a root of `E`'s characteristic polynomial.
-/
theorem geom_sol_iff_root_charPoly (q : R) :
    (E.IsSolution fun n ↦ q ^ n) ↔ E.charPoly.IsRoot q := by
  rw [charPoly, Polynomial.IsRoot.def, Polynomial.eval]
  simp only [Polynomial.eval₂_finsetSum, one_mul, RingHom.id_apply, Polynomial.eval₂_monomial,
    Polynomial.eval₂_sub]
  constructor
  · intro h
    simpa [sub_eq_zero] using h 0
  · intro h n
    simp only [pow_add, sub_eq_zero.mp h, mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring

end CommRing

end LinearRecurrence

