/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Evaluating polynomials and scalar multiplication

## Main results
* `eval₂_smul`, `eval_smul`, `map_smul`, `comp_smul`: the functions preserve scalar multiplication
* `Polynomial.leval`: `Polynomial.eval` as linear map

-/

@[expose] public section

noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

section

variable [Semiring S]
variable (f : R →+* S) (x : S)

@[simp]
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_smul (g : R →+* S) (p : R[X]) (x : S) {s : R} :
    eval₂ g x (s • p) = g s * eval₂ g x p := by
  have A : p.natDegree < p.natDegree.succ := Nat.lt_succ_self _
  have B : (s • p).natDegree < p.natDegree.succ := (natDegree_smul_le _ _).trans_lt A
  rw [eval₂_eq_sum, eval₂_eq_sum, sum_over_range' _ _ _ A, sum_over_range' _ _ _ B] <;>
    simp [mul_sum, mul_assoc]

end

section Eval

variable {x : R}

@[simp]
/-
**Polynomial.eval_smul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_smul [SMulZeroClass S R] [IsScalarTower S R R] (s : S) (p : R[X]) (x 
: R) : (s • p).eval x = s • p.eval x
参数：s : S；p : R[X]；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `Polynomial.eval.eq_1`：∀ {R : Type u} [inst : Semiring R] (x : R) (p : Po
lynomial R), Polynomial.eval x p = Polynomial.eval₂ (RingHom.id R) x p
· 使用定理 `Polynomial.eval₂_smul`：eval₂_smul (g : R ->+* S) (p : R[X]) (x : S) {s :
 R} : eval₂ g x (s • p) = g s * eval₂ g x p
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
· 使用引理 `smul_one_mul`：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTow
er M N N] (x : M) (y : N) : x • (1 : N) * y = x • y
· 使用定理 `Polynomial.eval₂_id`：eval₂_id : eval₂ (RingHom.id _) x p = p.eval x
-/
theorem eval_smul [SMulZeroClass S R] [IsScalarTower S R R] (s : S) (p : R[X])
    (x : R) : (s • p).eval x = s • p.eval x := by
  rw [← smul_one_smul R s p, eval, eval₂_smul, RingHom.id_apply, smul_one_mul, eval₂_id]

/-- `Polynomial.eval` as linear map -/
@[simps]
/-
**Polynomial.leval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：leval {R : Type*} [Semiring R] (r : R) : R[X] ->ₗ[R] R where toFun f
参数：r : R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x

--- 原说明 ---
`Polynomial.eval` as linear map
-/
def leval {R : Type*} [Semiring R] (r : R) : R[X] →ₗ[R] R where
  toFun f := f.eval r
  map_add' _f _g := eval_add
  map_smul' c f := eval_smul c f r

end Eval

section Comp

@[simp]
/-
**Polynomial.smul_comp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smul_comp [SMulZeroClass S R] [IsScalarTower S R R] (s : S) (p q : R[X]) :
 (s • p).comp q = s • p.comp q
参数：s : S；p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `Polynomial.comp.eq_1`：∀ {R : Type u} [inst : Semiring R] (p q : Polynomi
al R), p.comp q = Polynomial.eval₂ Polynomial.C q p
· 使用定理 `Polynomial.eval₂_smul`：eval₂_smul (g : R ->+* S) (p : R[X]) (x : S) {s :
 R} : eval₂ g x (s • p) = g s * eval₂ g x p
· 使用定理 `Polynomial.smul_eq_C_mul`：smul_eq_C_mul (a : R) : a • p = C a * p
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem smul_comp [SMulZeroClass S R] [IsScalarTower S R R] (s : S) (p q : R[X]) :
    (s • p).comp q = s • p.comp q := by
  rw [← smul_one_smul R s p, comp, comp, eval₂_smul, ← smul_eq_C_mul, smul_assoc, one_smul]

end Comp

section Map

variable [Semiring S]
variable (f : R →+* S)

@[simp]
/-
**Polynomial.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p : Polynomial R} [inst_1
 : Semiring S] (f : R →+* S) (r : R),   Polynomial.map f (r • p) = f r • Polynom
ial.map f p
参数：f : R →+* S；r : R；r • p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map.eq_1`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S),   Polynomial.map f = Polynomial.eval₂ (Polynom
ial.C.com…
· 使用定理 `Polynomial.eval₂_smul`：eval₂_smul (g : R ->+* S) (p : R[X]) (x : S) {s :
 R} : eval₂ g x (s • p) = g s * eval₂ g x p
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `Polynomial.C_mul'`：C_mul' (a : R) (f : R[X]) : C a * f = a • f
-/
protected theorem map_smul (r : R) : (r • p).map f = f r • p.map f := by
  rw [map, eval₂_smul, RingHom.comp_apply, C_mul']

end Map

end Semiring

end Polynomial

