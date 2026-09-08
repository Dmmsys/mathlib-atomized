/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Bimodules

One frequently encounters situations in which several sets of scalars act on a single space, subject
to compatibility condition(s). A distinguished instance of this is the theory of bimodules: one has
two rings `R`, `S` acting on an additive group `M`, with `R` acting covariantly ("on the left")
and `S` acting contravariantly ("on the right"). The compatibility condition is just:
`(r • m) • s = r • (m • s)` for all `r : R`, `s : S`, `m : M`.

This situation can be set up in Mathlib as:
```lean
variable (R S M : Type*) [Ring R] [Ring S]
variable [AddCommGroup M] [Module R M] [Module Sᵐᵒᵖ M] [SMulCommClass R Sᵐᵒᵖ M]
```
The key fact is:
```lean
example : Module (R ⊗[ℕ] Sᵐᵒᵖ) M := TensorProduct.Algebra.module
```
Note that the corresponding result holds for the canonically isomorphic ring `R ⊗[ℤ] Sᵐᵒᵖ` but it is
preferable to use the `R ⊗[ℕ] Sᵐᵒᵖ` instance since it works without additive inverses.

Bimodules are thus just a special case of `Module`s and most of their properties follow from the
theory of `Module`s. In particular a two-sided Submodule of a bimodule is simply a term of type
`Submodule (R ⊗[ℕ] Sᵐᵒᵖ) M`.

This file is a place to collect results which are specific to bimodules.

## Main definitions

* `Subbimodule.mk`
* `Subbimodule.smul_mem`
* `Subbimodule.smul_mem'`
* `Subbimodule.toSubmodule`
* `Subbimodule.toSubmodule'`

## Implementation details

For many definitions and lemmas it is preferable to set things up without opposites, i.e., as:
`[Module S M] [SMulCommClass R S M]` rather than `[Module Sᵐᵒᵖ M] [SMulCommClass R Sᵐᵒᵖ M]`.
The corresponding results for opposites then follow automatically and do not require taking
advantage of the fact that `(Sᵐᵒᵖ)ᵐᵒᵖ` is defeq to `S`.

## TODO

Develop the theory of two-sided ideals, which have type `Submodule (R ⊗[ℕ] Rᵐᵒᵖ) R`.

-/

@[expose] public section


open TensorProduct

attribute [local instance] TensorProduct.Algebra.module

namespace Subbimodule

section Algebra

variable {R A B M : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [Semiring A] [Semiring B] [Module A M] [Module B M]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R A M] [IsScalarTower R B M]
variable [SMulCommClass A B M]

/-- A constructor for a subbimodule which demands closure under the two sets of scalars
individually, rather than jointly via their tensor product.

Note that `R` plays no role but it is convenient to make this generalisation to support the cases
`R = ℕ` and `R = ℤ` which both show up naturally. See also `Subbimodule.baseChange`. -/
@[simps]
/-
**Subbimodule.mk** 是 Mathlib 中的一个定义，位于命名空间 `Subbimodule`。
形式化陈述：mk (p : AddSubmonoid M) (hA : forall (a : A) {m : M}, m in p -> a • m in p
) (hB : forall (b : B) {m : M}, m in p -> b • m in p) : Submodule (A otimes[R] B
) M
参数：p : AddSubmonoid M；hA : forall (a : A) {m : M}, m in p -> a • m in p；hB : for
all (b : B) {m : M}, m in p -> b • m in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for a subbimodule which demands closure under the two sets of scal
ars
individually, rather than jointly via their tensor product.

Note that `R` plays no role but it is convenient to make this generalisation to 
support the cases
`R = ℕ` and `R = ℤ` which both show up naturally. See also `Subbimodule.baseChan
ge`.
-/
def mk (p : AddSubmonoid M) (hA : ∀ (a : A) {m : M}, m ∈ p → a • m ∈ p)
    (hB : ∀ (b : B) {m : M}, m ∈ p → b • m ∈ p) : Submodule (A ⊗[R] B) M :=
  { p with
    carrier := p
    smul_mem' := fun ab m =>
      TensorProduct.induction_on ab (fun _ => by simp only [zero_smul, SetLike.mem_coe, zero_mem])
        (fun a b hm => by simpa only [TensorProduct.Algebra.smul_def] using! hA a (hB b hm))
        fun z w hz hw hm => by simpa only [add_smul] using! p.add_mem (hz hm) (hw hm) }
/-
**Subbimodule.smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subbimodule`。
形式化陈述：smul_mem (p : Submodule (A otimes[R] B) M) (a : A) {m : M} (hm : m in p) :
 a • m in p
参数：p : Submodule (A otimes[R] B) M；a : A；hm : m in p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem smul_mem (p : Submodule (A ⊗[R] B) M) (a : A) {m : M} (hm : m ∈ p) : a • m ∈ p := by
  suffices a • m = a ⊗ₜ[R] (1 : B) • m by exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]
/-
**Subbimodule.smul_mem'** 是 Mathlib 中的一个定理，位于命名空间 `Subbimodule`。
形式化陈述：smul_mem' (p : Submodule (A otimes[R] B) M) (b : B) {m : M} (hm : m in p) 
: b • m in p
参数：p : Submodule (A otimes[R] B) M；b : B；hm : m in p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem smul_mem' (p : Submodule (A ⊗[R] B) M) (b : B) {m : M} (hm : m ∈ p) : b • m ∈ p := by
  suffices b • m = (1 : A) ⊗ₜ[R] b • m by exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]

/-- If `A` and `B` are also `Algebra`s over yet another set of scalars `S` then we may "base change"
from `R` to `S`. -/
@[simps!]
/-
**Subbimodule.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `Subbimodule`。
形式化陈述：baseChange (S : Type*) [CommSemiring S] [Module S M] [Algebra S A] [Algebr
a S B] [IsScalarTower S A M] [IsScalarTower S B M] (p : Submodule (A otimes[R] B
) M) : Submodule (A otimes[S] B) M
参数：S : Type*；p : Submodule (A otimes[R] B) M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subbimodule.smul_mem`：smul_mem (p : Submodule (A otimes[R] B) M) (a : A)
 {m : M} (hm : m in p) : a • m in p
· 使用定理 `Subbimodule.smul_mem'`：smul_mem' (p : Submodule (A otimes[R] B) M) (b : 
B) {m : M} (hm : m in p) : b • m in p

--- 原说明 ---
If `A` and `B` are also `Algebra`s over yet another set of scalars `S` then we m
ay "base change"
from `R` to `S`.
-/
def baseChange (S : Type*) [CommSemiring S] [Module S M] [Algebra S A] [Algebra S B]
    [IsScalarTower S A M] [IsScalarTower S B M] (p : Submodule (A ⊗[R] B) M) :
    Submodule (A ⊗[S] B) M :=
  mk p.toAddSubmonoid (smul_mem p) (smul_mem' p)

/-- Forgetting the `B` action, a `Submodule` over `A ⊗[R] B` is just a `Submodule` over `A`. -/
@[simps]
/-
**Subbimodule.toSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Subbimodule`。
形式化陈述：toSubmodule (p : Submodule (A otimes[R] B) M) : Submodule A M
参数：p : Submodule (A otimes[R] B) M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subbimodule.smul_mem`：smul_mem (p : Submodule (A otimes[R] B) M) (a : A)
 {m : M} (hm : m in p) : a • m in p

--- 原说明 ---
Forgetting the `B` action, a `Submodule` over `A ⊗[R] B` is just a `Submodule` o
ver `A`.
-/
def toSubmodule (p : Submodule (A ⊗[R] B) M) : Submodule A M :=
  { p with
    carrier := p
    smul_mem' := smul_mem p }

/-- Forgetting the `A` action, a `Submodule` over `A ⊗[R] B` is just a `Submodule` over `B`. -/
@[simps]
/-
**Subbimodule.toSubmodule'** 是 Mathlib 中的一个定义，位于命名空间 `Subbimodule`。
形式化陈述：toSubmodule' (p : Submodule (A otimes[R] B) M) : Submodule B M
参数：p : Submodule (A otimes[R] B) M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subbimodule.smul_mem'`：smul_mem' (p : Submodule (A otimes[R] B) M) (b : 
B) {m : M} (hm : m in p) : b • m in p

--- 原说明 ---
Forgetting the `A` action, a `Submodule` over `A ⊗[R] B` is just a `Submodule` o
ver `B`.
-/
def toSubmodule' (p : Submodule (A ⊗[R] B) M) : Submodule B M :=
  { p with
    carrier := p
    smul_mem' := smul_mem' p }

end Algebra

section Ring

variable (R S M : Type*) [Ring R] [Ring S]
variable [AddCommGroup M] [Module R M] [Module S M] [SMulCommClass R S M]

/-- A `Submodule` over `R ⊗[ℕ] S` is naturally also a `Submodule` over the canonically-isomorphic
ring `R ⊗[ℤ] S`. -/
@[simps!]
/-
**Subbimodule.toSubbimoduleInt** 是 Mathlib 中的一个定义，位于命名空间 `Subbimodule`。
形式化陈述：toSubbimoduleInt (p : Submodule (R otimes[Nat] S) M) : Submodule (R otimes
[Int] S) M
参数：p : Submodule (R otimes[Nat] S) M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Submodule` over `R ⊗[ℕ] S` is naturally also a `Submodule` over the canonical
ly-isomorphic
ring `R ⊗[ℤ] S`.
-/
def toSubbimoduleInt (p : Submodule (R ⊗[ℕ] S) M) : Submodule (R ⊗[ℤ] S) M :=
  baseChange ℤ p

/-- A `Submodule` over `R ⊗[ℤ] S` is naturally also a `Submodule` over the canonically-isomorphic
ring `R ⊗[ℕ] S`. -/
@[simps!]
/-
**Subbimodule.toSubbimoduleNat** 是 Mathlib 中的一个定义，位于命名空间 `Subbimodule`。
形式化陈述：toSubbimoduleNat (p : Submodule (R otimes[Int] S) M) : Submodule (R otimes
[Nat] S) M
参数：p : Submodule (R otimes[Int] S) M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Submodule` over `R ⊗[ℤ] S` is naturally also a `Submodule` over the canonical
ly-isomorphic
ring `R ⊗[ℕ] S`.
-/
def toSubbimoduleNat (p : Submodule (R ⊗[ℤ] S) M) : Submodule (R ⊗[ℕ] S) M :=
  baseChange ℕ p

end Ring

end Subbimodule

