/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Data.Finsupp.Option
public import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# `Finsupp.linearCombination`

## Main definitions

* `Finsupp.linearCombination R (v : ι → M)`: sends `l : ι →₀ R` to the linear combination of
  `v i` with coefficients `l i`;
* `Finsupp.linearCombinationOn`: a restricted version of `Finsupp.linearCombination` with domain

* `Fintype.linearCombination R (v : ι → M)`: sends `l : ι → R` to the linear combination of
  `v i` with coefficients `l i` (for a finite type `ι`)

* `Finsupp.bilinearCombination R S`, `Fintype.bilinearCombination R S`:
  a bilinear version of `Finsupp.linearCombination` and `Fintype.linearCombination`.
  It requires that `M` is both an `R`-module and an `S`-module, with `SMulCommClass R S M`;
  the case `S = R` typically requires that `R` is commutative.

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

section LinearCombination

variable (R)
variable {α' : Type*} {M' : Type*} [AddCommMonoid M'] [Module R M'] (v : α → M) {v' : α' → M'}

/-- Interprets (l : α →₀ R) as a linear combination of the elements in the family (v : α → M) and
    evaluates this linear combination. -/
/-
**Finsupp.linearCombination** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：linearCombination : (α ->₀ R) ->ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interprets (l : α →₀ R) as a linear combination of the elements in the family (v
 : α → M) and
    evaluates this linear combination.
-/
def linearCombination : (α →₀ R) →ₗ[R] M :=
  Finsupp.lsum ℕ fun i => LinearMap.id.smulRight (v i)

variable {v}
/-
**Finsupp.linearCombination_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_apply (l : α ->₀ R) : linearCombination R v l = l.sum fu
n i a => a • v i
参数：l : α ->₀ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linearCombination_apply (l : α →₀ R) : linearCombination R v l = l.sum fun i a => a • v i :=
  rfl
/-
**Finsupp.linearCombination_apply_of_mem_supported** 是 Mathlib 中的一个定理，位于命名空间 `Fi
nsupp`。
形式化陈述：linearCombination_apply_of_mem_supported {l : α ->₀ R} {s : Finset α} (hs 
: l in supported R R (↑s : Set α)) : linearCombination R v l = s.sum fun i => l 
i • v i
参数：hs : l in supported R R (↑s : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem linearCombination_apply_of_mem_supported {l : α →₀ R} {s : Finset α}
    (hs : l ∈ supported R R (↑s : Set α)) : linearCombination R v l = s.sum fun i => l i • v i :=
  Finset.sum_subset hs fun x _ hxg =>
    show l x • v x = 0 by rw [notMem_support_iff.1 hxg, zero_smul]

@[simp]
/-
**Finsupp.linearCombination_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_single (c : R) (a : α) : linearCombination R v (single a
 c) = c • v a
参数：c : R；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearCombination_single (c : R) (a : α) :
    linearCombination R v (single a c) = c • v a := by
  simp [linearCombination_apply, sum_single_index]
/-
**Finsupp.linearCombination_zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_zero_apply (x : α ->₀ R) : (linearCombination R (0 : α -
> M)) x = 0
参数：x : α ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearCombination_zero_apply (x : α →₀ R) : (linearCombination R (0 : α → M)) x = 0 := by
  simp [linearCombination_apply]

variable (α M)

@[simp]
/-
**Finsupp.linearCombination_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_zero : linearCombination R (0 : α -> M) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finsupp.linearCombination_zero_apply`：linearCombination_zero_apply (x : 
α ->₀ R) : (linearCombination R (0 : α -> M)) x = 0
-/
theorem linearCombination_zero : linearCombination R (0 : α → M) = 0 :=
  LinearMap.ext (linearCombination_zero_apply R)

@[simp]
/-
**Finsupp.linearCombination_single_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_single_index (c : M) (a : α) (f : α ->₀ R) [DecidableEq 
α] : linearCombination R (Pi.single a c) f = f a • c
参数：c : M；a : α；f : α ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum_eq_single`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M} (a : α)   {g : α → M → N}
, (∀ (b : α…
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
theorem linearCombination_single_index (c : M) (a : α) (f : α →₀ R) [DecidableEq α] :
    linearCombination R (Pi.single a c) f = f a • c := by
  rw [linearCombination_apply, sum_eq_single a, Pi.single_eq_same]
  · exact fun i _ hi ↦ by rw [Pi.single_eq_of_ne hi, smul_zero]
  · exact fun _ ↦ by simp only [zero_smul]

variable {α M}
/-
**Finsupp.linearCombination_linear_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_linear_comp (f : M ->ₗ[R] M') : linearCombination R (f ∘
 v) = f ∘ₗ linearCombination R v
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem linearCombination_linear_comp (f : M →ₗ[R] M') :
    linearCombination R (f ∘ v) = f ∘ₗ linearCombination R v := by
  ext
  simp [linearCombination_apply]
/-
**Finsupp.apply_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：apply_linearCombination (f : M ->ₗ[R] M') (v) (l : α ->₀ R) : f (linearCom
bination R v l) = linearCombination R (f ∘ v) l
参数：f : M ->ₗ[R] M'；v；l : α ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_linear_comp`：linearCombination_linear_comp (f 
: M ->ₗ[R] M') : linearCombination R (f ∘ v) = f ∘ₗ linearCombination R v
-/
theorem apply_linearCombination (f : M →ₗ[R] M') (v) (l : α →₀ R) :
    f (linearCombination R v l) = linearCombination R (f ∘ v) l :=
  congr($(linearCombination_linear_comp R f) l).symm
/-
**Finsupp.apply_linearCombination_id** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：apply_linearCombination_id (f : M ->ₗ[R] M') (l : M ->₀ R) : f (linearComb
ination R _root_.id l) = linearCombination R f l
参数：f : M ->ₗ[R] M'；l : M ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.apply_linearCombination`：apply_linearCombination (f : M ->ₗ[R] M
') (v) (l : α ->₀ R) : f (linearCombination R v l) = linearCombination R (f ∘ v)
 l
-/
theorem apply_linearCombination_id (f : M →ₗ[R] M') (l : M →₀ R) :
    f (linearCombination R _root_.id l) = linearCombination R f l :=
  apply_linearCombination ..
/-
**Finsupp.linearCombination_unique** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_unique [Unique α] (l : α ->₀ R) (v : α -> M) : linearCom
bination R v l = l default • v default
参数：l : α ->₀ R；v : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `Finsupp.unique_single`：unique_single [Unique α] (x : α ->₀ M) : x = sing
le default (x default)
-/
theorem linearCombination_unique [Unique α] (l : α →₀ R) (v : α → M) :
    linearCombination R v l = l default • v default := by
  rw [← linearCombination_single, ← unique_single l]
/-
**Finsupp.linearCombination_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_surjective (h : Function.Surjective v) : Function.Surjec
tive (linearCombination R v)
参数：h : Function.Surjective v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearCombination_surjective (h : Function.Surjective v) :
    Function.Surjective (linearCombination R v) := by
  intro x
  obtain ⟨y, hy⟩ := h x
  exact ⟨single y 1, by simp [hy]⟩
/-
**Finsupp.linearCombination_range** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_range (h : Function.Surjective v) : LinearMap.range (lin
earCombination R v) = ⊤
参数：h : Function.Surjective v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Finsupp.linearCombination_surjective`：linearCombination_surjective (h : 
Function.Surjective v) : Function.Surjective (linearCombination R v)
-/
theorem linearCombination_range (h : Function.Surjective v) :
    LinearMap.range (linearCombination R v) = ⊤ :=
  range_eq_top.2 <| linearCombination_surjective R h

/-- Any module is a quotient of a free module. This is stated as surjectivity of
`Finsupp.linearCombination R id : (M →₀ R) →ₗ[R] M`. -/
/-
**Finsupp.linearCombination_id_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_id_surjective (M) [AddCommMonoid M] [Module R M] : Funct
ion.Surjective (linearCombination R (id : M -> M))
参数：M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.linearCombination_surjective`：linearCombination_surjective (h : 
Function.Surjective v) : Function.Surjective (linearCombination R v)
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id

--- 原说明 ---
Any module is a quotient of a free module. This is stated as surjectivity of
`Finsupp.linearCombination R id : (M →₀ R) →ₗ[R] M`.
-/
theorem linearCombination_id_surjective (M) [AddCommMonoid M] [Module R M] :
    Function.Surjective (linearCombination R (id : M → M)) :=
  linearCombination_surjective R Function.surjective_id
/-
**Finsupp.range_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：range_linearCombination : LinearMap.range (linearCombination R v) = span R
 (range v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_linearCombination : LinearMap.range (linearCombination R v) = span R (range v) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_range] at hx
    rcases hx with ⟨l, hl⟩
    rw [← hl]
    rw [linearCombination_apply]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (subset_span (mem_range_self i))
  · apply span_le.2
    intro x hx
    rcases hx with ⟨i, hi⟩
    rw [SetLike.mem_coe, LinearMap.mem_range]
    use single i 1
    simp [hi]
/-
**Finsupp._root_.span_range_eq_top_iff_surjective_finsuppLinearCombination** 是 M
athlib 中的一个定理，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.span_range_eq_top_iff_surjective_finsuppLinearCombination :
    Submodule.span R (Set.range v) = ⊤ ↔
      Function.Surjective (Finsupp.linearCombination R v) := by
  rw [← LinearMap.range_eq_top, range_linearCombination]
/-
**Finsupp.lmapDomain_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lmapDomain_linearCombination (f : α -> α') (g : M ->ₗ[R] M') (h : forall i
, g (v i) = v' (f i)) : (linearCombination R v').comp (lmapDomain R R f) = g.com
p (linearCombination R v)
参数：f : α -> α'；g : M ->ₗ[R] M'；h : forall i, g (v i) = v' (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem lmapDomain_linearCombination (f : α → α') (g : M →ₗ[R] M') (h : ∀ i, g (v i) = v' (f i)) :
    (linearCombination R v').comp (lmapDomain R R f) = g.comp (linearCombination R v) := by
  ext l
  simp [linearCombination_apply, h]
/-
**Finsupp.linearCombination_comp_lmapDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_comp_lmapDomain (f : α -> α') : (linearCombination R v')
.comp (Finsupp.lmapDomain R R f) = linearCombination R (v' ∘ f)
参数：f : α -> α'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearCombination_comp_lmapDomain (f : α → α') :
    (linearCombination R v').comp (Finsupp.lmapDomain R R f) = linearCombination R (v' ∘ f) := by
  ext
  simp

@[simp]
/-
**Finsupp.linearCombination_embDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_embDomain (f : α ↪ α') (l : α ->₀ R) : (linearCombinatio
n R v') (embDomain f l) = (linearCombination R (v' ∘ f)) l
参数：f : α ↪ α'；l : α ->₀ R。
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
· 使用定理 `Finsupp.embDomain_apply`：embDomain_apply (f : α ↪ β) (v : α ->₀ M) (b : 
β) : embDomain f v b = if h : exists a, f a = b then v h.choose else 0
· 使用定理 `dite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) 
[inst_1 : Decidable p] (a : α) (b : p → β) (c : ¬p → β),   (if h : p then b h e…
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `Classical.choose_eq`：∀ {α : Sort u_1} (a : α), ⋯.choose = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearCombination_embDomain (f : α ↪ α') (l : α →₀ R) :
    (linearCombination R v') (embDomain f l) = (linearCombination R (v' ∘ f)) l := by
  simp [linearCombination_apply, Finsupp.sum, support_embDomain, embDomain_apply]

@[simp]
/-
**Finsupp.linearCombination_mapDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_mapDomain (f : α -> α') (l : α ->₀ R) : (linearCombinati
on R v') (mapDomain f l) = (linearCombination R (v' ∘ f)) l
参数：f : α -> α'；l : α ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Finsupp.linearCombination_comp_lmapDomain`：linearCombination_comp_lmapDo
main (f : α -> α') : (linearCombination R v').comp (Finsupp.lmapDomain R R f) = 
linearCombination R (v' ∘ f)
-/
theorem linearCombination_mapDomain (f : α → α') (l : α →₀ R) :
    (linearCombination R v') (mapDomain f l) = (linearCombination R (v' ∘ f)) l :=
  LinearMap.congr_fun (linearCombination_comp_lmapDomain _ _) l

@[simp]
/-
**Finsupp.linearCombination_equivMapDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_equivMapDomain (f : α ≃ α') (l : α ->₀ R) : (linearCombi
nation R v') (equivMapDomain f l) = (linearCombination R (v' ∘ f)) l
参数：f : α ≃ α'；l : α ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.equivMapDomain_eq_mapDomain`：equivMapDomain_eq_mapDomain {M} [Ad
dCommMonoid M] (f : α ≃ β) (l : α ->₀ M) : equivMapDomain f l = mapDomain f l
· 使用定理 `Finsupp.linearCombination_mapDomain`：linearCombination_mapDomain (f : α 
-> α') (l : α ->₀ R) : (linearCombination R v') (mapDomain f l) = (linearCombina
tion R (v' ∘ f)) l
-/
theorem linearCombination_equivMapDomain (f : α ≃ α') (l : α →₀ R) :
    (linearCombination R v') (equivMapDomain f l) = (linearCombination R (v' ∘ f)) l := by
  rw [equivMapDomain_eq_mapDomain, linearCombination_mapDomain]

/-- A version of `Finsupp.range_linearCombination` which is useful for going in the other
direction -/
/-
**Finsupp.span_eq_range_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：span_eq_range_linearCombination (s : Set M) : span R s = LinearMap.range (
linearCombination R ((↑) : s -> M))
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.range_linearCombination`：range_linearCombination : LinearMap.ran
ge (linearCombination R v) = span R (range v)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.ofPred_mem_eq`：∀ {α : Type u} {s : Set α}, {x | x ∈ s} = s

--- 原说明 ---
A version of `Finsupp.range_linearCombination` which is useful for going in the 
other
direction
-/
theorem span_eq_range_linearCombination (s : Set M) :
    span R s = LinearMap.range (linearCombination R ((↑) : s → M)) := by
  rw [range_linearCombination, Subtype.range_coe_subtype, Set.ofPred_mem_eq]
/-
**Finsupp.mem_span_iff_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_span_iff_linearCombination (s : Set M) (x : M) : x in span R s ↔ exist
s l : s ->₀ R, linearCombination R (↑) l = x
参数：s : Set M；x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Finsupp.span_eq_range_linearCombination`：span_eq_range_linearCombination
 (s : Set M) : span R s = LinearMap.range (linearCombination R ((↑) : s -> M))
-/
theorem mem_span_iff_linearCombination (s : Set M) (x : M) :
    x ∈ span R s ↔ ∃ l : s →₀ R, linearCombination R (↑) l = x :=
  (SetLike.ext_iff.1 <| span_eq_range_linearCombination _ _) x

variable {R} in
/-
**Finsupp.mem_span_range_iff_exists_finsupp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_span_range_iff_exists_finsupp {v : α -> M} {x : M} : x in span R (rang
e v) ↔ exists c : α ->₀ R, (c.sum fun i a => a • v i) = x
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
theorem mem_span_range_iff_exists_finsupp {v : α → M} {x : M} :
    x ∈ span R (range v) ↔ ∃ c : α →₀ R, (c.sum fun i a => a • v i) = x := by
  simp only [← Finsupp.range_linearCombination, LinearMap.mem_range, linearCombination_apply]
/-
**Finsupp.span_image_eq_map_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp
`。
形式化陈述：span_image_eq_map_linearCombination (s : Set α) : span R (v '' s) = Submod
ule.map (linearCombination R v) (supported R R s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_eq_of_le`：span_eq_of_le (h₁ : s subseteq p) (h₂ : p <= sp
an R s) : span R s = p
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Finsupp.single_mem_supported`：single_mem_supported {s : Set α} {a : α} (
b : M) (h : a in s) : single a b in supported M R s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_supported'`：mem_supported' {s : Set α} (p : α ->₀ M) : p in 
supported M R s ↔ forall x ∉ s, p x = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem span_image_eq_map_linearCombination (s : Set α) :
    span R (v '' s) = Submodule.map (linearCombination R v) (supported R R s) := by
  apply span_eq_of_le
  · intro x hx
    rw [Set.mem_image] at hx
    apply Exists.elim hx
    intro i hi
    exact ⟨_, Finsupp.single_mem_supported R 1 hi.1, by simp [hi.2]⟩
  · refine map_le_iff_le_comap.2 fun z hz => ?_
    have : ∀ i, z i • v i ∈ span R (v '' s) := by
      intro c
      have := Classical.decPred fun x => x ∈ s
      by_cases h : c ∈ s
      · exact smul_mem _ _ (subset_span (Set.mem_image_of_mem _ h))
      · simp [(Finsupp.mem_supported' R _).1 hz _ h]
    rw [mem_comap, linearCombination_apply]
    refine sum_mem ?_
    simp [this]
/-
**Finsupp.mem_span_image_iff_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 `Finsup
p`。
形式化陈述：mem_span_image_iff_linearCombination {s : Set α} {x : M} : x in span R (v 
'' s) ↔ exists l in supported R R s, linearCombination R v l = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.span_image_eq_map_linearCombination`：span_image_eq_map_linearCom
bination (s : Set α) : span R (v '' s) = Submodule.map (linearCombination R v) (
supported R R s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_span_image_iff_linearCombination {s : Set α} {x : M} :
    x ∈ span R (v '' s) ↔ ∃ l ∈ supported R R s, linearCombination R v l = x := by
  rw [span_image_eq_map_linearCombination]
  simp
/-
**Finsupp.linearCombination_option** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_option (v : Option α -> M) (f : Option α ->₀ R) : linear
Combination R v f = f none • v none + linearCombination R (v ∘ Option.some) f.so
me
参数：v : Option α -> M；f : Option α ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum_option_index_smul`：sum_option_index_smul [Semiring R] [AddCo
mmMonoid M] [Module R M] (f : Option α ->₀ R) (b : Option α -> M) : (f.sum fun o
 r => r • b o) = f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearCombination_option (v : Option α → M) (f : Option α →₀ R) :
    linearCombination R v f =
      f none • v none + linearCombination R (v ∘ Option.some) f.some := by
  rw [linearCombination_apply, sum_option_index_smul, linearCombination_apply]; simp
/-
**Finsupp.linearCombination_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp
`。
形式化陈述：linearCombination_linearCombination {α β : Type*} (A : α -> M) (B : β -> α
 ->₀ R) (f : β ->₀ R) : linearCombination R A (linearCombination R B f) = linear
Combination R (fun b => linearCombination R A (B b)) f
参数：A : α -> M；B : β -> α ->₀ R；f : β ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.induction_linear`：induction_linear {motive : (ι ->₀ M) -> Prop} 
(f : ι ->₀ M) (zero : motive 0) (add : forall f g : ι ->₀ M, motive f -> motive 
g -> motive (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.sum_add_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : DecidableEq α] [inst_1 : AddZeroClass M]   [inst_2 : AddCommMonoid N] {f 
g : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `Finsupp.sum_smul_index`：sum_smul_index [MulZeroClass R] [AddCommMonoid M
] {g : α ->₀ R} {b : R} {h : α -> R -> M} (h0 : forall i, h i 0 = 0) : (b • g).s
um h = g.sum…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Finsupp.smul_sum`：smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] 
{v : α ->₀ β} {c : R} {h : α -> β -> M} : c • v.sum h = v.sum fun a b => c • h a
 b
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
-/
theorem linearCombination_linearCombination {α β : Type*} (A : α → M) (B : β → α →₀ R)
    (f : β →₀ R) : linearCombination R A (linearCombination R B f) =
      linearCombination R (fun b => linearCombination R A (B b)) f := by
  classical
  simp only [linearCombination_apply]
  induction f using induction_linear with
  | zero => simp only [sum_zero_index]
  | add f₁ f₂ h₁ h₂ => simp [sum_add_index, h₁, h₂, add_smul]
  | single => simp [sum_single_index, sum_smul_index, smul_sum, mul_smul]
/-
**Finsupp.linearCombination_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_smul [Module R S] [Module S M] [IsScalarTower R S M] {w 
: α' -> S} : linearCombination R (fun i : α × α' => w i.2 • v i.1) = (linearComb
ination S v).restrictScalars R ∘ₗ mapRange.linearMap (linearCombination R w) ∘ₗ 
(curryLinearEquiv R).toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.CompatibleSMul.finsupp_dom`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Finsupp.curryLinearEquiv_apply`：∀ {α : Type u_9} {β : Type u_10} (R : Ty
pe u_11) {M : Type u_12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R …
· 使用引理 `Finsupp.curry_single`：curry_single (a : α × β) (m : M) : (single a m).cu
rry = single a.1 (single a.2 m)
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearCombination_smul [Module R S] [Module S M] [IsScalarTower R S M] {w : α' → S} :
    linearCombination R (fun i : α × α' ↦ w i.2 • v i.1) = (linearCombination S v).restrictScalars R
      ∘ₗ mapRange.linearMap (linearCombination R w) ∘ₗ (curryLinearEquiv R).toLinearMap := by
  ext; simp

@[simp]
/-
**Finsupp.linearCombination_fin_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_fin_zero (f : Fin 0 -> M) : linearCombination R f = 0
参数：f : Fin 0 -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
-/
theorem linearCombination_fin_zero (f : Fin 0 → M) : linearCombination R f = 0 := by
  ext i
  apply finZeroElim i

variable (α) (M) (v)

/-- `Finsupp.linearCombinationOn M v s` interprets `p : α →₀ R` as a linear combination of a
subset of the vectors in `v`, mapping it to the span of those vectors.

The subset is indicated by a set `s : Set α` of indices.
-/
/-
**Finsupp.linearCombinationOn** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：linearCombinationOn (s : Set α) : supported R R s ->ₗ[R] span R (v '' s)
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.linearCombinationOn M v s` interprets `p : α →₀ R` as a linear combinat
ion of a
subset of the vectors in `v`, mapping it to the span of those vectors.

The subset is indicated by a set `s : Set α` of indices.
-/
def linearCombinationOn (s : Set α) : supported R R s →ₗ[R] span R (v '' s) :=
  LinearMap.codRestrict _ ((linearCombination _ v).comp (Submodule.subtype (supported R R s)))
    fun ⟨l, hl⟩ => (mem_span_image_iff_linearCombination _).2 ⟨l, hl, rfl⟩

variable {α} {M} {v}
/-
**Finsupp.linearCombinationOn_range** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombinationOn_range (s : Set α) : LinearMap.range (linearCombination
On α M R v s) = ⊤
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombinationOn.eq_1`：∀ (α : Type u_1) (M : Type u_2) (R : T
ype u_5) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] (v : α → M) (s …
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `LinearMap.map_codRestrict`：map_codRestrict [RingHomSurjective σ₂₁] (p : 
Submodule R M) (f : M₂ ->ₛₗ[σ₂₁] M) (h p') : map (codRestrict p f h) p' = comap 
p.subtype (p'.m…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_le_iff_comap`：range_le_iff_comap [RingHomSurjective τ₁₂]
 {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R₂ M₂} : range f <= p ↔ comap f p = ⊤
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finsupp.span_image_eq_map_linearCombination`：span_image_eq_map_linearCom
bination (s : Set α) : span R (v '' s) = Submodule.map (linearCombination R v) (
supported R R s)
-/
theorem linearCombinationOn_range (s : Set α) :
    LinearMap.range (linearCombinationOn α M R v s) = ⊤ := by
  rw [linearCombinationOn, LinearMap.range_eq_map, LinearMap.map_codRestrict,
    ← LinearMap.range_le_iff_comap, range_subtype, Submodule.map_top, LinearMap.range_comp,
    range_subtype]
  exact (span_image_eq_map_linearCombination _ _).le

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.linearCombination_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_restrict (s : Set α) : linearCombination R (s.domRestric
t v) = Submodule.subtype _ ∘ₗ linearCombinationOn α M R v s ∘ₗ (supportedEquivFi
nsupp s).symm.toLinearMap
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finsupp.supportedEquivFinsupp_symm_single`：∀ {α : Type u_1} {M : Type u_
2} {R : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _ro
ot_.Module R M] (s : Set α) (i …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearCombination_restrict (s : Set α) :
    linearCombination R (s.domRestrict v) = Submodule.subtype _ ∘ₗ
      linearCombinationOn α M R v s ∘ₗ (supportedEquivFinsupp s).symm.toLinearMap := by
  ext; simp [linearCombinationOn]
/-
**Finsupp.linearCombination_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_comp (f : α' -> α) : linearCombination R (v ∘ f) = (line
arCombination R v).comp (lmapDomain R R f)
参数：f : α' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
-/
theorem linearCombination_comp (f : α' → α) :
    linearCombination R (v ∘ f) = (linearCombination R v).comp (lmapDomain R R f) := by
  ext
  simp [linearCombination_apply]
/-
**Finsupp.linearCombination_comapDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_comapDomain (f : α -> α') (l : α' ->₀ R) (hf : Set.InjOn
 f (f ⁻¹' ↑l.support)) : linearCombination R v (Finsupp.comapDomain f l hf) = (l
.support.preimage f hf).sum fun i => l (f i) • v i
参数：f : α -> α'；l : α' ->₀ R；hf : Set.InjOn f (f ⁻¹' ↑l.support)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
-/
theorem linearCombination_comapDomain (f : α → α') (l : α' →₀ R)
    (hf : Set.InjOn f (f ⁻¹' ↑l.support)) : linearCombination R v (Finsupp.comapDomain f l hf) =
      (l.support.preimage f hf).sum fun i => l (f i) • v i := by
  rw [linearCombination_apply]; rfl
/-
**Finsupp.linearCombination_onFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearCombination_onFinset {s : Finset α} {f : α -> R} (g : α -> M) (hf : 
forall a, f a != 0 -> a in s) : linearCombination R g (Finsupp.onFinset s f hf) 
= Finset.sum s fun x : α => f x • g x
参数：g : α -> M；hf : forall a, f a != 0 -> a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.support_onFinset`：support_onFinset [DecidableEq M] {s : Finset α
} {f : α -> M} (hf : forall a : α, f a != 0 -> a in s) : (Finsupp.onFinset s f h
f).support = {…
· 使用定理 `Finset.sum_filter_of_ne`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} 
[inst : AddCommMonoid M] {f : ι → M} {p : ι → Prop}   [inst_1 : DecidablePred p]
, (∀ x ∈ s, f…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearCombination_onFinset {s : Finset α} {f : α → R} (g : α → M)
    (hf : ∀ a, f a ≠ 0 → a ∈ s) :
    linearCombination R g (Finsupp.onFinset s f hf) = Finset.sum s fun x : α => f x • g x := by
  classical
  simp only [linearCombination_apply, Finsupp.sum, Finsupp.onFinset_apply, Finsupp.support_onFinset]
  rw [Finset.sum_filter_of_ne]
  intro x _ h
  contrapose h
  simp [h]

variable [Module S M] [SMulCommClass R S M]

variable (S) in
/-- `Finsupp.bilinearCombination R S v f` is the linear combination of vectors in `v` with weights
in `f`, as a bilinear map of `v` and `f`.
In the absence of `SMulCommClass R S M`, use `Finsupp.linearCombination`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.
-/
/-
**Finsupp.bilinearCombination** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：bilinearCombination : (α -> M) ->ₗ[S] (α ->₀ R) ->ₗ[R] M where toFun v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.bilinearCombination R S v f` is the linear combination of vectors in `v
` with weights
in `f`, as a bilinear map of `v` and `f`.
In the absence of `SMulCommClass R S M`, use `Finsupp.linearCombination`.

See note [bundled maps over different rings] for why separate `R` and `S` semiri
ngs are used.
-/
def bilinearCombination : (α → M) →ₗ[S] (α →₀ R) →ₗ[R] M where
  toFun v := linearCombination R v
  map_add' u v := by ext; simp [Pi.add_apply, smul_add]
  map_smul' r v := by ext; simp [smul_comm]

@[simp]
/-
**Finsupp.bilinearCombination_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：bilinearCombination_apply : bilinearCombination R S v = linearCombination 
R v
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bilinearCombination_apply :
    bilinearCombination R S v = linearCombination R v :=
  rfl

end LinearCombination

end Finsupp

section Fintype

variable {α M : Type*} (R : Type*) [Fintype α] [Semiring R] [AddCommMonoid M] [Module R M]
variable (S : Type*) [Semiring S] [Module S M] [SMulCommClass R S M]
variable (v : α → M)

/-- `Fintype.linearCombination R v f` is the linear combination of vectors in `v` with weights
in `f`. This variant of `Finsupp.linearCombination` is defined on fintype indexed vectors.

This map is linear in `v` if `R` is commutative, and always linear in `f`.
See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.
-/
/-
**Fintype.linearCombination** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：{α : Type u_1} →   {M : Type u_2} →     (R : Type u_3) →       [Fintype α]
 →         [inst : Semiring R] → [inst_1 : AddCommMonoid M] → [inst_2 : _root_.M
odule R M] → (α → M) → (α → R) →ₗ[R] M
参数：R : Type u_3；α → M；α → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fintype.linearCombination R v f` is the linear combination of vectors in `v` wi
th weights
in `f`. This variant of `Finsupp.linearCombination` is defined on fintype indexe
d vectors.

This map is linear in `v` if `R` is commutative, and always linear in `f`.
See note [bundled maps over different rings] for why separate `R` and `S` semiri
ngs are used.
-/
protected def Fintype.linearCombination : (α → R) →ₗ[R] M where
  toFun f := ∑ i, f i • v i
  map_add' f g := by simp_rw [← Finset.sum_add_distrib, ← add_smul]; rfl
  map_smul' r f := by simp_rw [Finset.smul_sum, smul_smul]; rfl
/-
**Fintype.linearCombination_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.linearCombination_apply (f) : Fintype.linearCombination R v f = ∑ 
i, f i • v i
参数：f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.linearCombination_apply (f) : Fintype.linearCombination R v f = ∑ i, f i • v i :=
  rfl

@[simp]
/-
**Fintype.linearCombination_apply_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.linearCombination_apply_single [DecidableEq α] (i : α) (r : R) : F
intype.linearCombination R v (Pi.single i r) = r • v i
参数：i : α；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem Fintype.linearCombination_apply_single [DecidableEq α] (i : α) (r : R) :
    Fintype.linearCombination R v (Pi.single i r) = r • v i := by
  simp_rw [Fintype.linearCombination_apply, Pi.single_apply, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
/-
**Finsupp.linearCombination_eq_fintype_linearCombination_apply** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：Finsupp.linearCombination_eq_fintype_linearCombination_apply (x : α -> R) 
: linearCombination R v ((Finsupp.linearEquivFunOnFinite R R α).symm x) = Fintyp
e.linearCombination R v x
参数：x : α -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem Finsupp.linearCombination_eq_fintype_linearCombination_apply (x : α → R) :
    linearCombination R v ((Finsupp.linearEquivFunOnFinite R R α).symm x) =
      Fintype.linearCombination R v x := by
  apply Finset.sum_subset
  · exact Finset.subset_univ _
  · intro x _ hx
    rw [Finsupp.notMem_support_iff.mp hx]
    exact zero_smul _ _
/-
**Finsupp.linearCombination_eq_fintype_linearCombination** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：Finsupp.linearCombination_eq_fintype_linearCombination : (linearCombinatio
n R v).comp (Finsupp.linearEquivFunOnFinite R R α).symm.toLinearMap = Fintype.li
nearCombination R v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finsupp.linearCombination_eq_fintype_linearCombination_apply`：Finsupp.li
nearCombination_eq_fintype_linearCombination_apply (x : α -> R) : linearCombinat
ion R v ((Finsupp.linearEquivFunOnFinite R R α).sy…
-/
theorem Finsupp.linearCombination_eq_fintype_linearCombination :
    (linearCombination R v).comp (Finsupp.linearEquivFunOnFinite R R α).symm.toLinearMap =
      Fintype.linearCombination R v :=
  LinearMap.ext <| linearCombination_eq_fintype_linearCombination_apply R v

@[simp]
/-
**Fintype.range_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.range_linearCombination : LinearMap.range (Fintype.linearCombinati
on R v) = Submodule.span R (Set.range v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.linearCombination_eq_fintype_linearCombination`：Finsupp.linearCo
mbination_eq_fintype_linearCombination : (linearCombination R v).comp (Finsupp.l
inearEquivFunOnFinite R R α).symm.toLinearMa…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Finsupp.range_linearCombination`：range_linearCombination : LinearMap.ran
ge (linearCombination R v) = span R (range v)
-/
theorem Fintype.range_linearCombination :
    LinearMap.range (Fintype.linearCombination R v) = Submodule.span R (Set.range v) := by
  rw [← Finsupp.linearCombination_eq_fintype_linearCombination, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, Finsupp.range_linearCombination]
/-
**span_range_eq_top_iff_surjective_fintypeLinearCombination** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：span_range_eq_top_iff_surjective_fintypeLinearCombination : Submodule.span
 R (Set.range v) = ⊤ ↔ Function.Surjective (Fintype.linearCombination R v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Fintype.range_linearCombination`：Fintype.range_linearCombination : Linea
rMap.range (Fintype.linearCombination R v) = Submodule.span R (Set.range v)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem span_range_eq_top_iff_surjective_fintypeLinearCombination :
    Submodule.span R (Set.range v) = ⊤ ↔
      Function.Surjective (Fintype.linearCombination R v) := by
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]

/-- `Fintype.bilinearCombination R S v f` is the linear combination of vectors in `v` with weights
in `f`. This variant of `Finsupp.linearCombination` is defined on fintype indexed vectors.

This map is linear in `v` if `R` is commutative, and always linear in `f`.
See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.
-/
/-
**Fintype.bilinearCombination** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：{α : Type u_1} →   {M : Type u_2} →     (R : Type u_3) →       [Fintype α]
 →         [inst : Semiring R] →           [inst_1 : AddCommMonoid M] →         
    [inst_2 : _root_.Module R M] →               (S : Type u_4) →               
  [inst_3 : Semiring S] →                   [inst_4 : _root_.Module S M] → [inst
_5 : SMulCommClass R S M] → (α → M) →ₗ[S] (α → R) →ₗ[R] M
参数：R : Type u_3；S : Type u_4；α → M；α → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fintype.bilinearCombination R S v f` is the linear combination of vectors in `v
` with weights
in `f`. This variant of `Finsupp.linearCombination` is defined on fintype indexe
d vectors.

This map is linear in `v` if `R` is commutative, and always linear in `f`.
See note [bundled maps over different rings] for why separate `R` and `S` semiri
ngs are used.
-/
protected def Fintype.bilinearCombination : (α → M) →ₗ[S] (α → R) →ₗ[R] M where
  toFun v := Fintype.linearCombination R v
  map_add' u v := by ext; simp [Fintype.linearCombination,
    Finset.sum_add_distrib, Pi.add_apply, smul_add]
  map_smul' r v := by ext; simp [Fintype.linearCombination, Finset.smul_sum, smul_comm]

variable {S}

@[simp]
/-
**Fintype.bilinearCombination_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.bilinearCombination_apply : Fintype.bilinearCombination R S v = Fi
ntype.linearCombination R v
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.bilinearCombination_apply :
    Fintype.bilinearCombination R S v = Fintype.linearCombination R v :=
  rfl
/-
**Fintype.bilinearCombination_apply_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.bilinearCombination_apply_single [DecidableEq α] (i : α) (r : R) :
 Fintype.bilinearCombination R S v (Pi.single i r) = r • v i
参数：i : α；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.linearCombination_apply_single`：Fintype.linearCombination_apply_
single [DecidableEq α] (i : α) (r : R) : Fintype.linearCombination R v (Pi.singl
e i r) = r • v i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Fintype.bilinearCombination_apply_single [DecidableEq α] (i : α) (r : R) :
    Fintype.bilinearCombination R S v (Pi.single i r) = r • v i := by
  simp [Fintype.bilinearCombination]

section SpanRange

variable {v} {x : M}

/-- An element `x` lies in the span of `v` iff it can be written as sum `∑ cᵢ • vᵢ = x`.
-/
/-
**Submodule.mem_span_range_iff_exists_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.mem_span_range_iff_exists_fun : x in span R (range v) ↔ exists c
 : α -> R, ∑ i, c i • v i = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.equivFunOnFinite_apply`：∀ {α : Type u_1} {M : Type u_4} [inst : 
Zero M] [inst_1 : Finite α] (a : α →₀ M) (a_1 : α),   Finsupp.equivFunOnFinite a
 a_1 = a a_1
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Eq.congr_left`：∀ {α : Sort u_1} {x y z : α}, x = y → (x = z ↔ y = z)
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0

--- 原说明 ---
An element `x` lies in the span of `v` iff it can be written as sum `∑ cᵢ • vᵢ =
 x`.
-/
theorem Submodule.mem_span_range_iff_exists_fun :
    x ∈ span R (range v) ↔ ∃ c : α → R, ∑ i, c i • v i = x := by
  rw [Finsupp.equivFunOnFinite.surjective.exists]
  simp only [Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.equivFunOnFinite_apply]
  exact exists_congr fun c => Eq.congr_left <| Finsupp.sum_fintype _ _ fun i => zero_smul _ _

/-- A family `v : α → V` is generating `V` iff every element `(x : V)`
can be written as sum `∑ cᵢ • vᵢ = x`.
-/
/-
**Submodule.top_le_span_range_iff_forall_exists_fun** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Submodule.top_le_span_range_iff_forall_exists_fun : ⊤ <= span R (range v) 
↔ forall x, exists c : α -> R, ∑ i, c i • v i = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `trivial`：True

--- 原说明 ---
A family `v : α → V` is generating `V` iff every element `(x : V)`
can be written as sum `∑ cᵢ • vᵢ = x`.
-/
theorem Submodule.top_le_span_range_iff_forall_exists_fun :
    ⊤ ≤ span R (range v) ↔ ∀ x, ∃ c : α → R, ∑ i, c i • v i = x := by
  simp_rw [← mem_span_range_iff_exists_fun]
  exact ⟨fun h x => h trivial, fun h x _ => h x⟩

omit [Fintype α]
/-
**Submodule.mem_span_image_iff_exists_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.mem_span_image_iff_exists_fun {s : Set α} : x in span R (v '' s)
 ↔ exists t : Finset α, ↑t subseteq s ∧ exists c : t -> R, ∑ i, c i • v i = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用定理 `Submodule.sum_smul_mem`：sum_smul_mem {t : Finset ι} {f : ι -> M} (r : ι 
-> R) (hyp : forall c in t, f c in p) : (∑ i in t, r i • f i) in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem Submodule.mem_span_image_iff_exists_fun {s : Set α} :
    x ∈ span R (v '' s) ↔ ∃ t : Finset α, ↑t ⊆ s ∧ ∃ c : t → R, ∑ i, c i • v i = x := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht, c, hx⟩ ↦ ?_⟩
  · obtain ⟨l, hl, hx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).mp h
    refine ⟨l.support, hl, l ∘ (↑), ?_⟩
    rw [← hx]
    exact l.support.sum_coe_sort fun a ↦ l a • v a
  · rw [← hx]
    exact sum_smul_mem (span R (v '' s)) c fun a _ ↦ subset_span <| by aesop
/-
**Submodule.mem_span_image_finset_iff_exists_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.mem_span_image_finset_iff_exists_fun {s : Finset α} : x in span 
R (v '' s) ↔ exists c : s -> R, ∑ i, c i • v i = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_span_range_iff_exists_fun`：Submodule.mem_span_range_iff_ex
ists_fun : x in span R (range v) ↔ exists c : α -> R, ∑ i, c i • v i = x
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Submodule.mem_span_image_finset_iff_exists_fun {s : Finset α} :
    x ∈ span R (v '' s) ↔ ∃ c : s → R, ∑ i, c i • v i = x := by
  rw [← mem_span_range_iff_exists_fun, image_eq_range]
  rfl
/-
**Submodule.mem_span_image_finset_iff_exists_fun'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.mem_span_image_finset_iff_exists_fun' {s : Finset α} : x in span
 R (v '' s) ↔ exists c : α -> R, ∑ i in s, c i • v i = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_span_image_finset_iff_exists_fun`：Submodule.mem_span_image
_finset_iff_exists_fun {s : Finset α} : x in span R (v '' s) ↔ exists c : s -> R
, ∑ i, c i • v i = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Submodule.mem_span_image_finset_iff_exists_fun' {s : Finset α} :
    x ∈ span R (v '' s) ↔ ∃ c : α → R, ∑ i ∈ s, c i • v i = x := by
  classical
  rw [Submodule.mem_span_image_finset_iff_exists_fun]
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun ⟨c, hc⟩ ↦ ?_⟩
  · refine ⟨fun i ↦ if h : i ∈ s then c ⟨i, h⟩ else 0, ?_⟩
    rw [← hc, ← Finset.sum_coe_sort (s := s)]
    simp
  · refine ⟨fun i ↦ c i, ?_⟩
    rw [← hc, ← Finset.sum_coe_sort (s := s)]
/-
**Fintype.mem_span_image_iff_exists_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.mem_span_image_iff_exists_fun {s : Set α} [Fintype s] : x in span 
R (v '' s) ↔ exists c : s -> R, ∑ i, c i • v i = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_span_range_iff_exists_fun`：Submodule.mem_span_range_iff_ex
ists_fun : x in span R (range v) ↔ exists c : α -> R, ∑ i, c i • v i = x
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Fintype.mem_span_image_iff_exists_fun {s : Set α} [Fintype s] :
    x ∈ span R (v '' s) ↔ ∃ c : s → R, ∑ i, c i • v i = x := by
  rw [← mem_span_range_iff_exists_fun, image_eq_range]

end SpanRange

end Fintype

variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Finsupp

section

variable (R)

/-- Pick some representation of `x : span R w` as a linear combination in `w`,
`((Finsupp.mem_span_iff_linearCombination _ _ _).mp x.2).choose`
-/
irreducible_def Span.repr (w : Set M) (x : span R w) : w →₀ R :=
  ((Finsupp.mem_span_iff_linearCombination _ _ _).mp x.2).choose

@[simp]
/-
**Span.finsupp_linearCombination_repr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Span.finsupp_linearCombination_repr {w : Set M} (x : span R w) : Finsupp.l
inearCombination R ((↑) : w -> M) (Span.repr R w x) = x
参数：x : span R w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Span.repr_def`：∀ (R : Type u_4) {M : Type u_5} [inst : Semiring R] [inst
_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (w : Set M)   (x : ↥(Submodul
e.s…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_span_iff_linearCombination`：mem_span_iff_linearCombination (
s : Set M) (x : M) : x in span R s ↔ exists l : s ->₀ R, linearCombination R (↑)
 l = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Span.finsupp_linearCombination_repr {w : Set M} (x : span R w) :
    Finsupp.linearCombination R ((↑) : w → M) (Span.repr R w x) = x := by
  rw [Span.repr_def]
  exact ((Finsupp.mem_span_iff_linearCombination _ _ _).mp x.2).choose_spec

end

/-
**LinearMap.map_finsupp_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.map_finsupp_linearCombination (f : M ->ₗ[R] N) {ι : Type*} {g : 
ι -> M} (l : ι ->₀ R) : f (linearCombination R g l) = linearCombination R (f ∘ g
) l
参数：f : M ->ₗ[R] N；l : ι ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.apply_linearCombination`：apply_linearCombination (f : M ->ₗ[R] M
') (v) (l : α ->₀ R) : f (linearCombination R v l) = linearCombination R (f ∘ v)
 l
-/
theorem LinearMap.map_finsupp_linearCombination (f : M →ₗ[R] N) {ι : Type*} {g : ι → M}
    (l : ι →₀ R) : f (linearCombination R g l) = linearCombination R (f ∘ g) l :=
  apply_linearCombination _ _ _ _
/-
**Submodule.mem_span_iff_exists_finset_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.mem_span_iff_exists_finset_subset {s : Set M} {x : M} : x in spa
n R s ↔ exists (f : M -> R) (t : Finset M), ↑t subseteq s ∧ f.support subseteq t
 ∧ ∑ a in t, f a • a = x where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.fun_support_eq`：fun_support_eq (f : α ->₀ M) : Function.support 
f = f.support
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
lemma Submodule.mem_span_iff_exists_finset_subset {s : Set M} {x : M} :
    x ∈ span R s ↔
      ∃ (f : M → R) (t : Finset M), ↑t ⊆ s ∧ f.support ⊆ t ∧ ∑ a ∈ t, f a • a = x where
  mp := by
    rw [← s.image_id, mem_span_image_iff_linearCombination]
    rintro ⟨l, hl, rfl⟩
    exact ⟨l, l.support, by simpa [linearCombination, Finsupp.sum] using! hl⟩
  mpr := by
    rintro ⟨n, t, hts, -, rfl⟩; exact sum_mem fun x hx ↦ smul_mem _ _ <| subset_span <| hts hx
/-
**Submodule.mem_span_finset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.mem_span_finset {s : Finset M} {x : M} : x in span R s ↔ exists 
f : M -> R, f.support subseteq s ∧ ∑ a in s, f a • a = x where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.mem_span_iff_exists_finset_subset`：Submodule.mem_span_iff_exis
ts_finset_subset {s : Set M} {x : M} : x in span R s ↔ exists (f : M -> R) (t : 
Finset M), ↑t subseteq s ∧ f.supp…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
lemma Submodule.mem_span_finset {s : Finset M} {x : M} :
    x ∈ span R s ↔ ∃ f : M → R, f.support ⊆ s ∧ ∑ a ∈ s, f a • a = x where
  mp := by
    rw [mem_span_iff_exists_finset_subset]
    rintro ⟨f, t, hts, hf, rfl⟩
    refine ⟨f, hf.trans hts, .symm <| Finset.sum_subset hts ?_⟩
    simp +contextual [Function.support_subset_iff'.1 hf]
  mpr := by rintro ⟨f, -, rfl⟩; exact sum_mem fun x hx ↦ smul_mem _ _ <| subset_span <| hx
/-
**Submodule.mem_span_iff_of_fintype** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.mem_span_iff_of_fintype {s : Set M} [Fintype s] {x : M} : x in s
pan R s ↔ exists f : s -> R, ∑ a : s, f a • a.1 = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
· 使用定理 `Submodule.mem_span_range_iff_exists_fun`：Submodule.mem_span_range_iff_ex
ists_fun : x in span R (range v) ↔ exists c : α -> R, ∑ i, c i • v i = x
-/
lemma Submodule.mem_span_iff_of_fintype {s : Set M} [Fintype s] {x : M} :
    x ∈ span R s ↔ ∃ f : s → R, ∑ a : s, f a • a.1 = x := by
  conv_lhs => rw [← Subtype.range_val (s := s)]
  exact mem_span_range_iff_exists_fun _

/-- A variant of `Submodule.mem_span_finset` using `s` as the index type. -/
/-
**Submodule.mem_span_finset'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.mem_span_finset' {s : Finset M} {x : M} : x in span R s ↔ exists
 f : s -> R, ∑ a : s, f a • a.1 = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.mem_span_iff_of_fintype`：Submodule.mem_span_iff_of_fintype {s 
: Set M} [Fintype s] {x : M} : x in span R s ↔ exists f : s -> R, ∑ a : s, f a •
 a.1 = x

--- 原说明 ---
A variant of `Submodule.mem_span_finset` using `s` as the index type.
-/
lemma Submodule.mem_span_finset' {s : Finset M} {x : M} :
    x ∈ span R s ↔ ∃ f : s → R, ∑ a : s, f a • a.1 = x :=
  mem_span_iff_of_fintype

/-- An element `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, if and only if
`m` can be written as a finite `R`-linear combination of elements of `s`.
The implementation uses `Finsupp.sum`. -/
/-
**Submodule.mem_span_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.mem_span_set {m : M} {s : Set M} : m in Submodule.span R s ↔ exi
sts c : M ->₀ R, (c.support : Set M) subseteq s ∧ (c.sum fun mi r => r • mi) = m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x

--- 原说明 ---
An element `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, i
f and only if
`m` can be written as a finite `R`-linear combination of elements of `s`.
The implementation uses `Finsupp.sum`.
-/
theorem Submodule.mem_span_set {m : M} {s : Set M} :
    m ∈ Submodule.span R s ↔
      ∃ c : M →₀ R, (c.support : Set M) ⊆ s ∧ (c.sum fun mi r => r • mi) = m := by
  conv_lhs => rw [← Set.image_id s]
  exact Finsupp.mem_span_image_iff_linearCombination R (v := _root_.id (α := M))

/-- An element `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, if and only if
`m` can be written as a finite `R`-linear combination of elements of `s`.
The implementation uses a sum indexed by `Fin n` for some `n`. -/
/-
**Submodule.mem_span_set'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.mem_span_set' {m : M} {s : Set M} : m in Submodule.span R s ↔ ex
ists (n : Nat) (f : Fin n -> R) (g : Fin n -> s), ∑ i, f i • (g i : M) = m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_set`：Submodule.mem_span_set {m : M} {s : Set M} : m i
n Submodule.span R s ↔ exists c : M ->₀ R, (c.support : Set M) subseteq s ∧ (c.s
um fun mi r …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s

--- 原说明 ---
An element `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, i
f and only if
`m` can be written as a finite `R`-linear combination of elements of `s`.
The implementation uses a sum indexed by `Fin n` for some `n`.
-/
lemma Submodule.mem_span_set' {m : M} {s : Set M} :
    m ∈ Submodule.span R s ↔ ∃ (n : ℕ) (f : Fin n → R) (g : Fin n → s),
      ∑ i, f i • (g i : M) = m := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases mem_span_set.1 h with ⟨c, cs, rfl⟩
    have A : c.support ≃ Fin c.support.card := Finset.equivFin _
    refine ⟨_, fun i ↦ c (A.symm i), fun i ↦ ⟨A.symm i, cs (A.symm i).2⟩, ?_⟩
    rw [Finsupp.sum, ← Finset.sum_coe_sort c.support]
    exact Fintype.sum_equiv A.symm _ (fun j ↦ c j • (j : M)) (fun i ↦ rfl)
  · rintro ⟨n, f, g, rfl⟩
    exact Submodule.sum_mem _ (fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (g i).2))

/-- The span of a subset `s` is the union over all `n` of the set of linear combinations of at most
`n` terms belonging to `s`. -/
/-
**Submodule.span_eq_iUnion_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.span_eq_iUnion_nat (s : Set M) : (Submodule.span R s : Set M) = 
⋃ (n : Nat), (fun (f : Fin n -> (R × M)) => ∑ i, (f i).1 • (f i).2) '' ({f | for
all i, (f i).2 in s})
参数：s : Set M。
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
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The span of a subset `s` is the union over all `n` of the set of linear combinat
ions of at most
`n` terms belonging to `s`.
-/
lemma Submodule.span_eq_iUnion_nat (s : Set M) :
    (Submodule.span R s : Set M) = ⋃ (n : ℕ),
      (fun (f : Fin n → (R × M)) ↦ ∑ i, (f i).1 • (f i).2) '' ({f | ∀ i, (f i).2 ∈ s}) := by
  ext m
  simp only [SetLike.mem_coe, mem_iUnion, mem_image, mem_ofPred_eq, mem_span_set']
  refine exists_congr (fun n ↦ ⟨?_, ?_⟩)
  · rintro ⟨f, g, rfl⟩
    exact ⟨fun i ↦ (f i, g i), fun i ↦ (g i).2, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun i ↦ (f i).1, fun i ↦ ⟨(f i).2, (hf i)⟩, rfl⟩

section Ring

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] (i : ι) (c : ι → R) (h₀ : c i = 0)

/-- Given `c : ι → R` and an index `i` such that `c i = 0`, this is the linear isomorphism sending
the `j`-th standard basis vector to itself plus `c j` multiplied with the `i`-th standard basis
vector (in particular, the `i`-th standard basis vector is kept invariant). -/
/-
**Finsupp.addSingleEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Finsupp.addSingleEquiv : (ι ->₀ R) ≃ₗ[R] (ι ->₀ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `c : ι → R` and an index `i` such that `c i = 0`, this is the linear isomo
rphism sending
the `j`-th standard basis vector to itself plus `c j` multiplied with the `i`-th
 standard basis
vector (in particular, the `i`-th standard basis vector is kept invariant).
-/
def Finsupp.addSingleEquiv : (ι →₀ R) ≃ₗ[R] (ι →₀ R) := by
  refine .ofLinearMap (linearCombination _ fun j ↦ single j 1 + single i (c j))
    (linearCombination _ fun j ↦ single j 1 - single i (c j)) ?_ ?_ <;>
  ext j k <;> obtain rfl | hk := eq_or_ne i k
  · simp [h₀]
  · simp [hk]
  · simp [h₀]
  · simp [hk]
/-
**Finsupp.linearCombination_comp_addSingleEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.linearCombination_comp_addSingleEquiv (v : ι -> M) : linearCombina
tion R v ∘ₗ addSingleEquiv i c h₀ = linearCombination R (v + (c · • v i))
参数：v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finsupp.linearCombination_comp_addSingleEquiv (v : ι → M) :
    linearCombination R v ∘ₗ addSingleEquiv i c h₀ = linearCombination R (v + (c · • v i)) := by
  ext; simp [addSingleEquiv]

end Ring

