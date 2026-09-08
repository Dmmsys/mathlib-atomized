/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Some lemmas about linear functionals on division rings

This file proves some results on linear functionals on division semirings.

## Main results

* `LinearMap.surjective_iff_ne_zero`: a linear functional `f` is surjective iff `f ≠ 0`.
* `LinearMap.range_smulRight_apply`: for a nonzero linear functional `f` and element `x`,
  the range of `f.smulRight x` is the span of the set `{x}`.
-/

public section

namespace LinearMap
variable {R M M₁ : Type*} [AddCommMonoid M] [AddCommMonoid M₁]

/-
**LinearMap.surjective_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：surjective_iff_ne_zero [DivisionSemiring R] [Module R M] {f : M ->ₗ[R] R} 
: Function.Surjective f ↔ f != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ne_zero_of_surjective`：ne_zero_of_surjective [Nontrivial M₂] {
f : M ->ₛₗ[σ₁₂] M₂} (hf : Surjective f) : f != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `inv_mul_cancel_right₀`：inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b⁻¹ * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem surjective_iff_ne_zero [DivisionSemiring R] [Module R M] {f : M →ₗ[R] R} :
    Function.Surjective f ↔ f ≠ 0 := by
  refine ⟨ne_zero_of_surjective, fun hf z ↦ ?_⟩
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by simpa [Ne, LinearMap.ext_iff] using hf
  exact ⟨(z * (f y)⁻¹) • y, by simp [hy]⟩

protected alias ⟨_, surjective⟩ := surjective_iff_ne_zero
/-
**LinearMap.range_smulRight_apply_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap`。
形式化陈述：range_smulRight_apply_of_surjective [Semiring R] [Module R M] [Module R M₁
] {f : M ->ₗ[R] R} (hf : Function.Surjective f) (x : M₁) : range (f.smulRight x)
 = Submodule.span R {x}
参数：hf : Function.Surjective f；x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem range_smulRight_apply_of_surjective [Semiring R] [Module R M] [Module R M₁]
    {f : M →ₗ[R] R} (hf : Function.Surjective f) (x : M₁) :
    range (f.smulRight x) = Submodule.span R {x} := Submodule.ext fun z ↦ by
  simp_rw [mem_range, smulRight_apply, Submodule.mem_span_singleton]
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨f w, hw ▸ rfl⟩, fun ⟨w, hw⟩ ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hf w
  exact ⟨y, hw⟩
/-
**LinearMap.range_smulRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_smulRight_apply [DivisionSemiring R] [Module R M] [Module R M₁] {f :
 M ->ₗ[R] R} (hf : f != 0) (x : M₁) : range (f.smulRight x) = Submodule.span R {
x}
参数：hf : f != 0；x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.range_smulRight_apply_of_surjective`：range_smulRight_apply_of_
surjective [Semiring R] [Module R M] [Module R M₁] {f : M ->ₗ[R] R} (hf : Functi
on.Surjective f) (x : M₁) : range (…
· 使用定理 `LinearMap.surjective`：∀ {R : Type u_1} {M : Type u_2} [inst : AddCommMon
oid M] [inst_1 : DivisionSemiring R] [inst_2 : _root_.Module R M]   {f : M →ₗ[R]
 R}, f ≠ 0…
-/
theorem range_smulRight_apply [DivisionSemiring R] [Module R M] [Module R M₁]
    {f : M →ₗ[R] R} (hf : f ≠ 0) (x : M₁) :
    range (f.smulRight x) = Submodule.span R {x} :=
  range_smulRight_apply_of_surjective (f.surjective hf) x

end LinearMap

