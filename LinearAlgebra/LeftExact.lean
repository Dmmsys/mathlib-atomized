/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# The Left Exactness of Hom


If `M1 → M2 → M3 → 0` is an exact sequence of `R`-modules and `N` is an `R`-module,
then `0 → (M3 →ₗ[R] N) → (M2 →ₗ[R] N) → (M1 →ₗ[R] N)` is exact. In this file, we
show the exactness at `M2 →ₗ[R] N` (`exact_lcomp_of_exact_of_surjective`);
the injectivity part is `LinearMap.lcomp_injective_of_surjective` in the file
`Mathlib.LinearAlgebra.BilinearMap`.


-/

public section

namespace LinearMap

variable {R : Type*} [CommRing R] {M1 M2 M3 : Type*} (N : Type*)
  [AddCommGroup M1] [AddCommGroup M2] [AddCommGroup M3] [AddCommGroup N]
  [Module R M1] [Module R M2] [Module R M3] [Module R N]

/-
**LinearMap.exact_lcomp_of_exact_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Linear
Map`。
形式化陈述：exact_lcomp_of_exact_of_surjective {f : M1 ->ₗ[R] M2} {g : M2 ->ₗ[R] M3} (
exac : Function.Exact f g) (surj : Function.Surjective g) : Function.Exact (Line
arMap.lcomp R N g) (LinearMap.lcomp R N f)
参数：exac : Function.Exact f g；surj : Function.Surjective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_le_ker_iff`：range_le_ker_iff {f : M ->ₛₗ[τ₁₂] M₂} {g : M
₂ ->ₛₗ[τ₂₃] M₃} : range f <= ker g ↔ (g.comp f : M ->ₛₗ[τ₁₃] M₃) = 0
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Function.Exact.linearEquivOfSurjective_symm_apply`：Function.Exact.linear
EquivOfSurjective_symm_apply (h : Function.Exact f g) (hg : Function.Surjective 
g) (x : N) : (h.linearEquivOfSurjective…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `Function.Exact.linearMap_comp_eq_zero`：∀ {R : Type u_1} {M : Type u_2} {
N : Type u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMonoid N] [i…
· 使用定理 `LinearMap.comp_zero`：comp_zero (g : M₂ ->ₛₗ[σ₂₃] M₃) : (g.comp (0 : M ->
ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = 0
-/
lemma exact_lcomp_of_exact_of_surjective {f : M1 →ₗ[R] M2} {g : M2 →ₗ[R] M3}
    (exac : Function.Exact f g) (surj : Function.Surjective g) :
    Function.Exact (LinearMap.lcomp R N g) (LinearMap.lcomp R N f) := by
  intro h
  simp only [LinearMap.lcomp_apply', Set.mem_range]
  refine ⟨fun hh ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · use ((LinearMap.range f).liftQ h (LinearMap.range_le_ker_iff.mpr hh)).comp
      (exac.linearEquivOfSurjective surj).symm.toLinearMap
    ext x
    simp
  · rw [← hy, LinearMap.comp_assoc, exac.linearMap_comp_eq_zero, LinearMap.comp_zero y]

end LinearMap

