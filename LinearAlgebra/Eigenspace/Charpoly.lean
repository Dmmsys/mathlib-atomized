/-
Copyright (c) 2025 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Eigenvalues are the roots of the characteristic polynomial.

## Tags

eigenvalue, characteristic polynomial
-/

public section

namespace Module

namespace End

open LinearMap

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

/--
The roots of the characteristic polynomial are exactly the eigenvalues.

`R` is required to be an integral domain, otherwise there is the counterexample:
R = M = Z/6Z, f(x) = 2x, v = 3, μ = 4, but p = X - 2.
-/
/-
**Module.End.hasEigenvalue_iff_isRoot_charpoly** 是 Mathlib 中的一个引理，位于命名空间 `Module
.End`。
形式化陈述：hasEigenvalue_iff_isRoot_charpoly (f : End R M) (μ : R) : f.HasEigenvalue 
μ ↔ f.charpoly.IsRoot μ
参数：f : End R M；μ : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.hasEigenvalue_iff`：hasEigenvalue_iff {f : End R M} {μ : R} : 
f.HasEigenvalue μ ↔ f.eigenspace μ != ⊥
· 使用引理 `Module.End.eigenspace_def`：eigenspace_def {f : End R M} {μ : R} : f.eige
nspace μ = LinearMap.ker (f - μ • 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_eq_zero_iff_ker_ne_bot`：det_eq_zero_iff_ker_ne_bot [IsDoma
in R] [Free R M] [Module.Finite R M] {f : M ->ₗ[R] M} : f.det = 0 ↔ ker f != ⊥
· 使用引理 `LinearMap.det_eq_sign_charpoly_coeff`：LinearMap.det_eq_sign_charpoly_coe
ff : LinearMap.det f = (-1) ^ Module.finrank R M * f.charpoly.coeff 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.charpoly_sub_smul`：charpoly_sub_smul (f : Module.End R M) (μ :
 R) : (f - μ • 1).charpoly = f.charpoly.comp (X + C μ)
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The roots of the characteristic polynomial are exactly the eigenvalues.

`R` is required to be an integral domain, otherwise there is the counterexample:
R = M = Z/6Z, f(x) = 2x, v = 3, μ = 4, but p = X - 2.
-/
lemma hasEigenvalue_iff_isRoot_charpoly (f : End R M) (μ : R) :
    f.HasEigenvalue μ ↔ f.charpoly.IsRoot μ := by
  rw [hasEigenvalue_iff, eigenspace_def, ← det_eq_zero_iff_ker_ne_bot, det_eq_sign_charpoly_coeff]
  simp [Polynomial.coeff_zero_eq_eval_zero, charpoly_sub_smul]
/-
**Module.End.mem_spectrum_iff_isRoot_charpoly** 是 Mathlib 中的一个引理，位于命名空间 `Module.
End`。
形式化陈述：mem_spectrum_iff_isRoot_charpoly (f : End K V) (μ : K) : μ in spectrum K f
 ↔ f.charpoly.IsRoot μ
参数：f : End K V；μ : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.hasEigenvalue_iff_mem_spectrum`：hasEigenvalue_iff_mem_spectru
m [FiniteDimensional K V] {f : End K V} {μ : K} : f.HasEigenvalue μ ↔ μ in spect
rum K f
· 使用引理 `Module.End.hasEigenvalue_iff_isRoot_charpoly`：hasEigenvalue_iff_isRoot_c
harpoly (f : End R M) (μ : R) : f.HasEigenvalue μ ↔ f.charpoly.IsRoot μ
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_spectrum_iff_isRoot_charpoly (f : End K V) (μ : K) :
    μ ∈ spectrum K f ↔ f.charpoly.IsRoot μ := by
  rw [← hasEigenvalue_iff_mem_spectrum, hasEigenvalue_iff_isRoot_charpoly]
/-
**Module.End.det_eq_prod_roots_charpoly_of_splits** 是 Mathlib 中的一个引理，位于命名空间 `Mod
ule.End`。
形式化陈述：det_eq_prod_roots_charpoly_of_splits {f : End K V} (h : f.charpoly.Splits)
 : f.det = f.charpoly.roots.prod
参数：h : f.charpoly.Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Matrix.det_eq_prod_roots_charpoly_of_splits`：det_eq_prod_roots_charpoly_
of_splits [IsDomain R] (hAps : B.charpoly.Splits) : B.det = (Matrix.charpoly B).
roots.prod
· 使用定理 `LinearMap.charpoly_toMatrix`：charpoly_toMatrix {ι : Type w} [DecidableEq
 ι] [Fintype ι] (b : Basis ι R M) : (toMatrix b b f).charpoly = f.charpoly
-/
lemma det_eq_prod_roots_charpoly_of_splits {f : End K V} (h : f.charpoly.Splits) :
    f.det = f.charpoly.roots.prod := by
  rw [← det_toMatrix (Module.Free.chooseBasis K V),
    Matrix.det_eq_prod_roots_charpoly_of_splits (by simpa using h), charpoly_toMatrix]
/-
**Module.End.trace_eq_sum_roots_charpoly_of_splits** 是 Mathlib 中的一个引理，位于命名空间 `Mo
dule.End`。
形式化陈述：trace_eq_sum_roots_charpoly_of_splits {f : End K V} (h : f.charpoly.Splits
) : f.trace K V = f.charpoly.roots.sum
参数：h : f.charpoly.Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_eq_matrix_trace`：trace_eq_matrix_trace (f : M ->ₗ[R] M) 
: trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用定理 `Matrix.trace_eq_sum_roots_charpoly_of_splits`：trace_eq_sum_roots_charpol
y_of_splits [IsDomain R] (hAps : B.charpoly.Splits) : B.trace = (Matrix.charpoly
 B).roots.sum
· 使用定理 `LinearMap.charpoly_toMatrix`：charpoly_toMatrix {ι : Type w} [DecidableEq
 ι] [Fintype ι] (b : Basis ι R M) : (toMatrix b b f).charpoly = f.charpoly
-/
lemma trace_eq_sum_roots_charpoly_of_splits {f : End K V} (h : f.charpoly.Splits) :
    f.trace K V = f.charpoly.roots.sum := by
  let b := Module.Free.chooseBasis K V
  rw [trace_eq_matrix_trace K (Module.Free.chooseBasis K V),
    Matrix.trace_eq_sum_roots_charpoly_of_splits (by simpa using h), charpoly_toMatrix]

end End

end Module

