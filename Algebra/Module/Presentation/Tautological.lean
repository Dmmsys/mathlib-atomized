/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Module.Presentation.Basic

/-!
# The tautological presentation of a module

Given an `A`-module `M`, we provide its tautological presentation:
* there is a generator `[m]` for each `m : M`;
* the relations are `[m₁] + [m₂] - [m₁ + m₂] = 0` and `a • [m] - [a • m] = 0`.

-/

@[expose] public section

universe w v u

namespace Module

variable (A : Type u) [Ring A] (M : Type v) [AddCommGroup M] [Module A M]

namespace Presentation

/-- The type which parametrizes the tautological relations in an `A`-module `M`. -/
/-
**Module.Presentation.tautological.R** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module.Present
ation.tautological`。
形式化陈述：Type u → Type v → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type which parametrizes the tautological relations in an `A`-module `M`.
-/
inductive tautological.R
  | add (m₁ m₂ : M)
  | smul (a : A) (m : M)

/-- The system of equations corresponding to the tautological presentation of an `A`-module. -/
@[simps]
/-
**Module.Presentation.tautologicalRelations** 是 Mathlib 中的一个定义，位于命名空间 `Module.Pr
esentation`。
形式化陈述：tautologicalRelations : Relations A where G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The system of equations corresponding to the tautological presentation of an `A`
-module.
-/
noncomputable def tautologicalRelations : Relations A where
  G := M
  R := tautological.R A M
  relation
    | .add m₁ m₂ => Finsupp.single m₁ 1 + Finsupp.single m₂ 1 - Finsupp.single (m₁ + m₂) 1
    | .smul a m => a • Finsupp.single m 1 - Finsupp.single (a • m) 1

set_option backward.isDefEq.respectTransparency false in
variable {A M} in
/-- Solutions of `tautologicalRelations A M` in an `A`-module `N` identify to `M →ₗ[A] N`. -/
/-
**Module.Presentation.tautologicalRelationsSolutionEquiv** 是 Mathlib 中的一个定义，位于命名
空间 `Module.Presentation`。
形式化陈述：tautologicalRelationsSolutionEquiv {N : Type w} [AddCommGroup N] [Module A
 N] : (tautologicalRelations A M).Solution N ≃ (M ->ₗ[A] N) where toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Solutions of `tautologicalRelations A M` in an `A`-module `N` identify to `M →ₗ[
A] N`.
-/
noncomputable def tautologicalRelationsSolutionEquiv {N : Type w} [AddCommGroup N] [Module A N] :
    (tautologicalRelations A M).Solution N ≃ (M →ₗ[A] N) where
  toFun s :=
    { toFun := s.var
      map_add' := fun m₁ m₂ ↦ by
        symm
        rw [← sub_eq_zero]
        simpa using s.linearCombination_var_relation (.add m₁ m₂)
      map_smul' := fun a m ↦ by
        symm
        rw [← sub_eq_zero]
        simpa using s.linearCombination_var_relation (.smul a m) }
  invFun f :=
    { var := f
      linearCombination_var_relation := by rintro (_ | _) <;> simp }

/-- The obvious solution of `tautologicalRelations A M` in the module `M`. -/
@[simps! var]
/-
**Module.Presentation.tautologicalSolution** 是 Mathlib 中的一个定义，位于命名空间 `Module.Pre
sentation`。
形式化陈述：tautologicalSolution : (tautologicalRelations A M).Solution M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The obvious solution of `tautologicalRelations A M` in the module `M`.
-/
noncomputable def tautologicalSolution : (tautologicalRelations A M).Solution M :=
  tautologicalRelationsSolutionEquiv.symm .id

/-- Any `A`-module admits a tautological presentation by generators and relations. -/
/-
**Module.Presentation.tautologicalSolutionIsPresentationCore** 是 Mathlib 中的一个定义，
位于命名空间 `Module.Presentation`。
形式化陈述：tautologicalSolutionIsPresentationCore : Relations.Solution.IsPresentation
Core.{w} (tautologicalSolution A M) where desc s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any `A`-module admits a tautological presentation by generators and relations.
-/
noncomputable def tautologicalSolutionIsPresentationCore :
    Relations.Solution.IsPresentationCore.{w} (tautologicalSolution A M) where
  desc s := tautologicalRelationsSolutionEquiv s
  postcomp_desc _ := rfl
  postcomp_injective h := by
    ext m
    exact Relations.Solution.congr_var h m
/-
**Module.Presentation.tautologicalSolution_isPresentation** 是 Mathlib 中的一个引理，位于命
名空间 `Module.Presentation`。
形式化陈述：tautologicalSolution_isPresentation : (tautologicalSolution A M).IsPresent
ation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Relations.Solution.IsPresentationCore.isPresentation`：isPresentat
ion {solution : relations.Solution M} (h : IsPresentationCore.{max u v w₀} solut
ion) : solution.IsPresentation where bijective
-/
lemma tautologicalSolution_isPresentation :
    (tautologicalSolution A M).IsPresentation :=
  (tautologicalSolutionIsPresentationCore A M).isPresentation

/-- The tautological presentation of any `A`-module `M` by generators and relations.
There is a generator `[m]` for any element `m : M`, and there are two types of relations:
* `[m₁] + [m₂] - [m₁ + m₂] = 0`
* `a • [m] - [a • m] = 0`. -/
@[simps!]
/-
**Module.Presentation.tautological** 是 Mathlib 中的一个定义，位于命名空间 `Module.Presentatio
n`。
形式化陈述：tautological : Presentation A M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Presentation.tautologicalSolution_isPresentation`：tautologicalSol
ution_isPresentation : (tautologicalSolution A M).IsPresentation

--- 原说明 ---
The tautological presentation of any `A`-module `M` by generators and relations.
There is a generator `[m]` for any element `m : M`, and there are two types of r
elations:
* `[m₁] + [m₂] - [m₁ + m₂] = 0`
* `a • [m] - [a • m] = 0`.
-/
noncomputable def tautological : Presentation A M :=
  ofIsPresentation (tautologicalSolution_isPresentation A M)

end Presentation

end Module

