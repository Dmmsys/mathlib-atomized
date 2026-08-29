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

/--
Inductive type `tautological.R` / 归纳类型 `tautological.R`

English:
inductive tautological.R
  constructors (2):
    - add: (m₁ m₂ : M)
    - smul: (a : A) (m : M)

中文:
归纳类型 tautological.R
  构造子 (2 个):
    - add: (m₁ m₂ : M)
    - smul: (a : A) (m : M)
-/
inductive tautological.R
  | add (m₁ m₂ : M)
  | smul (a : A) (m : M)

/-- The system of equations corresponding to the tautological presentation of an `A`-module. -/
@[simps]
/--
Definition of `tautologicalRelations` / `tautologicalRelations` 的定义

English:
definition tautologicalRelations
  signature: : Relations A where
  body: M
  R := tautological.R A M
  relation
    | .add m₁ m₂ => Finsupp.single m₁ 1 + Finsupp.single m₂ 1 - Finsupp.single (m₁ + m₂) 1
    | .smul a m => a • Finsupp.single m 1 - Finsupp.single (a • m) 1

中文:
定义 tautologicalRelations
  签名: : Relations A where
  定义体: M
  R := tautological.R A M
  relation
    | .add m₁ m₂ => Finsupp.single m₁ 1 + Finsupp.single m₂ 1 - Finsupp.single (m₁ + m₂) 1
    | .smul a m => a • Finsupp.single m 1 - Finsupp.single (a • m) 1
-/
noncomputable def tautologicalRelations : Relations A where
  G := M
  R := tautological.R A M
  relation
    | .add m₁ m₂ => Finsupp.single m₁ 1 + Finsupp.single m₂ 1 - Finsupp.single (m₁ + m₂) 1
    | .smul a m => a • Finsupp.single m 1 - Finsupp.single (a • m) 1

set_option backward.isDefEq.respectTransparency false in
variable {A M} in
/--
Definition of `tautologicalRelationsSolutionEquiv` / `tautologicalRelationsSolutionEquiv` 的定义

English:
definition tautologicalRelationsSolutionEquiv
  signature: {N : Type w} [AddCommGroup N] [Module A N]
  body: { toFun := s.var
      map_add' := fun m₁ m₂ => by
        symm
        rw [← sub_eq_zero]
        simpa using s.linearCombination_var_relation (.add m₁ m₂)
      map_smul' := fun a m => by
        symm
        rw [← sub_eq_zero]
        simpa using s.linearCombination_var_relation (.smul a m) }
  i

中文:
定义 tautologicalRelationsSolutionEquiv
  签名: {N : Type w} [AddCommGroup N] [Module A N]
  定义体: { toFun := s.var
      map_add' := fun m₁ m₂ => by
        symm
        rw [← sub_eq_zero]
        simpa using s.linearCombination_var_relation (.add m₁ m₂)
      map_smul' := fun a m => by
        symm
        rw [← sub_eq_zero]
        simpa using s.linearCombination_var_relation (.smul a m) }
  i

Depends on / 依赖: invFun, linearCombination_var_relation, map_add, map_smul, s.linearCombination_var_relation, s.var, sub_eq_zero
-/
noncomputable def tautologicalRelationsSolutionEquiv {N : Type w} [AddCommGroup N] [Module A N] :
    (tautologicalRelations A M).Solution N ≃ (M ->ₗ[A] N) where
  toFun s :=
    { toFun := s.var
      map_add' := fun m₁ m₂ => by
        symm
        rw [← sub_eq_zero]
        simpa using s.linearCombination_var_relation (.add m₁ m₂)
      map_smul' := fun a m => by
        symm
        rw [← sub_eq_zero]
        simpa using s.linearCombination_var_relation (.smul a m) }
  invFun f :=
    { var := f
      linearCombination_var_relation := by rintro (_ | _) <;> simp }

/-- The obvious solution of `tautologicalRelations A M` in the module `M`. -/
@[simps! var]
/--
Definition of `tautologicalSolution` / `tautologicalSolution` 的定义

English:
definition tautologicalSolution
  signature: : (tautologicalRelations A M).Solution M
  body: tautologicalRelationsSolutionEquiv.symm .id

中文:
定义 tautologicalSolution
  签名: : (tautologicalRelations A M).Solution M
  定义体: tautologicalRelationsSolutionEquiv.symm .id

Depends on / 依赖: tautologicalRelationsSolutionEquiv, tautologicalRelationsSolutionEquiv.symm
-/
noncomputable def tautologicalSolution : (tautologicalRelations A M).Solution M :=
  tautologicalRelationsSolutionEquiv.symm .id

/--
Definition of `tautologicalSolutionIsPresentationCore` / `tautologicalSolutionIsPresentationCore` 的定义

English:
definition tautologicalSolutionIsPresentationCore
  signature: :
  body: tautologicalRelationsSolutionEquiv s
  postcomp_desc _ := rfl
  postcomp_injective h := by
    ext m
    exact Relations.Solution.congr_var h m

中文:
定义 tautologicalSolutionIsPresentationCore
  签名: :
  定义体: tautologicalRelationsSolutionEquiv s
  postcomp_desc _ := rfl
  postcomp_injective h := by
    ext m
    exact Relations.Solution.congr_var h m

Depends on / 依赖: tautologicalRelationsSolutionEquiv
-/
noncomputable def tautologicalSolutionIsPresentationCore :
    Relations.Solution.IsPresentationCore.{w} (tautologicalSolution A M) where
  desc s := tautologicalRelationsSolutionEquiv s
  postcomp_desc _ := rfl
  postcomp_injective h := by
    ext m
    exact Relations.Solution.congr_var h m

/--
lemma `tautologicalSolution_isPresentation` / 引理 `tautologicalSolution_isPresentation`

English:
lemma tautologicalSolution_isPresentation
  proof: (tautologicalSolutionIsPresentationCore A M).isPresentation

中文:
引理 tautologicalSolution_isPresentation
  证明: (tautologicalSolutionIsPresentationCore A M).isPresentation

Depends on / 依赖: isPresentation, tautologicalSolutionIsPresentationCore
-/
lemma tautologicalSolution_isPresentation :
    (tautologicalSolution A M).IsPresentation :=
  (tautologicalSolutionIsPresentationCore A M).isPresentation

/-- The tautological presentation of any `A`-module `M` by generators and relations.
There is a generator `[m]` for any element `m : M`, and there are two types of relations:
* `[m₁] + [m₂] - [m₁ + m₂] = 0`
* `a • [m] - [a • m] = 0`. -/
@[simps!]
/--
Definition of `tautological` / `tautological` 的定义

English:
definition tautological
  signature: : Presentation A M
  body: ofIsPresentation (tautologicalSolution_isPresentation A M)

中文:
定义 tautological
  签名: : Presentation A M
  定义体: ofIsPresentation (tautologicalSolution_isPresentation A M)

Depends on / 依赖: ofIsPresentation, tautologicalSolution_isPresentation
-/
noncomputable def tautological : Presentation A M :=
  ofIsPresentation (tautologicalSolution_isPresentation A M)

end Presentation

end Module
