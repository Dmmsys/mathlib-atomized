/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Module.Presentation.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Presentation of a direct sum

If `M : ι → Type _` is a family of `A`-modules, then the data of a presentation
of each `M i`, we obtain a presentation of the module `⨁ i, M i`.
In particular, from a presentation of an `A`-module `M`, we get
a presentation of `ι →₀ M`.

-/

@[expose] public section

universe w' w₀ w₁ w v u

namespace Module

open DirectSum

variable {A : Type u} [Ring A] {ι : Type w} [DecidableEq ι]
  (relations : ι -> Relations.{w₀, w₁} A)
  {M : ι -> Type v} [forall i, AddCommGroup (M i)] [forall i, Module A (M i)]

namespace Relations

/-- The direct sum operations on `Relations A`. Given a family
`relations : ι → Relations A`, the type of generators and relations
in `directSum relations` are the corresponding `Sigma` types. -/
@[simps G R relation]
/--
Definition of `directSum` / `directSum` 的定义

English:
definition directSum
  signature: : Relations A where
  body: Σ i, (relations i).G
  R := Σ i, (relations i).R
  relation := fun ⟨i, r⟩ => Finsupp.embDomain (Function.Embedding.sigmaMk
      (β := fun i => (relations i).G) i) ((relations i).relation r)

中文:
定义 directSum
  签名: : 关系 A where
  定义体: Σ i, (relations i).G
  R := Σ i, (relations i).R
  relation := fun ⟨i, r⟩ => Finsupp.embDomain (Function.Embedding.sigmaMk
      (β := fun i => (relations i).G) i) ((relations i).relation r)

Depends on / 依赖: relations
-/
noncomputable def directSum : Relations A where
  G := Σ i, (relations i).G
  R := Σ i, (relations i).R
  relation := fun ⟨i, r⟩ => Finsupp.embDomain (Function.Embedding.sigmaMk
      (β := fun i => (relations i).G) i) ((relations i).relation r)

namespace Solution

variable {relations}
variable {N : Type v} [AddCommGroup N] [Module A N]

/-- Given an `A`-module `N` and a family `relations : ι → Relations A`,
the data of a solution of `Relations.directSum relations` in `N`
is equivalent to the data of a family of solutions of `relations i` in `N`
for all `i`. -/
@[simps]
/--
Definition of `directSumEquiv` / `directSumEquiv` 的定义

English:
definition directSumEquiv
  signature: :
  body: { var := fun g => s.var ⟨i, g⟩
      linearCombination_var_relation := fun r => by
        rw [← s.linearCombination_var_relation ⟨i]; rw [r⟩]
        symm
        apply Finsupp.linearCombination_embDomain }
  invFun t :=
    { var := fun ⟨i, g⟩ => (t i).var g
      linearCombination_var_relation := fun ⟨i, r⟩ => by
        rw [← (t i).linearCombination_var_relation r]
        apply Finsupp.linearCombination_embDomain }

中文:
定义 directSumEquiv
  签名: :
  定义体: { var := fun g => s.var ⟨i, g⟩
      linearCombination_var_relation := fun r => by
        rw [← s.linearCombination_var_relation ⟨i]; rw [r⟩]
        symm
        apply Finsupp.linearCombination_embDomain }
  invFun t :=
    { var := fun ⟨i, g⟩ => (t i).var g
      linearCombination_var_relation := fun ⟨i, r⟩ => by
        rw [← (t i).linearCombination_var_relation r]
        apply Finsupp.linearCombination_embDomain }

Depends on / 依赖: Finsupp, Finsupp.linearCombination_embDomain, invFun, linearCombination_embDomain, linearCombination_var_relation, s.linearCombination_var_relation, s.var
-/
noncomputable def directSumEquiv :
    (Relations.directSum relations).Solution N ≃
      forall i, (relations i).Solution N where
  toFun s i :=
    { var := fun g => s.var ⟨i, g⟩
      linearCombination_var_relation := fun r => by
        rw [← s.linearCombination_var_relation ⟨i]; rw [r⟩]
        symm
        apply Finsupp.linearCombination_embDomain }
  invFun t :=
    { var := fun ⟨i, g⟩ => (t i).var g
      linearCombination_var_relation := fun ⟨i, r⟩ => by
        rw [← (t i).linearCombination_var_relation r]
        apply Finsupp.linearCombination_embDomain }

/--
Definition of `directSum` / `directSum` 的定义

English:
definition directSum
  signature: (solution : forall (i : ι), (relations i).Solution (M i))
  body: directSumEquiv.symm (fun i => (solution i).postcomp (lof A ι M i))

@[simp]

中文:
定义 directSum
  签名: (solution : 对任意 (i : ι), (relations i).解 (M i))
  定义体: directSumEquiv.symm (fun i => (solution i).postcomp (lof A ι M i))

@[simp]

Depends on / 依赖: directSumEquiv, directSumEquiv.symm, postcomp, solution
-/
noncomputable def directSum (solution : forall (i : ι), (relations i).Solution (M i)) :
    (Relations.directSum relations).Solution (⨁ i, M i) :=
  directSumEquiv.symm (fun i => (solution i).postcomp (lof A ι M i))

@[simp]
/--
lemma `directSum_var` / 引理 `directSum_var`

English:
lemma directSum_var
  statement: (solution : forall (i : ι), (relations i).Solution (M i))
  proof: rfl

中文:
引理 directSum_var
  结论: (solution : 对任意 (i : ι), (relations i).解 (M i))
  证明: rfl
-/
lemma directSum_var (solution : forall (i : ι), (relations i).Solution (M i))
    (i : ι) (g : (relations i).G) :
    (directSum solution).var ⟨i, g⟩ = lof A ι M i ((solution i).var g) := rfl

namespace IsPresentation

variable {solution : forall (i : ι), (relations i).Solution (M i)}
  (h : forall i, (solution i).IsPresentation)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `directSum.isRepresentationCore` / `directSum.isRepresentationCore` 的定义

English:
definition directSum.isRepresentationCore
  signature: :
  body: DirectSum.toModule _ _ _ (fun i => (h i).desc (directSumEquiv s i))
  postcomp_desc s := by ext ⟨i, g⟩; simp
  postcomp_injective h' := by
    ext i : 1
    apply (h i).postcomp_injective
    ext g
    exact Solution.congr_var h' ⟨i, g⟩

include h in

中文:
定义 directSum.isRepresentationCore
  签名: :
  定义体: DirectSum.toModule _ _ _ (fun i => (h i).desc (directSumEquiv s i))
  postcomp_desc s := by ext ⟨i, g⟩; simp
  postcomp_injective h' := by
    ext i : 1
    apply (h i).postcomp_injective
    ext g
    exact Solution.congr_var h' ⟨i, g⟩

include h in

Depends on / 依赖: DirectSum, DirectSum.toModule, directSumEquiv, toModule
-/
noncomputable def directSum.isRepresentationCore :
    Solution.IsPresentationCore.{w'} (directSum solution) where
  desc s := DirectSum.toModule _ _ _ (fun i => (h i).desc (directSumEquiv s i))
  postcomp_desc s := by ext ⟨i, g⟩; simp
  postcomp_injective h' := by
    ext i : 1
    apply (h i).postcomp_injective
    ext g
    exact Solution.congr_var h' ⟨i, g⟩

include h in
/--
lemma `directSum` / 引理 `directSum`

English:
lemma directSum
  statement: (directSum solution).IsPresentation
  proof: (directSum.isRepresentationCore h).isPresentation

中文:
引理 directSum
  结论: (directSum solution).是呈现
  证明: (directSum.isRepresentationCore h).isPresentation

Depends on / 依赖: directSum, directSum.isRepresentationCore, isPresentation, isRepresentationCore
-/
lemma directSum : (directSum solution).IsPresentation :=
  (directSum.isRepresentationCore h).isPresentation

end IsPresentation

end Solution

end Relations

namespace Presentation

/-- The obvious presentation of the module `⨁ i, M i` that is obtained from
the data of presentations of the module `M i` for each `i`. -/
@[simps! G R relation]
/--
Definition of `directSum` / `directSum` 的定义

English:
definition directSum
  signature: (pres : forall (i : ι), Presentation A (M i))
  body: ofIsPresentation
    (Relations.Solution.IsPresentation.directSum (fun i => (pres i).toIsPresentation))

@[simp]

中文:
定义 directSum
  签名: (pres : 对任意 (i : ι), 呈现 A (M i))
  定义体: ofIsPresentation
    (Relations.Solution.IsPresentation.directSum (fun i => (pres i).toIsPresentation))

@[simp]

Depends on / 依赖: IsPresentation, Relations, Relations.Solution.IsPresentation.directSum, Solution, directSum, ofIsPresentation, toIsPresentation
-/
noncomputable def directSum (pres : forall (i : ι), Presentation A (M i)) :
    Presentation A (⨁ i, M i) :=
  ofIsPresentation
    (Relations.Solution.IsPresentation.directSum (fun i => (pres i).toIsPresentation))

@[simp]
/--
lemma `directSum_var` / 引理 `directSum_var`

English:
lemma directSum_var
  given: (pres : forall (i : ι), Presentation A (M i)) (i : ι) (g : (pres i).G)
  proof: rfl

中文:
引理 directSum_var
  条件: (pres : 对任意 (i : ι), 呈现 A (M i)) (i : ι) (g : (pres i).G)
  证明: rfl
-/
lemma directSum_var (pres : forall (i : ι), Presentation A (M i)) (i : ι) (g : (pres i).G) :
    (directSum pres).var ⟨i, g⟩ = lof A ι M i ((pres i).var g) := rfl

section

variable {N : Type v} [AddCommGroup N] [Module A N]
  (pres : Presentation A N) (ι : Type w) [DecidableEq ι] [DecidableEq N]

/-- The obvious presentation of the module `ι →₀ N` that is deduced from a presentation
of the module `N`. -/
@[simps! G R relation]
/--
Definition of `finsupp` / `finsupp` 的定义

English:
definition finsupp
  signature: : Presentation A (ι ->₀ N)
  body: (directSum (fun (_ : ι) => pres)).ofLinearEquiv (finsuppLequivDFinsupp _).symm

@[simp]

中文:
定义 finsupp
  签名: : 呈现 A (ι ->₀ N)
  定义体: (directSum (fun (_ : ι) => pres)).ofLinearEquiv (finsuppLequivDFinsupp _).symm

@[simp]

Depends on / 依赖: directSum, finsuppLequivDFinsupp, ofLinearEquiv
-/
noncomputable def finsupp : Presentation A (ι ->₀ N) :=
  (directSum (fun (_ : ι) => pres)).ofLinearEquiv (finsuppLequivDFinsupp _).symm

@[simp]
/--
lemma `finsupp_var` / 引理 `finsupp_var`

English:
lemma finsupp_var
  given: (i : ι) (g : pres.G)
  proof: by
  apply (finsuppLequivDFinsupp A).injective
  erw [(finsuppLequivDFinsupp A).apply_symm_apply]
  rw [directSum_var]; rw [finsuppLequivDFinsupp_apply_apply]; rw [Finsupp.toDFinsupp_single]
  rfl

中文:
引理 finsupp_var
  条件: (i : ι) (g : pres.G)
  证明: by
  apply (finsuppLequivDFinsupp A).injective
  erw [(finsuppLequivDFinsupp A).apply_symm_apply]
  rw [directSum_var]; rw [finsuppLequivDFinsupp_apply_apply]; rw [Finsupp.toDFinsupp_single]
  rfl

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp_single, apply_symm_apply, directSum_var, finsuppLequivDFinsupp, finsuppLequivDFinsupp_apply_apply, injective, toDFinsupp_single
-/
lemma finsupp_var (i : ι) (g : pres.G) :
    (finsupp pres ι).var ⟨i, g⟩ = Finsupp.single i (pres.var g) := by
  apply (finsuppLequivDFinsupp A).injective
  erw [(finsuppLequivDFinsupp A).apply_symm_apply]
  rw [directSum_var]; rw [finsuppLequivDFinsupp_apply_apply]; rw [Finsupp.toDFinsupp_single]
  rfl

end

end Presentation

end Module
