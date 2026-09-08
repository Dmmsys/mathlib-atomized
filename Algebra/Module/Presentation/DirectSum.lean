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
  (relations : ι → Relations.{w₀, w₁} A)
  {M : ι → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]

namespace Relations

/-- The direct sum operations on `Relations A`. Given a family
`relations : ι → Relations A`, the type of generators and relations
in `directSum relations` are the corresponding `Sigma` types. -/
@[simps G R relation]
/-
**Module.Relations.directSum** 是 Mathlib 中的一个定义，位于命名空间 `Module.Relations`。
形式化陈述：directSum : Relations A where G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direct sum operations on `Relations A`. Given a family
`relations : ι → Relations A`, the type of generators and relations
in `directSum relations` are the corresponding `Sigma` types.
-/
noncomputable def directSum : Relations A where
  G := Σ i, (relations i).G
  R := Σ i, (relations i).R
  relation := fun ⟨i, r⟩ ↦ Finsupp.embDomain (Function.Embedding.sigmaMk
      (β := fun i ↦ (relations i).G) i) ((relations i).relation r)

namespace Solution

variable {relations}
variable {N : Type v} [AddCommGroup N] [Module A N]

/-- Given an `A`-module `N` and a family `relations : ι → Relations A`,
the data of a solution of `Relations.directSum relations` in `N`
is equivalent to the data of a family of solutions of `relations i` in `N`
for all `i`. -/
@[simps]
/-
**Module.Relations.Solution.directSumEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.Rel
ations.Solution`。
形式化陈述：directSumEquiv : (Relations.directSum relations).Solution N ≃ forall i, (r
elations i).Solution N where toFun s i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `A`-module `N` and a family `relations : ι → Relations A`,
the data of a solution of `Relations.directSum relations` in `N`
is equivalent to the data of a family of solutions of `relations i` in `N`
for all `i`.
-/
noncomputable def directSumEquiv :
    (Relations.directSum relations).Solution N ≃
      ∀ i, (relations i).Solution N where
  toFun s i :=
    { var := fun g ↦ s.var ⟨i, g⟩
      linearCombination_var_relation := fun r ↦ by
        rw [← s.linearCombination_var_relation ⟨i, r⟩]
        symm
        apply Finsupp.linearCombination_embDomain }
  invFun t :=
    { var := fun ⟨i, g⟩ ↦ (t i).var g
      linearCombination_var_relation := fun ⟨i, r⟩ ↦ by
        rw [← (t i).linearCombination_var_relation r]
        apply Finsupp.linearCombination_embDomain }

/-- Given `solution : ∀ (i : ι), (relations i).Solution (M i)`, this is the
canonical solution of `Relations.directSum relations` in `⨁ i, M i`. -/
/-
**Module.Relations.Solution.directSum** 是 Mathlib 中的一个定义，位于命名空间 `Module.Relation
s.Solution`。
形式化陈述：directSum (solution : forall (i : ι), (relations i).Solution (M i)) : (Rel
ations.directSum relations).Solution (⨁ i, M i)
参数：solution : forall (i : ι), (relations i).Solution (M i)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given `solution : ∀ (i : ι), (relations i).Solution (M i)`, this is the
canonical solution of `Relations.directSum relations` in `⨁ i, M i`.
-/
noncomputable def directSum (solution : ∀ (i : ι), (relations i).Solution (M i)) :
    (Relations.directSum relations).Solution (⨁ i, M i) :=
  directSumEquiv.symm (fun i ↦ (solution i).postcomp (lof A ι M i))

@[simp]
/-
**Module.Relations.Solution.directSum_var** 是 Mathlib 中的一个引理，位于命名空间 `Module.Rela
tions.Solution`。
形式化陈述：directSum_var (solution : forall (i : ι), (relations i).Solution (M i)) (i
 : ι) (g : (relations i).G) : (directSum solution).var ⟨i, g⟩ = lof A ι M i ((so
lution i).var g)
参数：solution : forall (i : ι), (relations i).Solution (M i)；i : ι；g : (relations 
i).G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma directSum_var (solution : ∀ (i : ι), (relations i).Solution (M i))
    (i : ι) (g : (relations i).G) :
    (directSum solution).var ⟨i, g⟩ = lof A ι M i ((solution i).var g) := rfl

namespace IsPresentation

variable {solution : ∀ (i : ι), (relations i).Solution (M i)}
  (h : ∀ i, (solution i).IsPresentation)

set_option backward.isDefEq.respectTransparency false in
/-- The direct sum admits a presentation by generators and relations. -/
/-
**Module.Relations.Solution.IsPresentation.directSum.isRepresentationCore** 是 Ma
thlib 中的一个定义，位于命名空间 `Module.Relations.Solution.IsPresentation.directSum`。
形式化陈述：{A : Type u} →   [inst : Ring A] →     {ι : Type w} →       [inst_1 : Deci
dableEq ι] →         {relations : ι → Module.Relations A} →           {M : ι → T
ype v} →             [inst_2 : (i : ι) → AddCommGroup (M i)] →               [in
st_3 : (i : ι) → _root_.Module A (M i)] →                 {solution : (i : ι) → 
(relations i).Solution (M i)} →                   (∀ (i : ι), (solution i).IsPre
sentation) →                     (Module.Relations.Solution.directSum solution).
IsPresentationCore
参数：i : ι；M i；i : ι；M i；i : ι；relations i；M i；∀ (i : ι), (solution i).IsPresentat
ion；Module.Relations.Solution.directSum solution。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direct sum admits a presentation by generators and relations.
-/
noncomputable def directSum.isRepresentationCore :
    Solution.IsPresentationCore.{w'} (directSum solution) where
  desc s := DirectSum.toModule _ _ _ (fun i ↦ (h i).desc (directSumEquiv s i))
  postcomp_desc s := by ext ⟨i, g⟩; simp
  postcomp_injective h' := by
    ext i : 1
    apply (h i).postcomp_injective
    ext g
    exact Solution.congr_var h' ⟨i, g⟩

include h in
/-
**Module.Relations.Solution.IsPresentation.directSum** 是 Mathlib 中的一个引理，位于命名空间 `
Module.Relations.Solution.IsPresentation`。
形式化陈述：directSum : (directSum solution).IsPresentation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Relations.Solution.IsPresentationCore.isPresentation`：isPresentat
ion {solution : relations.Solution M} (h : IsPresentationCore.{max u v w₀} solut
ion) : solution.IsPresentation where bijective
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
/-
**Module.Presentation.directSum** 是 Mathlib 中的一个定义，位于命名空间 `Module.Presentation`。
形式化陈述：directSum (pres : forall (i : ι), Presentation A (M i)) : Presentation A (
⨁ i, M i)
参数：pres : forall (i : ι), Presentation A (M i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious presentation of the module `⨁ i, M i` that is obtained from
the data of presentations of the module `M i` for each `i`.
-/
noncomputable def directSum (pres : ∀ (i : ι), Presentation A (M i)) :
    Presentation A (⨁ i, M i) :=
  ofIsPresentation
    (Relations.Solution.IsPresentation.directSum (fun i ↦ (pres i).toIsPresentation))

@[simp]
/-
**Module.Presentation.directSum_var** 是 Mathlib 中的一个引理，位于命名空间 `Module.Presentati
on`。
形式化陈述：directSum_var (pres : forall (i : ι), Presentation A (M i)) (i : ι) (g : (
pres i).G) : (directSum pres).var ⟨i, g⟩ = lof A ι M i ((pres i).var g)
参数：pres : forall (i : ι), Presentation A (M i)；i : ι；g : (pres i).G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma directSum_var (pres : ∀ (i : ι), Presentation A (M i)) (i : ι) (g : (pres i).G) :
    (directSum pres).var ⟨i, g⟩ = lof A ι M i ((pres i).var g) := rfl

section

variable {N : Type v} [AddCommGroup N] [Module A N]
  (pres : Presentation A N) (ι : Type w) [DecidableEq ι] [DecidableEq N]

/-- The obvious presentation of the module `ι →₀ N` that is deduced from a presentation
of the module `N`. -/
@[simps! G R relation]
/-
**Module.Presentation.finsupp** 是 Mathlib 中的一个定义，位于命名空间 `Module.Presentation`。
形式化陈述：finsupp : Presentation A (ι ->₀ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious presentation of the module `ι →₀ N` that is deduced from a presentat
ion
of the module `N`.
-/
noncomputable def finsupp : Presentation A (ι →₀ N) :=
  (directSum (fun (_ : ι) ↦ pres)).ofLinearEquiv (finsuppLequivDFinsupp _).symm

@[simp]
/-
**Module.Presentation.finsupp_var** 是 Mathlib 中的一个引理，位于命名空间 `Module.Presentation
`。
形式化陈述：finsupp_var (i : ι) (g : pres.G) : (finsupp pres ι).var ⟨i, g⟩ = Finsupp.s
ingle i (pres.var g)
参数：i : ι；g : pres.G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用引理 `Module.Presentation.directSum_var`：directSum_var (pres : forall (i : ι),
 Presentation A (M i)) (i : ι) (g : (pres i).G) : (directSum pres).var ⟨i, g⟩ = 
lof A ι M i ((pres i).v…
· 使用定理 `finsuppLequivDFinsupp_apply_apply`：finsuppLequivDFinsupp_apply_apply [De
cidableEq ι] [Semiring R] [AddCommMonoid M] [forall m : M, Decidable (m != 0)] [
Module R M] : (↑(finsup…
· 使用定理 `Finsupp.toDFinsupp_single`：Finsupp.toDFinsupp_single (i : ι) (m : M) : (
Finsupp.single i m).toDFinsupp = DFinsupp.single i m
-/
lemma finsupp_var (i : ι) (g : pres.G) :
    (finsupp pres ι).var ⟨i, g⟩ = Finsupp.single i (pres.var g) := by
  apply (finsuppLequivDFinsupp A).injective
  erw [(finsuppLequivDFinsupp A).apply_symm_apply]
  rw [directSum_var, finsuppLequivDFinsupp_apply_apply, Finsupp.toDFinsupp_single]
  rfl

end

end Presentation

end Module

