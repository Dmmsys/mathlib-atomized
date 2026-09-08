/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Module.Presentation.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Logic.UnivLE

/-!
# Presentation of free modules

A module is free iff it admits a presentation with generators but no relation,
see `Module.free_iff_exists_presentation`.

-/

@[expose] public section

assert_not_exists Cardinal

universe w w₀ w₁ v u

namespace Module

variable {A : Type u} [Ring A] (relations : Relations.{w₀, w₁} A)
  (M : Type v) [AddCommGroup M] [Module A M]

namespace Relations

variable [IsEmpty relations.R]

/-- If `relations : Relations A` involved no relation, then it has an obvious
solution in the module `relations.G →₀ A`. -/
@[simps]
/-
**Module.Relations.solutionFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Module.Relations`。
形式化陈述：solutionFinsupp : relations.Solution (relations.G ->₀ A) where var g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `relations : Relations A` involved no relation, then it has an obvious
solution in the module `relations.G →₀ A`.
-/
noncomputable def solutionFinsupp : relations.Solution (relations.G →₀ A) where
  var g := Finsupp.single g 1
  linearCombination_var_relation r := by exfalso; exact IsEmpty.false r

/-- If `relations : Relations A` involves no relations (`[IsEmpty relations.R]`),
then the free module `relations.G →₀ A` satisfies the universal property of the
corresponding module defined by generators (and relations). -/
/-
**Module.Relations.solutionFinsupp.isPresentationCore** 是 Mathlib 中的一个定义，位于命名空间 
`Module.Relations.solutionFinsupp`。
形式化陈述：{A : Type u} →   [inst : Ring A] →     (relations : Module.Relations A) → 
[inst_1 : IsEmpty relations.R] → relations.solutionFinsupp.IsPresentationCore
参数：relations : Module.Relations A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `relations : Relations A` involves no relations (`[IsEmpty relations.R]`),
then the free module `relations.G →₀ A` satisfies the universal property of the
corresponding module defined by generators (and relations).
-/
noncomputable def solutionFinsupp.isPresentationCore :
    Solution.IsPresentationCore.{w} relations.solutionFinsupp where
  desc s := Finsupp.linearCombination _ s.var
  postcomp_desc := by aesop
  postcomp_injective h := by ext; apply Solution.congr_var h
/-
**Module.Relations.solutionFinsupp_isPresentation** 是 Mathlib 中的一个引理，位于命名空间 `Mod
ule.Relations`。
形式化陈述：solutionFinsupp_isPresentation : relations.solutionFinsupp.IsPresentation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Relations.Solution.IsPresentationCore.isPresentation`：isPresentat
ion {solution : relations.Solution M} (h : IsPresentationCore.{max u v w₀} solut
ion) : solution.IsPresentation where bijective
-/
lemma solutionFinsupp_isPresentation :
    relations.solutionFinsupp.IsPresentation :=
  (solutionFinsupp.isPresentationCore relations).isPresentation

variable {relations}
/-
**Module.Relations.Solution.IsPresentation.free** 是 Mathlib 中的一个定理，位于命名空间 `Modul
e.Relations.Solution.IsPresentation`。
形式化陈述：∀ {A : Type u} [inst : Ring A] {relations : Module.Relations A} (M : Type 
v) [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module A M] [IsEmpty relations.R
] {solution : relations.Solution M},   solution.IsPresentation → Module.Free A M
参数：M : Type v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用引理 `Module.Relations.solutionFinsupp_isPresentation`：solutionFinsupp_isPrese
ntation : relations.solutionFinsupp.IsPresentation
· 使用定理 `Module.Free.finsupp`：∀ (R : Type u_1) (M : Type u_2) (ι : Type u_3) [ins
t : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Modul
e.Free R …
-/
lemma Solution.IsPresentation.free {solution : relations.Solution M}
    (h : solution.IsPresentation) :
    Module.Free A M :=
  Free.of_equiv ((solutionFinsupp_isPresentation relations).uniq h)

end Relations

variable (A)

/-- The presentation of the `A`-module `G →₀ A` with generators indexed by `G`,
and no relation. (Note that there is an auxiliary universe parameter `w₁` for the
empty type `R`.) -/
@[simps! G R var]
/-
**Module.presentationFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：presentationFinsupp (G : Type w₀) : Presentation.{w₀, w₁} A (G ->₀ A) wher
e G
参数：G : Type w₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presentation of the `A`-module `G →₀ A` with generators indexed by `G`,
and no relation. (Note that there is an auxiliary universe parameter `w₁` for th
e
empty type `R`.)
-/
noncomputable def presentationFinsupp (G : Type w₀) :
    Presentation.{w₀, w₁} A (G →₀ A) where
  G := G
  R := PEmpty.{w₁ + 1}
  relation := by rintro ⟨⟩
  toSolution := Relations.solutionFinsupp _
  toIsPresentation := by exact Relations.solutionFinsupp_isPresentation _

set_option backward.defeqAttrib.useBackward true in
/-
**Module.free_iff_exists_presentation** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：free_iff_exists_presentation : Free A M ↔ exists (p : Presentation.{v, w₁}
 A M), IsEmpty p.R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.free_def`：free_def [Small.{w, v} M] : Free R M ↔ exists I : Type 
w, Nonempty (Basis I R M) where mp h
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Module.Relations.Solution.IsPresentation.free`：∀ {A : Type u} [inst : Ri
ng A] {relations : Module.Relations A} (M : Type v) [inst_1 : AddCommGroup M]   
[inst_2 : _root_.Module A M] [IsEmp…
· 使用定理 `Module.Presentation.toIsPresentation`：∀ {A : Type u} [inst : Ring A] {M 
: Type v} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module A M]   (self : Modul
e.Presentation A M), self.…
-/
lemma free_iff_exists_presentation :
    Free A M ↔ ∃ (p : Presentation.{v, w₁} A M), IsEmpty p.R := by
  constructor
  · rw [free_def.{_, _, v}]
    rintro ⟨G, ⟨⟨e⟩⟩⟩
    exact ⟨(presentationFinsupp A G).ofLinearEquiv e.symm, by dsimp; infer_instance⟩
  · rintro ⟨p, h⟩
    exact p.toIsPresentation.free

end Module

