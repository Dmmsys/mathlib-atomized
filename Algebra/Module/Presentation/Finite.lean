/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Module.Presentation.Basic
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Characterization of finitely presented modules

A module is finitely presented (in the sense of `Module.FinitePresentation`) iff
it admits a presentation with finitely many generators and relations.

-/

public section

universe w₀ w₁ v u

namespace Module

variable {A : Type u} [Ring A] {M : Type v} [AddCommGroup M] [Module A M]

namespace Presentation

variable (pres : Presentation A M)

/-
**Module.Presentation.finite** 是 Mathlib 中的一个引理，位于命名空间 `Module.Presentation`。
形式化陈述：finite [Finite pres.G] : Module.Finite A M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用引理 `Module.Relations.Solution.IsPresentation.surjective_π`：surjective_π : Fu
nction.Surjective solution.π
· 使用定理 `Module.Presentation.toIsPresentation`：∀ {A : Type u} [inst : Ring A] {M 
: Type v} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module A M]   (self : Modul
e.Presentation A M), self.…
-/
lemma finite [Finite pres.G] :
    Module.Finite A M :=
  Finite.of_surjective _ pres.surjective_π
/-
**Module.Presentation.finitePresentation** 是 Mathlib 中的一个引理，位于命名空间 `Module.Prese
ntation`。
形式化陈述：finitePresentation [Finite pres.G] [Finite pres.R] : Module.FinitePresenta
tion A M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.finitePresentation_of_surjective`：Module.finitePresentation_of_su
rjective [h : Module.FinitePresentation R M] (l : M ->ₗ[R] N) (hl : Function.Sur
jective l) (hl' : (LinearMap.…
· 使用定理 `instFinitePresentationFinsupp`：∀ {R : Type u_1} [inst : Ring R] {ι : Typ
e u_2} [Finite ι], Module.FinitePresentation R (ι →₀ R)
· 使用引理 `Module.Relations.Solution.IsPresentation.surjective_π`：surjective_π : Fu
nction.Surjective solution.π
· 使用定理 `Module.Presentation.toIsPresentation`：∀ {A : Type u} [inst : Ring A] {M 
: Type v} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module A M]   (self : Modul
e.Presentation A M), self.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Relations.Solution.IsPresentation.ker_π`：ker_π : LinearMap.ker so
lution.π = Submodule.span A (Set.range relations.relation)
· 使用定理 `Submodule.fg_span`：fg_span {s : Set M} (hs : s.Finite) : FG (span R s)
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
-/
lemma finitePresentation [Finite pres.G] [Finite pres.R] :
    Module.FinitePresentation A M :=
  Module.finitePresentation_of_surjective _ pres.surjective_π (by
    rw [pres.ker_π]
    exact Submodule.fg_span (Set.finite_range _))

end Presentation

/-
**Module.finitePresentation_iff_exists_presentation** 是 Mathlib 中的一个引理，位于命名空间 `M
odule`。
形式化陈述：finitePresentation_iff_exists_presentation : Module.FinitePresentation A M
 ↔ exists (pres : Presentation.{w₀, w₁} A M), Finite pres.G ∧ Finite pres.R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Submodule.fg_iff_exists_finite_generating_family`：fg_iff_exists_finite_g
enerating_family {A : Type u} [Semiring A] {M : Type v} [AddCommMonoid M] [Modul
e A M] {N : Submodule A M} : N.FG ↔ ex…
· 使用定理 `Module.finite_def`：finite_def {R M} [Semiring R] [AddCommMonoid M] [Modu
le R M] : Module.Finite R M ↔ (⊤ : Submodule R M).FG
· 使用定理 `instFiniteOfFinitePresentation`：∀ (R : Type u_1) (M : Type u_2) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [h : Modul
e.FinitePresentation…
· 使用引理 `Module.FinitePresentation.fg_ker`：Module.FinitePresentation.fg_ker [Modu
le.Finite R M] [h : Module.FinitePresentation R N] (l : M ->ₗ[R] N) (hl : Functi
on.Surjective l) : (Li…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Finsupp.range_linearCombination`：range_linearCombination : LinearMap.ran
ge (linearCombination R v) = span R (range v)
· 使用定理 `Submodule.ext_iff`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p q : Submodule R M}, p = 
q ↔ ∀ (…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用引理 `Module.Relations.Solution.isPresentation_iff`：isPresentation_iff : solut
ion.IsPresentation ↔ Submodule.span A (Set.range solution.var) = ⊤ ∧ LinearMap.k
er solution.π = Submodule.span A (…
· 使用引理 `Module.Presentation.finitePresentation`：finitePresentation [Finite pres.
G] [Finite pres.R] : Module.FinitePresentation A M
-/
lemma finitePresentation_iff_exists_presentation :
    Module.FinitePresentation A M ↔
      ∃ (pres : Presentation.{w₀, w₁} A M), Finite pres.G ∧ Finite pres.R := by
  constructor
  · intro
    obtain ⟨G : Type w₀, _, var, hG⟩ :=
      Submodule.fg_iff_exists_finite_generating_family.1
        (finite_def.1 (inferInstance : Module.Finite A M))
    obtain ⟨R : Type w₁, _, relation, hR⟩ :=
      Submodule.fg_iff_exists_finite_generating_family.1
        (Module.FinitePresentation.fg_ker (Finsupp.linearCombination A var) (by
          rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hG]))
    exact
     ⟨{ G := G
        R := R
        relation := relation
        var := var
        linearCombination_var_relation := fun r ↦ by
          rw [Submodule.ext_iff] at hR
          exact (hR _).1 (Submodule.subset_span ⟨_, rfl⟩)
        toIsPresentation := by
          rw [Relations.Solution.isPresentation_iff]
          exact ⟨hG, hR.symm⟩ },
        inferInstance, inferInstance⟩
  · rintro ⟨pres, _, _⟩
    exact pres.finitePresentation

end Module

