/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Linear maps of modules with coefficients in a principal ideal domain

Since a submodule of a free module over a PID is free, certain constructions which are often
developed only for vector spaces may be generalised to any module with coefficients in a PID.

This file is a location for such results and exists to avoid making large parts of the linear
algebra import hierarchy have to depend on the theory of PIDs.

## Main results:
* `LinearMap.trace_restrict_eq_of_forall_mem`

-/

public section

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Free R M]

/-- If a linear endomorphism of a (finite, free) module `M` takes values in a submodule `p ⊆ M`,
then the trace of its restriction to `p` is equal to its trace on `M`. -/
/-
**LinearMap.trace_restrict_eq_of_forall_mem** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
`。
形式化陈述：trace_restrict_eq_of_forall_mem [IsDomain R] [IsPrincipalIdealRing R] (p :
 Submodule R M) (f : M ->ₗ[R] M) (hf : forall x, f x in p) (hf' : forall x in p,
 f x in p
参数：p : Submodule R M；f : M ->ₗ[R] M；hf : forall x, f x in p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.trace_eq_matrix_trace`：trace_eq_matrix_trace (f : M ->ₗ[R] M) 
: trace R M f = Matrix.trace (LinearMap.toMatrix b b f)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用引理 `Module.Basis.SmithNormalForm.repr_eq_zero_of_notMem_range`：repr_eq_zero_
of_notMem_range {i : ι} (hi : i ∉ Set.range snf.f) : snf.bM.repr m i = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_filter_of_ne`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} 
[inst : AddCommMonoid M] {f : ι → M} {p : ι → Prop}   [inst_1 : DecidablePred p]
, (∀ x ∈ s, f…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Module.Basis.SmithNormalForm.toMatrix_restrict_eq_toMatrix`：toMatrix_res
trict_eq_toMatrix [Fintype ι] [DecidableEq ι] (f : M ->ₗ[R] M) (hf : forall x, f
 x in N) (hf' : forall x in N, f x in N
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.univ_filter_exists`：univ_filter_exists (f : α -> β) [Fintype β] [
DecidablePred fun y => exists x, f x = y] [DecidableEq β] : (Finset.univ.filter 
fun y => exists…
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a linear endomorphism of a (finite, free) module `M` takes values in a submod
ule `p ⊆ M`,
then the trace of its restriction to `p` is equal to its trace on `M`.
-/
lemma trace_restrict_eq_of_forall_mem [IsDomain R] [IsPrincipalIdealRing R]
    (p : Submodule R M) (f : M →ₗ[R] M)
    (hf : ∀ x, f x ∈ p) (hf' : ∀ x ∈ p, f x ∈ p := fun x _ ↦ hf x) :
    trace R p (f.restrict hf') = trace R M f := by
  let ι := Module.Free.ChooseBasisIndex R M
  obtain ⟨n, snf⟩ := p.smithNormalForm (Module.Free.chooseBasis R M)
  rw [trace_eq_matrix_trace R snf.bM, trace_eq_matrix_trace R snf.bN]
  set A : Matrix (Fin n) (Fin n) R := toMatrix snf.bN snf.bN (f.restrict hf')
  set B : Matrix ι ι R := toMatrix snf.bM snf.bM f
  have aux : ∀ i, B i i ≠ 0 → i ∈ Set.range snf.f := fun i hi ↦ by
    contrapose hi; exact snf.repr_eq_zero_of_notMem_range ⟨_, (hf _)⟩ hi
  change ∑ i, A i i = ∑ i, B i i
  rw [← Finset.sum_filter_of_ne (p := fun j ↦ j ∈ Set.range snf.f) (by simpa using aux)]
  simp [A, B, hf, Finset.sum_image snf.f.injective.injOn]

end LinearMap

