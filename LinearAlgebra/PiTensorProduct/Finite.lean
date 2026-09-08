/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-!
# A multiple tensor product of finitely generated modules is finitely generated

-/

public section

open TensorProduct

namespace PiTensorProduct

/-
**PiTensorProduct.finite** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
形式化陈述：finite {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {M : ι -> Type*} [f
orall i, AddCommGroup (M i)] [forall i, Module R (M i)] [forall i, Module.Finite
 R (M i)] : Module.Finite R (⨂[R] i, M i)
参数：M i；M i；M i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finite_def`：finite_def {R M} [Semiring R] [AddCommMonoid M] [Modu
le R M] : Module.Finite R M ↔ (⊤ : Submodule R M).FG
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PiTensorProduct.submodule_span_eq_top`：submodule_span_eq_top (hg : foral
l i, Submodule.span R (Set.range (@g i)) = ⊤) : Submodule.span R (Set.range (fun
 j : ((i : ι) -> γ i) => ⨂ₜ…
· 使用定理 `Submodule.fg_span`：fg_span {s : Set M} (hs : s.Finite) : FG (span R s)
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `Module.Finite.exists_fin`：exists_fin [Module.Finite R M] : exists (n : N
at) (s : Fin n -> M), span R (range s) = ⊤
-/
instance finite {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Finite R (M i)] :
    Module.Finite R (⨂[R] i, M i) := by
  choose n γ hg using fun i => Module.Finite.exists_fin (R := R) (M := M i)
  rw [Module.finite_def, ← submodule_span_eq_top hg]
  exact Submodule.fg_span (Set.finite_range _)

end PiTensorProduct

