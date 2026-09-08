/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Set.Countable
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Countable modules
-/

public section

noncomputable section

namespace Finsupp

variable {M : Type*} {R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- If `R` is countable, then any `R`-submodule spanned by a countable family of vectors is
countable. -/
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is countable, then any `R`-submodule spanned by a countable family of vec
tors is
countable.
-/
instance {ι : Type*} [Countable R] [Countable ι] (v : ι → M) :
    Countable (Submodule.span R (Set.range v)) := by
  refine Set.countable_coe_iff.mpr (Set.Countable.mono ?_ (Set.countable_range
      (fun c : (ι →₀ R) => c.sum fun i _ => (c i) • v i)))
  exact fun _ h => Finsupp.mem_span_range_iff_exists_finsupp.mp (SetLike.mem_coe.mp h)
/-
**Finsupp.Countable.of_moduleFinite** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Countable
`。
形式化陈述：∀ {M : Type u_1} {R : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   [Countable R] [Module.Finite R M], Countable
 M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.exists_fin`：exists_fin [Module.Finite R M] : exists (n : N
at) (s : Fin n -> M), span R (range s) = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.countable_univ_iff`：countable_univ_iff : (univ : Set α).Countable ↔ 
Countable α
· 使用定理 `Finsupp.instCountableSubtypeMemSubmoduleSpanRange`：∀ {M : Type u_1} {R :
 Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Modul
e R M]   {ι : Type u_3} [Countable R] […
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
-/
theorem Countable.of_moduleFinite [Countable R] [Module.Finite R M] : Countable M := by
  obtain ⟨n, s, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  rw [← Set.countable_univ_iff]
  have : Countable (Submodule.span R (Set.range s)) := inferInstance
  rwa [h] at this
/-
**Finsupp.Uncountable.of_moduleFinite** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Uncount
able`。
形式化陈述：∀ {M : Type u_1} {R : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   [hM : Uncountable M] [Module.Finite R M], Un
countable R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uncountable_iff_not_countable`：∀ (α : Sort u_1), Uncountable α ↔ ¬Counta
ble α
· 使用定理 `Finsupp.Countable.of_moduleFinite`：∀ {M : Type u_1} {R : Type u_2} [inst
 : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Counta
ble R] [Module.Finite R…
-/
theorem Uncountable.of_moduleFinite [hM : Uncountable M] [Module.Finite R M] : Uncountable R := by
  by_contra!
  exact (uncountable_iff_not_countable _).mp hM <| Countable.of_moduleFinite (R := R)

end Finsupp

