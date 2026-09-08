/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Algebra.Monoid

/-! # Topological properties of the unitary (sub)group

* In a topological star monoid `R`, `unitary R` is a topological group
* In a topological star monoid `R` which is T1, `unitary R` is closed as a subset of `R`.
-/

public section

variable {R : Type*} [Monoid R] [StarMul R] [TopologicalSpace R]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ContinuousStar R] : ContinuousStar (unitary R) where
  continuous_star := continuous_induced_rng.mpr continuous_subtype_val.star
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ContinuousStar R] : ContinuousInv (unitary R) where
  continuous_inv := continuous_star
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ContinuousMul R] [ContinuousStar R] : IsTopologicalGroup (unitary R) where
/-
**isClosed_unitary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_unitary [T1Space R] [ContinuousStar R] [ContinuousMul R] : IsClos
ed (unitary R : Set R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fun_mul`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Mul M] [ContinuousMul M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g 
: X → M}…
· 使用定理 `Continuous.star`：Continuous.star (hf : Continuous f) : Continuous fun x 
=> star (f x)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `instT1SpaceProd`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace Y] [T1Space X] [T1Space Y],   T1Space (X × Y)
-/
lemma isClosed_unitary [T1Space R] [ContinuousStar R] [ContinuousMul R] :
    IsClosed (unitary R : Set R) := by
  let f (u : R) : R × R := (star u * u, u * star u)
  have hf : f ⁻¹' {(1, 1)} = unitary R := by ext u; simp [f, Unitary.mem_iff]
  rw [← hf]
  exact isClosed_singleton.preimage (by fun_prop)
