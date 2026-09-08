/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Continuity of the functoriality of `X → M` when `X` is finite

-/

public section

namespace FunOnFinite

/-
**FunOnFinite.continuous_map** 是 Mathlib 中的一个引理，位于命名空间 `FunOnFinite`。
形式化陈述：continuous_map (M : Type*) [AddCommMonoid M] [TopologicalSpace M] [Continu
ousAdd M] {X Y : Type*} [Finite X] [Finite Y] (f : X -> Y) : Continuous (FunOnFi
nite.map (M
参数：M : Type*；f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `FunOnFinite.map_apply_apply`：map_apply_apply [Fintype X] [Finite Y] [Dec
idableEq Y] (f : X -> Y) (s : X -> M) (y : Y) : map f s y = ∑ x with f x = y, s 
x
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
lemma continuous_map
    (M : Type*) [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M]
    {X Y : Type*} [Finite X] [Finite Y] (f : X → Y) :
    Continuous (FunOnFinite.map (M := M) f) := by
  classical
  have := Fintype.ofFinite X
  refine continuous_pi (fun y ↦ ?_)
  simp only [FunOnFinite.map_apply_apply]
  exact continuous_finsetSum _ (fun _ _ ↦ continuous_apply _)
/-
**FunOnFinite.continuous_linearMap** 是 Mathlib 中的一个引理，位于命名空间 `FunOnFinite`。
形式化陈述：continuous_linearMap (R M : Type*) [Semiring R] [AddCommMonoid M] [Module 
R M] [TopologicalSpace M] [ContinuousAdd M] {X Y : Type*} [Finite X] [Finite Y] 
(f : X -> Y) : Continuous (FunOnFinite.linearMap R M f)
参数：R M : Type*；f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FunOnFinite.continuous_map`：continuous_map (M : Type*) [AddCommMonoid M]
 [TopologicalSpace M] [ContinuousAdd M] {X Y : Type*} [Finite X] [Finite Y] (f :
 X -> Y) : Conti…
-/
lemma continuous_linearMap
    (R M : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    {X Y : Type*} [Finite X] [Finite Y] (f : X → Y) :
    Continuous (FunOnFinite.linearMap R M f) :=
  FunOnFinite.continuous_map _ _

end FunOnFinite

