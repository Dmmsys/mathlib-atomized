/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Infinite sums and products in topological fields

Lemmas on topological sums in rings with a strictly multiplicative norm, of which normed fields are
the most familiar examples.
-/

public section


section NormMulClass

variable {α E : Type*} [SeminormedCommRing E] [NormMulClass E] [NormOneClass E]
  {f : α → E} {x : E}

nonrec theorem HasProd.norm (hfx : HasProd f x) : HasProd (‖f ·‖) ‖x‖ := by
  simp only [HasProd, ← norm_prod]
  exact hfx.norm

/-
**Multipliable.norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.norm (hf : Multipliable f) : Multipliable (‖f ·‖)
参数：hf : Multipliable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.norm`：∀ {α : Type u_1} {E : Type u_2} [inst : SeminormedCommRing
 E] [NormMulClass E] [NormOneClass E] {f : α → E} {x : E},   HasProd f x → HasPr
od…
-/
theorem Multipliable.norm (hf : Multipliable f) : Multipliable (‖f ·‖) :=
  let ⟨x, hx⟩ := hf; ⟨‖x‖, hx.norm⟩
/-
**Multipliable.norm_tprod** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} [inst : SeminormedCommRing E] [NormMulClas
s E] [NormOneClass E] {f : α → E},   Multipliable f → ‖∏' (i : α), f i‖ = ∏' (i 
: α), ‖f i‖
参数：i : α；i : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.norm`：∀ {α : Type u_1} {E : Type u_2} [inst : SeminormedCommRing
 E] [NormMulClass E] [NormOneClass E] {f : α → E} {x : E},   HasProd f x → HasPr
od…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.norm_tprod (hf : Multipliable f) : ‖∏' i, f i‖ = ∏' i, ‖f i‖ :=
  hf.hasProd.norm.tprod_eq.symm

end NormMulClass

