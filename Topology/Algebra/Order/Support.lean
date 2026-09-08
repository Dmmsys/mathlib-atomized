/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Topology.Algebra.Support

/-!
# The topological support of sup and inf of functions

In a topological space `X` and a space `M` with `Sup` structure, for `f g : X → M` with compact
support, we show that `f ⊔ g` has compact support. Similarly, in `β` with `Inf` structure, `f ⊓ g`
has compact support if so do `f` and `g`.

-/

public section

variable {X M : Type*} [TopologicalSpace X] [One M]

section SemilatticeSup

variable [SemilatticeSup M]

@[to_additive]
/-
**HasCompactMulSupport.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.sup {f g : X -> M} (hf : HasCompactMulSupport f) (hg 
: HasCompactMulSupport g) : HasCompactMulSupport (f ⊔ g)
参数：hf : HasCompactMulSupport f；hg : HasCompactMulSupport g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用定理 `isClosed_mulTSupport`：isClosed_mulTSupport (f : X -> α) : IsClosed (mulT
Support f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mulTSupport.eq_1`：∀ {X : Type u_1} {α : Type u_2} [inst : One α] [inst_1
 : TopologicalSpace X] (f : X → α),   mulTSupport f = closure (Function.mulSuppo
rt f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_union`：closure_union : closure (s union t) = closure s union clo
sure t
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Function.mulSupport_sup`：mulSupport_sup [SemilatticeSup M] (f g : α -> M
) : mulSupport (fun x => f x ⊔ g x) subseteq mulSupport f union mulSupport g
-/
theorem HasCompactMulSupport.sup {f g : X → M} (hf : HasCompactMulSupport f)
    (hg : HasCompactMulSupport g) : HasCompactMulSupport (f ⊔ g) := by
  apply IsCompact.of_isClosed_subset (IsCompact.union hf hg) (isClosed_mulTSupport _)
  rw [mulTSupport, mulTSupport, mulTSupport, ← closure_union]
  apply closure_mono
  exact Function.mulSupport_sup f g

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf M]

@[to_additive]
/-
**HasCompactMulSupport.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.inf {f g : X -> M} (hf : HasCompactMulSupport f) (hg 
: HasCompactMulSupport g) : HasCompactMulSupport (f ⊓ g)
参数：hf : HasCompactMulSupport f；hg : HasCompactMulSupport g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用定理 `isClosed_mulTSupport`：isClosed_mulTSupport (f : X -> α) : IsClosed (mulT
Support f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mulTSupport.eq_1`：∀ {X : Type u_1} {α : Type u_2} [inst : One α] [inst_1
 : TopologicalSpace X] (f : X → α),   mulTSupport f = closure (Function.mulSuppo
rt f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_union`：closure_union : closure (s union t) = closure s union clo
sure t
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Function.mulSupport_inf`：mulSupport_inf [SemilatticeInf M] (f g : α -> M
) : mulSupport (fun x => f x ⊓ g x) subseteq mulSupport f union mulSupport g
-/
theorem HasCompactMulSupport.inf {f g : X → M} (hf : HasCompactMulSupport f)
    (hg : HasCompactMulSupport g) : HasCompactMulSupport (f ⊓ g) := by
  apply IsCompact.of_isClosed_subset (IsCompact.union hf hg) (isClosed_mulTSupport _)
  rw [mulTSupport, mulTSupport, mulTSupport, ← closure_union]
  apply closure_mono
  exact Function.mulSupport_inf f g

end SemilatticeInf

