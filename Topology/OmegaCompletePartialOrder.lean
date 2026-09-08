/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Order.BourbakiWitt
public import Mathlib.Topology.Order.ScottTopology

/-!
# Scott Topological Spaces

A type of topological spaces whose notion
of continuity is equivalent to continuity in ωCPOs.

## Reference

* https://ncatlab.org/nlab/show/Scott+topology

-/

@[expose] public section

open Set OmegaCompletePartialOrder Topology

universe u

open Topology.IsScott in
/-
**Topology.IsScott.** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Topology.IsScott.ωScottContinuous_iff_continuous {α : Type*}
    [OmegaCompletePartialOrder α] [TopologicalSpace α]
    [Topology.IsScott α (Set.range fun c : Chain α => Set.range c)] {f : α → Prop} :
    ωScottContinuous f ↔ Continuous f := by
  rw [ωScottContinuous, scottContinuousOn_iff_continuous (fun a b hab => by
    use Chain.pair a b hab; exact OmegaCompletePartialOrder.Chain.range_pair a b hab)]

namespace Scott

/-- `x` is an `ω`-Sup of a chain `c` if it is the least upper bound of the range of `c`. -/
/-
**Scott.Is** 是 Mathlib 中的一个定义，位于命名空间 `Scott`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x` is an `ω`-Sup of a chain `c` if it is the least upper bound of the range of 
`c`.
-/
def IsωSup {α : Type u} [Preorder α] (c : Chain α) (x : α) : Prop :=
  (∀ i, c i ≤ x) ∧ ∀ y, (∀ i, c i ≤ y) → x ≤ y
/-
**Scott.is** 是 Mathlib 中的一个定理，位于命名空间 `Scott`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isωSup_iff_isLUB {α : Type u} [Preorder α] {c : Chain α} {x : α} :
    IsωSup c x ↔ IsLUB (range c) x := by
  simp [IsωSup, IsLUB, IsLeast, upperBounds, lowerBounds]

variable (α : Type u) [OmegaCompletePartialOrder α]

/-- The characteristic function of open sets is monotone and preserves
the limits of chains. -/
/-
**Scott.IsOpen** 是 Mathlib 中的一个定义，位于命名空间 `Scott`。
形式化陈述：IsOpen (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The characteristic function of open sets is monotone and preserves
the limits of chains.
-/
def IsOpen (s : Set α) : Prop :=
  ωScottContinuous fun x ↦ x ∈ s
/-
**Scott.isOpen_univ** 是 Mathlib 中的一个定理，位于命名空间 `Scott`。
形式化陈述：isOpen_univ : IsOpen α univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteLattice.ωScottContinuous.top`：∀ {α : Type u_1} {β : Type u_2} [i
nst : OmegaCompletePartialOrder α] [inst_1 : CompleteLattice β],   OmegaComplete
PartialOrder.ωScottContinu…
-/
theorem isOpen_univ : IsOpen α univ := @CompleteLattice.ωScottContinuous.top α Prop _ _
/-
**Scott.IsOpen.inter** 是 Mathlib 中的一个定理，位于命名空间 `Scott.IsOpen`。
形式化陈述：∀ (α : Type u) [inst : OmegaCompletePartialOrder α] (s t : Set α),   Scott
.IsOpen α s → Scott.IsOpen α t → Scott.IsOpen α (s ∩ t)
参数：α : Type u；s t : Set α；s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteLattice.ωScottContinuous.inf`：∀ {α : Type u_1} {β : Type u_2} [i
nst : OmegaCompletePartialOrder α] [inst_1 : CompleteLinearOrder β] {f g : α → β
},   OmegaCompletePartialO…
-/
theorem IsOpen.inter (s t : Set α) : IsOpen α s → IsOpen α t → IsOpen α (s ∩ t) :=
  CompleteLattice.ωScottContinuous.inf

set_option backward.isDefEq.respectTransparency false in
/-
**Scott.isOpen_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Scott`。
形式化陈述：isOpen_sUnion (s : Set (Set α)) (hs : forall t in s, IsOpen α t) : IsOpen 
α (⋃₀ s)
参数：s : Set (Set α)；hs : forall t in s, IsOpen α t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_Prop_eq`：iSup_Prop_eq {p : ι -> Prop} : ⨆ i, p i = exists i, p i
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `CompleteLattice.ωScottContinuous.sSup`：∀ {α : Type u_1} {β : Type u_2} [
inst : OmegaCompletePartialOrder α] [inst_1 : CompleteLattice β] {s : Set (α → β
)},   (∀ f ∈ s, OmegaComple…
-/
theorem isOpen_sUnion (s : Set (Set α)) (hs : ∀ t ∈ s, IsOpen α t) : IsOpen α (⋃₀ s) := by
  simp only [IsOpen] at hs ⊢
  convert! CompleteLattice.ωScottContinuous.sSup hs
  aesop
/-
**Scott.IsOpen.isUpperSet** 是 Mathlib 中的一个定理，位于命名空间 `Scott.IsOpen`。
形式化陈述：∀ (α : Type u) [inst : OmegaCompletePartialOrder α] {s : Set α}, Scott.IsO
pen α s → IsUpperSet s
参数：α : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OmegaCompletePartialOrder.ωScottContinuous.monotone`：∀ {α : Type u_2} {β
 : Type u_3} [inst : OmegaCompletePartialOrder α] [inst_1 : OmegaCompletePartial
Order β] {f : α → β},   OmegaCompletePart…
-/
theorem IsOpen.isUpperSet {s : Set α} (hs : IsOpen α s) : IsUpperSet s := hs.monotone

end Scott

open Scott hiding IsOpen IsOpen.isUpperSet

/-
**is** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：is nearly impossible to state nicely in terms of `cfcHom` (see `cfcHom_com
p`). An additional advantage of the unbundled approach is that expressions like 
`fun x : R ↦ x⁻¹` are valid arguments to `cfc`, and a bundled continuous counter
part can only make sense when the spectrum of `a` does not contain zero and when
 we have an `⁻¹` operation on the domain.  A reader familiar with C⋆-algebra the
ory may be somewhat surprised at the level of abstraction here. For instance, wh
y not require `A` to be an
参数：see `cfcHom_comp`。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isωSup_ωSup {α} [OmegaCompletePartialOrder α] (c : Chain α) : IsωSup c (ωSup c) := by
  constructor
  · apply le_ωSup
  · apply ωSup_le
