/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.IsNormal
public import Mathlib.Topology.Order.IsLUB

/-!
# A normal function is strictly monotone and continuous

We defined the predicate `Order.IsNormal` in terms of `IsLUB`, which avoids having to import
topology in order theory files. This file shows that the predicate is equivalent to the definition
in the literature, being that of a strictly monotonic function, continuous in the order topology.
-/

public section

open Set

namespace Order
variable {α β : Type*}
  [LinearOrder α] [WellFoundedLT α] [TopologicalSpace α] [OrderTopology α]
  [LinearOrder β] [WellFoundedLT β] [TopologicalSpace β] [OrderTopology β]

attribute [local instance]
  WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot in
/-
**Order.IsNormal.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [WellFoundedLT α] [
inst_2 : TopologicalSpace α] [OrderTopology α]   [inst_4 : LinearOrder β] [WellF
oundedLT β] [inst_6 : TopologicalSpace β] [OrderTopology β] {f : α → β},   Order
.IsNormal f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderTopology.continuous_iff`：∀ {α : Type u} {β : Type v} [ts : Topologi
calSpace α] [inst : Preorder α] [OrderTopology α]   [inst_2 : TopologicalSpace β
] {f : β → α},   C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Set.compl_Ioi`：∀ {α : Type u_1} [inst : LinearOrder α] {a : α}, (Set.Ioi
 a)ᶜ = Set.Iic a
· 使用定理 `IsLowerSet.eq_univ_or_Iio`：IsLowerSet.eq_univ_or_Iio [WellFoundedLT α] (
h : IsLowerSet s) : s = univ ∨ exists a, s = Iio a
· 使用定理 `IsLowerSet.preimage`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α]
 [inst_1 : Preorder β] {s : Set α},   IsLowerSet s → ∀ {f : β → α}, Monotone f →
 IsLowerS…
· 使用定理 `isLowerSet_Iic`：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsLowerSet
 (Set.Iic a)
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
· 使用定理 `Order.IsNormal.preimage_Iic`：preimage_Iic (hf : IsNormal f) {x : β} (h₁ 
: (f ⁻¹' Iic x).Nonempty) (h₂ : BddAbove (f ⁻¹' Iic x)) : f ⁻¹' Iic x = Iic (sSu
p (f ⁻¹' Iic x))
· 使用定理 `bddAbove_Iio`：bddAbove_Iio : BddAbove (Iio a)
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `IsLowerSet.isOpen`：IsLowerSet.isOpen [WellFoundedLT α] {s : Set α} (h : 
IsLowerSet s) : IsOpen s
· 使用定理 `isLowerSet_Iio`：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsLowerSet
 (Set.Iio a)
-/
theorem IsNormal.continuous {f : α → β} (hf : IsNormal f) : Continuous f := by
  rw [OrderTopology.continuous_iff]
  refine fun b ↦ ⟨?_, ((isLowerSet_Iio b).preimage hf.strictMono.monotone).isOpen⟩
  rw [← isClosed_compl_iff, ← Set.preimage_compl, Set.compl_Ioi]
  obtain ha | ⟨a, ha⟩ := ((isLowerSet_Iic b).preimage hf.strictMono.monotone).eq_univ_or_Iio
  · exact ha ▸ isClosed_univ
  · obtain h | h := (f ⁻¹' Iic b).eq_empty_or_nonempty
    · exact h ▸ isClosed_empty
    · have : Nonempty α := ⟨a⟩
      have : Nonempty β := ⟨b⟩
      rw [hf.preimage_Iic h (ha ▸ bddAbove_Iio)]
      exact isClosed_Iic

/-- A normal function between well-orders is equivalent to a strictly monotone,
continuous function. -/
/-
**Order.isNormal_iff_strictMono_and_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Order`
。
形式化陈述：isNormal_iff_strictMono_and_continuous {f : α -> β} : IsNormal f ↔ StrictM
ono f ∧ Continuous f where mp hf
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Order.IsNormal.continuous`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [WellFoundedLT α] [inst_2 : TopologicalSpace α] [OrderTopology α]   [i
nst_4 : LinearO…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isLUB_of_mem_closure`：isLUB_of_mem_closure {s : Set α} {a : α} (hsa : a 
in upperBounds s) (hsf : a in closure s) : IsLUB s a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `IsLUB.mem_closure`：IsLUB.mem_closure {a : α} {s : Set α} (ha : IsLUB s a
) (hs : s.Nonempty) : a in closure s
· 使用定理 `Order.IsSuccLimit.isLUB_Iio`：∀ {α : Type u_1} {a : α} [inst : LinearOrde
r α], Order.IsSuccLimit a → IsLUB (Set.Iio a) a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.Iio_nonempty`：Iio_nonempty : (Iio a).Nonempty ↔ ¬ IsMin a
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a

--- 原说明 ---
A normal function between well-orders is equivalent to a strictly monotone,
continuous function.
-/
theorem isNormal_iff_strictMono_and_continuous {f : α → β} :
    IsNormal f ↔ StrictMono f ∧ Continuous f where
  mp hf := ⟨hf.strictMono, hf.continuous⟩
  mpr := by
    rintro ⟨hs, hc⟩
    refine ⟨hs, fun {a} ha ↦ (isLUB_of_mem_closure ?_ ?_).2⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact (hs hb).le
    · apply image_closure_subset_closure_image hc (mem_image_of_mem ..)
      exact ha.isLUB_Iio.mem_closure (Iio_nonempty.2 ha.1)

end Order

