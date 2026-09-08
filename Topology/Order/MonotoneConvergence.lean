/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Basic

/-!
# Bounded monotone sequences converge

In this file we prove a few theorems of the form “if the range of a monotone function `f : ι → α`
admits a least upper bound `a`, then `f x` tends to `a` as `x → ∞`”, as well as version of this
statement for (conditionally) complete lattices that use `⨆ x, f x` instead of `IsLUB`.

These theorems work for linear orders with order topologies as well as their products (both in terms
of `Prod` and in terms of function types). In order to reduce code duplication, we introduce two
typeclasses (one for the property formulated above and one for the dual property), prove theorems
assuming one of these typeclasses, and provide instances for linear orders and their products.

We also prove some "inverse" results: if `f n` is a monotone sequence and `a` is its limit,
then `f n ≤ a` for all `n`.

## Tags

monotone convergence
-/

public section

open Filter Set Function
open scoped Topology

variable {α β : Type*}

/-- We say that `α` is a `SupConvergenceClass` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a least upper bound of `Set.range f`. Then `f x` tends to `𝓝 a`
as `x → ∞` (formally, at the filter `Filter.atTop`). We require this for `ι = (s : Set α)`,
`f = (↑)` in the definition, then prove it for any `f` in `tendsto_atTop_isLUB`.

This property holds for linear orders with order topology as well as their products. -/
/-
**SupConvergenceClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [Preorder α] → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `α` is a `SupConvergenceClass` if the following holds. Let `f : ι → 
α` be a
monotone function, let `a : α` be a least upper bound of `Set.range f`. Then `f 
x` tends to `𝓝 a`
as `x → ∞` (formally, at the filter `Filter.atTop`). We require this for `ι = (s
 : Set α)`,
`f = (↑)` in the definition, then prove it for any `f` in `tendsto_atTop_isLUB`.

This property holds for linear orders with order topology as well as their produ
cts.
-/
class SupConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → ∞` -/
  tendsto_coe_atTop_isLUB :
    ∀ (a : α) (s : Set α), IsLUB s a → Tendsto ((↑) : s → α) atTop (𝓝 a)

/-- We say that `α` is an `InfConvergenceClass` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a greatest lower bound of `Set.range f`. Then `f x` tends to `𝓝 a`
as `x → -∞` (formally, at the filter `Filter.atBot`). We require this for `ι = (s : Set α)`,
`f = (↑)` in the definition, then prove it for any `f` in `tendsto_atBot_isGLB`.

This property holds for linear orders with order topology as well as their products. -/
/-
**InfConvergenceClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [Preorder α] → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `α` is an `InfConvergenceClass` if the following holds. Let `f : ι →
 α` be a
monotone function, let `a : α` be a greatest lower bound of `Set.range f`. Then 
`f x` tends to `𝓝 a`
as `x → -∞` (formally, at the filter `Filter.atBot`). We require this for `ι = (
s : Set α)`,
`f = (↑)` in the definition, then prove it for any `f` in `tendsto_atBot_isGLB`.

This property holds for linear orders with order topology as well as their produ
cts.
-/
class InfConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → -∞` -/
  tendsto_coe_atBot_isGLB :
    ∀ (a : α) (s : Set α), IsGLB s a → Tendsto ((↑) : s → α) atBot (𝓝 a)
/-
**OrderDual.supConvergenceClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.supConvergenceClass [Preorder α] [TopologicalSpace α] [InfConver
genceClass α] : SupConvergenceClass αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `InfConvergenceClass.tendsto_coe_atBot_isGLB`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : TopologicalSpace α} [self : InfConvergenceClass α] (a : α) (
s : Set α),   IsGLB s a → Filter.…
-/
instance OrderDual.supConvergenceClass [Preorder α] [TopologicalSpace α] [InfConvergenceClass α] :
    SupConvergenceClass αᵒᵈ :=
  ⟨‹InfConvergenceClass α›.1⟩
/-
**OrderDual.infConvergenceClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.infConvergenceClass [Preorder α] [TopologicalSpace α] [SupConver
genceClass α] : InfConvergenceClass αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SupConvergenceClass.tendsto_coe_atTop_isLUB`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : TopologicalSpace α} [self : SupConvergenceClass α] (a : α) (
s : Set α),   IsLUB s a → Filter.…
-/
instance OrderDual.infConvergenceClass [Preorder α] [TopologicalSpace α] [SupConvergenceClass α] :
    InfConvergenceClass αᵒᵈ :=
  ⟨‹SupConvergenceClass α›.1⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) LinearOrder.supConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : SupConvergenceClass α := by
  refine ⟨fun a s ha => tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩⟩
  · rcases ha.exists_between hb with ⟨c, hcs, bc, bca⟩
    lift c to s using hcs
    exact (eventually_ge_atTop c).mono fun x hx => bc.trans_le hx
  · exact Eventually.of_forall fun x => (ha.1 x.2).trans_lt hb

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) LinearOrder.infConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : InfConvergenceClass α :=
  show InfConvergenceClass αᵒᵈᵒᵈ from OrderDual.infConvergenceClass

section

variable {ι : Type*} [Preorder ι] [TopologicalSpace α]

section IsLUB

variable [Preorder α] [SupConvergenceClass α] {f : ι → α} {a : α}

/-
**tendsto_atTop_isLUB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsLUB (Set.range f) a) : T
endsto f atTop (𝓝 a)
参数：h_mono : Monotone f；ha : IsLUB (Set.range f) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atTop_atTop`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, b ≤
 f a) → Filter.Ten…
· 使用定理 `Monotone.rangeFactorization`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] {f : α → β},   Monotone f → Monotone (Set.rangeFa
ctorization f)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `SupConvergenceClass.tendsto_coe_atTop_isLUB`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : TopologicalSpace α} [self : SupConvergenceClass α] (a : α) (
s : Set α),   IsLUB s a → Filter.…
-/
theorem tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by
  suffices Tendsto (rangeFactorization f) atTop atTop from
    (SupConvergenceClass.tendsto_coe_atTop_isLUB _ _ ha).comp this
  exact h_mono.rangeFactorization.tendsto_atTop_atTop fun b => b.2.imp fun a ha => ha.ge
/-
**tendsto_atBot_isLUB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atBot_isLUB (h_anti : Antitone f) (ha : IsLUB (Set.range f) a) : T
endsto f atBot (𝓝 a)
参数：h_anti : Antitone f；ha : IsLUB (Set.range f) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `tendsto_atTop_isLUB`：tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsL
UB (Set.range f) a) : Tendsto f atTop (𝓝 a)
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)
-/
theorem tendsto_atBot_isLUB (h_anti : Antitone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by convert! tendsto_atTop_isLUB h_anti.dual_left ha using 1

end IsLUB

section IsGLB

variable [Preorder α] [InfConvergenceClass α] {f : ι → α} {a : α}

/-
**tendsto_atBot_isGLB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atBot_isGLB (h_mono : Monotone f) (ha : IsGLB (Set.range f) a) : T
endsto f atBot (𝓝 a)
参数：h_mono : Monotone f；ha : IsGLB (Set.range f) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `tendsto_atTop_isLUB`：tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsL
UB (Set.range f) a) : Tendsto f atTop (𝓝 a)
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
· 使用定理 `IsGLB.dual`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α},   
IsGLB s a → IsLUB (⇑OrderDual.ofDual ⁻¹' s) (OrderDual.toDual a)
-/
theorem tendsto_atBot_isGLB (h_mono : Monotone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by convert! tendsto_atTop_isLUB h_mono.dual ha.dual using 1
/-
**tendsto_atTop_isGLB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atTop_isGLB (h_anti : Antitone f) (ha : IsGLB (Set.range f) a) : T
endsto f atTop (𝓝 a)
参数：h_anti : Antitone f；ha : IsGLB (Set.range f) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `tendsto_atBot_isLUB`：tendsto_atBot_isLUB (h_anti : Antitone f) (ha : IsL
UB (Set.range f) a) : Tendsto f atBot (𝓝 a)
· 使用定理 `Antitone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Antitone f → Antitone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
· 使用定理 `IsGLB.dual`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α},   
IsGLB s a → IsLUB (⇑OrderDual.ofDual ⁻¹' s) (OrderDual.toDual a)
-/
theorem tendsto_atTop_isGLB (h_anti : Antitone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by convert! tendsto_atBot_isLUB h_anti.dual ha.dual using 1

end IsGLB

section CiSup

variable [ConditionallyCompletePartialOrderSup α] [SupConvergenceClass α] {f : ι → α}

/-
**tendsto_atTop_ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : BddAbove <| range f) : T
endsto f atTop (𝓝 (⨆ i, f i))
参数：h_mono : Monotone f；hbdd : BddAbove <| range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.atTop_neBot_iff`：atTop_neBot_iff {α : Type*} [Preorder α] : (atTo
p : Filter α).NeBot ↔ Nonempty α ∧ IsDirectedOrder α
· 使用定理 `tendsto_atTop_isLUB`：tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsL
UB (Set.range f) a) : Tendsto f atTop (𝓝 a)
· 使用定理 `DirectedOn.isLUB_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompletePa
rtialOrderSup α] {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Nonempty
 → BddAbove …
· 使用定理 `Directed.directedOn_range`：∀ {α : Type u_1} {ι : Sort u_3} {r : α → α → 
Prop} {f : ι → α}, Directed r f → DirectedOn r (Set.range f)
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
theorem tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : BddAbove <| range f) :
    Tendsto f atTop (𝓝 (⨆ i, f i)) := by
  obtain (h | h) := eq_or_ne atTop (⊥ : Filter ι)
  · simp [h]
  · obtain ⟨h₁, h₂⟩ := Filter.atTop_neBot_iff.mp ⟨h⟩
    exact tendsto_atTop_isLUB h_mono <|
      h_mono.directed_le.directedOn_range.isLUB_csSup (Set.range_nonempty f) hbdd
/-
**tendsto_atBot_ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atBot_ciSup (h_anti : Antitone f) (hbdd : BddAbove <| range f) : T
endsto f atBot (𝓝 (⨆ i, f i))
参数：h_anti : Antitone f；hbdd : BddAbove <| range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendsto_atTop_ciSup`：tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : B
ddAbove <| range f) : Tendsto f atTop (𝓝 (⨆ i, f i))
· 使用定理 `Antitone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Antitone f → Antitone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
· 使用定理 `BddAbove.dual`：BddAbove.dual (h : BddAbove s) : BddBelow (ofDual ⁻¹' s)
-/
theorem tendsto_atBot_ciSup (h_anti : Antitone f) (hbdd : BddAbove <| range f) :
    Tendsto f atBot (𝓝 (⨆ i, f i)) := by convert! tendsto_atTop_ciSup h_anti.dual hbdd.dual using 1

end CiSup

section CiInf

variable [ConditionallyCompletePartialOrderInf α] [InfConvergenceClass α] {f : ι → α}

/-
**tendsto_atBot_ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atBot_ciInf (h_mono : Monotone f) (hbdd : BddBelow <| range f) : T
endsto f atBot (𝓝 (⨅ i, f i))
参数：h_mono : Monotone f；hbdd : BddBelow <| range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `tendsto_atTop_ciSup`：tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : B
ddAbove <| range f) : Tendsto f atTop (𝓝 (⨆ i, f i))
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
· 使用定理 `BddBelow.dual`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, BddBelo
w s → BddAbove (⇑OrderDual.ofDual ⁻¹' s)
-/
theorem tendsto_atBot_ciInf (h_mono : Monotone f) (hbdd : BddBelow <| range f) :
    Tendsto f atBot (𝓝 (⨅ i, f i)) := by convert! tendsto_atTop_ciSup h_mono.dual hbdd.dual using 1
/-
**tendsto_atTop_ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atTop_ciInf (h_anti : Antitone f) (hbdd : BddBelow <| range f) : T
endsto f atTop (𝓝 (⨅ i, f i))
参数：h_anti : Antitone f；hbdd : BddBelow <| range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `tendsto_atBot_ciSup`：tendsto_atBot_ciSup (h_anti : Antitone f) (hbdd : B
ddAbove <| range f) : Tendsto f atBot (𝓝 (⨆ i, f i))
· 使用定理 `Antitone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Antitone f → Antitone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
· 使用定理 `BddBelow.dual`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, BddBelo
w s → BddAbove (⇑OrderDual.ofDual ⁻¹' s)
-/
theorem tendsto_atTop_ciInf (h_anti : Antitone f) (hbdd : BddBelow <| range f) :
    Tendsto f atTop (𝓝 (⨅ i, f i)) := by convert! tendsto_atBot_ciSup h_anti.dual hbdd.dual using 1

end CiInf

section iSup

variable [CompleteLattice α] [SupConvergenceClass α] {f : ι → α}

/-
**tendsto_atTop_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f atTop (𝓝 (⨆ i, f i))
参数：h_mono : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_ciSup`：tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : B
ddAbove <| range f) : Tendsto f atTop (𝓝 (⨆ i, f i))
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s
-/
theorem tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f atTop (𝓝 (⨆ i, f i)) :=
  tendsto_atTop_ciSup h_mono (OrderTop.bddAbove _)
/-
**tendsto_atBot_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atBot_iSup (h_anti : Antitone f) : Tendsto f atBot (𝓝 (⨆ i, f i))
参数：h_anti : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atBot_ciSup`：tendsto_atBot_ciSup (h_anti : Antitone f) (hbdd : B
ddAbove <| range f) : Tendsto f atBot (𝓝 (⨆ i, f i))
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s
-/
theorem tendsto_atBot_iSup (h_anti : Antitone f) : Tendsto f atBot (𝓝 (⨆ i, f i)) :=
  tendsto_atBot_ciSup h_anti (OrderTop.bddAbove _)

end iSup

section iInf

variable [CompleteLattice α] [InfConvergenceClass α] {f : ι → α}

/-
**tendsto_atBot_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atBot_iInf (h_mono : Monotone f) : Tendsto f atBot (𝓝 (⨅ i, f i))
参数：h_mono : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atBot_ciInf`：tendsto_atBot_ciInf (h_mono : Monotone f) (hbdd : B
ddBelow <| range f) : Tendsto f atBot (𝓝 (⨅ i, f i))
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem tendsto_atBot_iInf (h_mono : Monotone f) : Tendsto f atBot (𝓝 (⨅ i, f i)) :=
  tendsto_atBot_ciInf h_mono (OrderBot.bddBelow _)
/-
**tendsto_atTop_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atTop_iInf (h_anti : Antitone f) : Tendsto f atTop (𝓝 (⨅ i, f i))
参数：h_anti : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_ciInf`：tendsto_atTop_ciInf (h_anti : Antitone f) (hbdd : B
ddBelow <| range f) : Tendsto f atTop (𝓝 (⨅ i, f i))
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem tendsto_atTop_iInf (h_anti : Antitone f) : Tendsto f atTop (𝓝 (⨅ i, f i)) :=
  tendsto_atTop_ciInf h_anti (OrderBot.bddBelow _)

end iInf

end

/-
**Prod.supConvergenceClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.supConvergenceClass [Preorder α] [Preorder β] [TopologicalSpace α] [T
opologicalSpace β] [SupConvergenceClass α] [SupConvergenceClass β] : SupConverge
nceClass (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_isLUB`：tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsL
UB (Set.range f) a) : Tendsto f atTop (𝓝 a)
· 使用定理 `Monotone.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α
] [inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), Monotone (s.d
omRestrict…
· 使用定理 `monotone_fst`：monotone_fst : Monotone (@Prod.fst α β)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_domRestrict`：range_domRestrict (f : α -> β) (s : Set α) : Set.
range (s.domRestrict f) = f '' s
· 使用定理 `isLUB_prod`：isLUB_prod {s : Set (α × β)} {p : α × β} : IsLUB s p ↔ IsLUB
 (Prod.fst '' s) p.1 ∧ IsLUB (Prod.snd '' s) p.2
· 使用定理 `monotone_snd`：monotone_snd : Monotone (@Prod.snd α β)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
instance Prod.supConvergenceClass
    [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
    [SupConvergenceClass α] [SupConvergenceClass β] : SupConvergenceClass (α × β) := by
  constructor
  rintro ⟨a, b⟩ s h
  rw [isLUB_prod, ← range_domRestrict, ← range_domRestrict] at h
  have A : Tendsto (fun x : s => (x : α × β).1) atTop (𝓝 a) :=
    tendsto_atTop_isLUB (monotone_fst.domRestrict s) h.1
  have B : Tendsto (fun x : s => (x : α × β).2) atTop (𝓝 b) :=
    tendsto_atTop_isLUB (monotone_snd.domRestrict s) h.2
  exact A.prodMk_nhds B
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β] [InfConvergenceClass α]
    [InfConvergenceClass β] : InfConvergenceClass (α × β) :=
  show InfConvergenceClass (αᵒᵈ × βᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass
/-
**Pi.supConvergenceClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.supConvergenceClass {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α
 i)] [forall i, TopologicalSpace (α i)] [forall i, SupConvergenceClass (α i)] : 
SupConvergenceClass (forall i, α i)
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `tendsto_atTop_isLUB`：tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsL
UB (Set.range f) a) : Tendsto f atTop (𝓝 a)
· 使用定理 `Monotone.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α
] [inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), Monotone (s.d
omRestrict…
· 使用定理 `Function.monotone_eval`：Function.monotone_eval {ι : Type u} {α : ι -> Ty
pe v} [forall i, Preorder (α i)] (i : ι) : Monotone (Function.eval i : (forall i
, α i) -> α …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance Pi.supConvergenceClass
    {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, SupConvergenceClass (α i)] : SupConvergenceClass (∀ i, α i) := by
  refine ⟨fun f s h => ?_⟩
  simp only [isLUB_pi, ← range_domRestrict] at h
  exact tendsto_pi_nhds.2 fun i => tendsto_atTop_isLUB ((monotone_eval _).domRestrict _) (h i)
/-
**Pi.infConvergenceClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.infConvergenceClass {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α
 i)] [forall i, TopologicalSpace (α i)] [forall i, InfConvergenceClass (α i)] : 
InfConvergenceClass (forall i, α i)
参数：α i；α i；α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.infConvergenceClass
    {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, InfConvergenceClass (α i)] : InfConvergenceClass (∀ i, α i) :=
  show InfConvergenceClass (∀ i, (α i)ᵒᵈ)ᵒᵈ from OrderDual.infConvergenceClass
/-
**Pi.supConvergenceClass'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.supConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α] [Sup
ConvergenceClass α] : SupConvergenceClass (ι -> α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.supConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α]
    [SupConvergenceClass α] : SupConvergenceClass (ι → α) :=
  supConvergenceClass
/-
**Pi.infConvergenceClass'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.infConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α] [Inf
ConvergenceClass α] : InfConvergenceClass (ι -> α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.infConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α]
    [InfConvergenceClass α] : InfConvergenceClass (ι → α) :=
  Pi.infConvergenceClass
/-
**tendsto_atTop_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atTop_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α] 
[ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι -> α} (h_mono : Mo
notone f) : Tendsto f atTop atTop ∨ exists l, Tendsto f atTop (𝓝 l)
参数：h_mono : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_ciSup`：tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : B
ddAbove <| range f) : Tendsto f atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `Filter.tendsto_atTop_atTop_of_monotone'`：tendsto_atTop_atTop_of_monotone
' [Preorder ι] [LinearOrder α] {u : ι -> α} (h : Monotone u) (H : ¬BddAbove (ran
ge u)) : Tendsto u atTop atTo…
-/
theorem tendsto_atTop_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Monotone f) :
    Tendsto f atTop atTop ∨ ∃ l, Tendsto f atTop (𝓝 l) := by
  classical
  exact if H : BddAbove (range f) then Or.inr ⟨_, tendsto_atTop_ciSup h_mono H⟩
  else Or.inl <| tendsto_atTop_atTop_of_monotone' h_mono H

@[deprecated (since := "2026-01-22")] alias tendsto_of_monotone := tendsto_atTop_of_monotone
/-
**tendsto_atTop_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atTop_of_antitone {ι α : Type*} [Preorder ι] [TopologicalSpace α] 
[ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι -> α} (h_mono : An
titone f) : Tendsto f atTop atBot ∨ exists l, Tendsto f atTop (𝓝 l)
参数：h_mono : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_of_monotone`：tendsto_atTop_of_monotone {ι α : Type*} [Preo
rder ι] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology
 α] {f : ι -> α…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem tendsto_atTop_of_antitone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Antitone f) :
    Tendsto f atTop atBot ∨ ∃ l, Tendsto f atTop (𝓝 l) :=
  tendsto_atTop_of_monotone (α := αᵒᵈ) h_mono

@[deprecated (since := "2026-01-22")] alias tendsto_of_antitone := tendsto_atTop_of_antitone
/-
**tendsto_atBot_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atBot_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α] 
[ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι -> α} (h_mono : Mo
notone f) : Tendsto f atBot atBot ∨ exists l, Tendsto f atBot (𝓝 l)
参数：h_mono : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_of_monotone`：tendsto_atTop_of_monotone {ι α : Type*} [Preo
rder ι] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology
 α] {f : ι -> α…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem tendsto_atBot_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Monotone f) :
    Tendsto f atBot atBot ∨ ∃ l, Tendsto f atBot (𝓝 l) :=
  tendsto_atTop_of_monotone (ι := ιᵒᵈ) (α := αᵒᵈ) h_mono.dual
/-
**tendsto_atBot_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atBot_of_antitone {ι α : Type*} [Preorder ι] [TopologicalSpace α] 
[ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι -> α} (h_mono : An
titone f) : Tendsto f atBot atTop ∨ exists l, Tendsto f atBot (𝓝 l)
参数：h_mono : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_of_antitone`：tendsto_atTop_of_antitone {ι α : Type*} [Preo
rder ι] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology
 α] {f : ι -> α…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Antitone f → Antitone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem tendsto_atBot_of_antitone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Antitone f) :
    Tendsto f atBot atTop ∨ ∃ l, Tendsto f atBot (𝓝 l) :=
  tendsto_atTop_of_antitone (ι := ιᵒᵈ) (α := αᵒᵈ) h_mono.dual
/-
**tendsto_iff_tendsto_subseq_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_iff_tendsto_subseq_of_monotone {ι₁ ι₂ α : Type*} [SemilatticeSup ι
₁] [Preorder ι₂] [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinear
Order α] [OrderTopology α] [NoMaxOrder α] {f : ι₂ -> α} {φ : ι₁ -> ι₂} {l : α} (
hf : Monotone f) (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto 
(f ∘ φ) atTop (𝓝 l)
参数：hf : Monotone f；hg : Tendsto φ atTop atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_atTop_of_monotone`：tendsto_atTop_of_monotone {ι α : Type*} [Preo
rder ι] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology
 α] {f : ι -> α…
· 使用定理 `not_tendsto_atTop_of_tendsto_nhds`：∀ {α : Type u} {β : Type v} [inst : P
reorder α] [NoTopOrder α] [inst_2 : TopologicalSpace α] [ClosedIciTopology α]   
{a : α} {l : Filter β} …
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
-/
theorem tendsto_iff_tendsto_subseq_of_monotone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂]
    [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [NoMaxOrder α] {f : ι₂ → α} {φ : ι₁ → ι₂} {l : α} (hf : Monotone f)
    (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto (f ∘ φ) atTop (𝓝 l) := by
  constructor <;> intro h
  · exact h.comp hg
  · rcases tendsto_atTop_of_monotone hf with (h' | ⟨l', hl'⟩)
    · exact (not_tendsto_atTop_of_tendsto_nhds h (h'.comp hg)).elim
    · rwa [tendsto_nhds_unique h (hl'.comp hg)]
/-
**tendsto_iff_tendsto_subseq_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_iff_tendsto_subseq_of_antitone {ι₁ ι₂ α : Type*} [SemilatticeSup ι
₁] [Preorder ι₂] [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinear
Order α] [OrderTopology α] [NoMinOrder α] {f : ι₂ -> α} {φ : ι₁ -> ι₂} {l : α} (
hf : Antitone f) (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto 
(f ∘ φ) atTop (𝓝 l)
参数：hf : Antitone f；hg : Tendsto φ atTop atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_iff_tendsto_subseq_of_monotone`：tendsto_iff_tendsto_subseq_of_mo
notone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂] [Nonempty ι₁] [Topolo
gicalSpace α] [Conditionally…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ
-/
theorem tendsto_iff_tendsto_subseq_of_antitone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂]
    [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [NoMinOrder α] {f : ι₂ → α} {φ : ι₁ → ι₂} {l : α} (hf : Antitone f)
    (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto (f ∘ φ) atTop (𝓝 l) :=
  tendsto_iff_tendsto_subseq_of_monotone (α := αᵒᵈ) hf hg

/-! The next family of results, such as `isLUB_of_tendsto_atTop` and `iSup_eq_of_tendsto`, are
converses to the standard fact that bounded monotone functions converge. They state, that if a
monotone function `f` tends to `a` along `Filter.atTop`, then that value `a` is a least upper bound
for the range of `f`.

Related theorems above (`IsLUB.isLUB_of_tendsto`, `IsGLB.isGLB_of_tendsto` etc) cover the case
when `f x` tends to `a` as `x` tends to some point `b` in the domain. -/

/-
**Monotone.ge_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopol
ogy α] [Preorder β] [IsDirectedOrder β] {f : β -> α} {a : α} (hf : Monotone f) (
ha : Tendsto f atTop (𝓝 a)) (b : β) : f b <= a
参数：hf : Monotone f；ha : Tendsto f atTop (𝓝 a)；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x

--- 原说明 ---
The next family of results, such as `isLUB_of_tendsto_atTop` and `iSup_eq_of_ten
dsto`, are
converses to the standard fact that bounded monotone functions converge. They st
ate, that if a
monotone function `f` tends to `a` along `Filter.atTop`, then that value `a` is 
a least upper bound
for the range of `f`.

Related theorems above (`IsLUB.isLUB_of_tendsto`, `IsGLB.isGLB_of_tendsto` etc) 
cover the case
when `f x` tends to `a` as `x` tends to some point `b` in the domain.
-/
theorem Monotone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    f b ≤ a :=
  haveI : Nonempty β := Nonempty.intro b
  _root_.ge_of_tendsto ha ((eventually_ge_atTop b).mono fun _ hxy => hf hxy)
/-
**Monotone.le_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopol
ogy α] [Preorder β] [IsCodirectedOrder β] {f : β -> α} {a : α} (hf : Monotone f)
 (ha : Tendsto f atBot (𝓝 a)) (b : β) : a <= f b
参数：hf : Monotone f；ha : Tendsto f atBot (𝓝 a)；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.ge_of_tendsto`：Monotone.ge_of_tendsto [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] {f : β -> α} {
a : α} (hf :…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `OrderDual.isDirected_le`：∀ {α : Type u_1} [inst : LE α] [IsCodirectedOrd
er α], IsDirectedOrder αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem Monotone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    a ≤ f b :=
  hf.dual.ge_of_tendsto ha b
/-
**Antitone.le_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopol
ogy α] [Preorder β] [IsDirectedOrder β] {f : β -> α} {a : α} (hf : Antitone f) (
ha : Tendsto f atTop (𝓝 a)) (b : β) : a <= f b
参数：hf : Antitone f；ha : Tendsto f atTop (𝓝 a)；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.ge_of_tendsto`：Monotone.ge_of_tendsto [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] {f : β -> α} {
a : α} (hf :…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem Antitone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    a ≤ f b :=
  hf.dual_right.ge_of_tendsto ha b
/-
**Antitone.ge_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopol
ogy α] [Preorder β] [IsCodirectedOrder β] {f : β -> α} {a : α} (hf : Antitone f)
 (ha : Tendsto f atBot (𝓝 a)) (b : β) : f b <= a
参数：hf : Antitone f；ha : Tendsto f atBot (𝓝 a)；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_of_tendsto`：Monotone.le_of_tendsto [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsCodirectedOrder β] {f : β -> α}
 {a : α} (hf…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem Antitone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    f b ≤ a :=
  hf.dual_right.le_of_tendsto ha b
/-
**isLUB_of_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopol
ogy α] [Preorder β] [IsDirectedOrder β] [Nonempty β] {f : β -> α} {a : α} (hf : 
Monotone f) (ha : Tendsto f atTop (𝓝 a)) : IsLUB (Set.range f) a
参数：hf : Monotone f；ha : Tendsto f atTop (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.ge_of_tendsto`：Monotone.ge_of_tendsto [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] {f : β -> α} {
a : α} (hf :…
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem isLUB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsLUB (Set.range f) a := by
  constructor
  · rintro _ ⟨b, rfl⟩
    exact hf.ge_of_tendsto ha b
  · exact fun _ hb => le_of_tendsto' ha fun x => hb (Set.mem_range_self x)
/-
**isGLB_of_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopol
ogy α] [Preorder β] [IsCodirectedOrder β] [Nonempty β] {f : β -> α} {a : α} (hf 
: Monotone f) (ha : Tendsto f atBot (𝓝 a)) : IsGLB (Set.range f) a
参数：hf : Monotone f；ha : Tendsto f atBot (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_of_tendsto_atTop`：isLUB_of_tendsto_atTop [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] [Nonempty β] {
f : β -> α} …
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `OrderDual.isDirected_le`：∀ {α : Type u_1} [inst : LE α] [IsCodirectedOrd
er α], IsDirectedOrder αᵒᵈ
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem isGLB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsGLB (Set.range f) a :=
  isLUB_of_tendsto_atTop (α := αᵒᵈ) (β := βᵒᵈ) hf.dual ha
/-
**isLUB_of_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopol
ogy α] [Preorder β] [IsCodirectedOrder β] [Nonempty β] {f : β -> α} {a : α} (hf 
: Antitone f) (ha : Tendsto f atBot (𝓝 a)) : IsLUB (Set.range f) a
参数：hf : Antitone f；ha : Tendsto f atBot (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_of_tendsto_atTop`：isLUB_of_tendsto_atTop [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] [Nonempty β] {
f : β -> α} …
· 使用定理 `OrderDual.isDirected_le`：∀ {α : Type u_1} [inst : LE α] [IsCodirectedOrd
er α], IsDirectedOrder αᵒᵈ
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)
-/
theorem isLUB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsLUB (Set.range f) a :=
  isLUB_of_tendsto_atTop (α := α) (β := βᵒᵈ) hf.dual_left ha
/-
**isGLB_of_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopol
ogy α] [Preorder β] [IsDirectedOrder β] [Nonempty β] {f : β -> α} {a : α} (hf : 
Antitone f) (ha : Tendsto f atTop (𝓝 a)) : IsGLB (Set.range f) a
参数：hf : Antitone f；ha : Tendsto f atTop (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isGLB_of_tendsto_atBot`：isGLB_of_tendsto_atBot [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsCodirectedOrder β] [Nonempty β]
 {f : β -> α…
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)
-/
theorem isGLB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsGLB (Set.range f) a :=
  isGLB_of_tendsto_atBot (α := α) (β := βᵒᵈ) hf.dual_left ha
/-
**iSup_eq_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_eq_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [Ord
erTopology α] [Nonempty β] [SemilatticeSup β] {f : β -> α} {a : α} (hf : Monoton
e f) : Tendsto f atTop (𝓝 a) -> iSup f = a
参数：hf : Monotone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `tendsto_atTop_iSup`：tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f
 atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
-/
theorem iSup_eq_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Monotone f) :
    Tendsto f atTop (𝓝 a) → iSup f = a :=
  tendsto_nhds_unique (tendsto_atTop_iSup hf)
/-
**iInf_eq_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInf_eq_of_tendsto {α} [TopologicalSpace α] [CompleteLinearOrder α] [Order
Topology α] [Nonempty β] [SemilatticeSup β] {f : β -> α} {a : α} (hf : Antitone 
f) : Tendsto f atTop (𝓝 a) -> iInf f = a
参数：hf : Antitone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `tendsto_atTop_iInf`：tendsto_atTop_iInf (h_anti : Antitone f) : Tendsto f
 atTop (𝓝 (⨅ i, f i))
· 使用定理 `LinearOrder.infConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], InfConvergenceClass α
-/
theorem iInf_eq_of_tendsto {α} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Antitone f) :
    Tendsto f atTop (𝓝 a) → iInf f = a :=
  tendsto_nhds_unique (tendsto_atTop_iInf hf)
/-
**iSup_eq_iSup_subseq_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_eq_iSup_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteL
attice α] {l : Filter ι₁} [l.NeBot] {f : ι₂ -> α} {φ : ι₁ -> ι₂} (hf : Monotone 
f) (hφ : Tendsto φ l atTop) : ⨆ i, f i = ⨆ i, f (φ i)
参数：hf : Monotone f；hφ : Tendsto φ l atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem iSup_eq_iSup_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atTop) : ⨆ i, f i = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : i ≤ φ j) => hf hj) (hφ.eventually <| eventually_ge_atTop i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)
/-
**iSup_eq_iSup_subseq_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_eq_iSup_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteL
attice α] {l : Filter ι₁} [l.NeBot] {f : ι₂ -> α} {φ : ι₁ -> ι₂} (hf : Antitone 
f) (hφ : Tendsto φ l atBot) : ⨆ i, f i = ⨆ i, f (φ i)
参数：hf : Antitone f；hφ : Tendsto φ l atBot。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_le_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α)
, ∀ᶠ (x : α) in Filter.atBot, x ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem iSup_eq_iSup_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atBot) : ⨆ i, f i = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : φ j ≤ i) => hf hj) (hφ.eventually <| eventually_le_atBot i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)
/-
**iInf_eq_iInf_subseq_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInf_eq_iInf_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteL
attice α] {l : Filter ι₁} [l.NeBot] {f : ι₂ -> α} {φ : ι₁ -> ι₂} (hf : Monotone 
f) (hφ : Tendsto φ l atBot) : ⨅ i, f i = ⨅ i, f (φ i)
参数：hf : Monotone f；hφ : Tendsto φ l atBot。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_eq_iSup_subseq_of_monotone`：iSup_eq_iSup_subseq_of_monotone {ι₁ ι₂ 
α : Type*} [Preorder ι₂] [CompleteLattice α] {l : Filter ι₁} [l.NeBot] {f : ι₂ -
> α} {φ : ι₁ -> ι₂} (…
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem iInf_eq_iInf_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atBot) : ⨅ i, f i = ⨅ i, f (φ i) :=
  iSup_eq_iSup_subseq_of_monotone hf.dual hφ
/-
**iInf_eq_iInf_subseq_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInf_eq_iInf_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteL
attice α] {l : Filter ι₁} [l.NeBot] {f : ι₂ -> α} {φ : ι₁ -> ι₂} (hf : Antitone 
f) (hφ : Tendsto φ l atTop) : ⨅ i, f i = ⨅ i, f (φ i)
参数：hf : Antitone f；hφ : Tendsto φ l atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_eq_iSup_subseq_of_antitone`：iSup_eq_iSup_subseq_of_antitone {ι₁ ι₂ 
α : Type*} [Preorder ι₂] [CompleteLattice α] {l : Filter ι₁} [l.NeBot] {f : ι₂ -
> α} {φ : ι₁ -> ι₂} (…
· 使用定理 `Antitone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Antitone f → Antitone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem iInf_eq_iInf_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atTop) : ⨅ i, f i = ⨅ i, f (φ i) :=
  iSup_eq_iSup_subseq_of_antitone hf.dual hφ
