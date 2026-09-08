/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
module

public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Flows and invariant sets

This file defines a flow on a topological space `α` by a topological
monoid `τ` as a continuous monoid-action of `τ` on `α`. Anticipating the
cases where `τ` is one of `ℕ`, `ℤ`, `ℝ⁺`, or `ℝ`, we use additive
notation for the monoids, though the definition does not require
commutativity.

A subset `s` of `α` is invariant under a family of maps `ϕₜ : α → α`
if `ϕₜ s ⊆ s` for all `t`. In many cases `ϕ` will be a flow on
`α`. For the cases where `ϕ` is a flow by an ordered (additive,
commutative) monoid, we additionally define forward invariance, where
`t` ranges over those elements which are nonnegative.

Additionally, we define such constructions as the (forward) orbit, a
semiconjugacy between flows, a factor of a flow, the restriction of a
flow onto an invariant subset, and the time-reversal of a flow by a group.
-/

@[expose] public section


open Set Function Filter

variable {τ α : Type*}

/-!
### Invariant sets
-/
section Invariant

/-- A set `s ⊆ α` is invariant under `ϕ : τ → α → α` if `ϕ t s ⊆ s` for all `t` in `τ`. -/
/-
**IsInvariant** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsInvariant (ϕ : τ -> α -> α) (s : Set α) : Prop
参数：ϕ : τ -> α -> α；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s ⊆ α` is invariant under `ϕ : τ → α → α` if `ϕ t s ⊆ s` for all `t` in `
τ`.
-/
def IsInvariant (ϕ : τ → α → α) (s : Set α) : Prop :=
  ∀ t, MapsTo (ϕ t) s s

variable (ϕ : τ → α → α) (s : Set α)
/-
**isInvariant_iff_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isInvariant_iff_image : IsInvariant ϕ s ↔ forall t, ϕ t '' s subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isInvariant_iff_image : IsInvariant ϕ s ↔ ∀ t, ϕ t '' s ⊆ s := by
  simp_rw [IsInvariant, mapsTo_iff_image_subset]

/-- A set `s ⊆ α` is forward-invariant under `ϕ : τ → α → α` if `ϕ t s ⊆ s` for all `t ≥ 0`. -/
/-
**IsForwardInvariant** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsForwardInvariant [Preorder τ] [Zero τ] (ϕ : τ -> α -> α) (s : Set α) : P
rop
参数：ϕ : τ -> α -> α；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s ⊆ α` is forward-invariant under `ϕ : τ → α → α` if `ϕ t s ⊆ s` for all 
`t ≥ 0`.
-/
def IsForwardInvariant [Preorder τ] [Zero τ] (ϕ : τ → α → α) (s : Set α) : Prop :=
  ∀ ⦃t⦄, 0 ≤ t → MapsTo (ϕ t) s s
/-
**IsInvariant.isForwardInvariant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsInvariant.isForwardInvariant [Preorder τ] [Zero τ] {ϕ : τ -> α -> α} {s 
: Set α} (h : IsInvariant ϕ s) : IsForwardInvariant ϕ s
参数：h : IsInvariant ϕ s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsInvariant.isForwardInvariant [Preorder τ] [Zero τ] {ϕ : τ → α → α} {s : Set α}
    (h : IsInvariant ϕ s) : IsForwardInvariant ϕ s := fun t _ht => h t

/-- If `τ` is a `CanonicallyOrderedAdd` monoid (e.g., `ℕ` or `ℝ≥0`), then the notions
`IsForwardInvariant` and `IsInvariant` are equivalent. -/
/-
**IsForwardInvariant.isInvariant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsForwardInvariant.isInvariant [AddMonoid τ] [PartialOrder τ] [Canonically
OrderedAdd τ] {ϕ : τ -> α -> α} {s : Set α} (h : IsForwardInvariant ϕ s) : IsInv
ariant ϕ s
参数：h : IsForwardInvariant ϕ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α

--- 原说明 ---
If `τ` is a `CanonicallyOrderedAdd` monoid (e.g., `ℕ` or `ℝ≥0`), then the notion
s
`IsForwardInvariant` and `IsInvariant` are equivalent.
-/
theorem IsForwardInvariant.isInvariant [AddMonoid τ] [PartialOrder τ] [CanonicallyOrderedAdd τ]
    {ϕ : τ → α → α} {s : Set α}
    (h : IsForwardInvariant ϕ s) : IsInvariant ϕ s := fun _ => h zero_le

/-- If `τ` is a `CanonicallyOrderedAdd` monoid (e.g., `ℕ` or `ℝ≥0`), then the notions
`IsForwardInvariant` and `IsInvariant` are equivalent. -/
/-
**isForwardInvariant_iff_isInvariant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isForwardInvariant_iff_isInvariant [AddMonoid τ] [PartialOrder τ] [Canonic
allyOrderedAdd τ] {ϕ : τ -> α -> α} {s : Set α} : IsForwardInvariant ϕ s ↔ IsInv
ariant ϕ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsForwardInvariant.isInvariant`：IsForwardInvariant.isInvariant [AddMonoi
d τ] [PartialOrder τ] [CanonicallyOrderedAdd τ] {ϕ : τ -> α -> α} {s : Set α} (h
 : IsForwardInvarian…
· 使用定理 `IsInvariant.isForwardInvariant`：IsInvariant.isForwardInvariant [Preorder
 τ] [Zero τ] {ϕ : τ -> α -> α} {s : Set α} (h : IsInvariant ϕ s) : IsForwardInva
riant ϕ s

--- 原说明 ---
If `τ` is a `CanonicallyOrderedAdd` monoid (e.g., `ℕ` or `ℝ≥0`), then the notion
s
`IsForwardInvariant` and `IsInvariant` are equivalent.
-/
theorem isForwardInvariant_iff_isInvariant [AddMonoid τ] [PartialOrder τ] [CanonicallyOrderedAdd τ]
    {ϕ : τ → α → α} {s : Set α} :
    IsForwardInvariant ϕ s ↔ IsInvariant ϕ s :=
  ⟨IsForwardInvariant.isInvariant, IsInvariant.isForwardInvariant⟩

end Invariant

/-!
### Flows
-/

variable (τ α) in
/-- A flow on a topological space `α` by an additive topological
monoid `τ` is a continuous monoid action of `τ` on `α`. -/
/-
**Flow** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(τ : Type u_1) → (α : Type u_2) → [TopologicalSpace τ] → [TopologicalSpace
 α] → [AddZero τ] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A flow on a topological space `α` by an additive topological
monoid `τ` is a continuous monoid action of `τ` on `α`.
-/
structure Flow [TopologicalSpace τ] [TopologicalSpace α] [AddZero τ] where
  /-- The map `τ → α → α` underlying a flow of `τ` on `α`. -/
  toFun : τ → α → α
  cont' : Continuous (uncurry toFun)
  map_add' : ∀ t₁ t₂ x, toFun (t₁ + t₂) x = toFun t₁ (toFun t₂ x)
  map_zero' : ∀ x, toFun 0 x = x

namespace Flow

variable [TopologicalSpace τ] [TopologicalSpace α]

section AddZero

variable [AddZero τ] (ϕ : Flow τ α)

/-
**Flow.** 是 Mathlib 中的一个实例，位于命名空间 `Flow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (Flow τ α) fun _ => τ → α → α := ⟨Flow.toFun⟩

variable (τ α) in
/-- The identity map as a constant flow. -/
/-
**Flow.id** 是 Mathlib 中的一个定义，位于命名空间 `Flow`。
形式化陈述：(τ : Type u_1) →   (α : Type u_2) → [inst : TopologicalSpace τ] → [inst_1 
: TopologicalSpace α] → [inst_2 : AddZero τ] → Flow τ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
The identity map as a constant flow.
-/
protected def id : Flow τ α where
  toFun _ := id
  cont' := continuous_snd
  map_add' _ _ _ := rfl
  map_zero' _ := rfl

@[simp]
/-
**Flow.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：id_apply (t : τ) : Flow.id τ α t = id
参数：t : τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (t : τ) : Flow.id τ α t = id := rfl
/-
**Flow.** 是 Mathlib 中的一个实例，位于命名空间 `Flow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Flow τ α) :=
  ⟨Flow.id τ α⟩

@[ext]
/-
**Flow.ext** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：∀ {τ : Type u_1} {α : Type u_2} [inst : TopologicalSpace τ] [inst_1 : Topo
logicalSpace α] [inst_2 : AddZero τ]   {ϕ₁ ϕ₂ : Flow τ α}, (∀ (t : τ) (x : α), ϕ
₁.toFun t x = ϕ₂.toFun t x) → ϕ₁ = ϕ₂
参数：∀ (t : τ) (x : α), ϕ₁.toFun t x = ϕ₂.toFun t x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext : ∀ {ϕ₁ ϕ₂ : Flow τ α}, (∀ t x, ϕ₁ t x = ϕ₂ t x) → ϕ₁ = ϕ₂
  | ⟨f₁, _, _, _⟩, ⟨f₂, _, _, _⟩, h => by
    congr
    funext
    exact h _ _

@[continuity, fun_prop]
/-
**Flow.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：∀ {τ : Type u_1} {α : Type u_2} [inst : TopologicalSpace τ] [inst_1 : Topo
logicalSpace α] [inst_2 : AddZero τ]   (ϕ : Flow τ α) {β : Type u_3} [inst_3 : T
opologicalSpace β] {t : β → τ},   Continuous t → ∀ {f : β → α}, Continuous f → C
ontinuous fun x => ϕ.toFun (t x) (f x)
参数：ϕ : Flow τ α；t x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Flow.cont'`：∀ {τ : Type u_1} {α : Type u_2} [inst : TopologicalSpace τ] 
[inst_1 : TopologicalSpace α] [inst_2 : AddZero τ]   (self : Flow τ α), Continuo
…
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
-/
protected theorem continuous {β : Type*} [TopologicalSpace β] {t : β → τ} (ht : Continuous t)
    {f : β → α} (hf : Continuous f) : Continuous fun x => ϕ (t x) (f x) :=
  ϕ.cont'.comp (ht.prodMk hf)

alias _root_.Continuous.flow := Flow.continuous

@[continuity, fun_prop]
/-
**Flow.continuous_toFun** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：continuous_toFun (t : τ) : Continuous (ϕ.toFun t)
参数：t : τ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Flow.continuous`：∀ {τ : Type u_1} {α : Type u_2} [inst : TopologicalSpac
e τ] [inst_1 : TopologicalSpace α] [inst_2 : AddZero τ]   (ϕ : Flow τ α) {β : Ty
pe u_…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
-/
theorem continuous_toFun (t : τ) : Continuous (ϕ.toFun t) := by
  fun_prop
/-
**Flow.map_add** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：map_add (t₁ t₂ : τ) (x : α) : ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x)
参数：t₁ t₂ : τ；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Flow.map_add'`：∀ {τ : Type u_1} {α : Type u_2} [inst : TopologicalSpace 
τ] [inst_1 : TopologicalSpace α] [inst_2 : AddZero τ]   (self : Flow τ α) (t₁ t₂
 : …
-/
theorem map_add (t₁ t₂ : τ) (x : α) : ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x) := ϕ.map_add' _ _ _

@[simp]
/-
**Flow.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：map_zero : ϕ 0 = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Flow.map_zero'`：∀ {τ : Type u_1} {α : Type u_2} [inst : TopologicalSpace
 τ] [inst_1 : TopologicalSpace α] [inst_2 : AddZero τ]   (self : Flow τ α) (x : 
α), …
-/
theorem map_zero : ϕ 0 = id := funext ϕ.map_zero'
/-
**Flow.map_zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：map_zero_apply (x : α) : ϕ 0 x = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Flow.map_zero'`：∀ {τ : Type u_1} {α : Type u_2} [inst : TopologicalSpace
 τ] [inst_1 : TopologicalSpace α] [inst_2 : AddZero τ]   (self : Flow τ α) (x : 
α), …
-/
theorem map_zero_apply (x : α) : ϕ 0 x = x := ϕ.map_zero' x

/-- Iterations of a continuous function from a topological space `α`
to itself defines a semiflow by `ℕ` on `α`. -/
/-
**Flow.fromIter** 是 Mathlib 中的一个定义，位于命名空间 `Flow`。
形式化陈述：fromIter {g : α -> α} (h : Continuous g) : Flow Nat α where toFun n
参数：h : Continuous g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)

--- 原说明 ---
Iterations of a continuous function from a topological space `α`
to itself defines a semiflow by `ℕ` on `α`.
-/
def fromIter {g : α → α} (h : Continuous g) : Flow ℕ α where
  toFun n := g^[n]
  cont' := continuous_prod_of_discrete_left.mpr h.iterate
  map_add' := iterate_add_apply _
  map_zero' _x := rfl

@[simp]
/-
**Flow.fromIter_apply** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：fromIter_apply {g : α -> α} (h : Continuous g) (n : Nat) (x : α) : fromIte
r h n x = g^[n] x
参数：h : Continuous g；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromIter_apply {g : α → α} (h : Continuous g) (n : ℕ) (x : α) :
    fromIter h n x = g^[n] x := rfl

/-- Restriction of a flow onto an invariant set. -/
/-
**Flow.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Flow`。
形式化陈述：restrict {s : Set α} (h : IsInvariant ϕ s) : Flow τ s where toFun t
参数：h : IsInvariant ϕ s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of a flow onto an invariant set.
-/
def restrict {s : Set α} (h : IsInvariant ϕ s) : Flow τ s where
  toFun t := (h t).restrict _ _ _
  cont' := Continuous.subtype_mk (by fun_prop) _
  map_add' _ _ _ := Subtype.ext (map_add _ _ _ _)
  map_zero' _ := Subtype.ext (map_zero_apply _ _)

@[simp]
/-
**Flow.coe_restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：coe_restrict_apply {s : Set α} (h : IsInvariant ϕ s) (t : τ) (x : s) : res
trict ϕ h t x = ϕ t x
参数：h : IsInvariant ϕ s；t : τ；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrict_apply {s : Set α} (h : IsInvariant ϕ s) (t : τ) (x : s) :
    restrict ϕ h t x = ϕ t x := rfl

end AddZero

section AddMonoid

variable [AddMonoid τ] (ϕ : Flow τ α)

/-- Convert a flow to an additive monoid action. -/
@[instance_reducible]
/-
**Flow.toAddAction** 是 Mathlib 中的一个定义，位于命名空间 `Flow`。
形式化陈述：toAddAction : AddAction τ α where vadd
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a flow to an additive monoid action.
-/
def toAddAction : AddAction τ α where
  vadd := ϕ
  add_vadd := ϕ.map_add'
  zero_vadd := ϕ.map_zero'

/-- Restrict a flow by `τ` to a flow by an additive submonoid of `τ`. -/
/-
**Flow.restrictAddSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `Flow`。
形式化陈述：restrictAddSubmonoid (S : AddSubmonoid τ) : Flow S α where toFun t x
参数：S : AddSubmonoid τ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a flow by `τ` to a flow by an additive submonoid of `τ`.
-/
def restrictAddSubmonoid (S : AddSubmonoid τ) : Flow S α where
  toFun t x := ϕ t x
  cont' := by fun_prop
  map_add' t₁ t₂ x := ϕ.map_add' t₁ t₂ x
  map_zero' := ϕ.map_zero'
/-
**Flow.restrictAddSubmonoid_apply** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：restrictAddSubmonoid_apply (S : AddSubmonoid τ) (t : S) (x : α) : restrict
AddSubmonoid ϕ S t x = ϕ t x
参数：S : AddSubmonoid τ；t : S；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictAddSubmonoid_apply (S : AddSubmonoid τ) (t : S) (x : α) :
    restrictAddSubmonoid ϕ S t x = ϕ t x := rfl

section Orbit

/-- The orbit of a point under a flow. -/
/-
**Flow.orbit** 是 Mathlib 中的一个定义，位于命名空间 `Flow`。
形式化陈述：orbit (x : α) : Set α
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orbit of a point under a flow.
-/
def orbit (x : α) : Set α := @AddAction.orbit _ _ ϕ.toAddAction.toVAdd x
/-
**Flow.orbit_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：orbit_eq_range (x : α) : orbit ϕ x = Set.range (fun t => ϕ t x)
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orbit_eq_range (x : α) : orbit ϕ x = Set.range (fun t => ϕ t x) := rfl
/-
**Flow.mem_orbit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：mem_orbit_iff {x₁ x₂ : α} : x₂ in orbit ϕ x₁ ↔ exists t : τ, ϕ t x₁ = x₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_orbit_iff {x₁ x₂ : α} : x₂ ∈ orbit ϕ x₁ ↔ ∃ t : τ, ϕ t x₁ = x₂ := Iff.rfl
/-
**Flow.mem_orbit** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：mem_orbit (x : α) (t : τ) : ϕ t x in orbit ϕ x
参数：x : α；t : τ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddAction.mem_orbit`：∀ {γ : Type u_2} {α : Type u_3} [inst : VAdd γ α] (
a : α) (m : γ), m +ᵥ a ∈ AddAction.orbit γ a
-/
theorem mem_orbit (x : α) (t : τ) : ϕ t x ∈ orbit ϕ x :=
  @AddAction.mem_orbit _ _ ϕ.toAddAction.toVAdd x t
/-
**Flow.mem_orbit_self** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：mem_orbit_self (x : α) : x in orbit ϕ x
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddAction.mem_orbit_self`：∀ {M : Type u_1} {α : Type u_3} [inst : AddMon
oid M] [inst_1 : AddAction M α] (a : α), a ∈ AddAction.orbit M a
-/
theorem mem_orbit_self (x : α) : x ∈ orbit ϕ x := ϕ.toAddAction.mem_orbit_self x
/-
**Flow.nonempty_orbit** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：nonempty_orbit (x : α) : Set.Nonempty (orbit ϕ x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddAction.nonempty_orbit`：∀ {M : Type u_1} {α : Type u_3} [inst : AddMon
oid M] [inst_1 : AddAction M α] (a : α), (AddAction.orbit M a).Nonempty
-/
theorem nonempty_orbit (x : α) : Set.Nonempty (orbit ϕ x) := ϕ.toAddAction.nonempty_orbit x
/-
**Flow.mem_orbit_of_mem_orbit** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：mem_orbit_of_mem_orbit {x₁ x₂ : α} (t : τ) (h : x₂ in orbit ϕ x₁) : ϕ t x₂
 in orbit ϕ x₁
参数：t : τ；h : x₂ in orbit ϕ x₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddAction.mem_orbit_of_mem_orbit`：∀ {M : Type u_1} {α : Type u_3} [inst 
: AddMonoid M] [inst_1 : AddAction M α] {a₁ a₂ : α} (m : M),   a₂ ∈ AddAction.or
bit M a₁ → m +ᵥ a₂ ∈ A…
-/
theorem mem_orbit_of_mem_orbit {x₁ x₂ : α} (t : τ) (h : x₂ ∈ orbit ϕ x₁) : ϕ t x₂ ∈ orbit ϕ x₁ :=
  ϕ.toAddAction.mem_orbit_of_mem_orbit t h

/-- The orbit of a point under a flow `ϕ` is invariant under `ϕ`. -/
/-
**Flow.isInvariant_orbit** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：isInvariant_orbit (x : α) : IsInvariant ϕ (orbit ϕ x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddAction.mem_orbit_of_mem_orbit`：∀ {M : Type u_1} {α : Type u_3} [inst 
: AddMonoid M] [inst_1 : AddAction M α] {a₁ a₂ : α} (m : M),   a₂ ∈ AddAction.or
bit M a₁ → m +ᵥ a₂ ∈ A…

--- 原说明 ---
The orbit of a point under a flow `ϕ` is invariant under `ϕ`.
-/
theorem isInvariant_orbit (x : α) : IsInvariant ϕ (orbit ϕ x) :=
  fun t _ => ϕ.toAddAction.mem_orbit_of_mem_orbit t
/-
**Flow.orbit_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：orbit_restrict (s : Set α) (hs : IsInvariant ϕ s) (x : s) : orbit (ϕ.restr
ict hs) x = Subtype.val ⁻¹' orbit ϕ x
参数：s : Set α；hs : IsInvariant ϕ s；x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem orbit_restrict (s : Set α) (hs : IsInvariant ϕ s) (x : s) :
    orbit (ϕ.restrict hs) x = Subtype.val ⁻¹' orbit ϕ x :=
  Set.ext (fun x => by simp [orbit_eq_range, Subtype.ext_iff])

variable [Preorder τ] [AddLeftMono τ]

/-- Restrict a flow by `τ` to a flow by the additive submonoid of nonnegative elements of `τ`. -/
/-
**Flow.restrictNonneg** 是 Mathlib 中的一个定义，位于命名空间 `Flow`。
形式化陈述：restrictNonneg : Flow (AddSubmonoid.nonneg τ) α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a flow by `τ` to a flow by the additive submonoid of nonnegative elemen
ts of `τ`.
-/
def restrictNonneg : Flow (AddSubmonoid.nonneg τ) α := ϕ.restrictAddSubmonoid (.nonneg τ)

/-- The forward orbit of a point under a flow. -/
/-
**Flow.forwardOrbit** 是 Mathlib 中的一个定义，位于命名空间 `Flow`。
形式化陈述：forwardOrbit (x : α) : Set α
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forward orbit of a point under a flow.
-/
def forwardOrbit (x : α) : Set α := orbit ϕ.restrictNonneg x
/-
**Flow.forwardOrbit_eq_range_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：forwardOrbit_eq_range_nonneg (x : α) : forwardOrbit ϕ x = Set.range (fun t
 : {t : τ // 0 <= t} => ϕ t x)
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forwardOrbit_eq_range_nonneg (x : α) :
    forwardOrbit ϕ x = Set.range (fun t : {t : τ // 0 ≤ t} => ϕ t x) := rfl

/-- The forward orbit of a point under a flow `ϕ` is forward-invariant under `ϕ`. -/
/-
**Flow.isForwardInvariant_forwardOrbit** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：isForwardInvariant_forwardOrbit (x : α) : IsForwardInvariant ϕ (forwardOrb
it ϕ x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsInvariant.isForwardInvariant`：IsInvariant.isForwardInvariant [Preorder
 τ] [Zero τ] {ϕ : τ -> α -> α} {s : Set α} (h : IsInvariant ϕ s) : IsForwardInva
riant ϕ s
· 使用定理 `Flow.isInvariant_orbit`：isInvariant_orbit (x : α) : IsInvariant ϕ (orbit
 ϕ x)

--- 原说明 ---
The forward orbit of a point under a flow `ϕ` is forward-invariant under `ϕ`.
-/
theorem isForwardInvariant_forwardOrbit (x : α) : IsForwardInvariant ϕ (forwardOrbit ϕ x) :=
  fun t h => IsInvariant.isForwardInvariant (isInvariant_orbit ϕ.restrictNonneg x) (t := ⟨t, h⟩) h

/-- The forward orbit of a point `x` is contained in the orbit of `x`. -/
/-
**Flow.forwardOrbit_subset_orbit** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：forwardOrbit_subset_orbit (x : α) : forwardOrbit ϕ x subseteq orbit ϕ x
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddAction.orbit_addSubmonoid_subset`：∀ {M : Type u_1} {α : Type u_3} [in
st : AddMonoid M] [inst_1 : AddAction M α] (S : AddSubmonoid M) (a : α),   AddAc
tion.orbit (↥S) a ⊆ AddAc…

--- 原说明 ---
The forward orbit of a point `x` is contained in the orbit of `x`.
-/
theorem forwardOrbit_subset_orbit (x : α) : forwardOrbit ϕ x ⊆ orbit ϕ x :=
  ϕ.toAddAction.orbit_addSubmonoid_subset (AddSubmonoid.nonneg τ) x
/-
**Flow.mem_orbit_of_mem_forwardOrbit** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：mem_orbit_of_mem_forwardOrbit {x₁ x₂ : α} (h : x₁ in forwardOrbit ϕ x₂) : 
x₁ in orbit ϕ x₂
参数：h : x₁ in forwardOrbit ϕ x₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Flow.forwardOrbit_subset_orbit`：forwardOrbit_subset_orbit (x : α) : forw
ardOrbit ϕ x subseteq orbit ϕ x
-/
theorem mem_orbit_of_mem_forwardOrbit {x₁ x₂ : α} (h : x₁ ∈ forwardOrbit ϕ x₂) : x₁ ∈ orbit ϕ x₂ :=
  ϕ.forwardOrbit_subset_orbit x₂ h

end Orbit

variable {β γ : Type*} [TopologicalSpace β] [TopologicalSpace γ] (ψ : Flow τ β) (χ : Flow τ γ)

/-- Given flows `ϕ` by `τ` on `α` and `ψ` by `τ` on `β`, a function `π : α → β` is called a
*semiconjugacy* from `ϕ` to `ψ` if `π` is continuous and surjective, and `π ∘ (ϕ t) = (ψ t) ∘ π` for
all `t : τ`. -/
/-
**Flow.IsSemiconjugacy** 是 Mathlib 中的一个归纳类型，位于命名空间 `Flow`。
形式化陈述：{τ : Type u_1} →   {α : Type u_2} →     [inst : TopologicalSpace τ] →     
  [inst_1 : TopologicalSpace α] →         [inst_2 : AddMonoid τ] → {β : Type u_3
} → [inst_3 : TopologicalSpace β] → (α → β) → Flow τ α → Flow τ β → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given flows `ϕ` by `τ` on `α` and `ψ` by `τ` on `β`, a function `π : α → β` is c
alled a
*semiconjugacy* from `ϕ` to `ψ` if `π` is continuous and surjective, and `π ∘ (ϕ
 t) = (ψ t) ∘ π` for
all `t : τ`.
-/
structure IsSemiconjugacy (π : α → β) (ϕ : Flow τ α) (ψ : Flow τ β) : Prop where
  cont : Continuous π
  surj : Function.Surjective π
  semiconj : ∀ t, Function.Semiconj π (ϕ t) (ψ t)

/-- The composition of semiconjugacies is a semiconjugacy. -/
/-
**Flow.IsSemiconjugacy.comp** 是 Mathlib 中的一个定理，位于命名空间 `Flow.IsSemiconjugacy`。
形式化陈述：∀ {τ : Type u_1} {α : Type u_2} [inst : TopologicalSpace τ] [inst_1 : Topo
logicalSpace α] [inst_2 : AddMonoid τ]   (ϕ : Flow τ α) {β : Type u_3} {γ : Type
 u_4} [inst_3 : TopologicalSpace β] [inst_4 : TopologicalSpace γ]   (ψ : Flow τ 
β) (χ : Flow τ γ) {π : α → β} {ρ : β → γ},   Flow.IsSemiconjugacy π ϕ ψ → Flow.I
sSemiconjugacy ρ ψ χ → Flow.IsSemiconjugacy (ρ ∘ π) ϕ χ
参数：ϕ : Flow τ α；ψ : Flow τ β；χ : Flow τ γ；ρ ∘ π。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Flow.IsSemiconjugacy.cont`：∀ {τ : Type u_1} {α : Type u_2} [inst : Topol
ogicalSpace τ] [inst_1 : TopologicalSpace α] [inst_2 : AddMonoid τ]   {β : Type 
u_3} [inst_3 : …
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Flow.IsSemiconjugacy.surj`：∀ {τ : Type u_1} {α : Type u_2} [inst : Topol
ogicalSpace τ] [inst_1 : TopologicalSpace α] [inst_2 : AddMonoid τ]   {β : Type 
u_3} [inst_3 : …
· 使用定理 `Function.Semiconj.comp_left`：comp_left (hbc : Semiconj fbc gb gc) (hab :
 Semiconj fab ga gb) : Semiconj (fbc ∘ fab) ga gc
· 使用定理 `Flow.IsSemiconjugacy.semiconj`：∀ {τ : Type u_1} {α : Type u_2} [inst : T
opologicalSpace τ] [inst_1 : TopologicalSpace α] [inst_2 : AddMonoid τ]   {β : T
ype u_3} [inst_3 : …

--- 原说明 ---
The composition of semiconjugacies is a semiconjugacy.
-/
theorem IsSemiconjugacy.comp {π : α → β} {ρ : β → γ}
    (h₁ : IsSemiconjugacy π ϕ ψ) (h₂ : IsSemiconjugacy ρ ψ χ) : IsSemiconjugacy (ρ ∘ π) ϕ χ :=
  ⟨h₂.cont.comp h₁.cont, h₂.surj.comp h₁.surj, fun t => (h₂.semiconj t).comp_left (h₁.semiconj t)⟩

/-- The identity is a semiconjugacy from `ϕ` to `ψ` if and only if `ϕ` and `ψ` are equal. -/
/-
**Flow.isSemiconjugacy_id_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：isSemiconjugacy_id_iff_eq (ϕ ψ : Flow τ α) : IsSemiconjugacy id ϕ ψ ↔ ϕ = 
ψ
参数：ϕ ψ : Flow τ α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Flow.ext`：∀ {τ : Type u_1} {α : Type u_2} [inst : TopologicalSpace τ] [i
nst_1 : TopologicalSpace α] [inst_2 : AddZero τ]   {ϕ₁ ϕ₂ : Flow τ α}, (∀ (t :…
· 使用定理 `Flow.IsSemiconjugacy.semiconj`：∀ {τ : Type u_1} {α : Type u_2} [inst : T
opologicalSpace τ] [inst_1 : TopologicalSpace α] [inst_2 : AddMonoid τ]   {β : T
ype u_3} [inst_3 : …
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `Function.Semiconj.id_left`：id_left : Semiconj id ga ga

--- 原说明 ---
The identity is a semiconjugacy from `ϕ` to `ψ` if and only if `ϕ` and `ψ` are e
qual.
-/
theorem isSemiconjugacy_id_iff_eq (ϕ ψ : Flow τ α) : IsSemiconjugacy id ϕ ψ ↔ ϕ = ψ :=
  ⟨fun h => ext h.semiconj, fun h => h.recOn ⟨continuous_id, surjective_id, fun _ => .id_left⟩⟩

/-- A flow `ψ` is called a *factor* of `ϕ` if there exists a semiconjugacy from `ϕ` to `ψ`. -/
/-
**Flow.IsFactorOf** 是 Mathlib 中的一个定义，位于命名空间 `Flow`。
形式化陈述：IsFactorOf (ψ : Flow τ β) (ϕ : Flow τ α) : Prop
参数：ψ : Flow τ β；ϕ : Flow τ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A flow `ψ` is called a *factor* of `ϕ` if there exists a semiconjugacy from `ϕ` 
to `ψ`.
-/
def IsFactorOf (ψ : Flow τ β) (ϕ : Flow τ α) : Prop := ∃ π : α → β, IsSemiconjugacy π ϕ ψ
/-
**Flow.IsSemiconjugacy.isFactorOf** 是 Mathlib 中的一个定理，位于命名空间 `Flow.IsSemiconjugac
y`。
形式化陈述：∀ {τ : Type u_1} {α : Type u_2} [inst : TopologicalSpace τ] [inst_1 : Topo
logicalSpace α] [inst_2 : AddMonoid τ]   (ϕ : Flow τ α) {β : Type u_3} [inst_3 :
 TopologicalSpace β] (ψ : Flow τ β) {π : α → β},   Flow.IsSemiconjugacy π ϕ ψ → 
ψ.IsFactorOf ϕ
参数：ϕ : Flow τ α；ψ : Flow τ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSemiconjugacy.isFactorOf {π : α → β} (h : IsSemiconjugacy π ϕ ψ) : IsFactorOf ψ ϕ :=
  ⟨π, h⟩

/-- Transitivity of factors of flows. -/
/-
**Flow.IsFactorOf.trans** 是 Mathlib 中的一个定理，位于命名空间 `Flow.IsFactorOf`。
形式化陈述：∀ {τ : Type u_1} {α : Type u_2} [inst : TopologicalSpace τ] [inst_1 : Topo
logicalSpace α] [inst_2 : AddMonoid τ]   (ϕ : Flow τ α) {β : Type u_3} {γ : Type
 u_4} [inst_3 : TopologicalSpace β] [inst_4 : TopologicalSpace γ]   (ψ : Flow τ 
β) (χ : Flow τ γ), ϕ.IsFactorOf ψ → ψ.IsFactorOf χ → ϕ.IsFactorOf χ
参数：ϕ : Flow τ α；ψ : Flow τ β；χ : Flow τ γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Flow.IsSemiconjugacy.comp`：∀ {τ : Type u_1} {α : Type u_2} [inst : Topol
ogicalSpace τ] [inst_1 : TopologicalSpace α] [inst_2 : AddMonoid τ]   (ϕ : Flow 
τ α) {β : Type …

--- 原说明 ---
Transitivity of factors of flows.
-/
theorem IsFactorOf.trans (h₁ : IsFactorOf ϕ ψ) (h₂ : IsFactorOf ψ χ) : IsFactorOf ϕ χ :=
  h₁.elim fun π hπ => h₂.elim fun ρ hρ => ⟨π ∘ ρ, hρ.comp χ ψ ϕ hπ⟩

/-- Every flow is a factor of itself. -/
/-
**Flow.IsFactorOf.self** 是 Mathlib 中的一个定理，位于命名空间 `Flow.IsFactorOf`。
形式化陈述：∀ {τ : Type u_1} {α : Type u_2} [inst : TopologicalSpace τ] [inst_1 : Topo
logicalSpace α] [inst_2 : AddMonoid τ]   (ϕ : Flow τ α), ϕ.IsFactorOf ϕ
参数：ϕ : Flow τ α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Flow.isSemiconjugacy_id_iff_eq`：isSemiconjugacy_id_iff_eq (ϕ ψ : Flow τ 
α) : IsSemiconjugacy id ϕ ψ ↔ ϕ = ψ

--- 原说明 ---
Every flow is a factor of itself.
-/
theorem IsFactorOf.self : IsFactorOf ϕ ϕ := ⟨id, (isSemiconjugacy_id_iff_eq ϕ ϕ).mpr rfl⟩

end AddMonoid

section AddGroup

variable [AddGroup τ] (ϕ : Flow τ α)

/-- The map `ϕ t` as a homeomorphism. -/
/-
**Flow.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Flow`。
形式化陈述：toHomeomorph (t : τ) : (α ≃ₜ α) where toFun
参数：t : τ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `ϕ t` as a homeomorphism.
-/
def toHomeomorph (t : τ) : (α ≃ₜ α) where
  toFun := ϕ t
  invFun := ϕ (-t)
  left_inv x := by simp [← map_add]
  right_inv x := by simp [← map_add]

@[simp]
/-
**Flow.toHomeomorph_apply** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：toHomeomorph_apply (t : τ) (x : α) : ϕ.toHomeomorph t x = ϕ t x
参数：t : τ；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHomeomorph_apply (t : τ) (x : α) : ϕ.toHomeomorph t x = ϕ t x := rfl

@[simp]
/-
**Flow.toHomeomorph_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：toHomeomorph_symm_apply (t : τ) (x : α) : (ϕ.toHomeomorph t).symm x = ϕ (-
t) x
参数：t : τ；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHomeomorph_symm_apply (t : τ) (x : α) : (ϕ.toHomeomorph t).symm x = ϕ (-t) x := rfl
/-
**Flow.isInvariant_iff_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：isInvariant_iff_image_eq (s : Set α) : IsInvariant ϕ s ↔ forall t, ϕ t '' 
s = s
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isInvariant_iff_image`：isInvariant_iff_image : IsInvariant ϕ s ↔ forall 
t, ϕ t '' s subseteq s
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Flow.map_zero`：map_zero : ϕ 0 = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem isInvariant_iff_image_eq (s : Set α) : IsInvariant ϕ s ↔ ∀ t, ϕ t '' s = s :=
  (isInvariant_iff_image _ _).trans
    (Iff.intro
      (fun h t => Subset.antisymm (h t) fun _ hx => ⟨_, h (-t) ⟨_, hx, rfl⟩, by simp [← map_add]⟩)
      fun h t => by rw [h t])
/-
**Flow.image_eq_preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：image_eq_preimage_symm (t : τ) (s : Set α) : ϕ t '' s = ϕ (-t) ⁻¹' s
参数：t : τ；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem image_eq_preimage_symm (t : τ) (s : Set α) : ϕ t '' s = ϕ (-t) ⁻¹' s :=
  (ϕ.toHomeomorph t).toEquiv.image_eq_preimage_symm s

end AddGroup

section SubtractionCommMonoid

variable [SubtractionCommMonoid τ] [ContinuousNeg τ] (ϕ : Flow τ α)

/-- The time-reversal of a flow `ϕ` by a (commutative, additive) group
is defined `ϕ.reverse t x = ϕ (-t) x`. -/
/-
**Flow.reverse** 是 Mathlib 中的一个定义，位于命名空间 `Flow`。
形式化陈述：reverse : Flow τ α where toFun t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The time-reversal of a flow `ϕ` by a (commutative, additive) group
is defined `ϕ.reverse t x = ϕ (-t) x`.
-/
def reverse : Flow τ α where
  toFun t := ϕ (-t)
  cont' := by fun_prop
  map_add' _ _ _ := by rw [neg_add, map_add]
  map_zero' _ := by rw [neg_zero, map_zero_apply]

@[simp]
/-
**Flow.reverse_apply** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：reverse_apply (t : τ) (x : α) : ϕ.reverse t x = ϕ (-t) x
参数：t : τ；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reverse_apply (t : τ) (x : α) : ϕ.reverse t x = ϕ (-t) x := rfl

end SubtractionCommMonoid

end Flow

