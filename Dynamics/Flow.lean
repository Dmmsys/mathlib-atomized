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

/--
Definition of `IsInvariant` / `IsInvariant` 的定义

English:
definition IsInvariant
  signature: (ϕ : τ -> α -> α) (s : Set α)
  body: forall t, MapsTo (ϕ t) s s

中文:
定义 IsInvariant
  签名: (ϕ : τ -> α -> α) (s : Set α)
  定义体: forall t, MapsTo (ϕ t) s s

Depends on / 依赖: MapsTo
-/
def IsInvariant (ϕ : τ -> α -> α) (s : Set α) : Prop :=
  forall t, MapsTo (ϕ t) s s

variable (ϕ : τ -> α -> α) (s : Set α)

/--
theorem `isInvariant_iff_image` / 定理 `isInvariant_iff_image`

English:
theorem isInvariant_iff_image
  statement: IsInvariant ϕ s ↔ forall t, ϕ t '' s subseteq s
  proof: by
  simp_rw [IsInvariant, mapsTo_iff_image_subset]

中文:
定理 isInvariant_iff_image
  结论: IsInvariant ϕ s ↔ 对任意 t, ϕ t '' s subseteq s
  证明: by
  simp_rw [IsInvariant, mapsTo_iff_image_subset]

Depends on / 依赖: IsInvariant, mapsTo_iff_image_subset, simp_rw
-/
theorem isInvariant_iff_image : IsInvariant ϕ s ↔ forall t, ϕ t '' s subseteq s := by
  simp_rw [IsInvariant, mapsTo_iff_image_subset]

/--
Definition of `IsForwardInvariant` / `IsForwardInvariant` 的定义

English:
definition IsForwardInvariant
  signature: [Preorder τ] [Zero τ] (ϕ : τ -> α -> α) (s : Set α)
  body: forall ⦃t⦄, 0 <= t -> MapsTo (ϕ t) s s

中文:
定义 IsForwardInvariant
  签名: [Preorder τ] [Zero τ] (ϕ : τ -> α -> α) (s : Set α)
  定义体: forall ⦃t⦄, 0 <= t -> MapsTo (ϕ t) s s

Depends on / 依赖: MapsTo
-/
def IsForwardInvariant [Preorder τ] [Zero τ] (ϕ : τ -> α -> α) (s : Set α) : Prop :=
  forall ⦃t⦄, 0 <= t -> MapsTo (ϕ t) s s

/--
theorem `IsInvariant.isForwardInvariant` / 定理 `IsInvariant.isForwardInvariant`

English:
theorem IsInvariant.isForwardInvariant
  statement: [Preorder τ] [Zero τ] {ϕ : τ -> α -> α} {s : Set α}
  proof: fun t _ht => h t

中文:
定理 IsInvariant.isForwardInvariant
  结论: [Preorder τ] [Zero τ] {ϕ : τ -> α -> α} {s : Set α}
  证明: fun t _ht => h t
-/
theorem IsInvariant.isForwardInvariant [Preorder τ] [Zero τ] {ϕ : τ -> α -> α} {s : Set α}
    (h : IsInvariant ϕ s) : IsForwardInvariant ϕ s := fun t _ht => h t

/--
theorem `IsForwardInvariant.isInvariant` / 定理 `IsForwardInvariant.isInvariant`

English:
theorem IsForwardInvariant.isInvariant
  statement: [AddMonoid τ] [PartialOrder τ] [CanonicallyOrderedAdd τ]
  proof: fun _ => h zero_le

中文:
定理 IsForwardInvariant.isInvariant
  结论: [AddMonoid τ] [PartialOrder τ] [CanonicallyOrderedAdd τ]
  证明: fun _ => h zero_le

Depends on / 依赖: zero_le
-/
theorem IsForwardInvariant.isInvariant [AddMonoid τ] [PartialOrder τ] [CanonicallyOrderedAdd τ]
    {ϕ : τ -> α -> α} {s : Set α}
    (h : IsForwardInvariant ϕ s) : IsInvariant ϕ s := fun _ => h zero_le

/--
theorem `isForwardInvariant_iff_isInvariant` / 定理 `isForwardInvariant_iff_isInvariant`

English:
theorem isForwardInvariant_iff_isInvariant
  statement: [AddMonoid τ] [PartialOrder τ] [CanonicallyOrderedAdd τ]
  proof: ⟨IsForwardInvariant.isInvariant, IsInvariant.isForwardInvariant⟩

中文:
定理 isForwardInvariant_iff_isInvariant
  结论: [AddMonoid τ] [PartialOrder τ] [CanonicallyOrderedAdd τ]
  证明: ⟨IsForwardInvariant.isInvariant, IsInvariant.isForwardInvariant⟩

Depends on / 依赖: IsForwardInvariant, IsForwardInvariant.isInvariant, IsInvariant, IsInvariant.isForwardInvariant, isForwardInvariant, isInvariant
-/
theorem isForwardInvariant_iff_isInvariant [AddMonoid τ] [PartialOrder τ] [CanonicallyOrderedAdd τ]
    {ϕ : τ -> α -> α} {s : Set α} :
    IsForwardInvariant ϕ s ↔ IsInvariant ϕ s :=
  ⟨IsForwardInvariant.isInvariant, IsInvariant.isForwardInvariant⟩

end Invariant

/-!
### Flows
-/

variable (τ α) in
/--
Definition of `Flow` / `Flow` 的定义

English:
structure Flow
  parameters: [TopologicalSpace τ] [TopologicalSpace α] [AddZero τ]
  axioms and operations (4):
    - toFun : τ -> α -> α
    - cont' : Continuous (uncurry toFun)
    - map_add' : forall t₁ t₂ x, toFun (t₁ + t₂) x = toFun t₁ (toFun t₂ x)
    - map_zero' : forall x, toFun 0 x = x

中文:
结构 Flow
  参数: [TopologicalSpace τ] [TopologicalSpace α] [AddZero τ]
  公理与运算 (4 个):
    - toFun : τ -> α -> α
    - cont' : Continuous (uncurry toFun)
    - map_add' : 对任意 t₁ t₂ x, toFun (t₁ + t₂) x = toFun t₁ (toFun t₂ x)
    - map_zero' : 对任意 x, toFun 0 x = x
-/
structure Flow [TopologicalSpace τ] [TopologicalSpace α] [AddZero τ] where
  /-- The map `τ → α → α` underlying a flow of `τ` on `α`. -/
  toFun : τ -> α -> α
  cont' : Continuous (uncurry toFun)
  map_add' : forall t₁ t₂ x, toFun (t₁ + t₂) x = toFun t₁ (toFun t₂ x)
  map_zero' : forall x, toFun 0 x = x

namespace Flow

variable [TopologicalSpace τ] [TopologicalSpace α]

section AddZero

variable [AddZero τ] (ϕ : Flow τ α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (Flow τ α) fun _ => τ -> α -> α
  body: ⟨Flow.toFun⟩

中文:
实例 :
  签名: CoeFun (Flow τ α) fun _ => τ -> α -> α
  定义体: ⟨Flow.toFun⟩

Depends on / 依赖: Flow.toFun
-/
instance : CoeFun (Flow τ α) fun _ => τ -> α -> α := ⟨Flow.toFun⟩

variable (τ α) in
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Flow τ α where
  body: id
  cont' := continuous_snd
  map_add' _ _ _ := rfl
  map_zero' _ := rfl

@[simp]

中文:
定义 id
  签名: : Flow τ α where
  定义体: id
  cont' := continuous_snd
  map_add' _ _ _ := rfl
  map_zero' _ := rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.smulCommClass, coe_injective, smulCommClass
-/
protected def id : Flow τ α where
  toFun _ := id
  cont' := continuous_snd
  map_add' _ _ _ := rfl
  map_zero' _ := rfl

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (t : τ)
  statement: Flow.id τ α t = id
  proof: rfl

中文:
定理 id_apply
  条件: (t : τ)
  结论: Flow.id τ α t = id
  证明: rfl
-/
theorem id_apply (t : τ) : Flow.id τ α t = id := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Flow τ α)
  body: ⟨Flow.id τ α⟩

@[ext]

中文:
实例 :
  签名: Inhabited (Flow τ α)
  定义体: ⟨Flow.id τ α⟩

@[ext]

Depends on / 依赖: Flow.id
-/
instance : Inhabited (Flow τ α) :=
  ⟨Flow.id τ α⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: forall {ϕ₁ ϕ₂ : Flow τ α}, (forall t x, ϕ₁ t x = ϕ₂ t x) -> ϕ₁ = ϕ₂

中文:
定理 ext
  结论: 对任意 {ϕ₁ ϕ₂ : Flow τ α}, (对任意 t x, ϕ₁ t x = ϕ₂ t x) -> ϕ₁ = ϕ₂

Depends on / 依赖: DFunLike, DFunLike.coe_injective.mulAction, coe_injective, mulAction
-/
theorem ext : forall {ϕ₁ ϕ₂ : Flow τ α}, (forall t x, ϕ₁ t x = ϕ₂ t x) -> ϕ₁ = ϕ₂
  | ⟨f₁, _, _, _⟩, ⟨f₂, _, _, _⟩, h => by
    congr
    funext
    exact h _ _

@[continuity, fun_prop]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: {β : Type*} [TopologicalSpace β] {t : β -> τ} (ht : Continuous t)
  proof: ϕ.cont'.comp (ht.prodMk hf)

alias _root_.Continuous.flow := Flow.continuous

@[continuity, fun_prop]

中文:
定理 continuous
  结论: {β : 类型} [TopologicalSpace β] {t : β -> τ} (ht : Continuous t)
  证明: ϕ.cont'.comp (ht.prodMk hf)

alias _root_.Continuous.flow := Flow.continuous

@[continuity, fun_prop]
-/
protected theorem continuous {β : Type*} [TopologicalSpace β] {t : β -> τ} (ht : Continuous t)
    {f : β -> α} (hf : Continuous f) : Continuous fun x => ϕ (t x) (f x) :=
  ϕ.cont'.comp (ht.prodMk hf)

alias _root_.Continuous.flow := Flow.continuous

@[continuity, fun_prop]
/--
theorem `continuous_toFun` / 定理 `continuous_toFun`

English:
theorem continuous_toFun
  given: (t : τ)
  statement: Continuous (ϕ.toFun t)
  proof: by
  fun_prop

中文:
定理 continuous_toFun
  条件: (t : τ)
  结论: Continuous (ϕ.toFun t)
  证明: by
  fun_prop

Depends on / 依赖: DFunLike, DFunLike.coe_injective.smulCommClass, coe_injective, fun_prop, smulCommClass
-/
theorem continuous_toFun (t : τ) : Continuous (ϕ.toFun t) := by
  fun_prop

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (t₁ t₂ : τ) (x : α)
  statement: ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x)
  proof: ϕ.map_add' _ _ _

@[simp]

中文:
定理 map_add
  条件: (t₁ t₂ : τ) (x : α)
  结论: ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x)
  证明: ϕ.map_add' _ _ _

@[simp]

Depends on / 依赖: map_add
-/
theorem map_add (t₁ t₂ : τ) (x : α) : ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x) := ϕ.map_add' _ _ _

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: ϕ 0 = id
  proof: funext ϕ.map_zero'

中文:
定理 map_zero
  结论: ϕ 0 = id
  证明: funext ϕ.map_zero'

Depends on / 依赖: map_zero
-/
theorem map_zero : ϕ 0 = id := funext ϕ.map_zero'

/--
theorem `map_zero_apply` / 定理 `map_zero_apply`

English:
theorem map_zero_apply
  given: (x : α)
  statement: ϕ 0 x = x
  proof: ϕ.map_zero' x

中文:
定理 map_zero_apply
  条件: (x : α)
  结论: ϕ 0 x = x
  证明: ϕ.map_zero' x

Depends on / 依赖: DFunLike, DFunLike.coe_injective.mulAction, coe_injective, map_zero, mulAction
-/
theorem map_zero_apply (x : α) : ϕ 0 x = x := ϕ.map_zero' x

/--
Definition of `fromIter` / `fromIter` 的定义

English:
definition fromIter
  signature: {g : α -> α} (h : Continuous g)
  body: g^[n]
  cont' := continuous_prod_of_discrete_left.mpr h.iterate
  map_add' := iterate_add_apply _
  map_zero' _x := rfl

@[simp]

中文:
定义 fromIter
  签名: {g : α -> α} (h : Continuous g)
  定义体: g^[n]
  cont' := continuous_prod_of_discrete_left.mpr h.iterate
  map_add' := iterate_add_apply _
  map_zero' _x := rfl

@[simp]
-/
def fromIter {g : α -> α} (h : Continuous g) : Flow Nat α where
  toFun n := g^[n]
  cont' := continuous_prod_of_discrete_left.mpr h.iterate
  map_add' := iterate_add_apply _
  map_zero' _x := rfl

@[simp]
/--
theorem `fromIter_apply` / 定理 `fromIter_apply`

English:
theorem fromIter_apply
  given: {g : α -> α} (h : Continuous g) (n : Nat) (x : α)
  proof: rfl

中文:
定理 fromIter_apply
  条件: {g : α -> α} (h : Continuous g) (n : 自然数) (x : α)
  证明: rfl
-/
theorem fromIter_apply {g : α -> α} (h : Continuous g) (n : Nat) (x : α) :
    fromIter h n x = g^[n] x := rfl

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: {s : Set α} (h : IsInvariant ϕ s)
  body: (h t).restrict _ _ _
  cont' := Continuous.subtype_mk (by fun_prop) _
  map_add' _ _ _ := Subtype.ext (map_add _ _ _ _)
  map_zero' _ := Subtype.ext (map_zero_apply _ _)

@[simp]

中文:
定义 restrict
  签名: {s : Set α} (h : IsInvariant ϕ s)
  定义体: (h t).restrict _ _ _
  cont' := Continuous.subtype_mk (by fun_prop) _
  map_add' _ _ _ := Subtype.ext (map_add _ _ _ _)
  map_zero' _ := Subtype.ext (map_zero_apply _ _)

@[simp]

Depends on / 依赖: restrict
-/
def restrict {s : Set α} (h : IsInvariant ϕ s) : Flow τ s where
  toFun t := (h t).restrict _ _ _
  cont' := Continuous.subtype_mk (by fun_prop) _
  map_add' _ _ _ := Subtype.ext (map_add _ _ _ _)
  map_zero' _ := Subtype.ext (map_zero_apply _ _)

@[simp]
/--
theorem `coe_restrict_apply` / 定理 `coe_restrict_apply`

English:
theorem coe_restrict_apply
  given: {s : Set α} (h : IsInvariant ϕ s) (t : τ) (x : s)
  proof: rfl

中文:
定理 coe_restrict_apply
  条件: {s : Set α} (h : IsInvariant ϕ s) (t : τ) (x : s)
  证明: rfl
-/
theorem coe_restrict_apply {s : Set α} (h : IsInvariant ϕ s) (t : τ) (x : s) :
    restrict ϕ h t x = ϕ t x := rfl

end AddZero

section AddMonoid

variable [AddMonoid τ] (ϕ : Flow τ α)

/-- Convert a flow to an additive monoid action. -/
@[instance_reducible]
/--
Definition of `toAddAction` / `toAddAction` 的定义

English:
definition toAddAction
  signature: : AddAction τ α where
  body: ϕ
  add_vadd := ϕ.map_add'
  zero_vadd := ϕ.map_zero'

中文:
定义 toAddAction
  签名: : AddAction τ α where
  定义体: ϕ
  add_vadd := ϕ.map_add'
  zero_vadd := ϕ.map_zero'
-/
def toAddAction : AddAction τ α where
  vadd := ϕ
  add_vadd := ϕ.map_add'
  zero_vadd := ϕ.map_zero'

/--
Definition of `restrictAddSubmonoid` / `restrictAddSubmonoid` 的定义

English:
definition restrictAddSubmonoid
  signature: (S : AddSubmonoid τ)
  body: ϕ t x
  cont' := by fun_prop
  map_add' t₁ t₂ x := ϕ.map_add' t₁ t₂ x
  map_zero' := ϕ.map_zero'

中文:
定义 restrictAddSubmonoid
  签名: (S : AddSubmonoid τ)
  定义体: ϕ t x
  cont' := by fun_prop
  map_add' t₁ t₂ x := ϕ.map_add' t₁ t₂ x
  map_zero' := ϕ.map_zero'
-/
def restrictAddSubmonoid (S : AddSubmonoid τ) : Flow S α where
  toFun t x := ϕ t x
  cont' := by fun_prop
  map_add' t₁ t₂ x := ϕ.map_add' t₁ t₂ x
  map_zero' := ϕ.map_zero'

/--
theorem `restrictAddSubmonoid_apply` / 定理 `restrictAddSubmonoid_apply`

English:
theorem restrictAddSubmonoid_apply
  given: (S : AddSubmonoid τ) (t : S) (x : α)
  proof: rfl

中文:
定理 restrictAddSubmonoid_apply
  条件: (S : AddSubmonoid τ) (t : S) (x : α)
  证明: rfl
-/
theorem restrictAddSubmonoid_apply (S : AddSubmonoid τ) (t : S) (x : α) :
    restrictAddSubmonoid ϕ S t x = ϕ t x := rfl

section Orbit

/--
Definition of `orbit` / `orbit` 的定义

English:
definition orbit
  signature: (x : α)
  body: @AddAction.orbit _ _ ϕ.toAddAction.toVAdd x

中文:
定义 orbit
  签名: (x : α)
  定义体: @AddAction.orbit _ _ ϕ.toAddAction.toVAdd x

Depends on / 依赖: AddAction, AddAction.orbit, toAddAction, toAddAction.toVAdd, toVAdd
-/
def orbit (x : α) : Set α := @AddAction.orbit _ _ ϕ.toAddAction.toVAdd x

/--
theorem `orbit_eq_range` / 定理 `orbit_eq_range`

English:
theorem orbit_eq_range
  given: (x : α)
  statement: orbit ϕ x = Set.range (fun t => ϕ t x)
  proof: rfl

中文:
定理 orbit_eq_range
  条件: (x : α)
  结论: orbit ϕ x = Set.range (fun t => ϕ t x)
  证明: rfl
-/
theorem orbit_eq_range (x : α) : orbit ϕ x = Set.range (fun t => ϕ t x) := rfl

/--
theorem `mem_orbit_iff` / 定理 `mem_orbit_iff`

English:
theorem mem_orbit_iff
  given: {x₁ x₂ : α}
  statement: x₂ in orbit ϕ x₁ ↔ exists t : τ, ϕ t x₁ = x₂
  proof: Iff.rfl

中文:
定理 mem_orbit_iff
  条件: {x₁ x₂ : α}
  结论: x₂ in orbit ϕ x₁ ↔ 存在 t : τ, ϕ t x₁ = x₂
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_orbit_iff {x₁ x₂ : α} : x₂ in orbit ϕ x₁ ↔ exists t : τ, ϕ t x₁ = x₂ := Iff.rfl

/--
theorem `mem_orbit` / 定理 `mem_orbit`

English:
theorem mem_orbit
  given: (x : α) (t : τ)
  statement: ϕ t x in orbit ϕ x
  proof: @AddAction.mem_orbit _ _ ϕ.toAddAction.toVAdd x t

中文:
定理 mem_orbit
  条件: (x : α) (t : τ)
  结论: ϕ t x in orbit ϕ x
  证明: @AddAction.mem_orbit _ _ ϕ.toAddAction.toVAdd x t

Depends on / 依赖: AddAction, AddAction.mem_orbit, mem_orbit, toAddAction, toAddAction.toVAdd, toVAdd
-/
theorem mem_orbit (x : α) (t : τ) : ϕ t x in orbit ϕ x :=
  @AddAction.mem_orbit _ _ ϕ.toAddAction.toVAdd x t

/--
theorem `mem_orbit_self` / 定理 `mem_orbit_self`

English:
theorem mem_orbit_self
  given: (x : α)
  statement: x in orbit ϕ x
  proof: ϕ.toAddAction.mem_orbit_self x

中文:
定理 mem_orbit_self
  条件: (x : α)
  结论: x in orbit ϕ x
  证明: ϕ.toAddAction.mem_orbit_self x

Depends on / 依赖: mem_orbit_self, toAddAction, toAddAction.mem_orbit_self
-/
theorem mem_orbit_self (x : α) : x in orbit ϕ x := ϕ.toAddAction.mem_orbit_self x

/--
theorem `nonempty_orbit` / 定理 `nonempty_orbit`

English:
theorem nonempty_orbit
  given: (x : α)
  statement: Set.Nonempty (orbit ϕ x)
  proof: ϕ.toAddAction.nonempty_orbit x

中文:
定理 nonempty_orbit
  条件: (x : α)
  结论: Set.Nonempty (orbit ϕ x)
  证明: ϕ.toAddAction.nonempty_orbit x

Depends on / 依赖: nonempty_orbit, toAddAction, toAddAction.nonempty_orbit
-/
theorem nonempty_orbit (x : α) : Set.Nonempty (orbit ϕ x) := ϕ.toAddAction.nonempty_orbit x

/--
theorem `mem_orbit_of_mem_orbit` / 定理 `mem_orbit_of_mem_orbit`

English:
theorem mem_orbit_of_mem_orbit
  given: {x₁ x₂ : α} (t : τ) (h : x₂ in orbit ϕ x₁)
  statement: ϕ t x₂ in orbit ϕ x₁
  proof: ϕ.toAddAction.mem_orbit_of_mem_orbit t h

中文:
定理 mem_orbit_of_mem_orbit
  条件: {x₁ x₂ : α} (t : τ) (h : x₂ in orbit ϕ x₁)
  结论: ϕ t x₂ in orbit ϕ x₁
  证明: ϕ.toAddAction.mem_orbit_of_mem_orbit t h

Depends on / 依赖: mem_orbit_of_mem_orbit, toAddAction, toAddAction.mem_orbit_of_mem_orbit
-/
theorem mem_orbit_of_mem_orbit {x₁ x₂ : α} (t : τ) (h : x₂ in orbit ϕ x₁) : ϕ t x₂ in orbit ϕ x₁ :=
  ϕ.toAddAction.mem_orbit_of_mem_orbit t h

/--
theorem `isInvariant_orbit` / 定理 `isInvariant_orbit`

English:
theorem isInvariant_orbit
  given: (x : α)
  statement: IsInvariant ϕ (orbit ϕ x)
  proof: fun t _ => ϕ.toAddAction.mem_orbit_of_mem_orbit t

中文:
定理 isInvariant_orbit
  条件: (x : α)
  结论: IsInvariant ϕ (orbit ϕ x)
  证明: fun t _ => ϕ.toAddAction.mem_orbit_of_mem_orbit t

Depends on / 依赖: mem_orbit_of_mem_orbit, toAddAction, toAddAction.mem_orbit_of_mem_orbit
-/
theorem isInvariant_orbit (x : α) : IsInvariant ϕ (orbit ϕ x) :=
  fun t _ => ϕ.toAddAction.mem_orbit_of_mem_orbit t

/--
theorem `orbit_restrict` / 定理 `orbit_restrict`

English:
theorem orbit_restrict
  given: (s : Set α) (hs : IsInvariant ϕ s) (x : s)
  proof: Set.ext (fun x => by simp [orbit_eq_range, Subtype.ext_iff])

中文:
定理 orbit_restrict
  条件: (s : Set α) (hs : IsInvariant ϕ s) (x : s)
  证明: Set.ext (fun x => by simp [orbit_eq_range, Subtype.ext_iff])

Depends on / 依赖: Set.ext, Subtype, Subtype.ext_iff, ext_iff, orbit_eq_range
-/
theorem orbit_restrict (s : Set α) (hs : IsInvariant ϕ s) (x : s) :
    orbit (ϕ.restrict hs) x = Subtype.val ⁻¹' orbit ϕ x :=
  Set.ext (fun x => by simp [orbit_eq_range, Subtype.ext_iff])

variable [Preorder τ] [AddLeftMono τ]

/--
Definition of `restrictNonneg` / `restrictNonneg` 的定义

English:
definition restrictNonneg
  signature: : Flow (AddSubmonoid.nonneg τ) α
  body: ϕ.restrictAddSubmonoid (.nonneg τ)

中文:
定义 restrictNonneg
  签名: : Flow (AddSubmonoid.nonneg τ) α
  定义体: ϕ.restrictAddSubmonoid (.nonneg τ)

Depends on / 依赖: nonneg, restrictAddSubmonoid
-/
def restrictNonneg : Flow (AddSubmonoid.nonneg τ) α := ϕ.restrictAddSubmonoid (.nonneg τ)

/--
Definition of `forwardOrbit` / `forwardOrbit` 的定义

English:
definition forwardOrbit
  signature: (x : α)
  body: orbit ϕ.restrictNonneg x

中文:
定义 forwardOrbit
  签名: (x : α)
  定义体: orbit ϕ.restrictNonneg x

Depends on / 依赖: restrictNonneg
-/
def forwardOrbit (x : α) : Set α := orbit ϕ.restrictNonneg x

/--
theorem `forwardOrbit_eq_range_nonneg` / 定理 `forwardOrbit_eq_range_nonneg`

English:
theorem forwardOrbit_eq_range_nonneg
  given: (x : α)
  proof: rfl

中文:
定理 forwardOrbit_eq_range_nonneg
  条件: (x : α)
  证明: rfl
-/
theorem forwardOrbit_eq_range_nonneg (x : α) :
    forwardOrbit ϕ x = Set.range (fun t : {t : τ // 0 <= t} => ϕ t x) := rfl

/--
theorem `isForwardInvariant_forwardOrbit` / 定理 `isForwardInvariant_forwardOrbit`

English:
theorem isForwardInvariant_forwardOrbit
  given: (x : α)
  statement: IsForwardInvariant ϕ (forwardOrbit ϕ x)
  proof: fun t h => IsInvariant.isForwardInvariant (isInvariant_orbit ϕ.restrictNonneg x) (t := ⟨t, h⟩) h

中文:
定理 isForwardInvariant_forwardOrbit
  条件: (x : α)
  结论: IsForwardInvariant ϕ (forwardOrbit ϕ x)
  证明: fun t h => IsInvariant.isForwardInvariant (isInvariant_orbit ϕ.restrictNonneg x) (t := ⟨t, h⟩) h

Depends on / 依赖: IsInvariant, IsInvariant.isForwardInvariant, isForwardInvariant, isInvariant_orbit, restrictNonneg
-/
theorem isForwardInvariant_forwardOrbit (x : α) : IsForwardInvariant ϕ (forwardOrbit ϕ x) :=
  fun t h => IsInvariant.isForwardInvariant (isInvariant_orbit ϕ.restrictNonneg x) (t := ⟨t, h⟩) h

/--
theorem `forwardOrbit_subset_orbit` / 定理 `forwardOrbit_subset_orbit`

English:
theorem forwardOrbit_subset_orbit
  given: (x : α)
  statement: forwardOrbit ϕ x subseteq orbit ϕ x
  proof: ϕ.toAddAction.orbit_addSubmonoid_subset (AddSubmonoid.nonneg τ) x

中文:
定理 forwardOrbit_subset_orbit
  条件: (x : α)
  结论: forwardOrbit ϕ x subseteq orbit ϕ x
  证明: ϕ.toAddAction.orbit_addSubmonoid_subset (AddSubmonoid.nonneg τ) x

Depends on / 依赖: AddSubmonoid, AddSubmonoid.nonneg, nonneg, orbit_addSubmonoid_subset, toAddAction, toAddAction.orbit_addSubmonoid_subset
-/
theorem forwardOrbit_subset_orbit (x : α) : forwardOrbit ϕ x subseteq orbit ϕ x :=
  ϕ.toAddAction.orbit_addSubmonoid_subset (AddSubmonoid.nonneg τ) x

/--
theorem `mem_orbit_of_mem_forwardOrbit` / 定理 `mem_orbit_of_mem_forwardOrbit`

English:
theorem mem_orbit_of_mem_forwardOrbit
  given: {x₁ x₂ : α} (h : x₁ in forwardOrbit ϕ x₂)
  statement: x₁ in orbit ϕ x₂
  proof: ϕ.forwardOrbit_subset_orbit x₂ h

中文:
定理 mem_orbit_of_mem_forwardOrbit
  条件: {x₁ x₂ : α} (h : x₁ in forwardOrbit ϕ x₂)
  结论: x₁ in orbit ϕ x₂
  证明: ϕ.forwardOrbit_subset_orbit x₂ h

Depends on / 依赖: forwardOrbit_subset_orbit
-/
theorem mem_orbit_of_mem_forwardOrbit {x₁ x₂ : α} (h : x₁ in forwardOrbit ϕ x₂) : x₁ in orbit ϕ x₂ :=
  ϕ.forwardOrbit_subset_orbit x₂ h

end Orbit

variable {β γ : Type*} [TopologicalSpace β] [TopologicalSpace γ] (ψ : Flow τ β) (χ : Flow τ γ)

/--
Definition of `IsSemiconjugacy` / `IsSemiconjugacy` 的定义

English:
structure IsSemiconjugacy
  parameters: (π : α -> β) (ϕ : Flow τ α) (ψ : Flow τ β)
  axioms and operations (3):
    - cont : Continuous π
    - surj : Function.Surjective π
    - semiconj : forall t, Function.Semiconj π (ϕ t) (ψ t)

中文:
结构 IsSemiconjugacy
  参数: (π : α -> β) (ϕ : Flow τ α) (ψ : Flow τ β)
  公理与运算 (3 个):
    - cont : Continuous π
    - surj : Function.Surjective π
    - semiconj : 对任意 t, Function.Semiconj π (ϕ t) (ψ t)
-/
structure IsSemiconjugacy (π : α -> β) (ϕ : Flow τ α) (ψ : Flow τ β) : Prop where
  cont : Continuous π
  surj : Function.Surjective π
  semiconj : forall t, Function.Semiconj π (ϕ t) (ψ t)

/--
theorem `IsSemiconjugacy.comp` / 定理 `IsSemiconjugacy.comp`

English:
theorem IsSemiconjugacy.comp
  statement: {π : α -> β} {ρ : β -> γ}
  proof: ⟨h₂.cont.comp h₁.cont, h₂.surj.comp h₁.surj, fun t => (h₂.semiconj t).comp_left (h₁.semiconj t)⟩

中文:
定理 IsSemiconjugacy.comp
  结论: {π : α -> β} {ρ : β -> γ}
  证明: ⟨h₂.cont.comp h₁.cont, h₂.surj.comp h₁.surj, fun t => (h₂.semiconj t).comp_left (h₁.semiconj t)⟩

Depends on / 依赖: comp_left, cont.comp, semiconj, surj.comp
-/
theorem IsSemiconjugacy.comp {π : α -> β} {ρ : β -> γ}
    (h₁ : IsSemiconjugacy π ϕ ψ) (h₂ : IsSemiconjugacy ρ ψ χ) : IsSemiconjugacy (ρ ∘ π) ϕ χ :=
  ⟨h₂.cont.comp h₁.cont, h₂.surj.comp h₁.surj, fun t => (h₂.semiconj t).comp_left (h₁.semiconj t)⟩

/--
theorem `isSemiconjugacy_id_iff_eq` / 定理 `isSemiconjugacy_id_iff_eq`

English:
theorem isSemiconjugacy_id_iff_eq
  given: (ϕ ψ : Flow τ α)
  statement: IsSemiconjugacy id ϕ ψ ↔ ϕ = ψ
  proof: ⟨fun h => ext h.semiconj, fun h => h.recOn ⟨continuous_id, surjective_id, fun _ => .id_left⟩⟩

中文:
定理 isSemiconjugacy_id_iff_eq
  条件: (ϕ ψ : Flow τ α)
  结论: IsSemiconjugacy id ϕ ψ ↔ ϕ = ψ
  证明: ⟨fun h => ext h.semiconj, fun h => h.recOn ⟨continuous_id, surjective_id, fun _ => .id_left⟩⟩

Depends on / 依赖: continuous_id, h.recOn, h.semiconj, id_left, semiconj, surjective_id
-/
theorem isSemiconjugacy_id_iff_eq (ϕ ψ : Flow τ α) : IsSemiconjugacy id ϕ ψ ↔ ϕ = ψ :=
  ⟨fun h => ext h.semiconj, fun h => h.recOn ⟨continuous_id, surjective_id, fun _ => .id_left⟩⟩

/--
Definition of `IsFactorOf` / `IsFactorOf` 的定义

English:
definition IsFactorOf
  signature: (ψ : Flow τ β) (ϕ : Flow τ α)
  body: exists π : α -> β, IsSemiconjugacy π ϕ ψ

中文:
定义 IsFactorOf
  签名: (ψ : Flow τ β) (ϕ : Flow τ α)
  定义体: exists π : α -> β, IsSemiconjugacy π ϕ ψ

Depends on / 依赖: IsSemiconjugacy
-/
def IsFactorOf (ψ : Flow τ β) (ϕ : Flow τ α) : Prop := exists π : α -> β, IsSemiconjugacy π ϕ ψ

/--
theorem `IsSemiconjugacy.isFactorOf` / 定理 `IsSemiconjugacy.isFactorOf`

English:
theorem IsSemiconjugacy.isFactorOf
  given: {π : α -> β} (h : IsSemiconjugacy π ϕ ψ)
  statement: IsFactorOf ψ ϕ
  proof: ⟨π, h⟩

中文:
定理 IsSemiconjugacy.isFactorOf
  条件: {π : α -> β} (h : IsSemiconjugacy π ϕ ψ)
  结论: IsFactorOf ψ ϕ
  证明: ⟨π, h⟩
-/
theorem IsSemiconjugacy.isFactorOf {π : α -> β} (h : IsSemiconjugacy π ϕ ψ) : IsFactorOf ψ ϕ :=
  ⟨π, h⟩

/--
theorem `IsFactorOf.trans` / 定理 `IsFactorOf.trans`

English:
theorem IsFactorOf.trans
  given: (h₁ : IsFactorOf ϕ ψ) (h₂ : IsFactorOf ψ χ)
  statement: IsFactorOf ϕ χ
  proof: h₁.elim fun π hπ => h₂.elim fun ρ hρ => ⟨π ∘ ρ, hρ.comp χ ψ ϕ hπ⟩

中文:
定理 IsFactorOf.trans
  条件: (h₁ : IsFactorOf ϕ ψ) (h₂ : IsFactorOf ψ χ)
  结论: IsFactorOf ϕ χ
  证明: h₁.elim fun π hπ => h₂.elim fun ρ hρ => ⟨π ∘ ρ, hρ.comp χ ψ ϕ hπ⟩
-/
theorem IsFactorOf.trans (h₁ : IsFactorOf ϕ ψ) (h₂ : IsFactorOf ψ χ) : IsFactorOf ϕ χ :=
  h₁.elim fun π hπ => h₂.elim fun ρ hρ => ⟨π ∘ ρ, hρ.comp χ ψ ϕ hπ⟩

/--
theorem `IsFactorOf.self` / 定理 `IsFactorOf.self`

English:
theorem IsFactorOf.self
  statement: IsFactorOf ϕ ϕ
  proof: ⟨id, (isSemiconjugacy_id_iff_eq ϕ ϕ).mpr rfl⟩

中文:
定理 IsFactorOf.self
  结论: IsFactorOf ϕ ϕ
  证明: ⟨id, (isSemiconjugacy_id_iff_eq ϕ ϕ).mpr rfl⟩

Depends on / 依赖: isSemiconjugacy_id_iff_eq
-/
theorem IsFactorOf.self : IsFactorOf ϕ ϕ := ⟨id, (isSemiconjugacy_id_iff_eq ϕ ϕ).mpr rfl⟩

end AddMonoid

section AddGroup

variable [AddGroup τ] (ϕ : Flow τ α)

/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
definition toHomeomorph
  signature: (t : τ)
  body: ϕ t
  invFun := ϕ (-t)
  left_inv x := by simp [← map_add]
  right_inv x := by simp [← map_add]

@[simp]

中文:
定义 toHomeomorph
  签名: (t : τ)
  定义体: ϕ t
  invFun := ϕ (-t)
  left_inv x := by simp [← map_add]
  right_inv x := by simp [← map_add]

@[simp]
-/
def toHomeomorph (t : τ) : (α ≃ₜ α) where
  toFun := ϕ t
  invFun := ϕ (-t)
  left_inv x := by simp [← map_add]
  right_inv x := by simp [← map_add]

@[simp]
/--
theorem `toHomeomorph_apply` / 定理 `toHomeomorph_apply`

English:
theorem toHomeomorph_apply
  given: (t : τ) (x : α)
  statement: ϕ.toHomeomorph t x = ϕ t x
  proof: rfl

@[simp]

中文:
定理 toHomeomorph_apply
  条件: (t : τ) (x : α)
  结论: ϕ.toHomeomorph t x = ϕ t x
  证明: rfl

@[simp]
-/
theorem toHomeomorph_apply (t : τ) (x : α) : ϕ.toHomeomorph t x = ϕ t x := rfl

@[simp]
/--
theorem `toHomeomorph_symm_apply` / 定理 `toHomeomorph_symm_apply`

English:
theorem toHomeomorph_symm_apply
  given: (t : τ) (x : α)
  statement: (ϕ.toHomeomorph t).symm x = ϕ (-t) x
  proof: rfl

中文:
定理 toHomeomorph_symm_apply
  条件: (t : τ) (x : α)
  结论: (ϕ.toHomeomorph t).symm x = ϕ (-t) x
  证明: rfl
-/
theorem toHomeomorph_symm_apply (t : τ) (x : α) : (ϕ.toHomeomorph t).symm x = ϕ (-t) x := rfl

/--
theorem `isInvariant_iff_image_eq` / 定理 `isInvariant_iff_image_eq`

English:
theorem isInvariant_iff_image_eq
  given: (s : Set α)
  statement: IsInvariant ϕ s ↔ forall t, ϕ t '' s = s
  proof: (isInvariant_iff_image _ _).trans
    (Iff.intro
      (fun h t => Subset.antisymm (h t) fun _ hx => ⟨_, h (-t) ⟨_, hx, rfl⟩, by simp [← map_add]⟩)
      fun h t => by rw [h t])

中文:
定理 isInvariant_iff_image_eq
  条件: (s : Set α)
  结论: IsInvariant ϕ s ↔ 对任意 t, ϕ t '' s = s
  证明: (isInvariant_iff_image _ _).trans
    (Iff.intro
      (fun h t => Subset.antisymm (h t) fun _ hx => ⟨_, h (-t) ⟨_, hx, rfl⟩, by simp [← map_add]⟩)
      fun h t => by rw [h t])

Depends on / 依赖: Iff.intro, Subset, Subset.antisymm, antisymm, isInvariant_iff_image, map_add
-/
theorem isInvariant_iff_image_eq (s : Set α) : IsInvariant ϕ s ↔ forall t, ϕ t '' s = s :=
  (isInvariant_iff_image _ _).trans
    (Iff.intro
      (fun h t => Subset.antisymm (h t) fun _ hx => ⟨_, h (-t) ⟨_, hx, rfl⟩, by simp [← map_add]⟩)
      fun h t => by rw [h t])

/--
theorem `image_eq_preimage_symm` / 定理 `image_eq_preimage_symm`

English:
theorem image_eq_preimage_symm
  given: (t : τ) (s : Set α)
  statement: ϕ t '' s = ϕ (-t) ⁻¹' s
  proof: (ϕ.toHomeomorph t).toEquiv.image_eq_preimage_symm s

中文:
定理 image_eq_preimage_symm
  条件: (t : τ) (s : Set α)
  结论: ϕ t '' s = ϕ (-t) ⁻¹' s
  证明: (ϕ.toHomeomorph t).toEquiv.image_eq_preimage_symm s

Depends on / 依赖: image_eq_preimage_symm, toEquiv, toEquiv.image_eq_preimage_symm, toHomeomorph
-/
theorem image_eq_preimage_symm (t : τ) (s : Set α) : ϕ t '' s = ϕ (-t) ⁻¹' s :=
  (ϕ.toHomeomorph t).toEquiv.image_eq_preimage_symm s

end AddGroup

section SubtractionCommMonoid

variable [SubtractionCommMonoid τ] [ContinuousNeg τ] (ϕ : Flow τ α)

/--
Definition of `reverse` / `reverse` 的定义

English:
definition reverse
  signature: : Flow τ α where
  body: ϕ (-t)
  cont' := by fun_prop
  map_add' _ _ _ := by rw [neg_add, map_add]
  map_zero' _ := by rw [neg_zero, map_zero_apply]

@[simp]

中文:
定义 reverse
  签名: : Flow τ α where
  定义体: ϕ (-t)
  cont' := by fun_prop
  map_add' _ _ _ := by rw [neg_add, map_add]
  map_zero' _ := by rw [neg_zero, map_zero_apply]

@[simp]
-/
def reverse : Flow τ α where
  toFun t := ϕ (-t)
  cont' := by fun_prop
  map_add' _ _ _ := by rw [neg_add, map_add]
  map_zero' _ := by rw [neg_zero, map_zero_apply]

@[simp]
/--
theorem `reverse_apply` / 定理 `reverse_apply`

English:
theorem reverse_apply
  given: (t : τ) (x : α)
  statement: ϕ.reverse t x = ϕ (-t) x
  proof: rfl

中文:
定理 reverse_apply
  条件: (t : τ) (x : α)
  结论: ϕ.reverse t x = ϕ (-t) x
  证明: rfl
-/
theorem reverse_apply (t : τ) (x : α) : ϕ.reverse t x = ϕ (-t) x := rfl

end SubtractionCommMonoid

end Flow
