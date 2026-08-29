/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Nontrivial.Basic
public import Mathlib.Order.TypeTags
public import Mathlib.Data.Option.NAry
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Lift
public import Mathlib.Data.Option.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.BoundedOrder.Basic

/-!
# `WithBot`, `WithTop`

Adding a `bot` or a `top` to an order.

## Main declarations

* `With<Top/Bot> α`: Equips `Option α` with the order on `α` plus `none` as the top/bottom element.

-/

@[expose] public section

variable {α β γ δ : Type*}

namespace WithBot

variable {a b : α}

@[to_dual]
/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: [Nonempty α]
  body: inferInstanceAs Nontrivial (Option α)

@[to_dual]

中文:
实例 nontrivial
  签名: [非空 α]
  定义体: inferInstanceAs Nontrivial (Option α)

@[to_dual]

Depends on / 依赖: Nontrivial
-/
instance nontrivial [Nonempty α] : Nontrivial (WithBot α) :=
inferInstanceAs Nontrivial (Option α)

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Unique (WithBot α)
  body: inferInstanceAs Unique (Option α)

中文:
实例 [是空
  签名: α] : 唯一 (WithBot α)
  定义体: inferInstanceAs Unique (Option α)

Depends on / 依赖: Unique
-/
instance [IsEmpty α] : Unique (WithBot α) :=
inferInstanceAs Unique (Option α)

open Function

@[to_dual]
/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective ((↑) : α -> WithBot α)
  proof: Option.some_injective _

@[to_dual (attr := simp, norm_cast)]

中文:
定理 coe_injective
  结论: 单射 ((↑) : α -> WithBot α)
  证明: Option.some_injective _

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: Option.some_injective, some_injective
-/
theorem coe_injective : Injective ((↑) : α -> WithBot α) :=
  Option.some_injective _

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  statement: (a : WithBot α) = b ↔ a = b
  proof: Option.some_inj

@[to_dual]

中文:
定理 coe_inj
  结论: (a : WithBot α) = b ↔ a = b
  证明: Option.some_inj

@[to_dual]

Depends on / 依赖: Option.some_inj, some_inj
-/
theorem coe_inj : (a : WithBot α) = b ↔ a = b :=
  Option.some_inj

@[to_dual]
/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : WithBot α -> Prop}
  statement: (forall x, p x) ↔ p ⊥ ∧ forall x : α, p x
  proof: Option.forall

@[to_dual]

中文:
定理 «对任意»
  条件: {p : WithBot α -> 命题}
  结论: (对任意 x, p x) ↔ p ⊥ ∧ 对任意 x : α, p x
  证明: Option.forall

@[to_dual]
-/
protected theorem «forall» {p : WithBot α -> Prop} : (forall x, p x) ↔ p ⊥ ∧ forall x : α, p x :=
  Option.forall

@[to_dual]
/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {p : WithBot α -> Prop}
  statement: (exists x, p x) ↔ p ⊥ ∨ exists x : α, p x
  proof: Option.exists

@[to_dual]

中文:
定理 «存在»
  条件: {p : WithBot α -> 命题}
  结论: (存在 x, p x) ↔ p ⊥ ∨ 存在 x : α, p x
  证明: Option.exists

@[to_dual]
-/
protected theorem «exists» {p : WithBot α -> Prop} : (exists x, p x) ↔ p ⊥ ∨ exists x : α, p x :=
  Option.exists

@[to_dual]
/--
theorem `none_eq_bot` / 定理 `none_eq_bot`

English:
theorem none_eq_bot
  statement: (none : WithBot α) = (⊥ : WithBot α)
  proof: rfl

@[to_dual]

中文:
定理 none_eq_bot
  结论: (none : WithBot α) = (⊥ : WithBot α)
  证明: rfl

@[to_dual]
-/
theorem none_eq_bot : (none : WithBot α) = (⊥ : WithBot α) :=
  rfl

@[to_dual]
/--
theorem `some_eq_coe` / 定理 `some_eq_coe`

English:
theorem some_eq_coe
  given: (a : α)
  statement: (Option.some a : WithBot α) = (↑a : WithBot α)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 some_eq_coe
  条件: (a : α)
  结论: (选项类型.some a : WithBot α) = (↑a : WithBot α)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem some_eq_coe (a : α) : (Option.some a : WithBot α) = (↑a : WithBot α) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `bot_ne_coe` / 定理 `bot_ne_coe`

English:
theorem bot_ne_coe
  statement: ⊥ != (a : WithBot α)
  proof: nofun

@[to_dual (attr := simp)]

中文:
定理 bot_ne_coe
  结论: ⊥ != (a : WithBot α)
  证明: nofun

@[to_dual (attr := simp)]
-/
theorem bot_ne_coe : ⊥ != (a : WithBot α) :=
  nofun

@[to_dual (attr := simp)]
/--
theorem `coe_ne_bot` / 定理 `coe_ne_bot`

English:
theorem coe_ne_bot
  statement: (a : WithBot α) != ⊥
  proof: nofun

中文:
定理 coe_ne_bot
  结论: (a : WithBot α) != ⊥
  证明: nofun
-/
theorem coe_ne_bot : (a : WithBot α) != ⊥ :=
  nofun

/-- Specialization of `Option.getD` to values in `WithBot α` that respects API boundaries. -/
@[to_dual
/-- Specialization of `Option.getD` to values in `WithTop α` that respects API boundaries. -/]
/--
Definition of `unbotD` / `unbotD` 的定义

English:
definition unbotD
  signature: (d : α) (x : WithBot α)
  body: recBotCoe d id x

@[to_dual (attr := simp)]

中文:
定义 unbotD
  签名: (d : α) (x : WithBot α)
  定义体: recBotCoe d id x

@[to_dual (attr := simp)]

Depends on / 依赖: recBotCoe
-/
def unbotD (d : α) (x : WithBot α) : α :=
  recBotCoe d id x

@[to_dual (attr := simp)]
/--
theorem `unbotD_bot` / 定理 `unbotD_bot`

English:
theorem unbotD_bot
  given: {α} (d : α)
  statement: unbotD d ⊥ = d
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 unbotD_bot
  条件: {α} (d : α)
  结论: unbotD d ⊥ = d
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem unbotD_bot {α} (d : α) : unbotD d ⊥ = d :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `unbotD_coe` / 定理 `unbotD_coe`

English:
theorem unbotD_coe
  given: {α} (d x : α)
  statement: unbotD d x = x
  proof: rfl

@[to_dual]

中文:
定理 unbotD_coe
  条件: {α} (d x : α)
  结论: unbotD d x = x
  证明: rfl

@[to_dual]
-/
theorem unbotD_coe {α} (d x : α) : unbotD d x = x :=
  rfl

@[to_dual]
/--
theorem `coe_eq_coe` / 定理 `coe_eq_coe`

English:
theorem coe_eq_coe
  statement: (a : WithBot α) = b ↔ a = b
  proof: coe_inj

@[to_dual]

中文:
定理 coe_eq_coe
  结论: (a : WithBot α) = b ↔ a = b
  证明: coe_inj

@[to_dual]

Depends on / 依赖: Algebra, Algebra.TensorProduct.map, AlgebraicClosure, IsAlgClosed, IsAlgClosed.lift, Module, Module.Flat.rTensor_preserves_injective_linearMap, RingHom, RingHom.injective, TensorProduct, coe_inj, injective, isGeometricallyReduced_field_iff, isReduced_of_injective, rTensor_preserves_injective_linearMap
-/
theorem coe_eq_coe : (a : WithBot α) = b ↔ a = b := coe_inj

@[to_dual]
/--
theorem `unbotD_eq_iff` / 定理 `unbotD_eq_iff`

English:
theorem unbotD_eq_iff
  given: {d y : α} {x : WithBot α}
  statement: unbotD d x = y ↔ x = y ∨ x = ⊥ ∧ y = d
  proof: by
  induction x <;> simp [@eq_comm _ d]

@[to_dual (attr := simp)]

中文:
定理 unbotD_eq_iff
  条件: {d y : α} {x : WithBot α}
  结论: unbotD d x = y ↔ x = y ∨ x = ⊥ ∧ y = d
  证明: by
  induction x <;> simp [@eq_comm _ d]

@[to_dual (attr := simp)]

Depends on / 依赖: eq_comm
-/
theorem unbotD_eq_iff {d y : α} {x : WithBot α} : unbotD d x = y ↔ x = y ∨ x = ⊥ ∧ y = d := by
  induction x <;> simp [@eq_comm _ d]

@[to_dual (attr := simp)]
/--
theorem `unbotD_eq_self_iff` / 定理 `unbotD_eq_self_iff`

English:
theorem unbotD_eq_self_iff
  given: {d : α} {x : WithBot α}
  statement: unbotD d x = d ↔ x = d ∨ x = ⊥
  proof: by
  simp [unbotD_eq_iff]

@[to_dual]

中文:
定理 unbotD_eq_self_iff
  条件: {d : α} {x : WithBot α}
  结论: unbotD d x = d ↔ x = d ∨ x = ⊥
  证明: by
  simp [unbotD_eq_iff]

@[to_dual]

Depends on / 依赖: unbotD_eq_iff
-/
theorem unbotD_eq_self_iff {d : α} {x : WithBot α} : unbotD d x = d ↔ x = d ∨ x = ⊥ := by
  simp [unbotD_eq_iff]

@[to_dual]
/--
theorem `unbotD_eq_unbotD_iff` / 定理 `unbotD_eq_unbotD_iff`

English:
theorem unbotD_eq_unbotD_iff
  given: {d : α} {x y : WithBot α}
  proof: by
  induction y <;> simp [unbotD_eq_iff, or_comm]

中文:
定理 unbotD_eq_unbotD_iff
  条件: {d : α} {x y : WithBot α}
  证明: by
  induction y <;> simp [unbotD_eq_iff, or_comm]

Depends on / 依赖: or_comm, unbotD_eq_iff
-/
theorem unbotD_eq_unbotD_iff {d : α} {x y : WithBot α} :
    unbotD d x = unbotD d y ↔ x = y ∨ x = d ∧ y = ⊥ ∨ x = ⊥ ∧ y = d := by
  induction y <;> simp [unbotD_eq_iff, or_comm]

/-- Lift a map `f : α → β` to `WithBot α → WithBot β`. Implemented using `Option.map`. -/
@[to_dual
/-- Lift a map `f : α → β` to `WithTop α → WithTop β`. Implemented using `Option.map`. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)
  body: Option.map f

@[to_dual (attr := simp)]

中文:
定义 map
  签名: (f : α -> β)
  定义体: Option.map f

@[to_dual (attr := simp)]

Depends on / 依赖: Option.map
-/
def map (f : α -> β) : WithBot α -> WithBot β :=
  Option.map f

@[to_dual (attr := simp)]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : α -> β)
  statement: map f ⊥ = ⊥
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 map_bot
  条件: (f : α -> β)
  结论: map f ⊥ = ⊥
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem map_bot (f : α -> β) : map f ⊥ = ⊥ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `map_coe` / 定理 `map_coe`

English:
theorem map_coe
  given: (f : α -> β) (a : α)
  statement: map f a = f a
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 map_coe
  条件: (f : α -> β) (a : α)
  结论: map f a = f a
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem map_coe (f : α -> β) (a : α) : map f a = f a :=
  rfl

@[to_dual (attr := simp)]
/--
lemma `map_eq_bot_iff` / 引理 `map_eq_bot_iff`

English:
lemma map_eq_bot_iff
  given: {f : α -> β} {a : WithBot α}
  proof: Option.map_eq_none_iff

@[to_dual]

中文:
引理 map_eq_bot_iff
  条件: {f : α -> β} {a : WithBot α}
  证明: Option.map_eq_none_iff

@[to_dual]

Depends on / 依赖: Option.map_eq_none_iff, map_eq_none_iff
-/
lemma map_eq_bot_iff {f : α -> β} {a : WithBot α} :
    map f a = ⊥ ↔ a = ⊥ := Option.map_eq_none_iff

@[to_dual]
/--
theorem `map_eq_some_iff` / 定理 `map_eq_some_iff`

English:
theorem map_eq_some_iff
  given: {f : α -> β} {y : β} {v : WithBot α}
  proof: Option.map_eq_some_iff

@[to_dual]

中文:
定理 map_eq_some_iff
  条件: {f : α -> β} {y : β} {v : WithBot α}
  证明: Option.map_eq_some_iff

@[to_dual]

Depends on / 依赖: Option.map_eq_some_iff, map_eq_some_iff
-/
theorem map_eq_some_iff {f : α -> β} {y : β} {v : WithBot α} :
    WithBot.map f v = .some y ↔ exists x, v = .some x ∧ f x = y := Option.map_eq_some_iff

@[to_dual]
/--
theorem `some_eq_map_iff` / 定理 `some_eq_map_iff`

English:
theorem some_eq_map_iff
  given: {f : α -> β} {y : β} {v : WithBot α}
  proof: by
  cases v <;> simp [eq_comm]

@[to_dual (attr := simp)]

中文:
定理 some_eq_map_iff
  条件: {f : α -> β} {y : β} {v : WithBot α}
  证明: by
  cases v <;> simp [eq_comm]

@[to_dual (attr := simp)]

Depends on / 依赖: eq_comm
-/
theorem some_eq_map_iff {f : α -> β} {y : β} {v : WithBot α} :
    .some y = WithBot.map f v ↔ exists x, v = .some x ∧ f x = y := by
  cases v <;> simp [eq_comm]

@[to_dual (attr := simp)]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (id : α -> α) = id
  proof: Option.map_id

@[to_dual (attr := simp)]

中文:
定理 map_id
  结论: map (id : α -> α) = id
  证明: Option.map_id

@[to_dual (attr := simp)]

Depends on / 依赖: Option.map_id, map_id
-/
theorem map_id : map (id : α -> α) = id :=
  Option.map_id

@[to_dual (attr := simp)]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (h : β -> γ) (g : α -> β) (a : WithBot α)
  statement: map h (map g a) = map (h ∘ g) a
  proof: Option.map_map h g a

@[to_dual]

中文:
定理 map_map
  条件: (h : β -> γ) (g : α -> β) (a : WithBot α)
  结论: map h (map g a) = map (h ∘ g) a
  证明: Option.map_map h g a

@[to_dual]

Depends on / 依赖: Option.map_map, map_map
-/
theorem map_map (h : β -> γ) (g : α -> β) (a : WithBot α) : map h (map g a) = map (h ∘ g) a :=
  Option.map_map h g a

@[to_dual]
/--
theorem `comp_map` / 定理 `comp_map`

English:
theorem comp_map
  given: (h : β -> γ) (g : α -> β) (x : WithBot α)
  statement: x.map (h ∘ g) = (x.map g).map h
  proof: (map_map ..).symm

@[to_dual (attr := simp)]

中文:
定理 comp_map
  条件: (h : β -> γ) (g : α -> β) (x : WithBot α)
  结论: x.map (h ∘ g) = (x.map g).map h
  证明: (map_map ..).symm

@[to_dual (attr := simp)]

Depends on / 依赖: map_map
-/
theorem comp_map (h : β -> γ) (g : α -> β) (x : WithBot α) : x.map (h ∘ g) = (x.map g).map h :=
  (map_map ..).symm

@[to_dual (attr := simp)]
/--
theorem `map_comp_map` / 定理 `map_comp_map`

English:
theorem map_comp_map
  given: (f : α -> β) (g : β -> γ)
  proof: Option.map_comp_map f g

@[to_dual]

中文:
定理 map_comp_map
  条件: (f : α -> β) (g : β -> γ)
  证明: Option.map_comp_map f g

@[to_dual]

Depends on / 依赖: Option.map_comp_map, map_comp_map
-/
theorem map_comp_map (f : α -> β) (g : β -> γ) :
    WithBot.map g ∘ WithBot.map f = WithBot.map (g ∘ f) :=
  Option.map_comp_map f g

@[to_dual]
/--
theorem `map_comm` / 定理 `map_comm`

English:
theorem map_comm
  statement: {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ}
  proof: Option.map_comm h _

@[to_dual]

中文:
定理 map_comm
  结论: {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ}
  证明: Option.map_comm h _

@[to_dual]

Depends on / 依赖: Option.map_comm, map_comm
-/
theorem map_comm {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ}
    (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
    map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _

@[to_dual]
/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : α -> β} (Hf : Injective f)
  statement: Injective (WithBot.map f)
  proof: Option.map_injective Hf

中文:
定理 map_injective
  条件: {f : α -> β} (Hf : 单射 f)
  结论: 单射 (WithBot.map f)
  证明: Option.map_injective Hf

Depends on / 依赖: Option.map_injective, map_injective
-/
theorem map_injective {f : α -> β} (Hf : Injective f) : Injective (WithBot.map f) :=
  Option.map_injective Hf

/-- The image of a binary function `f : α → β → γ` as a function
`WithBot α → WithBot β → WithBot γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
@[to_dual
/-- The image of a binary function `f : α → β → γ` as a function
`WithTop α → WithTop β → WithTop γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/]
/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: : (α -> β -> γ) -> WithBot α -> WithBot β -> WithBot γ
  body: Option.map₂

中文:
定义 map₂
  签名: : (α -> β -> γ) -> WithBot α -> WithBot β -> WithBot γ
  定义体: Option.map₂

Depends on / 依赖: Option.map
-/
def map₂ : (α -> β -> γ) -> WithBot α -> WithBot β -> WithBot γ := Option.map₂

/--
lemma `map₂_coe_coe` / 引理 `map₂_coe_coe`

English:
lemma map₂_coe_coe
  given: (f : α -> β -> γ) (a : α) (b : β)
  statement: map₂ f a b = f a b
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 map₂_coe_coe
  条件: (f : α -> β -> γ) (a : α) (b : β)
  结论: map₂ f a b = f a b
  证明: rfl

@[to_dual (attr := simp)]
-/
@[to_dual] lemma map₂_coe_coe (f : α -> β -> γ) (a : α) (b : β) : map₂ f a b = f a b := rfl

@[to_dual (attr := simp)]
/--
lemma `map₂_bot_left` / 引理 `map₂_bot_left`

English:
lemma map₂_bot_left
  given: (f : α -> β -> γ) (b)
  statement: map₂ f ⊥ b = ⊥
  proof: rfl
@[to_dual (attr := simp)]

中文:
引理 map₂_bot_left
  条件: (f : α -> β -> γ) (b)
  结论: map₂ f ⊥ b = ⊥
  证明: rfl
@[to_dual (attr := simp)]
-/
lemma map₂_bot_left (f : α -> β -> γ) (b) : map₂ f ⊥ b = ⊥ := rfl
@[to_dual (attr := simp)]
/--
lemma `map₂_bot_right` / 引理 `map₂_bot_right`

English:
lemma map₂_bot_right
  given: (f : α -> β -> γ) (a)
  statement: map₂ f a ⊥ = ⊥
  proof: by cases a <;> rfl

@[to_dual (attr := simp)]

中文:
引理 map₂_bot_right
  条件: (f : α -> β -> γ) (a)
  结论: map₂ f a ⊥ = ⊥
  证明: by cases a <;> rfl

@[to_dual (attr := simp)]
-/
lemma map₂_bot_right (f : α -> β -> γ) (a) : map₂ f a ⊥ = ⊥ := by cases a <;> rfl

@[to_dual (attr := simp)]
/--
lemma `map₂_coe_left` / 引理 `map₂_coe_left`

English:
lemma map₂_coe_left
  given: (f : α -> β -> γ) (a : α) (b)
  statement: map₂ f a b = b.map fun b => f a b
  proof: rfl
@[to_dual (attr := simp)]

中文:
引理 map₂_coe_left
  条件: (f : α -> β -> γ) (a : α) (b)
  结论: map₂ f a b = b.map fun b => f a b
  证明: rfl
@[to_dual (attr := simp)]
-/
lemma map₂_coe_left (f : α -> β -> γ) (a : α) (b) : map₂ f a b = b.map fun b => f a b := rfl
@[to_dual (attr := simp)]
/--
lemma `map₂_coe_right` / 引理 `map₂_coe_right`

English:
lemma map₂_coe_right
  given: (f : α -> β -> γ) (a) (b : β)
  statement: map₂ f a b = a.map (f · b)
  proof: by cases a <;> rfl

@[to_dual (attr := simp)]

中文:
引理 map₂_coe_right
  条件: (f : α -> β -> γ) (a) (b : β)
  结论: map₂ f a b = a.map (f · b)
  证明: by cases a <;> rfl

@[to_dual (attr := simp)]
-/
lemma map₂_coe_right (f : α -> β -> γ) (a) (b : β) : map₂ f a b = a.map (f · b) := by cases a <;> rfl

@[to_dual (attr := simp)]
/--
lemma `map₂_eq_bot_iff` / 引理 `map₂_eq_bot_iff`

English:
lemma map₂_eq_bot_iff
  given: {f : α -> β -> γ} {a : WithBot α} {b : WithBot β}
  proof: Option.map₂_eq_none_iff

@[to_dual]

中文:
引理 map₂_eq_bot_iff
  条件: {f : α -> β -> γ} {a : WithBot α} {b : WithBot β}
  证明: Option.map₂_eq_none_iff

@[to_dual]

Depends on / 依赖: Option.map
-/
lemma map₂_eq_bot_iff {f : α -> β -> γ} {a : WithBot α} {b : WithBot β} :
    map₂ f a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := Option.map₂_eq_none_iff

@[to_dual]
/--
lemma `ne_bot_iff_exists` / 引理 `ne_bot_iff_exists`

English:
lemma ne_bot_iff_exists
  given: {x : WithBot α}
  statement: x != ⊥ ↔ exists a : α, ↑a = x
  proof: Option.ne_none_iff_exists

@[to_dual]

中文:
引理 ne_bot_iff_存在
  条件: {x : WithBot α}
  结论: x != ⊥ ↔ 存在 a : α, ↑a = x
  证明: Option.ne_none_iff_exists

@[to_dual]

Depends on / 依赖: Option.ne_none_iff_exists, ne_none_iff_exists
-/
lemma ne_bot_iff_exists {x : WithBot α} : x != ⊥ ↔ exists a : α, ↑a = x := Option.ne_none_iff_exists

@[to_dual]
/--
lemma `eq_bot_iff_forall_ne` / 引理 `eq_bot_iff_forall_ne`

English:
lemma eq_bot_iff_forall_ne
  given: {x : WithBot α}
  statement: x = ⊥ ↔ forall a : α, ↑a != x
  proof: Option.eq_none_iff_forall_some_ne

@[to_dual]

中文:
引理 eq_bot_iff_对任意_ne
  条件: {x : WithBot α}
  结论: x = ⊥ ↔ 对任意 a : α, ↑a != x
  证明: Option.eq_none_iff_forall_some_ne

@[to_dual]

Depends on / 依赖: Option.eq_none_iff_forall_some_ne, eq_none_iff_forall_some_ne
-/
lemma eq_bot_iff_forall_ne {x : WithBot α} : x = ⊥ ↔ forall a : α, ↑a != x :=
  Option.eq_none_iff_forall_some_ne

@[to_dual]
/--
theorem `forall_ne_bot` / 定理 `forall_ne_bot`

English:
theorem forall_ne_bot
  given: {p : WithBot α -> Prop}
  statement: (forall x != ⊥, p x) ↔ forall x : α, p x
  proof: by
  simp [ne_bot_iff_exists]

@[to_dual]

中文:
定理 对任意_ne_bot
  条件: {p : WithBot α -> 命题}
  结论: (对任意 x != ⊥, p x) ↔ 对任意 x : α, p x
  证明: by
  simp [ne_bot_iff_exists]

@[to_dual]

Depends on / 依赖: ne_bot_iff_exists
-/
theorem forall_ne_bot {p : WithBot α -> Prop} : (forall x != ⊥, p x) ↔ forall x : α, p x := by
  simp [ne_bot_iff_exists]

@[to_dual]
/--
theorem `exists_ne_bot` / 定理 `exists_ne_bot`

English:
theorem exists_ne_bot
  given: {p : WithBot α -> Prop}
  statement: (exists x != ⊥, p x) ↔ exists x : α, p x
  proof: by
  simp [ne_bot_iff_exists]

中文:
定理 存在_ne_bot
  条件: {p : WithBot α -> 命题}
  结论: (存在 x != ⊥, p x) ↔ 存在 x : α, p x
  证明: by
  simp [ne_bot_iff_exists]

Depends on / 依赖: ne_bot_iff_exists
-/
theorem exists_ne_bot {p : WithBot α -> Prop} : (exists x != ⊥, p x) ↔ exists x : α, p x := by
  simp [ne_bot_iff_exists]

/-- Deconstruct a `x : WithBot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
@[to_dual
/-- Deconstruct a `x : WithTop α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/]
/--
Definition of `unbot` / `unbot` 的定义

English:
definition unbot
  signature: : forall x : WithBot α, x != ⊥ -> α | (x : α), _ => x

中文:
定义 unbot
  签名: : 对任意 x : WithBot α, x != ⊥ -> α | (x : α), _ => x
-/
def unbot : forall x : WithBot α, x != ⊥ -> α | (x : α), _ => x

@[to_dual (attr := simp)]
/--
lemma `coe_unbot` / 引理 `coe_unbot`

English:
lemma coe_unbot
  statement: forall (x : WithBot α) hx, x.unbot hx = x | (x : α), _ => rfl

中文:
引理 coe_unbot
  结论: 对任意 (x : WithBot α) hx, x.unbot hx = x | (x : α), _ => rfl
-/
lemma coe_unbot : forall (x : WithBot α) hx, x.unbot hx = x | (x : α), _ => rfl

@[to_dual (attr := simp)]
/--
theorem `unbot_coe` / 定理 `unbot_coe`

English:
theorem unbot_coe
  given: (x : α) (h : (x : WithBot α) != ⊥ := coe_ne_bot)
  statement: (x : WithBot α).unbot h = x
  proof: rfl

@[to_dual]

中文:
定理 unbot_coe
  条件: (x : α) (h : (x : WithBot α) != ⊥ := coe_ne_bot)
  结论: (x : WithBot α).unbot h = x
  证明: rfl

@[to_dual]

Depends on / 依赖: WithBot, coe_ne_bot
-/
theorem unbot_coe (x : α) (h : (x : WithBot α) != ⊥ := coe_ne_bot) : (x : WithBot α).unbot h = x :=
  rfl

@[to_dual]
/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: : CanLift (WithBot α) α (↑) fun r => r != ⊥ where
  body: ⟨x.unbot h, coe_unbot _ _⟩

@[to_dual]

中文:
实例 canLift
  签名: : CanLift (WithBot α) α (↑) fun r => r != ⊥ where
  定义体: ⟨x.unbot h, coe_unbot _ _⟩

@[to_dual]

Depends on / 依赖: Finite, IsNoetherian, _root_, _root_.isNoetherian_of_finite, coe_unbot, isNoetherian_of_finite, x.unbot
-/
instance canLift : CanLift (WithBot α) α (↑) fun r => r != ⊥ where
  prf x h := ⟨x.unbot h, coe_unbot _ _⟩

@[to_dual]
/--
Instance `instTop` / 实例 `instTop`

English:
instance instTop
  signature: [Top α]
  body: (⊤ : α)

@[to_dual (attr := simp, norm_cast)]

中文:
实例 instTop
  签名: [顶元素 α]
  定义体: (⊤ : α)

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: Finite, IsNoetherian, IsNoetherian.finite, Module, Module.Finite, finite
-/
instance instTop [Top α] : Top (WithBot α) where
  top := (⊤ : α)

@[to_dual (attr := simp, norm_cast)]
/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  given: [Top α]
  statement: ((⊤ : α) : WithBot α) = ⊤
  proof: rfl
@[to_dual (attr := simp, norm_cast)]

中文:
引理 coe_top
  条件: [顶元素 α]
  结论: ((⊤ : α) : WithBot α) = ⊤
  证明: rfl
@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: IsNoetherian, IsNoetherian.finite, Submodule, finite, restrictScalars
-/
lemma coe_top [Top α] : ((⊤ : α) : WithBot α) = ⊤ := rfl
@[to_dual (attr := simp, norm_cast)]
/--
lemma `coe_eq_top` / 引理 `coe_eq_top`

English:
lemma coe_eq_top
  given: [Top α] {a : α}
  statement: (a : WithBot α) = ⊤ ↔ a = ⊤
  proof: coe_eq_coe
@[to_dual (attr := simp, norm_cast)]

中文:
引理 coe_eq_top
  条件: [顶元素 α] {a : α}
  结论: (a : WithBot α) = ⊤ ↔ a = ⊤
  证明: coe_eq_coe
@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: coe_eq_coe, fg_of_injective
-/
lemma coe_eq_top [Top α] {a : α} : (a : WithBot α) = ⊤ ↔ a = ⊤ := coe_eq_coe
@[to_dual (attr := simp, norm_cast)]
/--
lemma `top_eq_coe` / 引理 `top_eq_coe`

English:
lemma top_eq_coe
  given: [Top α] {a : α}
  statement: ⊤ = (a : WithBot α) ↔ ⊤ = a
  proof: coe_eq_coe

@[to_dual]

中文:
引理 top_eq_coe
  条件: [顶元素 α] {a : α}
  结论: ⊤ = (a : WithBot α) ↔ ⊤ = a
  证明: coe_eq_coe

@[to_dual]

Depends on / 依赖: coe_eq_coe
-/
lemma top_eq_coe [Top α] {a : α} : ⊤ = (a : WithBot α) ↔ ⊤ = a := coe_eq_coe

@[to_dual]
/--
theorem `unbot_eq_iff` / 定理 `unbot_eq_iff`

English:
theorem unbot_eq_iff
  given: {a : WithBot α} {b : α} (h : a != ⊥)
  proof: by
  induction a
  · simpa using h rfl
  · simp

@[to_dual]

中文:
定理 unbot_eq_iff
  条件: {a : WithBot α} {b : α} (h : a != ⊥)
  证明: by
  induction a
  · simpa using h rfl
  · simp

@[to_dual]
-/
theorem unbot_eq_iff {a : WithBot α} {b : α} (h : a != ⊥) :
    a.unbot h = b ↔ a = b := by
  induction a
  · simpa using h rfl
  · simp

@[to_dual]
/--
theorem `eq_unbot_iff` / 定理 `eq_unbot_iff`

English:
theorem eq_unbot_iff
  given: {a : α} {b : WithBot α} (h : b != ⊥)
  proof: by
  induction b
  · simpa using h rfl
  · simp

@[to_dual]

中文:
定理 eq_unbot_iff
  条件: {a : α} {b : WithBot α} (h : b != ⊥)
  证明: by
  induction b
  · simpa using h rfl
  · simp

@[to_dual]
-/
theorem eq_unbot_iff {a : α} {b : WithBot α} (h : b != ⊥) :
    a = b.unbot h ↔ a = b := by
  induction b
  · simpa using h rfl
  · simp

@[to_dual]
/--
theorem `unbot_inj` / 定理 `unbot_inj`

English:
theorem unbot_inj
  given: {a b : WithBot α} (ha : a != ⊥) (hb : b != ⊥)
  proof: by
  rw [unbot_eq_iff]; rw [coe_unbot]

中文:
定理 unbot_inj
  条件: {a b : WithBot α} (ha : a != ⊥) (hb : b != ⊥)
  证明: by
  rw [unbot_eq_iff]; rw [coe_unbot]

Depends on / 依赖: coe_unbot, unbot_eq_iff
-/
theorem unbot_inj {a b : WithBot α} (ha : a != ⊥) (hb : b != ⊥) :
    a.unbot ha = b.unbot hb ↔ a = b := by
  rw [unbot_eq_iff]; rw [coe_unbot]

/-- The equivalence between the non-bottom elements of `WithBot α` and `α`. -/
@[to_dual (attr := simps)
/-- The equivalence between the non-top elements of `WithTop α` and `α`. -/]
/--
Definition of `_root_.Equiv.withBotSubtypeNe` / `_root_.Equiv.withBotSubtypeNe` 的定义

English:
definition _root_.Equiv.withBotSubtypeNe
  signature: : {y : WithBot α // y != ⊥} ≃ α where
  body: fun ⟨x,h⟩ => WithBot.unbot x h
  invFun x := ⟨x, WithBot.coe_ne_bot⟩
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 _root_.等价.withBotSubtypeNe
  签名: : {y : WithBot α // y != ⊥} ≃ α where
  定义体: fun ⟨x,h⟩ => WithBot.unbot x h
  invFun x := ⟨x, WithBot.coe_ne_bot⟩
  left_inv _ := by simp
  right_inv _ := by simp

Depends on / 依赖: WithBot, WithBot.unbot
-/
def _root_.Equiv.withBotSubtypeNe : {y : WithBot α // y != ⊥} ≃ α where
  toFun := fun ⟨x,h⟩ => WithBot.unbot x h
  invFun x := ⟨x, WithBot.coe_ne_bot⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Function that sends an element of `WithBot α` to `α`,
with an arbitrary default value for `⊥`. -/
@[to_dual
/-- Function that sends an element of `WithTop α` to `α`,
with an arbitrary default value for `⊤`. -/]
/--
Definition of `unbotA` / `unbotA` 的定义

English:
abbreviation unbotA
  signature: [Nonempty α]
  body: unbotD (Classical.arbitrary α)

@[to_dual]

中文:
缩写 unbotA
  签名: [非空 α]
  定义体: unbotD (Classical.arbitrary α)

@[to_dual]

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, unbotD
-/
noncomputable abbrev unbotA [Nonempty α] : WithBot α -> α := unbotD (Classical.arbitrary α)

@[to_dual]
/--
lemma `unbotA_eq_unbot` / 引理 `unbotA_eq_unbot`

English:
lemma unbotA_eq_unbot
  given: [Nonempty α] {a : WithBot α} (ha : a != ⊥)
  statement: unbotA a = unbot a ha
  proof: by
  cases a with
  | bot => contradiction
  | coe a => simp

中文:
引理 unbotA_eq_unbot
  条件: [非空 α] {a : WithBot α} (ha : a != ⊥)
  结论: unbotA a = unbot a ha
  证明: by
  cases a with
  | bot => contradiction
  | coe a => simp
-/
lemma unbotA_eq_unbot [Nonempty α] {a : WithBot α} (ha : a != ⊥) : unbotA a = unbot a ha := by
  cases a with
  | bot => contradiction
  | coe a => simp

end WithBot

namespace Equiv

/-- A universe-polymorphic version of `EquivFunctor.mapEquiv WithBot e`. -/
@[to_dual (attr := simps apply)
/-- A universe-polymorphic version of `EquivFunctor.mapEquiv WithTop e`. -/]
/--
Definition of `withBotCongr` / `withBotCongr` 的定义

English:
definition withBotCongr
  signature: (e : α ≃ β)
  body: WithBot.map e
  invFun := WithBot.map e.symm
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

中文:
定义 withBotCongr
  签名: (e : α ≃ β)
  定义体: WithBot.map e
  invFun := WithBot.map e.symm
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

Depends on / 依赖: WithBot, WithBot.map
-/
def withBotCongr (e : α ≃ β) : WithBot α ≃ WithBot β where
  toFun := WithBot.map e
  invFun := WithBot.map e.symm
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

attribute [grind =] withBotCongr_apply withTopCongr_apply

@[to_dual (attr := simp)]
/--
theorem `withBotCongr_refl` / 定理 `withBotCongr_refl`

English:
theorem withBotCongr_refl
  statement: withBotCongr (Equiv.refl α) = Equiv.refl _
  proof: Equiv.ext congr_fun WithBot.map_id

@[to_dual (attr := simp, grind =)]

中文:
定理 withBotCongr_refl
  结论: withBotCongr (等价.refl α) = 等价.refl _
  证明: Equiv.ext congr_fun WithBot.map_id

@[to_dual (attr := simp, grind =)]

Depends on / 依赖: Equiv.ext, WithBot, WithBot.map_id, congr_fun, map_id
-/
theorem withBotCongr_refl : withBotCongr (Equiv.refl α) = Equiv.refl _ :=
Equiv.ext congr_fun WithBot.map_id

@[to_dual (attr := simp, grind =)]
/--
theorem `withBotCongr_symm` / 定理 `withBotCongr_symm`

English:
theorem withBotCongr_symm
  given: (e : α ≃ β)
  statement: withBotCongr e.symm = (withBotCongr e).symm
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 withBotCongr_symm
  条件: (e : α ≃ β)
  结论: withBotCongr e.symm = (withBotCongr e).symm
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem withBotCongr_symm (e : α ≃ β) : withBotCongr e.symm = (withBotCongr e).symm :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `withBotCongr_trans` / 定理 `withBotCongr_trans`

English:
theorem withBotCongr_trans
  given: (e₁ : α ≃ β) (e₂ : β ≃ γ)
  proof: by
  ext x
  simp

中文:
定理 withBotCongr_trans
  条件: (e₁ : α ≃ β) (e₂ : β ≃ γ)
  证明: by
  ext x
  simp
-/
theorem withBotCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    withBotCongr (e₁.trans e₂) = (withBotCongr e₁).trans (withBotCongr e₂) := by
  ext x
  simp

end Equiv

-- TODO: do we really need to preserve the def-eq between `LE` on `WithBot` and `WithTop`
-- moving forward? See discussion here:
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Order.20dual.20tactic/near/562584912

section LE
variable [LE α]

/-- Auxiliary definition for the order on `WithBot`. -/
@[mk_iff le_def_aux]
/--
Inductive type `WithBot.LE` / 归纳类型 `WithBot.LE`

English:
inductive WithBot.LE
  parameters: : WithBot α -> WithBot α -> Prop
  constructors (2):
    - protected: bot_le (x : WithBot α) : WithBot.LE ⊥ x
    - protected: coe_le_coe {a b : α} : a <= b -> WithBot.LE a b

中文:
归纳类型 WithBot.LE
  参数: : WithBot α -> WithBot α -> 命题
  构造子 (2 个):
    - protected: bot_le (x : WithBot α) : WithBot.LE ⊥ x
    - protected: coe_le_coe {a b : α} : a <= b -> WithBot.LE a b
-/
protected inductive WithBot.LE : WithBot α -> WithBot α -> Prop
  | protected bot_le (x : WithBot α) : WithBot.LE ⊥ x
  | protected coe_le_coe {a b : α} : a <= b -> WithBot.LE a b

/-- The order on `WithBot α`, defined by `⊥ ≤ y` and `a ≤ b → ↑a ≤ ↑b`.

Equivalently, `x ≤ y` can be defined as `∀ a : α, x = ↑a → ∃ b : α, y = ↑b ∧ a ≤ b`,
see `le_iff_forall`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
instance (priority := 10) WithBot.instLE : LE (WithBot α) where le := WithBot.LE

/-- The order on `WithTop α`, defined by `x ≤ ⊤` and `a ≤ b → ↑a ≤ ↑b`.

Equivalently, `x ≤ y` can be defined as `∀ b : α, y = ↑b → ∃ a : α, x = ↑a ∧ a ≤ b`,
see `le_iff_forall`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
@[to_dual existing]
instance (priority := 10) WithTop.instLE : LE (WithTop α) where le a b := WithBot.LE (α := αᵒᵈ) b a

/--
lemma `WithBot.le_def` / 引理 `WithBot.le_def`

English:
lemma WithBot.le_def
  given: {x y : WithBot α}
  statement: x <= y ↔ x = ⊥ ∨ exists a b : α, a <= b ∧ x = a ∧ y = b
  proof: le_def_aux ..

@[to_dual existing le_def]

中文:
引理 WithBot.le_def
  条件: {x y : WithBot α}
  结论: x <= y ↔ x = ⊥ ∨ 存在 a b : α, a <= b ∧ x = a ∧ y = b
  证明: le_def_aux ..

@[to_dual existing le_def]

Depends on / 依赖: le_def_aux
-/
lemma WithBot.le_def {x y : WithBot α} : x <= y ↔ x = ⊥ ∨ exists a b : α, a <= b ∧ x = a ∧ y = b :=
  le_def_aux ..

@[to_dual existing le_def]
/--
lemma `WithTop.le_def'` / 引理 `WithTop.le_def'`

English:
lemma WithTop.le_def'
  given: {x y : WithTop α}
  statement: x <= y ↔ y = ⊤ ∨ exists b a : α, a <= b ∧ y = b ∧ x = a
  proof: WithBot.le_def

@[to_dual le_def']

中文:
引理 WithTop.le_def'
  条件: {x y : WithTop α}
  结论: x <= y ↔ y = ⊤ ∨ 存在 b a : α, a <= b ∧ y = b ∧ x = a
  证明: WithBot.le_def

@[to_dual le_def']

Depends on / 依赖: WithBot, WithBot.le_def, le_def
-/
lemma WithTop.le_def' {x y : WithTop α} : x <= y ↔ y = ⊤ ∨ exists b a : α, a <= b ∧ y = b ∧ x = a :=
  WithBot.le_def

@[to_dual le_def']
/--
lemma `WithTop.le_def` / 引理 `WithTop.le_def`

English:
lemma WithTop.le_def
  given: {x y : WithTop α}
  statement: x <= y ↔ y = ⊤ ∨ exists a b : α, a <= b ∧ x = a ∧ y = b
  proof: by
  grind [WithTop.le_def']

中文:
引理 WithTop.le_def
  条件: {x y : WithTop α}
  结论: x <= y ↔ y = ⊤ ∨ 存在 a b : α, a <= b ∧ x = a ∧ y = b
  证明: by
  grind [WithTop.le_def']

Depends on / 依赖: WithTop, WithTop.le_def, le_def
-/
lemma WithTop.le_def {x y : WithTop α} : x <= y ↔ y = ⊤ ∨ exists a b : α, a <= b ∧ x = a ∧ y = b := by
  grind [WithTop.le_def']

end LE

section LT
variable [LT α]

/-- Auxiliary definition for the order on `WithBot`. -/
@[mk_iff lt_def_aux]
/--
Inductive type `WithBot.LT` / 归纳类型 `WithBot.LT`

English:
inductive WithBot.LT
  parameters: [LT α]
  constructors (2):
    - protected: bot_lt (b : α) : WithBot.LT ⊥ b
    - protected: coe_lt_coe {a b : α} : a < b -> WithBot.LT a b

中文:
归纳类型 WithBot.LT
  参数: [LT α]
  构造子 (2 个):
    - protected: bot_lt (b : α) : WithBot.LT ⊥ b
    - protected: coe_lt_coe {a b : α} : a < b -> WithBot.LT a b
-/
protected inductive WithBot.LT [LT α] : WithBot α -> WithBot α -> Prop
  | protected bot_lt (b : α) : WithBot.LT ⊥ b
  | protected coe_lt_coe {a b : α} : a < b -> WithBot.LT a b

/-- The order on `WithBot α`, defined by `⊥ < ↑a` and `a < b → ↑a < ↑b`.

Equivalently, `x < y` can be defined as `∃ b : α, y = ↑b ∧ ∀ a : α, x = ↑a → a < b`,
see `lt_iff_exists`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
instance (priority := 10) WithBot.instLT : LT (WithBot α) where lt := WithBot.LT

/-- The order on `WithTop α`, defined by `↑a < ⊤` and `a < b → ↑a < ↑b`.

Equivalently, `x < y` can be defined as `∃ a : α, x = ↑a ∧ ∀ b : α, y = ↑b → a < b`,
see `le_if_forall`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
@[to_dual existing]
instance (priority := 10) WithTop.instLT : LT (WithTop α) where lt a b := WithBot.LT (α := αᵒᵈ) b a

/--
lemma `WithBot.lt_def` / 引理 `WithBot.lt_def`

English:
lemma WithBot.lt_def
  given: {x y : WithBot α}
  proof: (lt_def_aux ..).trans by simp

@[to_dual existing lt_def]

中文:
引理 WithBot.lt_def
  条件: {x y : WithBot α}
  证明: (lt_def_aux ..).trans by simp

@[to_dual existing lt_def]

Depends on / 依赖: lt_def_aux
-/
lemma WithBot.lt_def {x y : WithBot α} :
    x < y ↔ (x = ⊥ ∧ exists b : α, y = b) ∨ exists a b : α, a < b ∧ x = a ∧ y = b :=
(lt_def_aux ..).trans by simp

@[to_dual existing lt_def]
/--
lemma `WithTop.lt_def'` / 引理 `WithTop.lt_def'`

English:
lemma WithTop.lt_def'
  given: {x y : WithTop α}
  proof: WithBot.lt_def

@[to_dual lt_def']

中文:
引理 WithTop.lt_def'
  条件: {x y : WithTop α}
  证明: WithBot.lt_def

@[to_dual lt_def']

Depends on / 依赖: WithBot, WithBot.lt_def, lt_def
-/
lemma WithTop.lt_def' {x y : WithTop α} :
    x < y ↔ (y = ⊤ ∧ exists a : α, x = a) ∨ exists b a : α, a < b ∧ y = b ∧ x = a :=
  WithBot.lt_def

@[to_dual lt_def']
/--
lemma `WithTop.lt_def` / 引理 `WithTop.lt_def`

English:
lemma WithTop.lt_def
  given: {x y : WithTop α}
  proof: by
  grind [WithTop.lt_def']

中文:
引理 WithTop.lt_def
  条件: {x y : WithTop α}
  证明: by
  grind [WithTop.lt_def']

Depends on / 依赖: Semiring, Subsingleton, WithTop, WithTop.lt_def, isNoetherian_of_subsingleton, lt_def
-/
lemma WithTop.lt_def {x y : WithTop α} :
    x < y ↔ (exists a : α, x = ↑a) ∧ y = ⊤ ∨ exists a b : α, a < b ∧ x = ↑a ∧ y = ↑b := by
  grind [WithTop.lt_def']

end LT

namespace WithBot

variable {a b : α}

section LE

variable [LE α] {x y : WithBot α}

@[to_dual]
/--
lemma `le_iff_forall` / 引理 `le_iff_forall`

English:
lemma le_iff_forall
  statement: x <= y ↔ forall a : α, x = ↑a -> exists b : α, y = ↑b ∧ a <= b
  proof: by
  cases x <;> cases y <;> simp [le_def]

@[to_dual (attr := simp, norm_cast)]

中文:
引理 le_iff_对任意
  结论: x <= y ↔ 对任意 a : α, x = ↑a -> 存在 b : α, y = ↑b ∧ a <= b
  证明: by
  cases x <;> cases y <;> simp [le_def]

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: le_def
-/
lemma le_iff_forall : x <= y ↔ forall a : α, x = ↑a -> exists b : α, y = ↑b ∧ a <= b := by
  cases x <;> cases y <;> simp [le_def]

@[to_dual (attr := simp, norm_cast)]
/--
lemma `coe_le_coe` / 引理 `coe_le_coe`

English:
lemma coe_le_coe
  statement: (a : WithBot α) <= b ↔ a <= b
  proof: by simp [le_def]

@[to_dual not_top_le_coe]

中文:
引理 coe_le_coe
  结论: (a : WithBot α) <= b ↔ a <= b
  证明: by simp [le_def]

@[to_dual not_top_le_coe]

Depends on / 依赖: le_def
-/
lemma coe_le_coe : (a : WithBot α) <= b ↔ a <= b := by simp [le_def]

@[to_dual not_top_le_coe]
/--
lemma `not_coe_le_bot` / 引理 `not_coe_le_bot`

English:
lemma not_coe_le_bot
  given: (a : α)
  statement: ¬(a : WithBot α) <= ⊥
  proof: by simp [le_def]

@[to_dual]

中文:
引理 not_coe_le_bot
  条件: (a : α)
  结论: ¬(a : WithBot α) <= ⊥
  证明: by simp [le_def]

@[to_dual]

Depends on / 依赖: le_def
-/
lemma not_coe_le_bot (a : α) : ¬(a : WithBot α) <= ⊥ := by simp [le_def]

@[to_dual]
/--
Instance `instOrderBot` / 实例 `instOrderBot`

English:
instance instOrderBot
  signature: : OrderBot (WithBot α) where bot_le
  body: by simp [le_def]

@[to_dual]

中文:
实例 instOrderBot
  签名: : 有底序 (WithBot α) where bot_le
  定义体: by simp [le_def]

@[to_dual]

Depends on / 依赖: le_def
-/
instance instOrderBot : OrderBot (WithBot α) where bot_le := by simp [le_def]

@[to_dual]
/--
Instance `instOrderTop` / 实例 `instOrderTop`

English:
instance instOrderTop
  signature: [OrderTop α]
  body: by cases x <;> simp [le_def]

@[to_dual]

中文:
实例 instOrderTop
  签名: [有顶序 α]
  定义体: by cases x <;> simp [le_def]

@[to_dual]

Depends on / 依赖: le_def
-/
instance instOrderTop [OrderTop α] : OrderTop (WithBot α) where
  le_top x := by cases x <;> simp [le_def]

@[to_dual]
/--
Instance `instBoundedOrder` / 实例 `instBoundedOrder`

English:
instance instBoundedOrder
  signature: [OrderTop α]

中文:
实例 instBoundedOrder
  签名: [有顶序 α]
-/
instance instBoundedOrder [OrderTop α] : BoundedOrder (WithBot α) where

/-- There is a general version `le_bot_iff`, but this lemma does not require a `PartialOrder`. -/
@[to_dual (attr := simp) top_le_iff
/-- There is a general version `top_le_iff`, but this lemma does not require a `PartialOrder`. -/]
/--
theorem `le_bot_iff` / 定理 `le_bot_iff`

English:
theorem le_bot_iff
  statement: forall {x : WithBot α}, x <= ⊥ ↔ x = ⊥

中文:
定理 le_bot_iff
  结论: 对任意 {x : WithBot α}, x <= ⊥ ↔ x = ⊥
-/
protected theorem le_bot_iff : forall {x : WithBot α}, x <= ⊥ ↔ x = ⊥
  | (a : α) => by simp [not_coe_le_bot]
  | ⊥ => by simp

@[to_dual le_coe]
/--
theorem `coe_le` / 定理 `coe_le`

English:
theorem coe_le
  statement: forall {o : Option α}, b in o -> ((a : WithBot α) <= o ↔ a <= b)

中文:
定理 coe_le
  结论: 对任意 {o : 选项类型 α}, b in o -> ((a : WithBot α) <= o ↔ a <= b)
-/
theorem coe_le : forall {o : Option α}, b in o -> ((a : WithBot α) <= o ↔ a <= b)
  | _, rfl => coe_le_coe

@[to_dual le_coe_iff]
/--
theorem `coe_le_iff` / 定理 `coe_le_iff`

English:
theorem coe_le_iff
  statement: a <= x ↔ exists b : α, x = b ∧ a <= b
  proof: by simp [le_iff_forall]
@[to_dual coe_le_iff]

中文:
定理 coe_le_iff
  结论: a <= x ↔ 存在 b : α, x = b ∧ a <= b
  证明: by simp [le_iff_forall]
@[to_dual coe_le_iff]

Depends on / 依赖: coe_le_iff, le_iff_forall, to_dual
-/
theorem coe_le_iff : a <= x ↔ exists b : α, x = b ∧ a <= b := by simp [le_iff_forall]
@[to_dual coe_le_iff]
/--
theorem `le_coe_iff` / 定理 `le_coe_iff`

English:
theorem le_coe_iff
  statement: x <= b ↔ forall a : α, x = ↑a -> a <= b
  proof: by simp [le_iff_forall]

@[to_dual]

中文:
定理 le_coe_iff
  结论: x <= b ↔ 对任意 a : α, x = ↑a -> a <= b
  证明: by simp [le_iff_forall]

@[to_dual]

Depends on / 依赖: le_iff_forall
-/
theorem le_coe_iff : x <= b ↔ forall a : α, x = ↑a -> a <= b := by simp [le_iff_forall]

@[to_dual]
/--
theorem `_root_.IsMax.withBot` / 定理 `_root_.IsMax.withBot`

English:
theorem _root_.IsMax.withBot
  given: (h : IsMax a)
  statement: IsMax (a : WithBot α)
  proof: fun x => by cases x <;> simp; simpa using @h _

@[to_dual (attr := simp) untop_le_iff]

中文:
定理 _root_.IsMax.withBot
  条件: (h : IsMax a)
  结论: IsMax (a : WithBot α)
  证明: fun x => by cases x <;> simp; simpa using @h _

@[to_dual (attr := simp) untop_le_iff]

Depends on / 依赖: Ideal.idealProdEquiv.toOrderEmbedding.wellFoundedGT, IsNoetherianRing, idealProdEquiv, isNoetherian_iff, toOrderEmbedding, wellFoundedGT
-/
protected theorem _root_.IsMax.withBot (h : IsMax a) : IsMax (a : WithBot α) :=
  fun x => by cases x <;> simp; simpa using @h _

@[to_dual (attr := simp) untop_le_iff]
/--
lemma `le_unbot_iff` / 引理 `le_unbot_iff`

English:
lemma le_unbot_iff
  given: (hx : x != ⊥)
  statement: a <= unbot x hx ↔ a <= x
  proof: by lift x to α using hx; simp
@[to_dual (attr := simp) le_untop_iff]

中文:
引理 le_unbot_iff
  条件: (hx : x != ⊥)
  结论: a <= unbot x hx ↔ a <= x
  证明: by lift x to α using hx; simp
@[to_dual (attr := simp) le_untop_iff]

Depends on / 依赖: Finite, Finite.induction_empty_option, induction_empty_option, infer_instance, isNoetherianRing_of_ringEquiv, le_untop_iff, piCongrLeft, piOptionEquivProd, to_dual
-/
lemma le_unbot_iff (hx : x != ⊥) : a <= unbot x hx ↔ a <= x := by lift x to α using hx; simp
@[to_dual (attr := simp) le_untop_iff]
/--
lemma `unbot_le_iff` / 引理 `unbot_le_iff`

English:
lemma unbot_le_iff
  given: (hx : x != ⊥)
  statement: unbot x hx <= a ↔ x <= a
  proof: by lift x to α using hx; simp

@[to_dual (reorder := hx hy)]

中文:
引理 unbot_le_iff
  条件: (hx : x != ⊥)
  结论: unbot x hx <= a ↔ x <= a
  证明: by lift x to α using hx; simp

@[to_dual (reorder := hx hy)]
-/
lemma unbot_le_iff (hx : x != ⊥) : unbot x hx <= a ↔ x <= a := by lift x to α using hx; simp

@[to_dual (reorder := hx hy)]
/--
lemma `unbot_le_unbot_iff` / 引理 `unbot_le_unbot_iff`

English:
lemma unbot_le_unbot_iff
  given: (hx : x != ⊥) (hy : y != ⊥)
  statement: x.unbot hx <= y.unbot hy ↔ x <= y
  proof: by simp

@[to_dual]
alias ⟨_, unbot_mono⟩ := unbot_le_unbot_iff

@[to_dual untopD_le_iff]

中文:
引理 unbot_le_unbot_iff
  条件: (hx : x != ⊥) (hy : y != ⊥)
  结论: x.unbot hx <= y.unbot hy ↔ x <= y
  证明: by simp

@[to_dual]
alias ⟨_, unbot_mono⟩ := unbot_le_unbot_iff

@[to_dual untopD_le_iff]
-/
lemma unbot_le_unbot_iff (hx : x != ⊥) (hy : y != ⊥) : x.unbot hx <= y.unbot hy ↔ x <= y := by simp

@[to_dual]
alias ⟨_, unbot_mono⟩ := unbot_le_unbot_iff

@[to_dual untopD_le_iff]
/--
lemma `le_unbotD_iff` / 引理 `le_unbotD_iff`

English:
lemma le_unbotD_iff
  given: (hx : x != ⊥)
  statement: b <= x.unbotD a ↔ b <= x
  proof: by lift x to α using hx; simp
@[to_dual le_untopD_iff]

中文:
引理 le_unbotD_iff
  条件: (hx : x != ⊥)
  结论: b <= x.unbotD a ↔ b <= x
  证明: by lift x to α using hx; simp
@[to_dual le_untopD_iff]

Depends on / 依赖: le_untopD_iff, to_dual
-/
lemma le_unbotD_iff (hx : x != ⊥) : b <= x.unbotD a ↔ b <= x := by lift x to α using hx; simp
@[to_dual le_untopD_iff]
/--
lemma `unbotD_le_iff` / 引理 `unbotD_le_iff`

English:
lemma unbotD_le_iff
  given: (hx : x = ⊥ -> a <= b)
  statement: x.unbotD a <= b ↔ x <= b
  proof: by cases x <;> simp [hx]

@[to_dual]

中文:
引理 unbotD_le_iff
  条件: (hx : x = ⊥ -> a <= b)
  结论: x.unbotD a <= b ↔ x <= b
  证明: by cases x <;> simp [hx]

@[to_dual]
-/
lemma unbotD_le_iff (hx : x = ⊥ -> a <= b) : x.unbotD a <= b ↔ x <= b := by cases x <;> simp [hx]

@[to_dual]
/--
lemma `unbotD_mono` / 引理 `unbotD_mono`

English:
lemma unbotD_mono
  given: (hx : x != ⊥) (h : x <= y)
  statement: x.unbotD a <= y.unbotD a
  proof: by
  lift x to α using hx
  cases y <;> simp_all

@[to_dual untopA_le_iff]

中文:
引理 unbotD_mono
  条件: (hx : x != ⊥) (h : x <= y)
  结论: x.unbotD a <= y.unbotD a
  证明: by
  lift x to α using hx
  cases y <;> simp_all

@[to_dual untopA_le_iff]
-/
lemma unbotD_mono (hx : x != ⊥) (h : x <= y) : x.unbotD a <= y.unbotD a := by
  lift x to α using hx
  cases y <;> simp_all

@[to_dual untopA_le_iff]
/--
lemma `le_unbotA_iff` / 引理 `le_unbotA_iff`

English:
lemma le_unbotA_iff
  given: [Nonempty α] (hx : x != ⊥)
  statement: a <= x.unbotA ↔ a <= x
  proof: le_unbotD_iff hx
@[to_dual le_untopA_iff]

中文:
引理 le_unbotA_iff
  条件: [非空 α] (hx : x != ⊥)
  结论: a <= x.unbotA ↔ a <= x
  证明: le_unbotD_iff hx
@[to_dual le_untopA_iff]

Depends on / 依赖: le_unbotD_iff
-/
lemma le_unbotA_iff [Nonempty α] (hx : x != ⊥) : a <= x.unbotA ↔ a <= x := le_unbotD_iff hx
@[to_dual le_untopA_iff]
/--
lemma `unbotA_le_iff` / 引理 `unbotA_le_iff`

English:
lemma unbotA_le_iff
  given: [Nonempty α] (hx : x != ⊥)
  statement: x.unbotA <= a ↔ x <= a
  proof: by
  lift x to α using hx; simp

@[to_dual]

中文:
引理 unbotA_le_iff
  条件: [非空 α] (hx : x != ⊥)
  结论: x.unbotA <= a ↔ x <= a
  证明: by
  lift x to α using hx; simp

@[to_dual]
-/
lemma unbotA_le_iff [Nonempty α] (hx : x != ⊥) : x.unbotA <= a ↔ x <= a := by
  lift x to α using hx; simp

@[to_dual]
/--
lemma `unbotA_mono` / 引理 `unbotA_mono`

English:
lemma unbotA_mono
  given: [Nonempty α] (hy : x != ⊥) (h : x <= y)
  statement: x.unbotA <= y.unbotA
  proof: unbotD_mono hy h

中文:
引理 unbotA_mono
  条件: [非空 α] (hy : x != ⊥) (h : x <= y)
  结论: x.unbotA <= y.unbotA
  证明: unbotD_mono hy h

Depends on / 依赖: unbotD_mono
-/
lemma unbotA_mono [Nonempty α] (hy : x != ⊥) (h : x <= y) : x.unbotA <= y.unbotA := unbotD_mono hy h

end LE

section LT

variable [LT α] {x y : WithBot α}

@[to_dual]
/--
lemma `lt_iff_exists` / 引理 `lt_iff_exists`

English:
lemma lt_iff_exists
  statement: x < y ↔ exists b : α, y = ↑b ∧ forall a : α, x = ↑a -> a < b
  proof: by
  cases x <;> cases y <;> simp [lt_def]

@[to_dual (attr := simp, norm_cast)]

中文:
引理 lt_iff_存在
  结论: x < y ↔ 存在 b : α, y = ↑b ∧ 对任意 a : α, x = ↑a -> a < b
  证明: by
  cases x <;> cases y <;> simp [lt_def]

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: lt_def
-/
lemma lt_iff_exists : x < y ↔ exists b : α, y = ↑b ∧ forall a : α, x = ↑a -> a < b := by
  cases x <;> cases y <;> simp [lt_def]

@[to_dual (attr := simp, norm_cast)]
/--
lemma `coe_lt_coe` / 引理 `coe_lt_coe`

English:
lemma coe_lt_coe
  statement: (a : WithBot α) < b ↔ a < b
  proof: by simp [lt_def]
@[to_dual (attr := simp) coe_lt_top]

中文:
引理 coe_lt_coe
  结论: (a : WithBot α) < b ↔ a < b
  证明: by simp [lt_def]
@[to_dual (attr := simp) coe_lt_top]

Depends on / 依赖: coe_lt_top, lt_def, to_dual
-/
lemma coe_lt_coe : (a : WithBot α) < b ↔ a < b := by simp [lt_def]
@[to_dual (attr := simp) coe_lt_top]
/--
lemma `bot_lt_coe` / 引理 `bot_lt_coe`

English:
lemma bot_lt_coe
  given: (a : α)
  statement: ⊥ < (a : WithBot α)
  proof: by simp [lt_def]
@[to_dual (attr := simp) not_top_lt]

中文:
引理 bot_lt_coe
  条件: (a : α)
  结论: ⊥ < (a : WithBot α)
  证明: by simp [lt_def]
@[to_dual (attr := simp) not_top_lt]

Depends on / 依赖: WithBot, lt_def, not_lt_bot, not_top_lt, protected, to_dual
-/
lemma bot_lt_coe (a : α) : ⊥ < (a : WithBot α) := by simp [lt_def]
@[to_dual (attr := simp) not_top_lt]
/--
lemma `not_lt_bot` / 引理 `not_lt_bot`

English:
lemma not_lt_bot
  given: (a : WithBot α)
  statement: ¬a < ⊥
  proof: by simp [lt_def]

@[to_dual]

中文:
引理 not_lt_bot
  条件: (a : WithBot α)
  结论: ¬a < ⊥
  证明: by simp [lt_def]

@[to_dual]
-/
protected lemma not_lt_bot (a : WithBot α) : ¬a < ⊥ := by simp [lt_def]

@[to_dual]
/--
lemma `lt_iff_exists_coe` / 引理 `lt_iff_exists_coe`

English:
lemma lt_iff_exists_coe
  statement: x < y ↔ exists b : α, y = b ∧ x < b
  proof: by cases y <;> simp

@[to_dual coe_lt_iff]

中文:
引理 lt_iff_存在_coe
  结论: x < y ↔ 存在 b : α, y = b ∧ x < b
  证明: by cases y <;> simp

@[to_dual coe_lt_iff]
-/
lemma lt_iff_exists_coe : x < y ↔ exists b : α, y = b ∧ x < b := by cases y <;> simp

@[to_dual coe_lt_iff]
/--
lemma `lt_coe_iff` / 引理 `lt_coe_iff`

English:
lemma lt_coe_iff
  statement: x < b ↔ forall a : α, x = a -> a < b
  proof: by simp [lt_iff_exists]

中文:
引理 lt_coe_iff
  结论: x < b ↔ 对任意 a : α, x = a -> a < b
  证明: by simp [lt_iff_exists]

Depends on / 依赖: lt_iff_exists
-/
lemma lt_coe_iff : x < b ↔ forall a : α, x = a -> a < b := by simp [lt_iff_exists]

/-- A version of `bot_lt_iff_ne_bot` for `WithBot` that only requires `LT α`, not
`PartialOrder α`. -/
@[to_dual lt_top_iff_ne_top
/-- A version of `lt_top_iff_ne_top` for `WithTop` that only requires `LT α`, not
`PartialOrder α`. -/]
/--
lemma `bot_lt_iff_ne_bot` / 引理 `bot_lt_iff_ne_bot`

English:
lemma bot_lt_iff_ne_bot
  statement: ⊥ < x ↔ x != ⊥
  proof: by cases x <;> simp

@[to_dual (attr := simp) untop_lt_iff]

中文:
引理 bot_lt_iff_ne_bot
  结论: ⊥ < x ↔ x != ⊥
  证明: by cases x <;> simp

@[to_dual (attr := simp) untop_lt_iff]
-/
protected lemma bot_lt_iff_ne_bot : ⊥ < x ↔ x != ⊥ := by cases x <;> simp

@[to_dual (attr := simp) untop_lt_iff]
/--
lemma `lt_unbot_iff` / 引理 `lt_unbot_iff`

English:
lemma lt_unbot_iff
  given: (hx : x != ⊥)
  statement: a < unbot x hx ↔ a < x
  proof: by lift x to α using hx; simp
@[to_dual (attr := simp) lt_untop_iff]

中文:
引理 lt_unbot_iff
  条件: (hx : x != ⊥)
  结论: a < unbot x hx ↔ a < x
  证明: by lift x to α using hx; simp
@[to_dual (attr := simp) lt_untop_iff]

Depends on / 依赖: lt_untop_iff, to_dual
-/
lemma lt_unbot_iff (hx : x != ⊥) : a < unbot x hx ↔ a < x := by lift x to α using hx; simp
@[to_dual (attr := simp) lt_untop_iff]
/--
lemma `unbot_lt_iff` / 引理 `unbot_lt_iff`

English:
lemma unbot_lt_iff
  given: (hx : x != ⊥)
  statement: unbot x hx < b ↔ x < b
  proof: by lift x to α using hx; simp

@[to_dual (reorder := hx hy)]

中文:
引理 unbot_lt_iff
  条件: (hx : x != ⊥)
  结论: unbot x hx < b ↔ x < b
  证明: by lift x to α using hx; simp

@[to_dual (reorder := hx hy)]
-/
lemma unbot_lt_iff (hx : x != ⊥) : unbot x hx < b ↔ x < b := by lift x to α using hx; simp

@[to_dual (reorder := hx hy)]
/--
lemma `unbot_lt_unbot_iff` / 引理 `unbot_lt_unbot_iff`

English:
lemma unbot_lt_unbot_iff
  given: (hx hy)
  statement: unbot x hx < unbot y hy ↔ x < y
  proof: by simp

@[to_dual untopD_lt_iff]

中文:
引理 unbot_lt_unbot_iff
  条件: (hx hy)
  结论: unbot x hx < unbot y hy ↔ x < y
  证明: by simp

@[to_dual untopD_lt_iff]
-/
lemma unbot_lt_unbot_iff (hx hy) : unbot x hx < unbot y hy ↔ x < y := by simp

@[to_dual untopD_lt_iff]
/--
lemma `lt_unbotD_iff` / 引理 `lt_unbotD_iff`

English:
lemma lt_unbotD_iff
  given: (hx : x != ⊥)
  statement: b < x.unbotD a ↔ b < x
  proof: by lift x to α using hx; simp
@[to_dual lt_untopD_iff]

中文:
引理 lt_unbotD_iff
  条件: (hx : x != ⊥)
  结论: b < x.unbotD a ↔ b < x
  证明: by lift x to α using hx; simp
@[to_dual lt_untopD_iff]

Depends on / 依赖: lt_untopD_iff, to_dual
-/
lemma lt_unbotD_iff (hx : x != ⊥) : b < x.unbotD a ↔ b < x := by lift x to α using hx; simp
@[to_dual lt_untopD_iff]
/--
lemma `unbotD_lt_iff` / 引理 `unbotD_lt_iff`

English:
lemma unbotD_lt_iff
  given: (hx : x = ⊥ -> a < b)
  statement: x.unbotD a < b ↔ x < b
  proof: by cases x <;> simp [hx]

@[to_dual untopA_lt_iff]

中文:
引理 unbotD_lt_iff
  条件: (hx : x = ⊥ -> a < b)
  结论: x.unbotD a < b ↔ x < b
  证明: by cases x <;> simp [hx]

@[to_dual untopA_lt_iff]
-/
lemma unbotD_lt_iff (hx : x = ⊥ -> a < b) : x.unbotD a < b ↔ x < b := by cases x <;> simp [hx]

@[to_dual untopA_lt_iff]
/--
lemma `lt_unbotA_iff` / 引理 `lt_unbotA_iff`

English:
lemma lt_unbotA_iff
  given: [Nonempty α] (hx : x != ⊥)
  statement: a < x.unbotA ↔ a < x
  proof: lt_unbotD_iff hx
@[to_dual lt_untopA_iff]

中文:
引理 lt_unbotA_iff
  条件: [非空 α] (hx : x != ⊥)
  结论: a < x.unbotA ↔ a < x
  证明: lt_unbotD_iff hx
@[to_dual lt_untopA_iff]

Depends on / 依赖: lt_unbotD_iff
-/
lemma lt_unbotA_iff [Nonempty α] (hx : x != ⊥) : a < x.unbotA ↔ a < x := lt_unbotD_iff hx
@[to_dual lt_untopA_iff]
/--
lemma `unbotA_lt_iff` / 引理 `unbotA_lt_iff`

English:
lemma unbotA_lt_iff
  given: [Nonempty α] (hx : x != ⊥)
  statement: x.unbotA < a ↔ x < a
  proof: by
  lift x to α using hx; simp

中文:
引理 unbotA_lt_iff
  条件: [非空 α] (hx : x != ⊥)
  结论: x.unbotA < a ↔ x < a
  证明: by
  lift x to α using hx; simp
-/
lemma unbotA_lt_iff [Nonempty α] (hx : x != ⊥) : x.unbotA < a ↔ x < a := by
  lift x to α using hx; simp

end LT

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : Preorder (WithBot α) where
  body: by cases x <;> cases y <;> simp [lt_iff_le_not_ge]
  le_refl x := by cases x <;> simp [le_def]
  le_trans x y z := by cases x <;> cases y <;> cases z <;> simp [le_def]; simpa using le_trans

中文:
实例 [预序
  签名: α] : 预序 (WithBot α) where
  定义体: by cases x <;> cases y <;> simp [lt_iff_le_not_ge]
  le_refl x := by cases x <;> simp [le_def]
  le_trans x y z := by cases x <;> cases y <;> cases z <;> simp [le_def]; simpa using le_trans

Depends on / 依赖: le_def, le_refl, le_trans, lt_iff_le_not_ge
-/
instance [Preorder α] : Preorder (WithBot α) where
  lt_iff_le_not_ge x y := by cases x <;> cases y <;> simp [lt_iff_le_not_ge]
  le_refl x := by cases x <;> simp [le_def]
  le_trans x y z := by cases x <;> cases y <;> cases z <;> simp [le_def]; simpa using le_trans

section Preorder

variable [Preorder α] [Preorder β] {x y : WithBot α}

@[to_dual]
/--
theorem `coe_strictMono` / 定理 `coe_strictMono`

English:
theorem coe_strictMono
  statement: StrictMono (fun (a : α) => (a : WithBot α))
  proof: fun _ _ => coe_lt_coe.2

@[to_dual]

中文:
定理 coe_strictMono
  结论: 严格递增 (fun (a : α) => (a : WithBot α))
  证明: fun _ _ => coe_lt_coe.2

@[to_dual]

Depends on / 依赖: coe_lt_coe
-/
theorem coe_strictMono : StrictMono (fun (a : α) => (a : WithBot α)) := fun _ _ => coe_lt_coe.2

@[to_dual]
/--
theorem `coe_mono` / 定理 `coe_mono`

English:
theorem coe_mono
  statement: Monotone (fun (a : α) => (a : WithBot α))
  proof: fun _ _ => coe_le_coe.2

@[to_dual]

中文:
定理 coe_mono
  结论: 递增 (fun (a : α) => (a : WithBot α))
  证明: fun _ _ => coe_le_coe.2

@[to_dual]

Depends on / 依赖: coe_le_coe
-/
theorem coe_mono : Monotone (fun (a : α) => (a : WithBot α)) := fun _ _ => coe_le_coe.2

@[to_dual]
/--
theorem `monotone_iff` / 定理 `monotone_iff`

English:
theorem monotone_iff
  given: {f : WithBot α -> β}
  proof: ⟨fun h => ⟨h.comp WithBot.coe_mono, fun _ => h bot_le⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨fun _ => le_rfl, fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_coe_le_bot _ h).elim,
          fun _ hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩

@[to_dual (attr := simp)]

中文:
定理 monotone_iff
  条件: {f : WithBot α -> β}
  证明: ⟨fun h => ⟨h.comp WithBot.coe_mono, fun _ => h bot_le⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨fun _ => le_rfl, fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_coe_le_bot _ h).elim,
          fun _ hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩

@[to_dual (attr := simp)]

Depends on / 依赖: WithBot, WithBot.coe_mono, WithBot.forall, bot_le, coe_le_coe, coe_mono, h.comp, le_rfl, not_coe_le_bot
-/
theorem monotone_iff {f : WithBot α -> β} :
    Monotone f ↔ Monotone (fun a => f a : α -> β) ∧ forall x : α, f ⊥ <= f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_mono, fun _ => h bot_le⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨fun _ => le_rfl, fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_coe_le_bot _ h).elim,
          fun _ hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩

@[to_dual (attr := simp)]
/--
theorem `monotone_map_iff` / 定理 `monotone_map_iff`

English:
theorem monotone_map_iff
  given: {f : α -> β}
  statement: Monotone (WithBot.map f) ↔ Monotone f
  proof: monotone_iff.trans by simp [Monotone]

@[to_dual]
alias ⟨_, _root_.Monotone.withBot_map⟩ := monotone_map_iff

@[to_dual]

中文:
定理 monotone_map_iff
  条件: {f : α -> β}
  结论: 递增 (WithBot.map f) ↔ 递增 f
  证明: monotone_iff.trans by simp [Monotone]

@[to_dual]
alias ⟨_, _root_.Monotone.withBot_map⟩ := monotone_map_iff

@[to_dual]

Depends on / 依赖: Monotone, monotone_iff, monotone_iff.trans
-/
theorem monotone_map_iff {f : α -> β} : Monotone (WithBot.map f) ↔ Monotone f :=
monotone_iff.trans by simp [Monotone]

@[to_dual]
alias ⟨_, _root_.Monotone.withBot_map⟩ := monotone_map_iff

@[to_dual]
/--
theorem `strictMono_iff` / 定理 `strictMono_iff`

English:
theorem strictMono_iff
  given: {f : WithBot α -> β}
  proof: ⟨fun h => ⟨h.comp WithBot.coe_strictMono, fun _ => h (bot_lt_coe _)⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨flip absurd (lt_irrefl _), fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_lt_bot h).elim, fun _ hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩

@[to_dual]

中文:
定理 strictMono_iff
  条件: {f : WithBot α -> β}
  证明: ⟨fun h => ⟨h.comp WithBot.coe_strictMono, fun _ => h (bot_lt_coe _)⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨flip absurd (lt_irrefl _), fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_lt_bot h).elim, fun _ hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩

@[to_dual]

Depends on / 依赖: WithBot, WithBot.coe_strictMono, WithBot.forall, absurd, bot_lt_coe, coe_lt_coe, coe_strictMono, h.comp, lt_irrefl, not_lt_bot
-/
theorem strictMono_iff {f : WithBot α -> β} :
    StrictMono f ↔ StrictMono (fun a => f a : α -> β) ∧ forall x : α, f ⊥ < f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_strictMono, fun _ => h (bot_lt_coe _)⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨flip absurd (lt_irrefl _), fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_lt_bot h).elim, fun _ hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩

@[to_dual]
/--
theorem `strictAnti_iff` / 定理 `strictAnti_iff`

English:
theorem strictAnti_iff
  given: {f : WithBot α -> β}
  proof: strictMono_iff (β := βᵒᵈ)

@[to_dual (attr := simp)]

中文:
定理 strictAnti_iff
  条件: {f : WithBot α -> β}
  证明: strictMono_iff (β := βᵒᵈ)

@[to_dual (attr := simp)]

Depends on / 依赖: strictMono_iff
-/
theorem strictAnti_iff {f : WithBot α -> β} :
    StrictAnti f ↔ StrictAnti (fun a => f a : α -> β) ∧ forall x : α, f x < f ⊥ :=
  strictMono_iff (β := βᵒᵈ)

@[to_dual (attr := simp)]
/--
theorem `strictMono_map_iff` / 定理 `strictMono_map_iff`

English:
theorem strictMono_map_iff
  given: {f : α -> β}
  proof: strictMono_iff.trans by simp [StrictMono, bot_lt_coe]

@[to_dual]
alias ⟨_, _root_.StrictMono.withBot_map⟩ := strictMono_map_iff

@[to_dual]

中文:
定理 strictMono_map_iff
  条件: {f : α -> β}
  证明: strictMono_iff.trans by simp [StrictMono, bot_lt_coe]

@[to_dual]
alias ⟨_, _root_.StrictMono.withBot_map⟩ := strictMono_map_iff

@[to_dual]

Depends on / 依赖: StrictMono, bot_lt_coe, strictMono_iff, strictMono_iff.trans
-/
theorem strictMono_map_iff {f : α -> β} :
    StrictMono (WithBot.map f) ↔ StrictMono f :=
strictMono_iff.trans by simp [StrictMono, bot_lt_coe]

@[to_dual]
alias ⟨_, _root_.StrictMono.withBot_map⟩ := strictMono_map_iff

@[to_dual]
/--
lemma `map_le_iff` / 引理 `map_le_iff`

English:
lemma map_le_iff
  given: (f : α -> β) (mono_iff : forall {a b}, f a <= f b ↔ a <= b)
  proof: by cases x <;> cases y <;> simp [mono_iff]

@[to_dual coe_untopD_le]

中文:
引理 map_le_iff
  条件: (f : α -> β) (mono_iff : 对任意 {a b}, f a <= f b ↔ a <= b)
  证明: by cases x <;> cases y <;> simp [mono_iff]

@[to_dual coe_untopD_le]

Depends on / 依赖: mono_iff
-/
lemma map_le_iff (f : α -> β) (mono_iff : forall {a b}, f a <= f b ↔ a <= b) :
    x.map f <= y.map f ↔ x <= y := by cases x <;> cases y <;> simp [mono_iff]

@[to_dual coe_untopD_le]
/--
theorem `le_coe_unbotD` / 定理 `le_coe_unbotD`

English:
theorem le_coe_unbotD
  given: (x : WithBot α) (b : α)
  statement: x <= x.unbotD b
  proof: by cases x <;> simp

@[to_dual (attr := simp) coe_top_lt]

中文:
定理 le_coe_unbotD
  条件: (x : WithBot α) (b : α)
  结论: x <= x.unbotD b
  证明: by cases x <;> simp

@[to_dual (attr := simp) coe_top_lt]
-/
theorem le_coe_unbotD (x : WithBot α) (b : α) : x <= x.unbotD b := by cases x <;> simp

@[to_dual (attr := simp) coe_top_lt]
/--
theorem `lt_coe_bot` / 定理 `lt_coe_bot`

English:
theorem lt_coe_bot
  given: [OrderBot α]
  statement: x < (⊥ : α) ↔ x = ⊥
  proof: by cases x <;> simp

@[to_dual eq_top_iff_forall_gt]

中文:
定理 lt_coe_bot
  条件: [有底序 α]
  结论: x < (⊥ : α) ↔ x = ⊥
  证明: by cases x <;> simp

@[to_dual eq_top_iff_forall_gt]
-/
theorem lt_coe_bot [OrderBot α] : x < (⊥ : α) ↔ x = ⊥ := by cases x <;> simp

@[to_dual eq_top_iff_forall_gt]
/--
lemma `eq_bot_iff_forall_lt` / 引理 `eq_bot_iff_forall_lt`

English:
lemma eq_bot_iff_forall_lt
  statement: x = ⊥ ↔ forall b : α, x < b
  proof: by
  cases x <;> simp; simpa using ⟨_, lt_irrefl _⟩

@[to_dual eq_top_iff_forall_ge]

中文:
引理 eq_bot_iff_对任意_lt
  结论: x = ⊥ ↔ 对任意 b : α, x < b
  证明: by
  cases x <;> simp; simpa using ⟨_, lt_irrefl _⟩

@[to_dual eq_top_iff_forall_ge]

Depends on / 依赖: lt_irrefl
-/
lemma eq_bot_iff_forall_lt : x = ⊥ ↔ forall b : α, x < b := by
  cases x <;> simp; simpa using ⟨_, lt_irrefl _⟩

@[to_dual eq_top_iff_forall_ge]
/--
lemma `eq_bot_iff_forall_le` / 引理 `eq_bot_iff_forall_le`

English:
lemma eq_bot_iff_forall_le
  given: [NoBotOrder α]
  statement: x = ⊥ ↔ forall b : α, x <= b
  proof: by
  refine ⟨by simp +contextual, fun h => (x.eq_bot_iff_forall_ne).2 fun y => ?_⟩
  rintro rfl
  exact not_isBot y fun z => coe_le_coe.1 (h z)

@[to_dual forall_le_coe_iff_le]

中文:
引理 eq_bot_iff_对任意_le
  条件: [无底序 α]
  结论: x = ⊥ ↔ 对任意 b : α, x <= b
  证明: by
  refine ⟨by simp +contextual, fun h => (x.eq_bot_iff_forall_ne).2 fun y => ?_⟩
  rintro rfl
  exact not_isBot y fun z => coe_le_coe.1 (h z)

@[to_dual forall_le_coe_iff_le]

Depends on / 依赖: IsNoetherianRing, IsNoetherianRing.orzechProperty, coe_le_coe, contextual, eq_bot_iff_forall_ne, not_isBot, orzechProperty, x.eq_bot_iff_forall_ne
-/
lemma eq_bot_iff_forall_le [NoBotOrder α] : x = ⊥ ↔ forall b : α, x <= b := by
  refine ⟨by simp +contextual, fun h => (x.eq_bot_iff_forall_ne).2 fun y => ?_⟩
  rintro rfl
  exact not_isBot y fun z => coe_le_coe.1 (h z)

@[to_dual forall_le_coe_iff_le]
/--
lemma `forall_coe_le_iff_le` / 引理 `forall_coe_le_iff_le`

English:
lemma forall_coe_le_iff_le
  given: [NoBotOrder α]
  statement: (forall a : α, a <= x -> a <= y) ↔ x <= y
  proof: by
  obtain _ | a := x
  · simpa [WithBot.none_eq_bot, eq_bot_iff_forall_le] using! fun a ha => (not_isBot _ ha).elim
  · exact ⟨fun h => h _ le_rfl, fun hay b => hay.trans'⟩

@[to_dual forall_coe_le_iff_le]

中文:
引理 对任意_coe_le_iff_le
  条件: [无底序 α]
  结论: (对任意 a : α, a <= x -> a <= y) ↔ x <= y
  证明: by
  obtain _ | a := x
  · simpa [WithBot.none_eq_bot, eq_bot_iff_forall_le] using! fun a ha => (not_isBot _ ha).elim
  · exact ⟨fun h => h _ le_rfl, fun hay b => hay.trans'⟩

@[to_dual forall_coe_le_iff_le]

Depends on / 依赖: IsNoetherianRing, IsNoetherianRing.wfDvdMonoid, WithBot, WithBot.none_eq_bot, eq_bot_iff_forall_le, hay.trans, le_rfl, none_eq_bot, not_isBot, wfDvdMonoid
-/
lemma forall_coe_le_iff_le [NoBotOrder α] : (forall a : α, a <= x -> a <= y) ↔ x <= y := by
  obtain _ | a := x
  · simpa [WithBot.none_eq_bot, eq_bot_iff_forall_le] using! fun a ha => (not_isBot _ ha).elim
  · exact ⟨fun h => h _ le_rfl, fun hay b => hay.trans'⟩

@[to_dual forall_coe_le_iff_le]
/--
lemma `forall_le_coe_iff_le` / 引理 `forall_le_coe_iff_le`

English:
lemma forall_le_coe_iff_le
  given: [NoBotOrder α]
  statement: (forall a : α, y <= a -> x <= a) ↔ x <= y
  proof: by
  obtain _ | y := y
  · simp [WithBot.none_eq_bot, eq_bot_iff_forall_le]
  · exact ⟨fun h => h _ le_rfl, fun hmn a ham => hmn.trans ham⟩

@[to_dual (attr := simp) forall_lt_coe]

中文:
引理 对任意_le_coe_iff_le
  条件: [无底序 α]
  结论: (对任意 a : α, y <= a -> x <= a) ↔ x <= y
  证明: by
  obtain _ | y := y
  · simp [WithBot.none_eq_bot, eq_bot_iff_forall_le]
  · exact ⟨fun h => h _ le_rfl, fun hmn a ham => hmn.trans ham⟩

@[to_dual (attr := simp) forall_lt_coe]

Depends on / 依赖: WithBot, WithBot.none_eq_bot, eq_bot_iff_forall_le, hmn.trans, le_rfl, none_eq_bot
-/
lemma forall_le_coe_iff_le [NoBotOrder α] : (forall a : α, y <= a -> x <= a) ↔ x <= y := by
  obtain _ | y := y
  · simp [WithBot.none_eq_bot, eq_bot_iff_forall_le]
  · exact ⟨fun h => h _ le_rfl, fun hmn a ham => hmn.trans ham⟩

@[to_dual (attr := simp) forall_lt_coe]
/--
theorem `forall_coe_lt` / 定理 `forall_coe_lt`

English:
theorem forall_coe_lt
  given: {p : WithBot α -> Prop}
  proof: by
  simp [WithBot.forall]

@[to_dual (attr := simp) exists_lt_coe]

中文:
定理 对任意_coe_lt
  条件: {p : WithBot α -> 命题}
  证明: by
  simp [WithBot.forall]

@[to_dual (attr := simp) exists_lt_coe]

Depends on / 依赖: WithBot, WithBot.forall
-/
theorem forall_coe_lt {p : WithBot α -> Prop} :
    (forall x, (a : WithBot α) < x -> p x) ↔ forall b, a < b -> p b := by
  simp [WithBot.forall]

@[to_dual (attr := simp) exists_lt_coe]
/--
theorem `exists_coe_lt` / 定理 `exists_coe_lt`

English:
theorem exists_coe_lt
  given: {p : WithBot α -> Prop}
  proof: by
  simp [WithBot.exists]

@[to_dual (attr := simp) forall_le_coe]

中文:
定理 存在_coe_lt
  条件: {p : WithBot α -> 命题}
  证明: by
  simp [WithBot.exists]

@[to_dual (attr := simp) forall_le_coe]

Depends on / 依赖: WithBot, WithBot.exists
-/
theorem exists_coe_lt {p : WithBot α -> Prop} :
    (exists x, (a : WithBot α) < x ∧ p x) ↔ exists b, a < b ∧ p b := by
  simp [WithBot.exists]

@[to_dual (attr := simp) forall_le_coe]
/--
theorem `forall_coe_le` / 定理 `forall_coe_le`

English:
theorem forall_coe_le
  given: {p : WithBot α -> Prop}
  proof: by
  simp [WithBot.forall]

@[to_dual (attr := simp) exists_le_coe]

中文:
定理 对任意_coe_le
  条件: {p : WithBot α -> 命题}
  证明: by
  simp [WithBot.forall]

@[to_dual (attr := simp) exists_le_coe]

Depends on / 依赖: WithBot, WithBot.forall
-/
theorem forall_coe_le {p : WithBot α -> Prop} :
    (forall x, (a : WithBot α) <= x -> p x) ↔ forall b, a <= b -> p b := by
  simp [WithBot.forall]

@[to_dual (attr := simp) exists_le_coe]
/--
theorem `exists_coe_le` / 定理 `exists_coe_le`

English:
theorem exists_coe_le
  given: {p : WithBot α -> Prop}
  proof: by
  simp [WithBot.exists]

中文:
定理 存在_coe_le
  条件: {p : WithBot α -> 命题}
  证明: by
  simp [WithBot.exists]

Depends on / 依赖: WithBot, WithBot.exists
-/
theorem exists_coe_le {p : WithBot α -> Prop} :
    (exists x, (a : WithBot α) <= x ∧ p x) ↔ exists b, a <= b ∧ p b := by
  simp [WithBot.exists]

end Preorder

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: α] : PartialOrder (WithBot α) where
  body: by cases x <;> cases y <;> simp [le_def]; simpa using le_antisymm

中文:
实例 [偏序
  签名: α] : 偏序 (WithBot α) where
  定义体: by cases x <;> cases y <;> simp [le_def]; simpa using le_antisymm

Depends on / 依赖: le_antisymm, le_def
-/
instance [PartialOrder α] : PartialOrder (WithBot α) where
  le_antisymm x y := by cases x <;> cases y <;> simp [le_def]; simpa using le_antisymm

section PartialOrder
variable [PartialOrder α] {x y : WithBot α} {a b : α}

@[to_dual untopD_le]
/--
lemma `le_unbotD` / 引理 `le_unbotD`

English:
lemma le_unbotD
  given: (hy : b <= y)
  statement: b <= y.unbotD a
  proof: by
  rwa [le_unbotD_iff]
  exact ne_bot_of_le_ne_bot (by simp) hy

@[to_dual untopA_le]

中文:
引理 le_unbotD
  条件: (hy : b <= y)
  结论: b <= y.unbotD a
  证明: by
  rwa [le_unbotD_iff]
  exact ne_bot_of_le_ne_bot (by simp) hy

@[to_dual untopA_le]

Depends on / 依赖: le_unbotD_iff, ne_bot_of_le_ne_bot
-/
lemma le_unbotD (hy : b <= y) : b <= y.unbotD a := by
  rwa [le_unbotD_iff]
  exact ne_bot_of_le_ne_bot (by simp) hy

@[to_dual untopA_le]
/--
lemma `le_unbotA` / 引理 `le_unbotA`

English:
lemma le_unbotA
  given: [Nonempty α] (hy : b <= y)
  statement: b <= y.unbotA
  proof: le_unbotD hy

@[to_dual eq_bot_iff_forall_le]

中文:
引理 le_unbotA
  条件: [非空 α] (hy : b <= y)
  结论: b <= y.unbotA
  证明: le_unbotD hy

@[to_dual eq_bot_iff_forall_le]

Depends on / 依赖: le_unbotD
-/
lemma le_unbotA [Nonempty α] (hy : b <= y) : b <= y.unbotA := le_unbotD hy

@[to_dual eq_bot_iff_forall_le]
/--
lemma `eq_top_iff_forall_ge` / 引理 `eq_top_iff_forall_ge`

English:
lemma eq_top_iff_forall_ge
  given: [Nonempty α] [NoTopOrder α] {x : WithBot (WithTop α)}
  proof: by
  refine ⟨by simp_all, fun H => ?_⟩
  induction x
  · simp at H
  · simpa [WithTop.eq_top_iff_forall_ge] using H

中文:
引理 eq_top_iff_对任意_ge
  条件: [非空 α] [无顶序 α] {x : WithBot (WithTop α)}
  证明: by
  refine ⟨by simp_all, fun H => ?_⟩
  induction x
  · simp at H
  · simpa [WithTop.eq_top_iff_forall_ge] using H

Depends on / 依赖: WithTop, WithTop.eq_top_iff_forall_ge, eq_top_iff_forall_ge
-/
lemma eq_top_iff_forall_ge [Nonempty α] [NoTopOrder α] {x : WithBot (WithTop α)} :
    x = ⊤ ↔ forall a : α, a <= x := by
  refine ⟨by simp_all, fun H => ?_⟩
  induction x
  · simp at H
  · simpa [WithTop.eq_top_iff_forall_ge] using H

variable [NoBotOrder α]

@[to_dual eq_of_forall_le_coe_iff]
/--
lemma `eq_of_forall_coe_le_iff` / 引理 `eq_of_forall_coe_le_iff`

English:
lemma eq_of_forall_coe_le_iff
  given: (h : forall a : α, a <= x ↔ a <= y)
  statement: x = y
  proof: le_antisymm (forall_coe_le_iff_le.mp fun a => (h a).1) (forall_coe_le_iff_le.mp fun a => (h a).2)

@[to_dual eq_of_forall_coe_le_iff]

中文:
引理 eq_of_对任意_coe_le_iff
  条件: (h : 对任意 a : α, a <= x ↔ a <= y)
  结论: x = y
  证明: le_antisymm (forall_coe_le_iff_le.mp fun a => (h a).1) (forall_coe_le_iff_le.mp fun a => (h a).2)

@[to_dual eq_of_forall_coe_le_iff]

Depends on / 依赖: forall_coe_le_iff_le, forall_coe_le_iff_le.mp, le_antisymm
-/
lemma eq_of_forall_coe_le_iff (h : forall a : α, a <= x ↔ a <= y) : x = y :=
  le_antisymm (forall_coe_le_iff_le.mp fun a => (h a).1) (forall_coe_le_iff_le.mp fun a => (h a).2)

@[to_dual eq_of_forall_coe_le_iff]
/--
lemma `eq_of_forall_le_coe_iff` / 引理 `eq_of_forall_le_coe_iff`

English:
lemma eq_of_forall_le_coe_iff
  given: (h : forall a : α, x <= a ↔ y <= a)
  statement: x = y
  proof: le_antisymm (forall_le_coe_iff_le.mp fun a => (h a).2) (forall_le_coe_iff_le.mp fun a => (h a).1)

中文:
引理 eq_of_对任意_le_coe_iff
  条件: (h : 对任意 a : α, x <= a ↔ y <= a)
  结论: x = y
  证明: le_antisymm (forall_le_coe_iff_le.mp fun a => (h a).2) (forall_le_coe_iff_le.mp fun a => (h a).1)

Depends on / 依赖: forall_le_coe_iff_le, forall_le_coe_iff_le.mp, le_antisymm
-/
lemma eq_of_forall_le_coe_iff (h : forall a : α, x <= a ↔ y <= a) : x = y :=
  le_antisymm (forall_le_coe_iff_le.mp fun a => (h a).2) (forall_le_coe_iff_le.mp fun a => (h a).1)

end PartialOrder

/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: [SemilatticeSup α]
  body: by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

@[to_dual existing]

中文:
实例 semilatticeSup
  签名: [SemilatticeSup α]
  定义体: by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

@[to_dual existing]

Depends on / 依赖: le_sup_right, sup_le
-/
instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithBot α) where
  sup
    -- note this is `Option.merge`, but with the right defeq when unfolding
    | ⊥, ⊥ => ⊥
    | (a : α), ⊥ => a
    | ⊥, (b : α) => b
    | (a : α), (b : α) => ↑(a ⊔ b)
  le_sup_left x y := by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

@[to_dual existing]
/--
Instance `_root_.WithTop.semilatticeInf` / 实例 `_root_.WithTop.semilatticeInf`

English:
instance _root_.WithTop.semilatticeInf
  signature: [SemilatticeInf α]
  body: by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

中文:
实例 _root_.WithTop.semilatticeInf
  签名: [SemilatticeInf α]
  定义体: by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

Depends on / 依赖: inf_le_right, le_inf
-/
instance _root_.WithTop.semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithTop α) where
  inf
    -- note this is `Option.merge`, but with the right defeq when unfolding
    | ⊤, ⊤ => ⊤
    | (a : α), ⊤ => a
    | ⊤, (b : α) => b
    | (a : α), (b : α) => ↑(a ⊓ b)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

/--
Instance `semilatticeInf` / 实例 `semilatticeInf`

English:
instance semilatticeInf
  signature: [SemilatticeInf α]
  body: .map₂ (· ⊓ ·)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

@[to_dual existing]

中文:
实例 semilatticeInf
  签名: [SemilatticeInf α]
  定义体: .map₂ (· ⊓ ·)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

@[to_dual existing]
-/
instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithBot α) where
  inf := .map₂ (· ⊓ ·)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

@[to_dual existing]
/--
Instance `_root_.WithTop.semilatticeSup` / 实例 `_root_.WithTop.semilatticeSup`

English:
instance _root_.WithTop.semilatticeSup
  signature: [SemilatticeSup α]
  body: .map₂ (· ⊔ ·)
  le_sup_left x y := by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

@[to_dual (attr := simp, norm_cast)]

中文:
实例 _root_.WithTop.semilatticeSup
  签名: [SemilatticeSup α]
  定义体: .map₂ (· ⊔ ·)
  le_sup_left x y := by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

@[to_dual (attr := simp, norm_cast)]
-/
instance _root_.WithTop.semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithTop α) where
  sup := .map₂ (· ⊔ ·)
  le_sup_left x y := by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: [SemilatticeSup α] (a b : α)
  proof: rfl

@[to_dual (attr := simp, norm_cast)]

中文:
定理 coe_sup
  条件: [SemilatticeSup α] (a b : α)
  证明: rfl

@[to_dual (attr := simp, norm_cast)]
-/
theorem coe_sup [SemilatticeSup α] (a b : α) :
    ((a ⊔ b : α) : WithBot α) = (a : WithBot α) ⊔ b := rfl

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: [SemilatticeInf α] (a b : α)
  proof: rfl

中文:
定理 coe_inf
  条件: [SemilatticeInf α] (a b : α)
  证明: rfl
-/
theorem coe_inf [SemilatticeInf α] (a b : α) :
    ((a ⊓ b : α) : WithBot α) = (a : WithBot α) ⊓ b := rfl

/--
Instance `lattice` / 实例 `lattice`

English:
instance lattice
  signature: [Lattice α]

中文:
实例 lattice
  签名: [格 α]
-/
instance lattice [Lattice α] : Lattice (WithBot α) where

@[to_dual existing]
/--
Instance `_root_.WithTop.lattice` / 实例 `_root_.WithTop.lattice`

English:
instance _root_.WithTop.lattice
  signature: [Lattice α]

中文:
实例 _root_.WithTop.lattice
  签名: [格 α]
-/
instance _root_.WithTop.lattice [Lattice α] : Lattice (WithTop α) where

/--
Instance `distribLattice` / 实例 `distribLattice`

English:
instance distribLattice
  signature: [DistribLattice α]
  body: by
    cases x <;> cases y <;> cases z <;> simp [← coe_inf, ← coe_sup]
    simpa [← coe_inf, ← coe_sup] using le_sup_inf

@[to_dual existing]

中文:
实例 distribLattice
  签名: [Distrib格 α]
  定义体: by
    cases x <;> cases y <;> cases z <;> simp [← coe_inf, ← coe_sup]
    simpa [← coe_inf, ← coe_sup] using le_sup_inf

@[to_dual existing]

Depends on / 依赖: coe_inf, coe_sup, le_sup_inf
-/
instance distribLattice [DistribLattice α] : DistribLattice (WithBot α) where
  le_sup_inf x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_inf, ← coe_sup]
    simpa [← coe_inf, ← coe_sup] using le_sup_inf

@[to_dual existing]
/--
Instance `_root_.WithTop.distribLattice` / 实例 `_root_.WithTop.distribLattice`

English:
instance _root_.WithTop.distribLattice
  signature: [DistribLattice α]
  body: by
    cases x <;> cases y <;> cases z <;> simp [← WithTop.coe_inf, ← WithTop.coe_sup]
    simpa [← coe_inf, ← coe_sup] using le_sup_inf

@[to_dual]

中文:
实例 _root_.WithTop.distribLattice
  签名: [Distrib格 α]
  定义体: by
    cases x <;> cases y <;> cases z <;> simp [← WithTop.coe_inf, ← WithTop.coe_sup]
    simpa [← coe_inf, ← coe_sup] using le_sup_inf

@[to_dual]

Depends on / 依赖: WithTop, WithTop.coe_inf, WithTop.coe_sup, coe_inf, coe_sup, le_sup_inf
-/
instance _root_.WithTop.distribLattice [DistribLattice α] : DistribLattice (WithTop α) where
  le_sup_inf x y z := by
    cases x <;> cases y <;> cases z <;> simp [← WithTop.coe_inf, ← WithTop.coe_sup]
    simpa [← coe_inf, ← coe_sup] using le_sup_inf

@[to_dual]
/--
Instance `decidableEq` / 实例 `decidableEq`

English:
instance decidableEq
  signature: [DecidableEq α]
  body: inferInstanceAs DecidableEq (Option α)

@[to_dual]

中文:
实例 decidableEq
  签名: [DecidableEq α]
  定义体: inferInstanceAs DecidableEq (Option α)

@[to_dual]

Depends on / 依赖: DecidableEq
-/
instance decidableEq [DecidableEq α] : DecidableEq (WithBot α) :=
inferInstanceAs DecidableEq (Option α)

@[to_dual]
/--
Instance `decidableLE` / 实例 `decidableLE`

English:
instance decidableLE
  signature: [LE α] [DecidableLE α]

中文:
实例 decidableLE
  签名: [LE α] [DecidableLE α]
-/
instance decidableLE [LE α] [DecidableLE α] : DecidableLE (WithBot α)
| ⊥, _ => isTrue by simp
| (a : α), ⊥ => isFalse by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_le_coe

@[to_dual]
/--
Instance `decidableLT` / 实例 `decidableLT`

English:
instance decidableLT
  signature: [LT α] [DecidableLT α]

中文:
实例 decidableLT
  签名: [LT α] [DecidableLT α]
-/
instance decidableLT [LT α] [DecidableLT α] : DecidableLT (WithBot α)
| _, ⊥ => isFalse by simp
| ⊥, (a : α) => isTrue by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_lt_coe

/--
Instance `total_le` / 实例 `total_le`

English:
instance total_le
  signature: [LE α] [@Std.Total α (· <= ·)]
  body: by cases x <;> cases y <;> simp; simpa using Std.Total.total ..

中文:
实例 total_le
  签名: [LE α] [@Std.全 α (· <= ·)]
  定义体: by cases x <;> cases y <;> simp; simpa using Std.Total.total ..

Depends on / 依赖: Std.Total.total
-/
instance total_le [LE α] [@Std.Total α (· <= ·)] : @Std.Total (WithBot α) (· <= ·) where
  total x y := by cases x <;> cases y <;> simp; simpa using Std.Total.total ..

/--
Instance `_root_.WithTop.total_le` / 实例 `_root_.WithTop.total_le`

English:
instance _root_.WithTop.total_le
  signature: [LE α] [@Std.Total α (· <= ·)]
  body: by cases x <;> cases y <;> simp; simpa using Std.Total.total ..

中文:
实例 _root_.WithTop.total_le
  签名: [LE α] [@Std.全 α (· <= ·)]
  定义体: by cases x <;> cases y <;> simp; simpa using Std.Total.total ..

Depends on / 依赖: Std.Total.total
-/
instance _root_.WithTop.total_le [LE α] [@Std.Total α (· <= ·)] :
    @Std.Total (WithTop α) (· <= ·) where
  total x y := by cases x <;> cases y <;> simp; simpa using Std.Total.total ..

/--
Instance `linearOrder` / 实例 `linearOrder`

English:
instance linearOrder
  signature: [LinearOrder α]
  body: Lattice.toLinearOrder _

@[to_dual existing]

中文:
实例 linearOrder
  签名: [线性序 α]
  定义体: Lattice.toLinearOrder _

@[to_dual existing]

Depends on / 依赖: Lattice, Lattice.toLinearOrder, toLinearOrder
-/
instance linearOrder [LinearOrder α] : LinearOrder (WithBot α) := Lattice.toLinearOrder _

@[to_dual existing]
/--
Instance `_root_.WithTop.linearOrder` / 实例 `_root_.WithTop.linearOrder`

English:
instance _root_.WithTop.linearOrder
  signature: [LinearOrder α]
  body: Lattice.toLinearOrder _

@[to_dual]

中文:
实例 _root_.WithTop.linearOrder
  签名: [线性序 α]
  定义体: Lattice.toLinearOrder _

@[to_dual]

Depends on / 依赖: Lattice, Lattice.toLinearOrder, toLinearOrder
-/
instance _root_.WithTop.linearOrder [LinearOrder α] : LinearOrder (WithTop α) :=
  Lattice.toLinearOrder _

@[to_dual]
/--
Instance `instWellFoundedLT` / 实例 `instWellFoundedLT`

English:
instance instWellFoundedLT
  signature: [LT α] [WellFoundedLT α]
  body: .intro fun
  | ⊥ => ⟨_, by simp⟩
  | (a : α) => (wellFounded_lt.1 a).rec fun _ _ ih => .intro _ fun
    | ⊥, _ => ⟨_, by simp⟩
    | (b : α), hlt => ih _ (coe_lt_coe.1 hlt)

@[to_dual]

中文:
实例 instWellFoundedLT
  签名: [LT α] [WellFoundedLT α]
  定义体: .intro fun
  | ⊥ => ⟨_, by simp⟩
  | (a : α) => (wellFounded_lt.1 a).rec fun _ _ ih => .intro _ fun
    | ⊥, _ => ⟨_, by simp⟩
    | (b : α), hlt => ih _ (coe_lt_coe.1 hlt)

@[to_dual]
-/
instance instWellFoundedLT [LT α] [WellFoundedLT α] : WellFoundedLT (WithBot α) where
  wf := .intro fun
  | ⊥ => ⟨_, by simp⟩
  | (a : α) => (wellFounded_lt.1 a).rec fun _ _ ih => .intro _ fun
    | ⊥, _ => ⟨_, by simp⟩
    | (b : α), hlt => ih _ (coe_lt_coe.1 hlt)

@[to_dual]
/--
Instance `instWellFoundedGT` / 实例 `instWellFoundedGT`

English:
instance instWellFoundedGT
  signature: [LT α] [WellFoundedGT α]
  body: have acc_some (a : α) : @Acc (WithBot α) (· > ·) a :=
    (wellFounded_gt.1 a).rec fun _ _ ih => ⟨_, by simpa [WithBot.forall]⟩
  .intro fun
    | (a : α) => acc_some a
    | ⊥ => ⟨_, by simpa [WithBot.forall]⟩

中文:
实例 instWellFoundedGT
  签名: [LT α] [WellFoundedGT α]
  定义体: have acc_some (a : α) : @Acc (WithBot α) (· > ·) a :=
    (wellFounded_gt.1 a).rec fun _ _ ih => ⟨_, by simpa [WithBot.forall]⟩
  .intro fun
    | (a : α) => acc_some a
    | ⊥ => ⟨_, by simpa [WithBot.forall]⟩

Depends on / 依赖: WithBot, acc_some
-/
instance instWellFoundedGT [LT α] [WellFoundedGT α] : WellFoundedGT (WithBot α) where
  wf := have acc_some (a : α) : @Acc (WithBot α) (· > ·) a :=
    (wellFounded_gt.1 a).rec fun _ _ ih => ⟨_, by simpa [WithBot.forall]⟩
  .intro fun
    | (a : α) => acc_some a
    | ⊥ => ⟨_, by simpa [WithBot.forall]⟩

/--
lemma `denselyOrdered_iff` / 引理 `denselyOrdered_iff`

English:
lemma denselyOrdered_iff
  given: [LT α] [NoMinOrder α]
  proof: by
  constructor <;> intro h <;> constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := exists_between (WithBot.coe_lt_coe.mpr hab)
    induction c with
    | bot => simp at hc
    | coe c => exact ⟨c, by simpa using hc⟩
  · simpa [WithBot.exists, WithBot.forall, exists_lt] using DenselyOrdered.dense



中文:
引理 denselyOrdered_iff
  条件: [LT α] [NoMin序 α]
  证明: by
  constructor <;> intro h <;> constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := exists_between (WithBot.coe_lt_coe.mpr hab)
    induction c with
    | bot => simp at hc
    | coe c => exact ⟨c, by simpa using hc⟩
  · simpa [WithBot.exists, WithBot.forall, exists_lt] using DenselyOrdered.dense



Depends on / 依赖: DenselyOrdered, DenselyOrdered.dense, WithBot, WithBot.coe_lt_coe.mpr, WithBot.exists, WithBot.forall, coe_lt_coe, exists_between, exists_lt
-/
lemma denselyOrdered_iff [LT α] [NoMinOrder α] :
    DenselyOrdered (WithBot α) ↔ DenselyOrdered α := by
  constructor <;> intro h <;> constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := exists_between (WithBot.coe_lt_coe.mpr hab)
    induction c with
    | bot => simp at hc
    | coe c => exact ⟨c, by simpa using hc⟩
  · simpa [WithBot.exists, WithBot.forall, exists_lt] using DenselyOrdered.dense

@[to_dual existing]
/--
lemma `_root_.WithTop.denselyOrdered_iff` / 引理 `_root_.WithTop.denselyOrdered_iff`

English:
lemma _root_.WithTop.denselyOrdered_iff
  given: [LT α] [NoMaxOrder α]
  proof: by
  constructor <;> intro h <;> constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := exists_between (WithTop.coe_lt_coe.mpr hab)
    induction c with
    | top => simp at hc
    | coe c => exact ⟨c, by simpa using hc⟩
  · simpa [WithTop.exists, WithTop.forall, exists_gt] using DenselyOrdered.dense



中文:
引理 _root_.WithTop.denselyOrdered_iff
  条件: [LT α] [NoMax序 α]
  证明: by
  constructor <;> intro h <;> constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := exists_between (WithTop.coe_lt_coe.mpr hab)
    induction c with
    | top => simp at hc
    | coe c => exact ⟨c, by simpa using hc⟩
  · simpa [WithTop.exists, WithTop.forall, exists_gt] using DenselyOrdered.dense



Depends on / 依赖: DenselyOrdered, DenselyOrdered.dense, WithTop, WithTop.coe_lt_coe.mpr, WithTop.exists, WithTop.forall, coe_lt_coe, exists_between, exists_gt
-/
lemma _root_.WithTop.denselyOrdered_iff [LT α] [NoMaxOrder α] :
    DenselyOrdered (WithTop α) ↔ DenselyOrdered α := by
  constructor <;> intro h <;> constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := exists_between (WithTop.coe_lt_coe.mpr hab)
    induction c with
    | top => simp at hc
    | coe c => exact ⟨c, by simpa using hc⟩
  · simpa [WithTop.exists, WithTop.forall, exists_gt] using DenselyOrdered.dense

@[to_dual]
/--
Instance `denselyOrdered` / 实例 `denselyOrdered`

English:
instance denselyOrdered
  signature: [LT α] [DenselyOrdered α] [NoMinOrder α]
  body: denselyOrdered_iff.mpr inferInstance

中文:
实例 denselyOrdered
  签名: [LT α] [稠密序 α] [NoMin序 α]
  定义体: denselyOrdered_iff.mpr inferInstance

Depends on / 依赖: denselyOrdered_iff, denselyOrdered_iff.mpr
-/
instance denselyOrdered [LT α] [DenselyOrdered α] [NoMinOrder α] :
    DenselyOrdered (WithBot α) :=
  denselyOrdered_iff.mpr inferInstance

/--
Instance `trichotomous.lt` / 实例 `trichotomous.lt`

English:
instance trichotomous.lt
  signature: [Preorder α] [@Std.Trichotomous α (· < ·)]
  body: Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} => by
    cases x <;> cases y <;> simp [trichotomous]

中文:
实例 trichotomous.lt
  签名: [预序 α] [@Std.三歧 α (· < ·)]
  定义体: Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} => by
    cases x <;> cases y <;> simp [trichotomous]

Depends on / 依赖: Std.trichotomous_of_rel_or_eq_or_rel_swap, trichotomous, trichotomous_of_rel_or_eq_or_rel_swap
-/
instance trichotomous.lt [Preorder α] [@Std.Trichotomous α (· < ·)] :
    @Std.Trichotomous (WithBot α) (· < ·) :=
  Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} => by
    cases x <;> cases y <;> simp [trichotomous]

/--
Instance `_root_.WithTop.trichotomous.lt` / 实例 `_root_.WithTop.trichotomous.lt`

English:
instance _root_.WithTop.trichotomous.lt
  signature: [Preorder α] [@Std.Trichotomous α (· < ·)]
  body: Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} => by
    cases x <;> cases y <;> simp [trichotomous]

中文:
实例 _root_.WithTop.trichotomous.lt
  签名: [预序 α] [@Std.三歧 α (· < ·)]
  定义体: Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} => by
    cases x <;> cases y <;> simp [trichotomous]

Depends on / 依赖: Std.trichotomous_of_rel_or_eq_or_rel_swap, trichotomous, trichotomous_of_rel_or_eq_or_rel_swap
-/
instance _root_.WithTop.trichotomous.lt [Preorder α] [@Std.Trichotomous α (· < ·)] :
    @Std.Trichotomous (WithTop α) (· < ·) :=
  Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} => by
    cases x <;> cases y <;> simp [trichotomous]

-- TODO: the hypotheses are equivalent to `LinearOrder` + `WellFoundedLT`, remove this.
/--
Instance `IsWellOrder.lt` / 实例 `IsWellOrder.lt`

English:
instance IsWellOrder.lt
  signature: [Preorder α] [IsWellOrder α (· < ·)]

中文:
实例 是良序.lt
  签名: [预序 α] [是良序 α (· < ·)]
-/
instance IsWellOrder.lt [Preorder α] [IsWellOrder α (· < ·)] :
  IsWellOrder (WithBot α) (· < ·) where

-- TODO: the hypotheses are equivalent to `LinearOrder` + `WellFoundedLT`, remove this.
/--
Instance `_root_.WithTop.IsWellOrder.lt` / 实例 `_root_.WithTop.IsWellOrder.lt`

English:
instance _root_.WithTop.IsWellOrder.lt
  signature: [Preorder α] [IsWellOrder α (· < ·)]

中文:
实例 _root_.WithTop.是良序.lt
  签名: [预序 α] [是良序 α (· < ·)]
-/
instance _root_.WithTop.IsWellOrder.lt [Preorder α] [IsWellOrder α (· < ·)] :
  IsWellOrder (WithTop α) (· < ·) where

/--
Instance `trichotomous.gt` / 实例 `trichotomous.gt`

English:
instance trichotomous.gt
  signature: [Preorder α] [@Std.Trichotomous α (· > ·)]
  body: have : @Std.Trichotomous α (· < ·) := inferInstanceAs Std.Trichotomous Function.swap _
  inferInstance

中文:
实例 trichotomous.gt
  签名: [预序 α] [@Std.三歧 α (· > ·)]
  定义体: have : @Std.Trichotomous α (· < ·) := inferInstanceAs Std.Trichotomous Function.swap _
  inferInstance

Depends on / 依赖: Function, Function.swap, Std.Trichotomous, Trichotomous
-/
instance trichotomous.gt [Preorder α] [@Std.Trichotomous α (· > ·)] :
    @Std.Trichotomous (WithBot α) (· > ·) :=
have : @Std.Trichotomous α (· < ·) := inferInstanceAs Std.Trichotomous Function.swap _
  inferInstance

/--
Instance `_root_.WithTop.trichotomous.gt` / 实例 `_root_.WithTop.trichotomous.gt`

English:
instance _root_.WithTop.trichotomous.gt
  signature: [Preorder α] [@Std.Trichotomous α (· > ·)]
  body: have : @Std.Trichotomous α (· < ·) := inferInstanceAs Std.Trichotomous Function.swap _
  inferInstance

中文:
实例 _root_.WithTop.trichotomous.gt
  签名: [预序 α] [@Std.三歧 α (· > ·)]
  定义体: have : @Std.Trichotomous α (· < ·) := inferInstanceAs Std.Trichotomous Function.swap _
  inferInstance

Depends on / 依赖: Function, Function.swap, Std.Trichotomous, Trichotomous
-/
instance _root_.WithTop.trichotomous.gt [Preorder α] [@Std.Trichotomous α (· > ·)] :
    @Std.Trichotomous (WithTop α) (· > ·) :=
have : @Std.Trichotomous α (· < ·) := inferInstanceAs Std.Trichotomous Function.swap _
  inferInstance

-- TODO: the hypotheses are equivalent to `LinearOrder` + `WellFoundedGT`, remove this.
/--
Instance `IsWellOrder.gt` / 实例 `IsWellOrder.gt`

English:
instance IsWellOrder.gt
  signature: [Preorder α] [IsWellOrder α (· > ·)]

中文:
实例 是良序.gt
  签名: [预序 α] [是良序 α (· > ·)]
-/
instance IsWellOrder.gt [Preorder α] [IsWellOrder α (· > ·)] :
    IsWellOrder (WithBot α) (· > ·) where

-- TODO: the hypotheses are equivalent to `LinearOrder` + `WellFoundedGT`, remove this.
/--
Instance `_root_.WithTop.IsWellOrder.gt` / 实例 `_root_.WithTop.IsWellOrder.gt`

English:
instance _root_.WithTop.IsWellOrder.gt
  signature: [Preorder α] [IsWellOrder α (· > ·)]

中文:
实例 _root_.WithTop.是良序.gt
  签名: [预序 α] [是良序 α (· > ·)]
-/
instance _root_.WithTop.IsWellOrder.gt [Preorder α] [IsWellOrder α (· > ·)] :
    IsWellOrder (WithTop α) (· > ·) where

section LinearOrder
variable [LinearOrder α] {x y : WithBot α}

@[to_dual]
/--
lemma `coe_min` / 引理 `coe_min`

English:
lemma coe_min
  given: (a b : α)
  statement: ↑(min a b) = min (a : WithBot α) b
  proof: rfl
@[to_dual]

中文:
引理 coe_min
  条件: (a b : α)
  结论: ↑(最小值 a b) = 最小值 (a : WithBot α) b
  证明: rfl
@[to_dual]
-/
lemma coe_min (a b : α) : ↑(min a b) = min (a : WithBot α) b := rfl
@[to_dual]
/--
lemma `coe_max` / 引理 `coe_max`

English:
lemma coe_max
  given: (a b : α)
  statement: ↑(max a b) = max (a : WithBot α) b
  proof: rfl

中文:
引理 coe_max
  条件: (a b : α)
  结论: ↑(最大值 a b) = 最大值 (a : WithBot α) b
  证明: rfl
-/
lemma coe_max (a b : α) : ↑(max a b) = max (a : WithBot α) b := rfl

variable [DenselyOrdered α] [NoMinOrder α]

@[to_dual ge_of_forall_gt_iff_ge]
/--
lemma `le_of_forall_lt_iff_le` / 引理 `le_of_forall_lt_iff_le`

English:
lemma le_of_forall_lt_iff_le
  statement: (forall z : α, x < z -> y <= z) ↔ y <= x
  proof: by
  cases x <;> cases y <;> simp [exists_lt, forall_gt_imp_ge_iff_le_of_dense]

@[to_dual le_of_forall_lt_iff_le]

中文:
引理 le_of_对任意_lt_iff_le
  结论: (对任意 z : α, x < z -> y <= z) ↔ y <= x
  证明: by
  cases x <;> cases y <;> simp [exists_lt, forall_gt_imp_ge_iff_le_of_dense]

@[to_dual le_of_forall_lt_iff_le]

Depends on / 依赖: exists_lt, forall_gt_imp_ge_iff_le_of_dense
-/
lemma le_of_forall_lt_iff_le : (forall z : α, x < z -> y <= z) ↔ y <= x := by
  cases x <;> cases y <;> simp [exists_lt, forall_gt_imp_ge_iff_le_of_dense]

@[to_dual le_of_forall_lt_iff_le]
/--
lemma `ge_of_forall_gt_iff_ge` / 引理 `ge_of_forall_gt_iff_ge`

English:
lemma ge_of_forall_gt_iff_ge
  statement: (forall z : α, z < x -> z <= y) ↔ x <= y
  proof: by
  cases x <;> cases y <;> simp [exists_lt, forall_lt_imp_le_iff_le_of_dense]

中文:
引理 ge_of_对任意_gt_iff_ge
  结论: (对任意 z : α, z < x -> z <= y) ↔ x <= y
  证明: by
  cases x <;> cases y <;> simp [exists_lt, forall_lt_imp_le_iff_le_of_dense]

Depends on / 依赖: exists_lt, forall_lt_imp_le_iff_le_of_dense
-/
lemma ge_of_forall_gt_iff_ge : (forall z : α, z < x -> z <= y) ↔ x <= y := by
  cases x <;> cases y <;> simp [exists_lt, forall_lt_imp_le_iff_le_of_dense]

end LinearOrder

@[to_dual lt_iff_exists_coe_btwn']
/--
theorem `lt_iff_exists_coe_btwn` / 定理 `lt_iff_exists_coe_btwn`

English:
theorem lt_iff_exists_coe_btwn
  given: [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α}
  proof: ⟨fun h =>
    let ⟨_, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨_, hx⟩ => lt_trans hx.1 hx.2⟩

@[to_dual lt_iff_exists_coe_btwn]

中文:
定理 lt_iff_存在_coe_btwn
  条件: [预序 α] [稠密序 α] [NoMin序 α] {a b : WithBot α}
  证明: ⟨fun h =>
    let ⟨_, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨_, hx⟩ => lt_trans hx.1 hx.2⟩

@[to_dual lt_iff_exists_coe_btwn]

Depends on / 依赖: NonUnitalCommSemiring, NonUnitalNonAssocRing, NonUnitalSubsemiring, NonUnitalSubsemiring.center, center, exists_between, lt_iff_exists_coe, lt_trans
-/
theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α} :
    a < b ↔ exists x : α, a < x ∧ x < b :=
  ⟨fun h =>
    let ⟨_, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨_, hx⟩ => lt_trans hx.1 hx.2⟩

@[to_dual lt_iff_exists_coe_btwn]
/--
theorem `lt_iff_exists_coe_btwn'` / 定理 `lt_iff_exists_coe_btwn'`

English:
theorem lt_iff_exists_coe_btwn'
  given: [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α}
  proof: by
  rw [lt_iff_exists_coe_btwn]; simp_rw [and_comm]

@[to_dual]

中文:
定理 lt_iff_存在_coe_btwn'
  条件: [预序 α] [稠密序 α] [NoMin序 α] {a b : WithBot α}
  证明: by
  rw [lt_iff_exists_coe_btwn]; simp_rw [and_comm]

@[to_dual]

Depends on / 依赖: and_comm, lt_iff_exists_coe_btwn, simp_rw
-/
theorem lt_iff_exists_coe_btwn' [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α} :
    a < b ↔ exists x : α, x < b ∧ a < x := by
  rw [lt_iff_exists_coe_btwn]; simp_rw [and_comm]

@[to_dual]
/--
Instance `noTopOrder` / 实例 `noTopOrder`

English:
instance noTopOrder
  signature: [LE α] [NoTopOrder α] [Nonempty α]
  body: fun
    | ⊥ => ‹Nonempty α›.elim fun a => ⟨a, by simp⟩
    | (a : α) => let ⟨b, hba⟩ := exists_not_le a; ⟨b, mod_cast hba⟩

@[to_dual]

中文:
实例 noTopOrder
  签名: [LE α] [无顶序 α] [非空 α]
  定义体: fun
    | ⊥ => ‹Nonempty α›.elim fun a => ⟨a, by simp⟩
    | (a : α) => let ⟨b, hba⟩ := exists_not_le a; ⟨b, mod_cast hba⟩

@[to_dual]
-/
instance noTopOrder [LE α] [NoTopOrder α] [Nonempty α] : NoTopOrder (WithBot α) where
  exists_not_le := fun
    | ⊥ => ‹Nonempty α›.elim fun a => ⟨a, by simp⟩
    | (a : α) => let ⟨b, hba⟩ := exists_not_le a; ⟨b, mod_cast hba⟩

@[to_dual]
/--
Instance `noMaxOrder` / 实例 `noMaxOrder`

English:
instance noMaxOrder
  signature: [LT α] [NoMaxOrder α] [Nonempty α]
  body: fun
    | ⊥ => ‹Nonempty α›.elim fun a => ⟨a, by simp⟩
    | (a : α) => let ⟨b, hba⟩ := exists_gt a; ⟨b, mod_cast hba⟩

中文:
实例 noMaxOrder
  签名: [LT α] [NoMax序 α] [非空 α]
  定义体: fun
    | ⊥ => ‹Nonempty α›.elim fun a => ⟨a, by simp⟩
    | (a : α) => let ⟨b, hba⟩ := exists_gt a; ⟨b, mod_cast hba⟩
-/
instance noMaxOrder [LT α] [NoMaxOrder α] [Nonempty α] : NoMaxOrder (WithBot α) where
  exists_gt := fun
    | ⊥ => ‹Nonempty α›.elim fun a => ⟨a, by simp⟩
    | (a : α) => let ⟨b, hba⟩ := exists_gt a; ⟨b, mod_cast hba⟩

variable {a b : α}

/-! ### `(WithBot α)ᵒᵈ ≃ WithTop αᵒᵈ`, `(WithTop α)ᵒᵈ ≃ WithBot αᵒᵈ` -/

open Function

/-- `WithBot.toDual` is the equivalence sending `⊥` to `⊤` and any `a : α` to `toDual a : αᵒᵈ`.
See `WithBot.toDualTopEquiv` for the related order-iso. -/
@[to_dual
/-- `WithTop.toDual` is the equivalence sending `⊤` to `⊥` and any `a : α` to `toDual a : αᵒᵈ`.
See `WithTop.toDualBotEquiv` for the related order-iso. -/]
/--
Definition of `toDual` / `toDual` 的定义

English:
definition toDual
  signature: : WithBot α ≃ WithTop αᵒᵈ
  body: Equiv.refl _

中文:
定义 toDual
  签名: : WithBot α ≃ WithTop αᵒᵈ
  定义体: Equiv.refl _
-/
protected def toDual : WithBot α ≃ WithTop αᵒᵈ :=
  Equiv.refl _

/-- `WithBot.ofDual` is the equivalence sending `⊥` to `⊤` and any `a : αᵒᵈ` to `ofDual a : α`.
See `WithBot.ofDualTopEquiv` for the related order-iso.
-/
@[to_dual
/-- `WithTop.ofDual` is the equivalence sending `⊤` to `⊥` and any `a : αᵒᵈ` to `ofDual a : α`.
See `WithTop.toDualBotEquiv` for the related order-iso. -/]
/--
Definition of `ofDual` / `ofDual` 的定义

English:
definition ofDual
  signature: : WithBot αᵒᵈ ≃ WithTop α
  body: Equiv.refl _

@[to_dual (attr := simp)]

中文:
定义 ofDual
  签名: : WithBot αᵒᵈ ≃ WithTop α
  定义体: Equiv.refl _

@[to_dual (attr := simp)]
-/
protected def ofDual : WithBot αᵒᵈ ≃ WithTop α :=
  Equiv.refl _

@[to_dual (attr := simp)]
/--
theorem `toDual_symm` / 定理 `toDual_symm`

English:
theorem toDual_symm
  statement: WithBot.toDual.symm = WithTop.ofDual (α := α)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 toDual_symm
  结论: WithBot.toDual.symm = WithTop.ofDual (α := α)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem toDual_symm : WithBot.toDual.symm = WithTop.ofDual (α := α) := rfl

@[to_dual (attr := simp)]
/--
theorem `ofDual_symm` / 定理 `ofDual_symm`

English:
theorem ofDual_symm
  statement: WithBot.ofDual.symm = WithTop.toDual (α := α)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 ofDual_symm
  结论: WithBot.ofDual.symm = WithTop.toDual (α := α)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem ofDual_symm : WithBot.ofDual.symm = WithTop.toDual (α := α) := rfl

@[to_dual (attr := simp)]
/--
theorem `toDual_bot` / 定理 `toDual_bot`

English:
theorem toDual_bot
  statement: WithBot.toDual (⊥ : WithBot α) = ⊤
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 toDual_bot
  结论: WithBot.toDual (⊥ : WithBot α) = ⊤
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem toDual_bot : WithBot.toDual (⊥ : WithBot α) = ⊤ := rfl

@[to_dual (attr := simp)]
/--
theorem `ofDual_bot` / 定理 `ofDual_bot`

English:
theorem ofDual_bot
  statement: WithBot.ofDual (⊥ : WithBot αᵒᵈ) = ⊤
  proof: rfl

中文:
定理 ofDual_bot
  结论: WithBot.ofDual (⊥ : WithBot αᵒᵈ) = ⊤
  证明: rfl
-/
theorem ofDual_bot : WithBot.ofDual (⊥ : WithBot αᵒᵈ) = ⊤ := rfl

open OrderDual

@[to_dual (attr := simp)]
/--
theorem `toDual_apply_coe` / 定理 `toDual_apply_coe`

English:
theorem toDual_apply_coe
  given: (a : α)
  statement: WithBot.toDual (a : WithBot α) = toDual a
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 toDual_apply_coe
  条件: (a : α)
  结论: WithBot.toDual (a : WithBot α) = toDual a
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem toDual_apply_coe (a : α) : WithBot.toDual (a : WithBot α) = toDual a := rfl

@[to_dual (attr := simp)]
/--
theorem `ofDual_apply_coe` / 定理 `ofDual_apply_coe`

English:
theorem ofDual_apply_coe
  given: (a : αᵒᵈ)
  statement: WithBot.ofDual (a : WithBot αᵒᵈ) = ofDual a
  proof: rfl

@[to_dual]

中文:
定理 ofDual_apply_coe
  条件: (a : αᵒᵈ)
  结论: WithBot.ofDual (a : WithBot αᵒᵈ) = ofDual a
  证明: rfl

@[to_dual]
-/
theorem ofDual_apply_coe (a : αᵒᵈ) : WithBot.ofDual (a : WithBot αᵒᵈ) = ofDual a := rfl

@[to_dual]
/--
theorem `map_toDual` / 定理 `map_toDual`

English:
theorem map_toDual
  given: (f : αᵒᵈ -> βᵒᵈ) (a : WithBot α)
  proof: rfl

@[to_dual]

中文:
定理 map_toDual
  条件: (f : αᵒᵈ -> βᵒᵈ) (a : WithBot α)
  证明: rfl

@[to_dual]
-/
theorem map_toDual (f : αᵒᵈ -> βᵒᵈ) (a : WithBot α) :
    map f (WithBot.toDual a) = a.map (toDual ∘ f) :=
  rfl

@[to_dual]
/--
theorem `map_ofDual` / 定理 `map_ofDual`

English:
theorem map_ofDual
  given: (f : α -> β) (a : WithBot αᵒᵈ)
  proof: rfl

@[to_dual]

中文:
定理 map_ofDual
  条件: (f : α -> β) (a : WithBot αᵒᵈ)
  证明: rfl

@[to_dual]
-/
theorem map_ofDual (f : α -> β) (a : WithBot αᵒᵈ) :
    map f (WithBot.ofDual a) = a.map (ofDual ∘ f) :=
  rfl

@[to_dual]
/--
theorem `toDual_map` / 定理 `toDual_map`

English:
theorem toDual_map
  given: (f : α -> β) (a : WithBot α)
  proof: rfl

@[to_dual]

中文:
定理 toDual_map
  条件: (f : α -> β) (a : WithBot α)
  证明: rfl

@[to_dual]
-/
theorem toDual_map (f : α -> β) (a : WithBot α) :
    WithBot.toDual (map f a) = WithTop.map (toDual ∘ f ∘ ofDual) (WithBot.toDual a) :=
  rfl

@[to_dual]
/--
theorem `ofDual_map` / 定理 `ofDual_map`

English:
theorem ofDual_map
  given: (f : αᵒᵈ -> βᵒᵈ) (a : WithBot αᵒᵈ)
  proof: rfl

中文:
定理 ofDual_map
  条件: (f : αᵒᵈ -> βᵒᵈ) (a : WithBot αᵒᵈ)
  证明: rfl
-/
theorem ofDual_map (f : αᵒᵈ -> βᵒᵈ) (a : WithBot αᵒᵈ) :
    WithBot.ofDual (map f a) = WithTop.map (ofDual ∘ f ∘ toDual) (WithBot.ofDual a) :=
  rfl

section LE
variable [LE α]

@[to_dual le_toDual_iff]
/--
lemma `toDual_le_iff` / 引理 `toDual_le_iff`

English:
lemma toDual_le_iff
  given: {x : WithBot α} {y : WithTop αᵒᵈ}
  proof: by cases x <;> cases y <;> simp [toDual_le]

@[to_dual toDual_le_iff]

中文:
引理 toDual_le_iff
  条件: {x : WithBot α} {y : WithTop αᵒᵈ}
  证明: by cases x <;> cases y <;> simp [toDual_le]

@[to_dual toDual_le_iff]

Depends on / 依赖: toDual_le
-/
lemma toDual_le_iff {x : WithBot α} {y : WithTop αᵒᵈ} :
    x.toDual <= y ↔ WithTop.ofDual y <= x := by cases x <;> cases y <;> simp [toDual_le]

@[to_dual toDual_le_iff]
/--
lemma `le_toDual_iff` / 引理 `le_toDual_iff`

English:
lemma le_toDual_iff
  given: {x : WithTop αᵒᵈ} {y : WithBot α}
  proof: by cases x <;> cases y <;> simp [le_toDual]

@[to_dual (attr := simp)]

中文:
引理 le_toDual_iff
  条件: {x : WithTop αᵒᵈ} {y : WithBot α}
  证明: by cases x <;> cases y <;> simp [le_toDual]

@[to_dual (attr := simp)]

Depends on / 依赖: le_toDual
-/
lemma le_toDual_iff {x : WithTop αᵒᵈ} {y : WithBot α} :
    x <= WithBot.toDual y ↔ y <= WithTop.ofDual x := by cases x <;> cases y <;> simp [le_toDual]

@[to_dual (attr := simp)]
/--
lemma `toDual_le_toDual_iff` / 引理 `toDual_le_toDual_iff`

English:
lemma toDual_le_toDual_iff
  given: {x y : WithBot α}
  proof: by cases x <;> cases y <;> simp

@[to_dual le_ofDual_iff]

中文:
引理 toDual_le_toDual_iff
  条件: {x y : WithBot α}
  证明: by cases x <;> cases y <;> simp

@[to_dual le_ofDual_iff]
-/
lemma toDual_le_toDual_iff {x y : WithBot α} :
    x.toDual <= y.toDual ↔ y <= x := by cases x <;> cases y <;> simp

@[to_dual le_ofDual_iff]
/--
lemma `ofDual_le_iff` / 引理 `ofDual_le_iff`

English:
lemma ofDual_le_iff
  given: {x : WithBot αᵒᵈ} {y : WithTop α}
  proof: by cases x <;> cases y <;> simp [toDual_le]

@[to_dual ofDual_le_iff]

中文:
引理 ofDual_le_iff
  条件: {x : WithBot αᵒᵈ} {y : WithTop α}
  证明: by cases x <;> cases y <;> simp [toDual_le]

@[to_dual ofDual_le_iff]

Depends on / 依赖: toDual_le
-/
lemma ofDual_le_iff {x : WithBot αᵒᵈ} {y : WithTop α} :
    WithBot.ofDual x <= y ↔ y.toDual <= x := by cases x <;> cases y <;> simp [toDual_le]

@[to_dual ofDual_le_iff]
/--
lemma `le_ofDual_iff` / 引理 `le_ofDual_iff`

English:
lemma le_ofDual_iff
  given: {x : WithTop α} {y : WithBot αᵒᵈ}
  proof: by cases x <;> cases y <;> simp [le_toDual]

@[to_dual (attr := simp)]

中文:
引理 le_ofDual_iff
  条件: {x : WithTop α} {y : WithBot αᵒᵈ}
  证明: by cases x <;> cases y <;> simp [le_toDual]

@[to_dual (attr := simp)]

Depends on / 依赖: le_toDual
-/
lemma le_ofDual_iff {x : WithTop α} {y : WithBot αᵒᵈ} :
    x <= WithBot.ofDual y ↔ y <= x.toDual := by cases x <;> cases y <;> simp [le_toDual]

@[to_dual (attr := simp)]
/--
lemma `ofDual_le_ofDual_iff` / 引理 `ofDual_le_ofDual_iff`

English:
lemma ofDual_le_ofDual_iff
  given: {x y : WithBot αᵒᵈ}
  proof: by cases x <;> cases y <;> simp_all

中文:
引理 ofDual_le_ofDual_iff
  条件: {x y : WithBot αᵒᵈ}
  证明: by cases x <;> cases y <;> simp_all
-/
lemma ofDual_le_ofDual_iff {x y : WithBot αᵒᵈ} :
    WithBot.ofDual x <= WithBot.ofDual y ↔ y <= x := by cases x <;> cases y <;> simp_all

end LE

section LT
variable [LT α]

@[to_dual lt_toDual_iff]
/--
lemma `toDual_lt_iff` / 引理 `toDual_lt_iff`

English:
lemma toDual_lt_iff
  given: {x : WithBot α} {y : WithTop αᵒᵈ}
  proof: by cases x <;> cases y <;> simp [toDual_lt]

@[to_dual toDual_lt_iff]

中文:
引理 toDual_lt_iff
  条件: {x : WithBot α} {y : WithTop αᵒᵈ}
  证明: by cases x <;> cases y <;> simp [toDual_lt]

@[to_dual toDual_lt_iff]

Depends on / 依赖: toDual_lt
-/
lemma toDual_lt_iff {x : WithBot α} {y : WithTop αᵒᵈ} :
    x.toDual < y ↔ WithTop.ofDual y < x := by cases x <;> cases y <;> simp [toDual_lt]

@[to_dual toDual_lt_iff]
/--
lemma `lt_toDual_iff` / 引理 `lt_toDual_iff`

English:
lemma lt_toDual_iff
  given: {x : WithTop αᵒᵈ} {y : WithBot α}
  proof: by cases x <;> cases y <;> simp [lt_toDual]

@[to_dual (attr := simp)]

中文:
引理 lt_toDual_iff
  条件: {x : WithTop αᵒᵈ} {y : WithBot α}
  证明: by cases x <;> cases y <;> simp [lt_toDual]

@[to_dual (attr := simp)]

Depends on / 依赖: lt_toDual
-/
lemma lt_toDual_iff {x : WithTop αᵒᵈ} {y : WithBot α} :
    x < y.toDual ↔ y < WithTop.ofDual x := by cases x <;> cases y <;> simp [lt_toDual]

@[to_dual (attr := simp)]
/--
lemma `toDual_lt_toDual_iff` / 引理 `toDual_lt_toDual_iff`

English:
lemma toDual_lt_toDual_iff
  given: {x y : WithBot α}
  proof: by cases x <;> cases y <;> simp

@[to_dual lt_ofDual_iff]

中文:
引理 toDual_lt_toDual_iff
  条件: {x y : WithBot α}
  证明: by cases x <;> cases y <;> simp

@[to_dual lt_ofDual_iff]
-/
lemma toDual_lt_toDual_iff {x y : WithBot α} :
    x.toDual < y.toDual ↔ y < x := by cases x <;> cases y <;> simp

@[to_dual lt_ofDual_iff]
/--
lemma `ofDual_lt_iff` / 引理 `ofDual_lt_iff`

English:
lemma ofDual_lt_iff
  given: {x : WithBot αᵒᵈ} {y : WithTop α}
  proof: by cases x <;> cases y <;> simp [toDual_lt]

@[to_dual ofDual_lt_iff]

中文:
引理 ofDual_lt_iff
  条件: {x : WithBot αᵒᵈ} {y : WithTop α}
  证明: by cases x <;> cases y <;> simp [toDual_lt]

@[to_dual ofDual_lt_iff]

Depends on / 依赖: toDual_lt
-/
lemma ofDual_lt_iff {x : WithBot αᵒᵈ} {y : WithTop α} :
    WithBot.ofDual x < y ↔ y.toDual < x := by cases x <;> cases y <;> simp [toDual_lt]

@[to_dual ofDual_lt_iff]
/--
lemma `lt_ofDual_iff` / 引理 `lt_ofDual_iff`

English:
lemma lt_ofDual_iff
  given: {x : WithTop α} {y : WithBot αᵒᵈ}
  proof: by cases x <;> cases y <;> simp [lt_toDual]

@[to_dual (attr := simp)]

中文:
引理 lt_ofDual_iff
  条件: {x : WithTop α} {y : WithBot αᵒᵈ}
  证明: by cases x <;> cases y <;> simp [lt_toDual]

@[to_dual (attr := simp)]

Depends on / 依赖: lt_toDual
-/
lemma lt_ofDual_iff {x : WithTop α} {y : WithBot αᵒᵈ} :
    x < WithBot.ofDual y ↔ y < x.toDual := by cases x <;> cases y <;> simp [lt_toDual]

@[to_dual (attr := simp)]
/--
lemma `ofDual_lt_ofDual_iff` / 引理 `ofDual_lt_ofDual_iff`

English:
lemma ofDual_lt_ofDual_iff
  given: {x y : WithBot αᵒᵈ}
  proof: by cases x <;> cases y <;> simp

中文:
引理 ofDual_lt_ofDual_iff
  条件: {x y : WithBot αᵒᵈ}
  证明: by cases x <;> cases y <;> simp
-/
lemma ofDual_lt_ofDual_iff {x y : WithBot αᵒᵈ} :
    WithBot.ofDual x < WithBot.ofDual y ↔ y < x := by cases x <;> cases y <;> simp

end LT

end WithBot
