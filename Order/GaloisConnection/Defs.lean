/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Monotone.Basic

/-!
# Galois connections, insertions and coinsertions

Galois connections are order-theoretic adjoints, i.e. a pair of functions `u` and `l`,
such that `∀ a b, l a ≤ b ↔ a ≤ u b`.

## Main definitions

* `GaloisConnection`: A Galois connection is a pair of functions `l` and `u` satisfying
  `l a ≤ b ↔ a ≤ u b`. They are special cases of adjoint functors in category theory,
  but do not depend on the category theory library in mathlib.
* `GaloisInsertion`: A Galois insertion is a Galois connection where `l ∘ u = id`
* `GaloisCoinsertion`: A Galois coinsertion is a Galois connection where `u ∘ l = id`
-/

@[expose] public section

assert_not_exists CompleteLattice RelIso

open Function OrderDual Set

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {κ : ι -> Sort*} {a₁ a₂ : α}
  {b₁ b₂ : β}

/-- A Galois connection is a pair of functions `l` and `u` satisfying
`l a ≤ b ↔ a ≤ u b`. They are special cases of adjoint functors in category theory,
but do not depend on the category theory library in mathlib. -/
@[to_dual self (reorder := α β, 3 4, l u)]
/--
Definition of `GaloisConnection` / `GaloisConnection` 的定义

English:
definition GaloisConnection
  signature: [Preorder α] [Preorder β] (l : α -> β) (u : β -> α)
  body: forall a b, l a <= b ↔ a <= u b

to_dual_insert_cast GaloisConnection := by
  rw [forall_comm]; simp only [Iff.comm]

to_dual_name_hint U L

中文:
定义 GaloisConnection
  签名: [预序 α] [预序 β] (l : α -> β) (u : β -> α)
  定义体: forall a b, l a <= b ↔ a <= u b

to_dual_insert_cast GaloisConnection := by
  rw [forall_comm]; simp only [Iff.comm]

to_dual_name_hint U L
-/
def GaloisConnection [Preorder α] [Preorder β] (l : α -> β) (u : β -> α) :=
  forall a b, l a <= b ↔ a <= u b

to_dual_insert_cast GaloisConnection := by
  rw [forall_comm]; simp only [Iff.comm]

to_dual_name_hint U L

namespace GaloisConnection

section

variable [Preorder α] [Preorder β] {l : α -> β} {u : β -> α}

@[to_dual self (reorder := α β, 3 4, l u, hu hl, h_u_l h_l_u)]
/--
theorem `monotone_intro` / 定理 `monotone_intro`

English:
theorem monotone_intro
  statement: (hu : Monotone u) (hl : Monotone l) (h_u_l : forall a, a <= u (l a))
  proof: fun _ _ =>
  ⟨fun h => (h_u_l _).trans (hu h), fun h => (hl h).trans (h_l_u _)⟩

@[to_dual self]

中文:
定理 monotone_intro
  结论: (hu : 递增 u) (hl : 递增 l) (h_u_l : 对任意 a, a <= u (l a))
  证明: fun _ _ =>
  ⟨fun h => (h_u_l _).trans (hu h), fun h => (hl h).trans (h_l_u _)⟩

@[to_dual self]
-/
theorem monotone_intro (hu : Monotone u) (hl : Monotone l) (h_u_l : forall a, a <= u (l a))
    (h_l_u : forall a, l (u a) <= a) : GaloisConnection l u := fun _ _ =>
  ⟨fun h => (h_u_l _).trans (hu h), fun h => (hl h).trans (h_l_u _)⟩

@[to_dual self]
/--
theorem `dual` / 定理 `dual`

English:
theorem dual
  given: {l : α -> β} {u : β -> α} (gc : GaloisConnection l u)
  proof: fun a b => (gc b a).symm

中文:
定理 dual
  条件: {l : α -> β} {u : β -> α} (gc : GaloisConnection l u)
  证明: fun a b => (gc b a).symm
-/
protected theorem dual {l : α -> β} {u : β -> α} (gc : GaloisConnection l u) :
    GaloisConnection (OrderDual.toDual ∘ u ∘ OrderDual.ofDual)
      (OrderDual.toDual ∘ l ∘ OrderDual.ofDual) :=
  fun a b => (gc b a).symm

variable (gc : GaloisConnection l u)
include gc

@[to_dual none]
/--
theorem `le_iff_le` / 定理 `le_iff_le`

English:
theorem le_iff_le
  given: {a : α} {b : β}
  statement: l a <= b ↔ a <= u b
  proof: gc _ _

@[to_dual le_u]

中文:
定理 le_iff_le
  条件: {a : α} {b : β}
  结论: l a <= b ↔ a <= u b
  证明: gc _ _

@[to_dual le_u]
-/
theorem le_iff_le {a : α} {b : β} : l a <= b ↔ a <= u b :=
  gc _ _

@[to_dual le_u]
/--
theorem `l_le` / 定理 `l_le`

English:
theorem l_le
  given: {a : α} {b : β}
  statement: a <= u b -> l a <= b
  proof: (gc _ _).mpr

@[to_dual l_u_le]

中文:
定理 l_le
  条件: {a : α} {b : β}
  结论: a <= u b -> l a <= b
  证明: (gc _ _).mpr

@[to_dual l_u_le]
-/
theorem l_le {a : α} {b : β} : a <= u b -> l a <= b :=
  (gc _ _).mpr

@[to_dual l_u_le]
/--
theorem `le_u_l` / 定理 `le_u_l`

English:
theorem le_u_l
  given: (a)
  statement: a <= u (l a)
  proof: gc.le_u le_rfl

@[to_dual]

中文:
定理 le_u_l
  条件: (a)
  结论: a <= u (l a)
  证明: gc.le_u le_rfl

@[to_dual]

Depends on / 依赖: gc.le_u, le_rfl, le_u
-/
theorem le_u_l (a) : a <= u (l a) :=
gc.le_u le_rfl

@[to_dual]
/--
theorem `monotone_u` / 定理 `monotone_u`

English:
theorem monotone_u
  statement: Monotone u
  proof: fun a _ H => gc.le_u ((gc.l_u_le a).trans H)

@[to_dual]

中文:
定理 monotone_u
  结论: 递增 u
  证明: fun a _ H => gc.le_u ((gc.l_u_le a).trans H)

@[to_dual]

Depends on / 依赖: gc.l_u_le, gc.le_u, l_u_le, le_u
-/
theorem monotone_u : Monotone u := fun a _ H => gc.le_u ((gc.l_u_le a).trans H)

@[to_dual]
/--
theorem `monotone_l_comp_u` / 定理 `monotone_l_comp_u`

English:
theorem monotone_l_comp_u
  statement: Monotone (l ∘ u)
  proof: gc.monotone_l.comp gc.monotone_u

中文:
定理 monotone_l_comp_u
  结论: 递增 (l ∘ u)
  证明: gc.monotone_l.comp gc.monotone_u

Depends on / 依赖: gc.monotone_l.comp, gc.monotone_u, monotone_l, monotone_u
-/
theorem monotone_l_comp_u : Monotone (l ∘ u) := gc.monotone_l.comp gc.monotone_u

/-- If `(l, u)` is a Galois connection, then the relation `x ≤ u (l y)` is a transitive relation.
If `l` is a closure operator (`Submodule.span`, `Subgroup.closure`, ...) and `u` is the coercion to
`Set`, this reads as "if `U` is in the closure of `V` and `V` is in the closure of `W` then `U` is
in the closure of `W`". -/
@[to_dual l_u_le_trans]
/--
theorem `le_u_l_trans` / 定理 `le_u_l_trans`

English:
theorem le_u_l_trans
  given: {x y z : α} (hxy : x <= u (l y)) (hyz : y <= u (l z))
  statement: x <= u (l z)
  proof: hxy.trans (gc.monotone_u <| gc.l_le hyz)

中文:
定理 le_u_l_trans
  条件: {x y z : α} (hxy : x <= u (l y)) (hyz : y <= u (l z))
  结论: x <= u (l z)
  证明: hxy.trans (gc.monotone_u <| gc.l_le hyz)

Depends on / 依赖: gc.l_le, gc.monotone_u, hxy.trans, l_le, monotone_u
-/
theorem le_u_l_trans {x y z : α} (hxy : x <= u (l y)) (hyz : y <= u (l z)) : x <= u (l z) :=
  hxy.trans (gc.monotone_u <| gc.l_le hyz)

end

section PartialOrder

variable [PartialOrder α] [Preorder β] {l : α -> β} {u : β -> α} (gc : GaloisConnection l u)
include gc

@[to_dual]
/--
theorem `u_l_u_eq_u` / 定理 `u_l_u_eq_u`

English:
theorem u_l_u_eq_u
  given: (b : β)
  statement: u (l (u b)) = u b
  proof: (gc.monotone_u (gc.l_u_le _)).antisymm (gc.le_u_l _)

@[to_dual]

中文:
定理 u_l_u_eq_u
  条件: (b : β)
  结论: u (l (u b)) = u b
  证明: (gc.monotone_u (gc.l_u_le _)).antisymm (gc.le_u_l _)

@[to_dual]

Depends on / 依赖: antisymm, gc.l_u_le, gc.le_u_l, gc.monotone_u, l_u_le, le_u_l, monotone_u
-/
theorem u_l_u_eq_u (b : β) : u (l (u b)) = u b :=
  (gc.monotone_u (gc.l_u_le _)).antisymm (gc.le_u_l _)

@[to_dual]
/--
theorem `u_l_u_eq_u'` / 定理 `u_l_u_eq_u'`

English:
theorem u_l_u_eq_u'
  statement: u ∘ l ∘ u = u
  proof: funext gc.u_l_u_eq_u

@[to_dual]

中文:
定理 u_l_u_eq_u'
  结论: u ∘ l ∘ u = u
  证明: funext gc.u_l_u_eq_u

@[to_dual]

Depends on / 依赖: gc.u_l_u_eq_u, u_l_u_eq_u
-/
theorem u_l_u_eq_u' : u ∘ l ∘ u = u :=
  funext gc.u_l_u_eq_u

@[to_dual]
/--
theorem `u_unique` / 定理 `u_unique`

English:
theorem u_unique
  statement: {l' : α -> β} {u' : β -> α} (gc' : GaloisConnection l' u') (hl : forall a, l a = l' a)
  proof: le_antisymm (gc'.le_u <| hl (u b) ▸ gc.l_u_le _) (gc.le_u <| (hl (u' b)).symm ▸ gc'.l_u_le _)

中文:
定理 u_unique
  结论: {l' : α -> β} {u' : β -> α} (gc' : GaloisConnection l' u') (hl : 对任意 a, l a = l' a)
  证明: le_antisymm (gc'.le_u <| hl (u b) ▸ gc.l_u_le _) (gc.le_u <| (hl (u' b)).symm ▸ gc'.l_u_le _)

Depends on / 依赖: gc.l_u_le, gc.le_u, l_u_le, le_antisymm, le_u
-/
theorem u_unique {l' : α -> β} {u' : β -> α} (gc' : GaloisConnection l' u') (hl : forall a, l a = l' a)
    {b : β} : u b = u' b :=
  le_antisymm (gc'.le_u <| hl (u b) ▸ gc.l_u_le _) (gc.le_u <| (hl (u' b)).symm ▸ gc'.l_u_le _)

/-- If there exists a `b` such that `a = u a`, then `b = l a` is one such element. -/
@[to_dual /-- If there exists an `b` such that `a = l b`, then `b = u a` is one such element. -/]
/--
theorem `exists_eq_u` / 定理 `exists_eq_u`

English:
theorem exists_eq_u
  given: (a : α)
  statement: (exists b : β, a = u b) ↔ a = u (l a)
  proof: ⟨fun ⟨_, hS⟩ => hS.symm ▸ (gc.u_l_u_eq_u _).symm, fun HI => ⟨_, HI⟩⟩

@[to_dual]

中文:
定理 存在_eq_u
  条件: (a : α)
  结论: (存在 b : β, a = u b) ↔ a = u (l a)
  证明: ⟨fun ⟨_, hS⟩ => hS.symm ▸ (gc.u_l_u_eq_u _).symm, fun HI => ⟨_, HI⟩⟩

@[to_dual]

Depends on / 依赖: gc.u_l_u_eq_u, hS.symm, u_l_u_eq_u
-/
theorem exists_eq_u (a : α) : (exists b : β, a = u b) ↔ a = u (l a) :=
  ⟨fun ⟨_, hS⟩ => hS.symm ▸ (gc.u_l_u_eq_u _).symm, fun HI => ⟨_, HI⟩⟩

@[to_dual]
/--
theorem `u_eq` / 定理 `u_eq`

English:
theorem u_eq
  given: {z : α} {y : β}
  statement: u y = z ↔ forall x, x <= z ↔ l x <= y
  proof: by
  constructor
  · rintro rfl x
    exact (gc x y).symm
  · intro H
    exact ((H <| u y).mpr (gc.l_u_le y)).antisymm ((gc _ _).mp <| (H z).mp le_rfl)

中文:
定理 u_eq
  条件: {z : α} {y : β}
  结论: u y = z ↔ 对任意 x, x <= z ↔ l x <= y
  证明: by
  constructor
  · rintro rfl x
    exact (gc x y).symm
  · intro H
    exact ((H <| u y).mpr (gc.l_u_le y)).antisymm ((gc _ _).mp <| (H z).mp le_rfl)

Depends on / 依赖: antisymm, gc.l_u_le, l_u_le, le_rfl
-/
theorem u_eq {z : α} {y : β} : u y = z ↔ forall x, x <= z ↔ l x <= y := by
  constructor
  · rintro rfl x
    exact (gc x y).symm
  · intro H
    exact ((H <| u y).mpr (gc.l_u_le y)).antisymm ((gc _ _).mp <| (H z).mp le_rfl)

end PartialOrder

section OrderTop

variable [PartialOrder α] [Preorder β] [OrderTop α]

@[to_dual]
/--
theorem `u_eq_top` / 定理 `u_eq_top`

English:
theorem u_eq_top
  given: {l : α -> β} {u : β -> α} (gc : GaloisConnection l u) {x}
  statement: u x = ⊤ ↔ l ⊤ <= x
  proof: top_le_iff.symm.trans gc.le_iff_le.symm

@[to_dual]

中文:
定理 u_eq_top
  条件: {l : α -> β} {u : β -> α} (gc : GaloisConnection l u) {x}
  结论: u x = ⊤ ↔ l ⊤ <= x
  证明: top_le_iff.symm.trans gc.le_iff_le.symm

@[to_dual]

Depends on / 依赖: gc.le_iff_le.symm, le_iff_le, top_le_iff, top_le_iff.symm.trans
-/
theorem u_eq_top {l : α -> β} {u : β -> α} (gc : GaloisConnection l u) {x} : u x = ⊤ ↔ l ⊤ <= x :=
  top_le_iff.symm.trans gc.le_iff_le.symm

@[to_dual]
/--
theorem `u_top` / 定理 `u_top`

English:
theorem u_top
  given: [OrderTop β] {l : α -> β} {u : β -> α} (gc : GaloisConnection l u)
  statement: u ⊤ = ⊤
  proof: gc.u_eq_top.2 le_top

@[to_dual]

中文:
定理 u_top
  条件: [有顶序 β] {l : α -> β} {u : β -> α} (gc : GaloisConnection l u)
  结论: u ⊤ = ⊤
  证明: gc.u_eq_top.2 le_top

@[to_dual]

Depends on / 依赖: gc.u_eq_top, le_top, u_eq_top
-/
theorem u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc : GaloisConnection l u) : u ⊤ = ⊤ :=
  gc.u_eq_top.2 le_top

@[to_dual]
/--
theorem `u_l_top` / 定理 `u_l_top`

English:
theorem u_l_top
  given: {l : α -> β} {u : β -> α} (gc : GaloisConnection l u)
  statement: u (l ⊤) = ⊤
  proof: gc.u_eq_top.mpr le_rfl

中文:
定理 u_l_top
  条件: {l : α -> β} {u : β -> α} (gc : GaloisConnection l u)
  结论: u (l ⊤) = ⊤
  证明: gc.u_eq_top.mpr le_rfl

Depends on / 依赖: gc.u_eq_top.mpr, le_rfl, u_eq_top
-/
theorem u_l_top {l : α -> β} {u : β -> α} (gc : GaloisConnection l u) : u (l ⊤) = ⊤ :=
  gc.u_eq_top.mpr le_rfl

end OrderTop

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {l : α -> β} {u : β -> α}

@[to_dual none]
/--
theorem `lt_iff_lt` / 定理 `lt_iff_lt`

English:
theorem lt_iff_lt
  given: (gc : GaloisConnection l u) {a : α} {b : β}
  statement: b < l a ↔ u b < a
  proof: lt_iff_lt_of_le_iff_le (gc a b)

中文:
定理 lt_iff_lt
  条件: (gc : GaloisConnection l u) {a : α} {b : β}
  结论: b < l a ↔ u b < a
  证明: lt_iff_lt_of_le_iff_le (gc a b)

Depends on / 依赖: lt_iff_lt_of_le_iff_le
-/
theorem lt_iff_lt (gc : GaloisConnection l u) {a : α} {b : β} : b < l a ↔ u b < a :=
  lt_iff_lt_of_le_iff_le (gc a b)

end LinearOrder

-- Constructing Galois connections
section Constructions

/--
theorem `id` / 定理 `id`

English:
theorem id
  given: [pα : Preorder α]
  statement: @GaloisConnection α α pα pα id id
  proof: fun _ _ =>
  Iff.intro (fun x => x) fun x => x

中文:
定理 id
  条件: [pα : 预序 α]
  结论: @GaloisConnection α α pα pα id id
  证明: fun _ _ =>
  Iff.intro (fun x => x) fun x => x
-/
protected theorem id [pα : Preorder α] : @GaloisConnection α α pα pα id id := fun _ _ =>
  Iff.intro (fun x => x) fun x => x

/--
theorem `compose` / 定理 `compose`

English:
theorem compose
  statement: [Preorder α] [Preorder β] [Preorder γ] {l1 : α -> β} {u1 : β -> α}
  proof: fun _ _ => (gc2 _ _).trans (gc1 _ _)

中文:
定理 compose
  结论: [预序 α] [预序 β] [预序 γ] {l1 : α -> β} {u1 : β -> α}
  证明: fun _ _ => (gc2 _ _).trans (gc1 _ _)
-/
protected theorem compose [Preorder α] [Preorder β] [Preorder γ] {l1 : α -> β} {u1 : β -> α}
    {l2 : β -> γ} {u2 : γ -> β} (gc1 : GaloisConnection l1 u1) (gc2 : GaloisConnection l2 u2) :
    GaloisConnection (l2 ∘ l1) (u1 ∘ u2) := fun _ _ => (gc2 _ _).trans (gc1 _ _)

/--
theorem `dfun` / 定理 `dfun`

English:
theorem dfun
  statement: {ι : Type u} {α : ι -> Type v} {β : ι -> Type w} [forall i, Preorder (α i)]
  proof: fun a b =>
  forall_congr' fun i => gc i (a i) (b i)

中文:
定理 dfun
  结论: {ι : 类型u} {α : ι -> 类型v} {β : ι -> 类型 w} [对任意 i, 预序 (α i)]
  证明: fun a b =>
  forall_congr' fun i => gc i (a i) (b i)
-/
protected theorem dfun {ι : Type u} {α : ι -> Type v} {β : ι -> Type w} [forall i, Preorder (α i)]
    [forall i, Preorder (β i)] (l : forall i, α i -> β i) (u : forall i, β i -> α i)
    (gc : forall i, GaloisConnection (l i) (u i)) :
    GaloisConnection (fun (a : forall i, α i) i => l i (a i)) fun b i => u i (b i) := fun a b =>
  forall_congr' fun i => gc i (a i) (b i)

end Constructions

/--
theorem `l_comm_of_u_comm` / 定理 `l_comm_of_u_comm`

English:
theorem l_comm_of_u_comm
  statement: {X : Type*} [Preorder X] {Y : Type*} [Preorder Y] {Z : Type*}
  proof: (hXZ.compose hZW).l_unique (hXY.compose hWY) h

中文:
定理 l_comm_of_u_comm
  结论: {X : 类型} [预序 X] {Y : 类型} [预序 Y] {Z : 类型}
  证明: (hXZ.compose hZW).l_unique (hXY.compose hWY) h

Depends on / 依赖: compose, hXY.compose, hXZ.compose, l_unique
-/
theorem l_comm_of_u_comm {X : Type*} [Preorder X] {Y : Type*} [Preorder Y] {Z : Type*}
    [Preorder Z] {W : Type*} [PartialOrder W] {lYX : X -> Y} {uXY : Y -> X}
    (hXY : GaloisConnection lYX uXY) {lWZ : Z -> W} {uZW : W -> Z} (hZW : GaloisConnection lWZ uZW)
    {lWY : Y -> W} {uYW : W -> Y} (hWY : GaloisConnection lWY uYW) {lZX : X -> Z} {uXZ : Z -> X}
    (hXZ : GaloisConnection lZX uXZ) (h : forall w, uXZ (uZW w) = uXY (uYW w)) {x : X} :
    lWZ (lZX x) = lWY (lYX x) :=
  (hXZ.compose hZW).l_unique (hXY.compose hWY) h

/--
theorem `u_comm_of_l_comm` / 定理 `u_comm_of_l_comm`

English:
theorem u_comm_of_l_comm
  statement: {X : Type*} [PartialOrder X] {Y : Type*} [Preorder Y] {Z : Type*}
  proof: (hXZ.compose hZW).u_unique (hXY.compose hWY) h

中文:
定理 u_comm_of_l_comm
  结论: {X : 类型} [偏序 X] {Y : 类型} [预序 Y] {Z : 类型}
  证明: (hXZ.compose hZW).u_unique (hXY.compose hWY) h

Depends on / 依赖: compose, hXY.compose, hXZ.compose, u_unique
-/
theorem u_comm_of_l_comm {X : Type*} [PartialOrder X] {Y : Type*} [Preorder Y] {Z : Type*}
    [Preorder Z] {W : Type*} [Preorder W] {lYX : X -> Y} {uXY : Y -> X}
    (hXY : GaloisConnection lYX uXY) {lWZ : Z -> W} {uZW : W -> Z} (hZW : GaloisConnection lWZ uZW)
    {lWY : Y -> W} {uYW : W -> Y} (hWY : GaloisConnection lWY uYW) {lZX : X -> Z} {uXZ : Z -> X}
    (hXZ : GaloisConnection lZX uXZ) (h : forall x, lWZ (lZX x) = lWY (lYX x)) {w : W} :
    uXZ (uZW w) = uXY (uYW w) :=
  (hXZ.compose hZW).u_unique (hXY.compose hWY) h

/--
theorem `l_comm_iff_u_comm` / 定理 `l_comm_iff_u_comm`

English:
theorem l_comm_iff_u_comm
  statement: {X : Type*} [PartialOrder X] {Y : Type*} [Preorder Y] {Z : Type*}
  proof: ⟨hXY.l_comm_of_u_comm hZW hWY hXZ, hXY.u_comm_of_l_comm hZW hWY hXZ⟩

中文:
定理 l_comm_iff_u_comm
  结论: {X : 类型} [偏序 X] {Y : 类型} [预序 Y] {Z : 类型}
  证明: ⟨hXY.l_comm_of_u_comm hZW hWY hXZ, hXY.u_comm_of_l_comm hZW hWY hXZ⟩

Depends on / 依赖: hXY.l_comm_of_u_comm, hXY.u_comm_of_l_comm, l_comm_of_u_comm, u_comm_of_l_comm
-/
theorem l_comm_iff_u_comm {X : Type*} [PartialOrder X] {Y : Type*} [Preorder Y] {Z : Type*}
    [Preorder Z] {W : Type*} [PartialOrder W] {lYX : X -> Y} {uXY : Y -> X}
    (hXY : GaloisConnection lYX uXY) {lWZ : Z -> W} {uZW : W -> Z} (hZW : GaloisConnection lWZ uZW)
    {lWY : Y -> W} {uYW : W -> Y} (hWY : GaloisConnection lWY uYW) {lZX : X -> Z} {uXZ : Z -> X}
    (hXZ : GaloisConnection lZX uXZ) :
    (forall w : W, uXZ (uZW w) = uXY (uYW w)) ↔ forall x : X, lWZ (lZX x) = lWY (lYX x) :=
  ⟨hXY.l_comm_of_u_comm hZW hWY hXZ, hXY.u_comm_of_l_comm hZW hWY hXZ⟩

end GaloisConnection

/--
Definition of `GaloisInsertion` / `GaloisInsertion` 的定义

English:
structure GaloisInsertion
  parameters: {α β : Type*} [Preorder α] [Preorder β] (l : α -> β) (u : β -> α)
  axioms and operations (4):
    - choice : forall x : α, u (l x) <= x -> β
    - gc : GaloisConnection l u
    - le_l_u : forall x, x <= l (u x)
    - choice_eq : forall a h, choice a h = l a

中文:
结构 Galois嵌入
  参数: {α β : 类型} [预序 α] [预序 β] (l : α -> β) (u : β -> α)
  公理与运算 (4 个):
    - choice : 对任意 x : α, u (l x) <= x -> β
    - gc : GaloisConnection l u
    - le_l_u : 对任意 x, x <= l (u x)
    - choice_eq : 对任意 a h, choice a h = l a
-/
structure GaloisInsertion {α β : Type*} [Preorder α] [Preorder β] (l : α -> β) (u : β -> α) where
  /-- A constructive choice function for images of `l`. -/
  choice : forall x : α, u (l x) <= x -> β
  /-- The Galois connection associated to a Galois insertion. -/
  gc : GaloisConnection l u
  /-- Main property of a Galois insertion. -/
  le_l_u : forall x, x <= l (u x)
  /-- Property of the choice function. -/
  choice_eq : forall a h, choice a h = l a

/-- A Galois coinsertion is a Galois connection where `u ∘ l = id`. It also contains a constructive
choice function, to give better definitional equalities when lifting order structures. Dual to
`GaloisInsertion` -/
@[to_dual (reorder := α β, 3 4, l u)]
/--
Definition of `GaloisCoinsertion` / `GaloisCoinsertion` 的定义

English:
structure GaloisCoinsertion
  parameters: [Preorder α] [Preorder β] (l : α -> β) (u : β -> α)
  axioms and operations (4):
    - choice : forall x : β, x <= l (u x) -> α
    - gc : GaloisConnection l u
    - u_l_le : forall x, u (l x) <= x
    - choice_eq : forall a h, choice a h = u a

中文:
结构 Galois余嵌入
  参数: [预序 α] [预序 β] (l : α -> β) (u : β -> α)
  公理与运算 (4 个):
    - choice : 对任意 x : β, x <= l (u x) -> α
    - gc : GaloisConnection l u
    - u_l_le : 对任意 x, u (l x) <= x
    - choice_eq : 对任意 a h, choice a h = u a
-/
structure GaloisCoinsertion [Preorder α] [Preorder β] (l : α -> β) (u : β -> α) where
  /-- A constructive choice function for images of `u`. -/
  choice : forall x : β, x <= l (u x) -> α
  /-- The Galois connection associated to a Galois coinsertion. -/
  gc : GaloisConnection l u
  /-- Main property of a Galois coinsertion. -/
  u_l_le : forall x, u (l x) <= x
  /-- Property of the choice function. -/
  choice_eq : forall a h, choice a h = u a

/-- A constructor for a Galois insertion with the trivial `choice` function. -/
@[to_dual (reorder := hu hl)
/-- A constructor for a Galois coinsertion with the trivial `choice` function. -/]
/--
Definition of `GaloisInsertion.monotoneIntro` / `GaloisInsertion.monotoneIntro` 的定义

English:
definition GaloisInsertion.monotoneIntro
  signature: {α β : Type*} [Preorder α] [Preorder β] {l : α -> β} {u : β -> α}
  body: l x
  gc := GaloisConnection.monotone_intro hu hl h_u_l fun b => le_of_eq (h_l_u b)
le_l_u b := le_of_eq (h_l_u b).symm
  choice_eq _ _ := rfl

中文:
定义 Galois嵌入.monotone整数ro
  签名: {α β : 类型} [预序 α] [预序 β] {l : α -> β} {u : β -> α}
  定义体: l x
  gc := GaloisConnection.monotone_intro hu hl h_u_l fun b => le_of_eq (h_l_u b)
le_l_u b := le_of_eq (h_l_u b).symm
  choice_eq _ _ := rfl
-/
def GaloisInsertion.monotoneIntro {α β : Type*} [Preorder α] [Preorder β] {l : α -> β} {u : β -> α}
    (hu : Monotone u) (hl : Monotone l) (h_u_l : forall a, a <= u (l a)) (h_l_u : forall b, l (u b) = b) :
    GaloisInsertion l u where
  choice x _ := l x
  gc := GaloisConnection.monotone_intro hu hl h_u_l fun b => le_of_eq (h_l_u b)
le_l_u b := le_of_eq (h_l_u b).symm
  choice_eq _ _ := rfl

/-- Make a `GaloisInsertion l u` from a `GaloisConnection l u` such that `∀ b, b ≤ l (u b)` -/
@[to_dual /-- Make a `GaloisCoinsertion` between `αᵒᵈ` and `βᵒᵈ` from a `GaloisInsertion` between
`α` and `β`. -/]
/--
Definition of `GaloisConnection.toGaloisInsertion` / `GaloisConnection.toGaloisInsertion` 的定义

English:
definition GaloisConnection.toGaloisInsertion
  signature: {α β : Type*} [Preorder α] [Preorder β] {l : α -> β}
  body: { choice := fun x _ => l x
    gc
    le_l_u := h
    choice_eq := fun _ _ => rfl }

中文:
定义 GaloisConnection.toGaloisInsertion
  签名: {α β : 类型} [预序 α] [预序 β] {l : α -> β}
  定义体: { choice := fun x _ => l x
    gc
    le_l_u := h
    choice_eq := fun _ _ => rfl }

Depends on / 依赖: choice, choice_eq, le_l_u
-/
def GaloisConnection.toGaloisInsertion {α β : Type*} [Preorder α] [Preorder β] {l : α -> β}
    {u : β -> α} (gc : GaloisConnection l u) (h : forall b, b <= l (u b)) : GaloisInsertion l u :=
  { choice := fun x _ => l x
    gc
    le_l_u := h
    choice_eq := fun _ _ => rfl }

/-- Lift the bottom along a Galois connection -/
@[to_dual (attr := instance_reducible) /-- Lift the top along a Galois connection -/]
/--
Definition of `GaloisConnection.liftOrderBot` / `GaloisConnection.liftOrderBot` 的定义

English:
definition GaloisConnection.liftOrderBot
  signature: {α β : Type*} [Preorder α] [OrderBot α] [PartialOrder β]
  body: l ⊥
bot_le _ := gc.l_le bot_le

中文:
定义 GaloisConnection.liftOrderBot
  签名: {α β : 类型} [预序 α] [有底序 α] [偏序 β]
  定义体: l ⊥
bot_le _ := gc.l_le bot_le
-/
def GaloisConnection.liftOrderBot {α β : Type*} [Preorder α] [OrderBot α] [PartialOrder β]
    {l : α -> β} {u : β -> α} (gc : GaloisConnection l u) :
    OrderBot β where
  bot := l ⊥
bot_le _ := gc.l_le bot_le

namespace GaloisInsertion

variable {l : α -> β} {u : β -> α}

@[to_dual]
/--
theorem `l_u_eq` / 定理 `l_u_eq`

English:
theorem l_u_eq
  given: [Preorder α] [PartialOrder β] (gi : GaloisInsertion l u) (b : β)
  statement: l (u b) = b
  proof: (gi.gc.l_u_le _).antisymm (gi.le_l_u _)

@[to_dual]

中文:
定理 l_u_eq
  条件: [预序 α] [偏序 β] (gi : Galois嵌入 l u) (b : β)
  结论: l (u b) = b
  证明: (gi.gc.l_u_le _).antisymm (gi.le_l_u _)

@[to_dual]

Depends on / 依赖: antisymm, gi.gc.l_u_le, gi.le_l_u, l_u_le, le_l_u
-/
theorem l_u_eq [Preorder α] [PartialOrder β] (gi : GaloisInsertion l u) (b : β) : l (u b) = b :=
  (gi.gc.l_u_le _).antisymm (gi.le_l_u _)

@[to_dual]
/--
theorem `leftInverse_l_u` / 定理 `leftInverse_l_u`

English:
theorem leftInverse_l_u
  given: [Preorder α] [PartialOrder β] (gi : GaloisInsertion l u)
  proof: gi.l_u_eq

@[deprecated (since := "2026-03-06")]
alias _root_.GaloisCoinsertion.u_l_leftInverse := GaloisCoinsertion.leftInverse_u_l

@[to_dual]

中文:
定理 leftInverse_l_u
  条件: [预序 α] [偏序 β] (gi : Galois嵌入 l u)
  证明: gi.l_u_eq

@[deprecated (since := "2026-03-06")]
alias _root_.GaloisCoinsertion.u_l_leftInverse := GaloisCoinsertion.leftInverse_u_l

@[to_dual]

Depends on / 依赖: gi.l_u_eq, l_u_eq
-/
theorem leftInverse_l_u [Preorder α] [PartialOrder β] (gi : GaloisInsertion l u) :
    LeftInverse l u :=
  gi.l_u_eq

@[deprecated (since := "2026-03-06")]
alias _root_.GaloisCoinsertion.u_l_leftInverse := GaloisCoinsertion.leftInverse_u_l

@[to_dual]
/--
theorem `l_top` / 定理 `l_top`

English:
theorem l_top
  statement: [Preorder α] [PartialOrder β] [OrderTop α] [OrderTop β]
  proof: top_unique (gi.le_l_u _).trans gi.gc.monotone_l le_top

@[to_dual]

中文:
定理 l_top
  结论: [预序 α] [偏序 β] [有顶序 α] [有顶序 β]
  证明: top_unique (gi.le_l_u _).trans gi.gc.monotone_l le_top

@[to_dual]

Depends on / 依赖: gi.gc.monotone_l, gi.le_l_u, le_l_u, le_top, monotone_l, top_unique
-/
theorem l_top [Preorder α] [PartialOrder β] [OrderTop α] [OrderTop β]
    (gi : GaloisInsertion l u) : l ⊤ = ⊤ :=
top_unique (gi.le_l_u _).trans gi.gc.monotone_l le_top

@[to_dual]
/--
theorem `l_surjective` / 定理 `l_surjective`

English:
theorem l_surjective
  given: [Preorder α] [PartialOrder β] (gi : GaloisInsertion l u)
  statement: Surjective l
  proof: gi.leftInverse_l_u.surjective

@[to_dual]

中文:
定理 l_surjective
  条件: [预序 α] [偏序 β] (gi : Galois嵌入 l u)
  结论: 满射 l
  证明: gi.leftInverse_l_u.surjective

@[to_dual]

Depends on / 依赖: gi.leftInverse_l_u.surjective, leftInverse_l_u, surjective
-/
theorem l_surjective [Preorder α] [PartialOrder β] (gi : GaloisInsertion l u) : Surjective l :=
  gi.leftInverse_l_u.surjective

@[to_dual]
/--
theorem `u_injective` / 定理 `u_injective`

English:
theorem u_injective
  given: [Preorder α] [PartialOrder β] (gi : GaloisInsertion l u)
  statement: Injective u
  proof: gi.leftInverse_l_u.injective

@[to_dual]

中文:
定理 u_injective
  条件: [预序 α] [偏序 β] (gi : Galois嵌入 l u)
  结论: 单射 u
  证明: gi.leftInverse_l_u.injective

@[to_dual]

Depends on / 依赖: gi.leftInverse_l_u.injective, injective, leftInverse_l_u
-/
theorem u_injective [Preorder α] [PartialOrder β] (gi : GaloisInsertion l u) : Injective u :=
  gi.leftInverse_l_u.injective

@[to_dual]
/--
theorem `u_le_u_iff` / 定理 `u_le_u_iff`

English:
theorem u_le_u_iff
  given: [Preorder α] [Preorder β] (gi : GaloisInsertion l u) {a b}
  statement: u a <= u b ↔ a <= b
  proof: ⟨fun h => (gi.le_l_u _).trans (gi.gc.l_le h), fun h => gi.gc.monotone_u h⟩

@[to_dual]

中文:
定理 u_le_u_iff
  条件: [预序 α] [预序 β] (gi : Galois嵌入 l u) {a b}
  结论: u a <= u b ↔ a <= b
  证明: ⟨fun h => (gi.le_l_u _).trans (gi.gc.l_le h), fun h => gi.gc.monotone_u h⟩

@[to_dual]

Depends on / 依赖: gi.gc.l_le, gi.gc.monotone_u, gi.le_l_u, l_le, le_l_u, monotone_u
-/
theorem u_le_u_iff [Preorder α] [Preorder β] (gi : GaloisInsertion l u) {a b} : u a <= u b ↔ a <= b :=
  ⟨fun h => (gi.le_l_u _).trans (gi.gc.l_le h), fun h => gi.gc.monotone_u h⟩

@[to_dual]
/--
theorem `strictMono_u` / 定理 `strictMono_u`

English:
theorem strictMono_u
  given: [Preorder α] [Preorder β] (gi : GaloisInsertion l u)
  statement: StrictMono u
  proof: strictMono_of_le_iff_le fun _ _ => gi.u_le_u_iff.symm

中文:
定理 strictMono_u
  条件: [预序 α] [预序 β] (gi : Galois嵌入 l u)
  结论: 严格递增 u
  证明: strictMono_of_le_iff_le fun _ _ => gi.u_le_u_iff.symm

Depends on / 依赖: gi.u_le_u_iff.symm, strictMono_of_le_iff_le, u_le_u_iff
-/
theorem strictMono_u [Preorder α] [Preorder β] (gi : GaloisInsertion l u) : StrictMono u :=
  strictMono_of_le_iff_le fun _ _ => gi.u_le_u_iff.symm

end GaloisInsertion

/-- Make a `GaloisInsertion` between `αᵒᵈ` and `βᵒᵈ` from a `GaloisCoinsertion` between `α` and
`β`. -/
@[to_dual /-- Make a `GaloisCoinsertion` between `αᵒᵈ` and `βᵒᵈ` from a `GaloisInsertion` between
`α` and `β`. -/]
/--
Definition of `GaloisCoinsertion.dual` / `GaloisCoinsertion.dual` 的定义

English:
definition GaloisCoinsertion.dual
  signature: [Preorder α] [Preorder β] {l : α -> β} {u : β -> α}
  body: fun x => ⟨x.1, x.2.dual, x.3, x.4⟩

中文:
定义 Galois余嵌入.dual
  签名: [预序 α] [预序 β] {l : α -> β} {u : β -> α}
  定义体: fun x => ⟨x.1, x.2.dual, x.3, x.4⟩
-/
def GaloisCoinsertion.dual [Preorder α] [Preorder β] {l : α -> β} {u : β -> α} :
    GaloisCoinsertion l u -> GaloisInsertion (toDual ∘ u ∘ ofDual) (toDual ∘ l ∘ ofDual) :=
  fun x => ⟨x.1, x.2.dual, x.3, x.4⟩

/-- Make a `GaloisInsertion` between `α` and `β` from a `GaloisCoinsertion` between `αᵒᵈ` and
`βᵒᵈ`. -/
@[to_dual /-- Make a `GaloisCoinsertion` between `α` and `β` from a `GaloisInsertion` between `αᵒᵈ`
and `βᵒᵈ`. -/]
/--
Definition of `GaloisCoinsertion.ofDual` / `GaloisCoinsertion.ofDual` 的定义

English:
definition GaloisCoinsertion.ofDual
  signature: [Preorder α] [Preorder β] {l : αᵒᵈ -> βᵒᵈ} {u : βᵒᵈ -> αᵒᵈ}
  body: fun x => ⟨x.1, x.2.dual, x.3, x.4⟩

中文:
定义 Galois余嵌入.ofDual
  签名: [预序 α] [预序 β] {l : αᵒᵈ -> βᵒᵈ} {u : βᵒᵈ -> αᵒᵈ}
  定义体: fun x => ⟨x.1, x.2.dual, x.3, x.4⟩
-/
def GaloisCoinsertion.ofDual [Preorder α] [Preorder β] {l : αᵒᵈ -> βᵒᵈ} {u : βᵒᵈ -> αᵒᵈ} :
    GaloisCoinsertion l u -> GaloisInsertion (ofDual ∘ u ∘ toDual) (ofDual ∘ l ∘ toDual) :=
  fun x => ⟨x.1, x.2.dual, x.3, x.4⟩
