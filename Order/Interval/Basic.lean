/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.SetLike.Basic

/-!
# Order intervals

This file defines (nonempty) closed intervals in an order (see `Set.Icc`). This is a prototype for
interval arithmetic.

## Main declarations

* `NonemptyInterval`: Nonempty intervals. Pairs where the second element is greater than the first.
* `Interval`: Intervals. Either `∅` or a nonempty interval.
-/

@[expose] public section


open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*} {κ : ι -> Sort*}

/-- The nonempty closed intervals in an order.

We define intervals by the pair of endpoints `fst`, `snd`. To convert intervals to the set of
elements between these endpoints, use the coercion `NonemptyInterval α → Set α`. -/
@[ext (flat := false)]
/--
Definition of `NonemptyInterval` / `NonemptyInterval` 的定义

English:
structure NonemptyInterval
  parameters: (α : Type*) [LE α]
  extends: Prod α α
  axioms and operations (1):
    - fst_le_snd : fst <= snd

中文:
结构 Nonempty整数erval
  参数: (α : 类型) [LE α]
  继承: 积类型 α α
  公理与运算 (1 个):
    - fst_le_snd : fst <= snd
-/
structure NonemptyInterval (α : Type*) [LE α] extends Prod α α where
  /-- The starting point of an interval is smaller than the endpoint. -/
  fst_le_snd : fst <= snd

namespace NonemptyInterval

section LE

variable [LE α] {s t : NonemptyInterval α}

/--
theorem `toProd_injective` / 定理 `toProd_injective`

English:
theorem toProd_injective
  statement: Injective (toProd : NonemptyInterval α -> α × α)
  proof: fun s t h => by cases s; cases t; congr

中文:
定理 toProd_injective
  结论: 单射 (toProd : Nonempty整数erval α -> α × α)
  证明: fun s t h => by cases s; cases t; congr
-/
theorem toProd_injective : Injective (toProd : NonemptyInterval α -> α × α) :=
  fun s t h => by cases s; cases t; congr

/--
Instance `instCanLift` / 实例 `instCanLift`

English:
instance instCanLift
  signature: :
  body: ⟨⟨x, hx⟩, rfl⟩

中文:
实例 instCanLift
  签名: :
  定义体: ⟨⟨x, hx⟩, rfl⟩
-/
instance instCanLift :
    CanLift (α × α) (NonemptyInterval α) NonemptyInterval.toProd (fun x => x.1 <= x.2) where
  prf x hx := ⟨⟨x, hx⟩, rfl⟩

/--
Definition of `toDualProd` / `toDualProd` 的定义

English:
definition toDualProd
  signature: : NonemptyInterval α -> αᵒᵈ × α
  body: toProd

@[simp]

中文:
定义 toDualProd
  签名: : Nonempty整数erval α -> αᵒᵈ × α
  定义体: toProd

@[simp]

Depends on / 依赖: toProd
-/
def toDualProd : NonemptyInterval α -> αᵒᵈ × α :=
  toProd

@[simp]
/--
theorem `toDualProd_apply` / 定理 `toDualProd_apply`

English:
theorem toDualProd_apply
  given: (s : NonemptyInterval α)
  statement: s.toDualProd = (toDual s.fst, s.snd)
  proof: rfl

中文:
定理 toDualProd_apply
  条件: (s : Nonempty整数erval α)
  结论: s.toDualProd = (toDual s.fst, s.snd)
  证明: rfl
-/
theorem toDualProd_apply (s : NonemptyInterval α) : s.toDualProd = (toDual s.fst, s.snd) :=
  rfl

/--
theorem `toDualProd_injective` / 定理 `toDualProd_injective`

English:
theorem toDualProd_injective
  statement: Injective (toDualProd : NonemptyInterval α -> αᵒᵈ × α)
  proof: toProd_injective

中文:
定理 toDualProd_injective
  结论: 单射 (toDualProd : Nonempty整数erval α -> αᵒᵈ × α)
  证明: toProd_injective

Depends on / 依赖: toProd_injective
-/
theorem toDualProd_injective : Injective (toDualProd : NonemptyInterval α -> αᵒᵈ × α) :=
  toProd_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : IsEmpty (NonemptyInterval α)
  body: ⟨fun s => isEmptyElim s.fst⟩

中文:
实例 [是空
  签名: α] : 是空 (Nonempty整数erval α)
  定义体: ⟨fun s => isEmptyElim s.fst⟩

Depends on / 依赖: isEmptyElim, s.fst
-/
instance [IsEmpty α] : IsEmpty (NonemptyInterval α) :=
  ⟨fun s => isEmptyElim s.fst⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] : Subsingleton (NonemptyInterval α)
  body: toDualProd_injective.subsingleton

中文:
实例 [子单例
  签名: α] : 子单例 (Nonempty整数erval α)
  定义体: toDualProd_injective.subsingleton

Depends on / 依赖: subsingleton, toDualProd_injective, toDualProd_injective.subsingleton
-/
instance [Subsingleton α] : Subsingleton (NonemptyInterval α) :=
  toDualProd_injective.subsingleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : DecidableEq (NonemptyInterval α)
  body: toDualProd_injective.decidableEq

中文:
实例 [DecidableEq
  签名: α] : DecidableEq (Nonempty整数erval α)
  定义体: toDualProd_injective.decidableEq

Depends on / 依赖: decidableEq, toDualProd_injective, toDualProd_injective.decidableEq
-/
instance [DecidableEq α] : DecidableEq (NonemptyInterval α) :=
  toDualProd_injective.decidableEq

/--
Instance `le` / 实例 `le`

English:
instance le
  signature: : LE (NonemptyInterval α)
  body: ⟨fun s t => t.fst <= s.fst ∧ s.snd <= t.snd⟩

中文:
实例 le
  签名: : LE (Nonempty整数erval α)
  定义体: ⟨fun s t => t.fst <= s.fst ∧ s.snd <= t.snd⟩

Depends on / 依赖: s.fst, s.snd, t.fst, t.snd
-/
instance le : LE (NonemptyInterval α) :=
  ⟨fun s t => t.fst <= s.fst ∧ s.snd <= t.snd⟩

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  statement: s <= t ↔ t.fst <= s.fst ∧ s.snd <= t.snd
  proof: Iff.rfl

中文:
定理 le_def
  结论: s <= t ↔ t.fst <= s.fst ∧ s.snd <= t.snd
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def : s <= t ↔ t.fst <= s.fst ∧ s.snd <= t.snd :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableLE
  signature: α] : DecidableLE (NonemptyInterval α)
  body: fun _ _ => decidable_of_iff' _ le_def

中文:
实例 [DecidableLE
  签名: α] : DecidableLE (Nonempty整数erval α)
  定义体: fun _ _ => decidable_of_iff' _ le_def

Depends on / 依赖: decidable_of_iff, le_def
-/
instance [DecidableLE α] : DecidableLE (NonemptyInterval α) :=
  fun _ _ => decidable_of_iff' _ le_def

/-- `toDualProd` as an order embedding. -/
@[simps]
/--
Definition of `toDualProdHom` / `toDualProdHom` 的定义

English:
definition toDualProdHom
  signature: : NonemptyInterval α ↪o αᵒᵈ × α where
  body: toDualProd
  inj' := toDualProd_injective
  map_rel_iff' := Iff.rfl

中文:
定义 toDualProdHom
  签名: : Nonempty整数erval α ↪o αᵒᵈ × α where
  定义体: toDualProd
  inj' := toDualProd_injective
  map_rel_iff' := Iff.rfl

Depends on / 依赖: toDualProd
-/
def toDualProdHom : NonemptyInterval α ↪o αᵒᵈ × α where
  toFun := toDualProd
  inj' := toDualProd_injective
  map_rel_iff' := Iff.rfl

/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : NonemptyInterval α ≃ NonemptyInterval αᵒᵈ where
  body: ⟨s.toProd.swap, s.fst_le_snd⟩
  invFun s := ⟨s.toProd.swap, s.fst_le_snd⟩

@[simp]

中文:
定义 dual
  签名: : Nonempty整数erval α ≃ Nonempty整数erval αᵒᵈ where
  定义体: ⟨s.toProd.swap, s.fst_le_snd⟩
  invFun s := ⟨s.toProd.swap, s.fst_le_snd⟩

@[simp]

Depends on / 依赖: fst_le_snd, s.fst_le_snd, s.toProd.swap, toProd
-/
def dual : NonemptyInterval α ≃ NonemptyInterval αᵒᵈ where
  toFun s := ⟨s.toProd.swap, s.fst_le_snd⟩
  invFun s := ⟨s.toProd.swap, s.fst_le_snd⟩

@[simp]
/--
theorem `fst_dual` / 定理 `fst_dual`

English:
theorem fst_dual
  given: (s : NonemptyInterval α)
  statement: s.dual.fst = toDual s.snd
  proof: rfl

@[simp]

中文:
定理 fst_dual
  条件: (s : Nonempty整数erval α)
  结论: s.dual.fst = toDual s.snd
  证明: rfl

@[simp]
-/
theorem fst_dual (s : NonemptyInterval α) : s.dual.fst = toDual s.snd :=
  rfl

@[simp]
/--
theorem `snd_dual` / 定理 `snd_dual`

English:
theorem snd_dual
  given: (s : NonemptyInterval α)
  statement: s.dual.snd = toDual s.fst
  proof: rfl

中文:
定理 snd_dual
  条件: (s : Nonempty整数erval α)
  结论: s.dual.snd = toDual s.fst
  证明: rfl
-/
theorem snd_dual (s : NonemptyInterval α) : s.dual.snd = toDual s.fst :=
  rfl

end LE

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] {s : NonemptyInterval α} {x : α × α} {a : α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (NonemptyInterval α)
  body: fast_instance% Preorder.lift toDualProd

中文:
实例 :
  签名: 预序 (Nonempty整数erval α)
  定义体: fast_instance% Preorder.lift toDualProd

Depends on / 依赖: Preorder, Preorder.lift, fast_instance, toDualProd
-/
instance : Preorder (NonemptyInterval α) :=
  fast_instance% Preorder.lift toDualProd

/--
theorem `toDualProd_mono` / 定理 `toDualProd_mono`

English:
theorem toDualProd_mono
  statement: Monotone (toDualProd : _ -> αᵒᵈ × α)
  proof: fun _ _ => id

中文:
定理 toDualProd_mono
  结论: 递增 (toDualProd : _ -> αᵒᵈ × α)
  证明: fun _ _ => id
-/
theorem toDualProd_mono : Monotone (toDualProd : _ -> αᵒᵈ × α) := fun _ _ => id

/--
theorem `toDualProd_strictMono` / 定理 `toDualProd_strictMono`

English:
theorem toDualProd_strictMono
  statement: StrictMono (toDualProd : _ -> αᵒᵈ × α)
  proof: fun _ _ => id

中文:
定理 toDualProd_strictMono
  结论: 严格递增 (toDualProd : _ -> αᵒᵈ × α)
  证明: fun _ _ => id
-/
theorem toDualProd_strictMono : StrictMono (toDualProd : _ -> αᵒᵈ × α) := fun _ _ => id

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (NonemptyInterval α) (Set α)
  body: ⟨fun s => Icc s.fst s.snd⟩

中文:
实例 :
  签名: Coe (Nonempty整数erval α) (集合 α)
  定义体: ⟨fun s => Icc s.fst s.snd⟩

Depends on / 依赖: s.fst, s.snd
-/
instance : Coe (NonemptyInterval α) (Set α) :=
  ⟨fun s => Icc s.fst s.snd⟩

instance (priority := 100) : Membership α (NonemptyInterval α) :=
  ⟨fun s a => a in (s : Set α)⟩

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {hx : x.1 <= x.2}
  statement: a in mk x hx ↔ x.1 <= a ∧ a <= x.2
  proof: Iff.rfl

中文:
定理 mem_mk
  条件: {hx : x.1 <= x.2}
  结论: a in mk x hx ↔ x.1 <= a ∧ a <= x.2
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk {hx : x.1 <= x.2} : a in mk x hx ↔ x.1 <= a ∧ a <= x.2 :=
  Iff.rfl

/--
theorem `mem_def` / 定理 `mem_def`

English:
theorem mem_def
  statement: a in s ↔ s.fst <= a ∧ a <= s.snd
  proof: Iff.rfl

中文:
定理 mem_def
  结论: a in s ↔ s.fst <= a ∧ a <= s.snd
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_def : a in s ↔ s.fst <= a ∧ a <= s.snd :=
  Iff.rfl

/--
theorem `coe_nonempty` / 定理 `coe_nonempty`

English:
theorem coe_nonempty
  given: (s : NonemptyInterval α)
  statement: (s : Set α).Nonempty
  proof: nonempty_Icc.2 s.fst_le_snd

中文:
定理 coe_nonempty
  条件: (s : Nonempty整数erval α)
  结论: (s : 集合 α).非空
  证明: nonempty_Icc.2 s.fst_le_snd

Depends on / 依赖: fst_le_snd, nonempty_Icc, s.fst_le_snd
-/
theorem coe_nonempty (s : NonemptyInterval α) : (s : Set α).Nonempty :=
  nonempty_Icc.2 s.fst_le_snd

/-- `{a}` as an interval. -/
@[simps]
/--
Definition of `pure` / `pure` 的定义

English:
definition pure
  signature: (a : α)
  body: ⟨⟨a, a⟩, le_rfl⟩

中文:
定义 pure
  签名: (a : α)
  定义体: ⟨⟨a, a⟩, le_rfl⟩

Depends on / 依赖: le_rfl
-/
def pure (a : α) : NonemptyInterval α :=
  ⟨⟨a, a⟩, le_rfl⟩

/--
theorem `mem_pure_self` / 定理 `mem_pure_self`

English:
theorem mem_pure_self
  given: (a : α)
  statement: a in pure a
  proof: ⟨le_rfl, le_rfl⟩

中文:
定理 mem_pure_self
  条件: (a : α)
  结论: a in pure a
  证明: ⟨le_rfl, le_rfl⟩

Depends on / 依赖: le_rfl
-/
theorem mem_pure_self (a : α) : a in pure a :=
  ⟨le_rfl, le_rfl⟩

/--
theorem `pure_injective` / 定理 `pure_injective`

English:
theorem pure_injective
  statement: Injective (pure : α -> NonemptyInterval α)
  proof: fun _ _ =>
congr_arg Prod.fst ∘ toProd

@[simp]

中文:
定理 pure_injective
  结论: 单射 (pure : α -> Nonempty整数erval α)
  证明: fun _ _ =>
congr_arg Prod.fst ∘ toProd

@[simp]
-/
theorem pure_injective : Injective (pure : α -> NonemptyInterval α) := fun _ _ =>
congr_arg Prod.fst ∘ toProd

@[simp]
/--
theorem `dual_pure` / 定理 `dual_pure`

English:
theorem dual_pure
  given: (a : α)
  statement: dual (pure a) = pure (toDual a)
  proof: rfl

中文:
定理 dual_pure
  条件: (a : α)
  结论: dual (pure a) = pure (toDual a)
  证明: rfl
-/
theorem dual_pure (a : α) : dual (pure a) = pure (toDual a) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (NonemptyInterval α)
  body: ⟨pure default⟩

中文:
实例 [可居
  签名: α] : 可居 (Nonempty整数erval α)
  定义体: ⟨pure default⟩
-/
instance [Inhabited α] : Inhabited (NonemptyInterval α) :=
  ⟨pure default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nonempty (NonemptyInterval α)
  body: Nonempty.map pure (by infer_instance)

中文:
实例 [非空
  签名: α] : 非空 (Nonempty整数erval α)
  定义体: Nonempty.map pure (by infer_instance)

Depends on / 依赖: Nonempty, Nonempty.map, infer_instance
-/
instance [Nonempty α] : Nonempty (NonemptyInterval α) :=
  Nonempty.map pure (by infer_instance)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: α] : Nontrivial (NonemptyInterval α)
  body: pure_injective.nontrivial

中文:
实例 [非平凡
  签名: α] : 非平凡 (Nonempty整数erval α)
  定义体: pure_injective.nontrivial

Depends on / 依赖: nontrivial, pure_injective, pure_injective.nontrivial
-/
instance [Nontrivial α] : Nontrivial (NonemptyInterval α) :=
  pure_injective.nontrivial

/-- Pushforward of nonempty intervals. -/
@[simps!]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α ->o β) (a : NonemptyInterval α)
  body: ⟨a.toProd.map f f, f.mono a.fst_le_snd⟩

@[simp]

中文:
定义 map
  签名: (f : α ->o β) (a : Nonempty整数erval α)
  定义体: ⟨a.toProd.map f f, f.mono a.fst_le_snd⟩

@[simp]

Depends on / 依赖: a.fst_le_snd, a.toProd.map, f.mono, fst_le_snd, toProd
-/
def map (f : α ->o β) (a : NonemptyInterval α) : NonemptyInterval β :=
  ⟨a.toProd.map f f, f.mono a.fst_le_snd⟩

@[simp]
/--
theorem `map_pure` / 定理 `map_pure`

English:
theorem map_pure
  given: (f : α ->o β) (a : α)
  statement: (pure a).map f = pure (f a)
  proof: rfl

@[simp]

中文:
定理 map_pure
  条件: (f : α ->o β) (a : α)
  结论: (pure a).map f = pure (f a)
  证明: rfl

@[simp]
-/
theorem map_pure (f : α ->o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : β ->o γ) (f : α ->o β) (a : NonemptyInterval α)
  proof: rfl

@[simp]

中文:
定理 map_map
  条件: (g : β ->o γ) (f : α ->o β) (a : Nonempty整数erval α)
  证明: rfl

@[simp]
-/
theorem map_map (g : β ->o γ) (f : α ->o β) (a : NonemptyInterval α) :
    (a.map f).map g = a.map (g.comp f) :=
  rfl

@[simp]
/--
theorem `dual_map` / 定理 `dual_map`

English:
theorem dual_map
  given: (f : α ->o β) (a : NonemptyInterval α)
  proof: rfl

中文:
定理 dual_map
  条件: (f : α ->o β) (a : Nonempty整数erval α)
  证明: rfl
-/
theorem dual_map (f : α ->o β) (a : NonemptyInterval α) :
    dual (a.map f) = a.dual.map f.dual :=
  rfl

/-- Binary pushforward of nonempty intervals. -/
@[simps]
/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (f : α -> β -> γ) (h₀ : forall b, Monotone fun a => f a b) (h₁ : forall a, Monotone (f a))
  body: fun s t =>
⟨(f s.fst t.fst, f s.snd t.snd), (h₀ _ s.fst_le_snd).trans h₁ _ t.fst_le_snd⟩

@[simp]

中文:
定义 map₂
  签名: (f : α -> β -> γ) (h₀ : 对任意 b, 递增 fun a => f a b) (h₁ : 对任意 a, 递增 (f a))
  定义体: fun s t =>
⟨(f s.fst t.fst, f s.snd t.snd), (h₀ _ s.fst_le_snd).trans h₁ _ t.fst_le_snd⟩

@[simp]
-/
def map₂ (f : α -> β -> γ) (h₀ : forall b, Monotone fun a => f a b) (h₁ : forall a, Monotone (f a)) :
    NonemptyInterval α -> NonemptyInterval β -> NonemptyInterval γ := fun s t =>
⟨(f s.fst t.fst, f s.snd t.snd), (h₀ _ s.fst_le_snd).trans h₁ _ t.fst_le_snd⟩

@[simp]
/--
theorem `map₂_pure` / 定理 `map₂_pure`

English:
theorem map₂_pure
  given: (f : α -> β -> γ) (h₀ h₁) (a : α) (b : β)
  proof: rfl

@[simp]

中文:
定理 map₂_pure
  条件: (f : α -> β -> γ) (h₀ h₁) (a : α) (b : β)
  证明: rfl

@[simp]
-/
theorem map₂_pure (f : α -> β -> γ) (h₀ h₁) (a : α) (b : β) :
    map₂ f h₀ h₁ (pure a) (pure b) = pure (f a b) :=
  rfl

@[simp]
/--
theorem `dual_map₂` / 定理 `dual_map₂`

English:
theorem dual_map₂
  given: (f : α -> β -> γ) (h₀ h₁ s t)
  proof: rfl

中文:
定理 dual_map₂
  条件: (f : α -> β -> γ) (h₀ h₁ s t)
  证明: rfl
-/
theorem dual_map₂ (f : α -> β -> γ) (h₀ h₁ s t) :
    dual (map₂ f h₀ h₁ s t) =
      map₂ (fun a b => toDual <| f (ofDual a) <| ofDual b) (fun _ => (h₀ _).dual)
        (fun _ => (h₁ _).dual) (dual s) (dual t) :=
  rfl

variable [BoundedOrder α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop (NonemptyInterval α)
  body: ⟨⟨⊥, ⊤⟩, bot_le⟩
  le_top _ := ⟨bot_le, le_top⟩

@[simp]

中文:
实例 :
  签名: 有顶序 (Nonempty整数erval α)
  定义体: ⟨⟨⊥, ⊤⟩, bot_le⟩
  le_top _ := ⟨bot_le, le_top⟩

@[simp]

Depends on / 依赖: bot_le
-/
instance : OrderTop (NonemptyInterval α) where
  top := ⟨⟨⊥, ⊤⟩, bot_le⟩
  le_top _ := ⟨bot_le, le_top⟩

@[simp]
/--
theorem `dual_top` / 定理 `dual_top`

English:
theorem dual_top
  statement: dual (⊤ : NonemptyInterval α) = ⊤
  proof: rfl

中文:
定理 dual_top
  结论: dual (⊤ : Nonempty整数erval α) = ⊤
  证明: rfl
-/
theorem dual_top : dual (⊤ : NonemptyInterval α) = ⊤ :=
  rfl

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {s t : NonemptyInterval α} {a b : α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (NonemptyInterval α)
  body: fast_instance% PartialOrder.lift _ toDualProd_injective

中文:
实例 :
  签名: 偏序 (Nonempty整数erval α)
  定义体: fast_instance% PartialOrder.lift _ toDualProd_injective

Depends on / 依赖: PartialOrder, PartialOrder.lift, fast_instance, toDualProd_injective
-/
instance : PartialOrder (NonemptyInterval α) :=
  fast_instance% PartialOrder.lift _ toDualProd_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableLE
  signature: α] : DecidableLE (NonemptyInterval α)
  body: fun _ _ => decidable_of_iff' _ le_def

中文:
实例 [DecidableLE
  签名: α] : DecidableLE (Nonempty整数erval α)
  定义体: fun _ _ => decidable_of_iff' _ le_def

Depends on / 依赖: decidable_of_iff, le_def
-/
instance [DecidableLE α] : DecidableLE (NonemptyInterval α) :=
  fun _ _ => decidable_of_iff' _ le_def

/--
Definition of `coeHom` / `coeHom` 的定义

English:
definition coeHom
  signature: : NonemptyInterval α ↪o Set α
  body: OrderEmbedding.ofMapLEIff (fun s => Icc s.fst s.snd) fun s _ => Icc_subset_Icc_iff s.fst_le_snd

中文:
定义 coeHom
  签名: : Nonempty整数erval α ↪o 集合 α
  定义体: OrderEmbedding.ofMapLEIff (fun s => Icc s.fst s.snd) fun s _ => Icc_subset_Icc_iff s.fst_le_snd

Depends on / 依赖: Icc_subset_Icc_iff, OrderEmbedding, OrderEmbedding.ofMapLEIff, fst_le_snd, ofMapLEIff, s.fst, s.fst_le_snd, s.snd
-/
def coeHom : NonemptyInterval α ↪o Set α :=
  OrderEmbedding.ofMapLEIff (fun s => Icc s.fst s.snd) fun s _ => Icc_subset_Icc_iff s.fst_le_snd

/--
Instance `setLike` / 实例 `setLike`

English:
instance setLike
  signature: : SetLike (NonemptyInterval α) α where
  body: Icc s.fst s.snd
  coe_injective := coeHom.injective

@[norm_cast]

中文:
实例 setLike
  签名: : 集合状 (Nonempty整数erval α) α where
  定义体: Icc s.fst s.snd
  coe_injective := coeHom.injective

@[norm_cast]

Depends on / 依赖: s.fst, s.snd
-/
instance setLike : SetLike (NonemptyInterval α) α where
  coe s := Icc s.fst s.snd
  coe_injective := coeHom.injective

@[norm_cast]
/--
theorem `coe_subset_coe` / 定理 `coe_subset_coe`

English:
theorem coe_subset_coe
  statement: (s : Set α) subseteq t ↔ (s : NonemptyInterval α) <= t
  proof: (@coeHom α _).le_iff_le

@[norm_cast]

中文:
定理 coe_subset_coe
  结论: (s : 集合 α) subseteq t ↔ (s : Nonempty整数erval α) <= t
  证明: (@coeHom α _).le_iff_le

@[norm_cast]

Depends on / 依赖: coeHom, le_iff_le
-/
theorem coe_subset_coe : (s : Set α) subseteq t ↔ (s : NonemptyInterval α) <= t :=
  (@coeHom α _).le_iff_le

@[norm_cast]
/--
theorem `coe_ssubset_coe` / 定理 `coe_ssubset_coe`

English:
theorem coe_ssubset_coe
  statement: (s : Set α) ⊂ t ↔ s < t
  proof: (@coeHom α _).lt_iff_lt

@[simp]

中文:
定理 coe_ssubset_coe
  结论: (s : 集合 α) ⊂ t ↔ s < t
  证明: (@coeHom α _).lt_iff_lt

@[simp]

Depends on / 依赖: coeHom, lt_iff_lt
-/
theorem coe_ssubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt

@[simp]
/--
theorem `coe_coeHom` / 定理 `coe_coeHom`

English:
theorem coe_coeHom
  statement: (coeHom : NonemptyInterval α -> Set α) = ((↑) : NonemptyInterval α -> Set α)
  proof: rfl

中文:
定理 coe_coeHom
  结论: (coeHom : Nonempty整数erval α -> 集合 α) = ((↑) : Nonempty整数erval α -> 集合 α)
  证明: rfl
-/
theorem coe_coeHom : (coeHom : NonemptyInterval α -> Set α) = ((↑) : NonemptyInterval α -> Set α) :=
  rfl

/--
theorem `coe_def` / 定理 `coe_def`

English:
theorem coe_def
  given: (s : NonemptyInterval α)
  statement: (s : Set α) = Set.Icc s.toProd.1 s.toProd.2
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_def
  条件: (s : Nonempty整数erval α)
  结论: (s : 集合 α) = 集合.闭区间 s.toProd.1 s.toProd.2
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_def (s : NonemptyInterval α) : (s : Set α) = Set.Icc s.toProd.1 s.toProd.2 := rfl

@[simp, norm_cast]
/--
theorem `coe_pure` / 定理 `coe_pure`

English:
theorem coe_pure
  given: (a : α)
  statement: (pure a : Set α) = {a}
  proof: Icc_self _

@[simp]

中文:
定理 coe_pure
  条件: (a : α)
  结论: (pure a : 集合 α) = {a}
  证明: Icc_self _

@[simp]

Depends on / 依赖: Icc_self
-/
theorem coe_pure (a : α) : (pure a : Set α) = {a} :=
  Icc_self _

@[simp]
/--
theorem `mem_pure` / 定理 `mem_pure`

English:
theorem mem_pure
  statement: b in pure a ↔ b = a
  proof: by
  rw [← SetLike.mem_coe]; rw [coe_pure]; rw [mem_singleton_iff]

@[simp, norm_cast]

中文:
定理 mem_pure
  结论: b in pure a ↔ b = a
  证明: by
  rw [← SetLike.mem_coe]; rw [coe_pure]; rw [mem_singleton_iff]

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.mem_coe, coe_pure, mem_coe, mem_singleton_iff
-/
theorem mem_pure : b in pure a ↔ b = a := by
  rw [← SetLike.mem_coe]; rw [coe_pure]; rw [mem_singleton_iff]

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  given: [BoundedOrder α]
  statement: ((⊤ : NonemptyInterval α) : Set α) = univ
  proof: Icc_bot_top

@[simp, norm_cast]

中文:
定理 coe_top
  条件: [有界序 α]
  结论: ((⊤ : Nonempty整数erval α) : 集合 α) = univ
  证明: Icc_bot_top

@[simp, norm_cast]

Depends on / 依赖: Icc_bot_top
-/
theorem coe_top [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Set α) = univ :=
  Icc_bot_top

@[simp, norm_cast]
/--
theorem `coe_dual` / 定理 `coe_dual`

English:
theorem coe_dual
  given: (s : NonemptyInterval α)
  statement: (dual s : Set αᵒᵈ) = ofDual ⁻¹' s
  proof: Icc_toDual

中文:
定理 coe_dual
  条件: (s : Nonempty整数erval α)
  结论: (dual s : 集合 αᵒᵈ) = ofDual ⁻¹' s
  证明: Icc_toDual

Depends on / 依赖: Icc_toDual
-/
theorem coe_dual (s : NonemptyInterval α) : (dual s : Set αᵒᵈ) = ofDual ⁻¹' s :=
  Icc_toDual

/--
theorem `subset_coe_map` / 定理 `subset_coe_map`

English:
theorem subset_coe_map
  given: (f : α ->o β) (s : NonemptyInterval α)
  statement: f '' s subseteq s.map f
  proof: image_subset_iff.2 fun _ ha => ⟨f.mono ha.1, f.mono ha.2⟩

中文:
定理 subset_coe_map
  条件: (f : α ->o β) (s : Nonempty整数erval α)
  结论: f '' s subseteq s.map f
  证明: image_subset_iff.2 fun _ ha => ⟨f.mono ha.1, f.mono ha.2⟩

Depends on / 依赖: f.mono, image_subset_iff
-/
theorem subset_coe_map (f : α ->o β) (s : NonemptyInterval α) : f '' s subseteq s.map f :=
  image_subset_iff.2 fun _ ha => ⟨f.mono ha.1, f.mono ha.2⟩

end PartialOrder

section Lattice

variable [Lattice α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (NonemptyInterval α)
  body: ⟨fun s t => ⟨⟨s.fst ⊓ t.fst, s.snd ⊔ t.snd⟩, inf_le_left.trans s.fst_le_snd.trans le_sup_left⟩⟩

中文:
实例 :
  签名: 最大值 (Nonempty整数erval α)
  定义体: ⟨fun s t => ⟨⟨s.fst ⊓ t.fst, s.snd ⊔ t.snd⟩, inf_le_left.trans s.fst_le_snd.trans le_sup_left⟩⟩

Depends on / 依赖: fst_le_snd, inf_le_left, inf_le_left.trans, le_sup_left, s.fst, s.fst_le_snd.trans, s.snd, t.fst, t.snd
-/
instance : Max (NonemptyInterval α) :=
⟨fun s t => ⟨⟨s.fst ⊓ t.fst, s.snd ⊔ t.snd⟩, inf_le_left.trans s.fst_le_snd.trans le_sup_left⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (NonemptyInterval α)
  body: fast_instance% toDualProd_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[simp]

中文:
实例 :
  签名: SemilatticeSup (Nonempty整数erval α)
  定义体: fast_instance% toDualProd_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[simp]

Depends on / 依赖: fast_instance, semilatticeSup, toDualProd_injective, toDualProd_injective.semilatticeSup
-/
instance : SemilatticeSup (NonemptyInterval α) :=
  fast_instance% toDualProd_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[simp]
/--
theorem `fst_sup` / 定理 `fst_sup`

English:
theorem fst_sup
  given: (s t : NonemptyInterval α)
  statement: (s ⊔ t).fst = s.fst ⊓ t.fst
  proof: rfl

@[simp]

中文:
定理 fst_sup
  条件: (s t : Nonempty整数erval α)
  结论: (s ⊔ t).fst = s.fst ⊓ t.fst
  证明: rfl

@[simp]
-/
theorem fst_sup (s t : NonemptyInterval α) : (s ⊔ t).fst = s.fst ⊓ t.fst :=
  rfl

@[simp]
/--
theorem `snd_sup` / 定理 `snd_sup`

English:
theorem snd_sup
  given: (s t : NonemptyInterval α)
  statement: (s ⊔ t).snd = s.snd ⊔ t.snd
  proof: rfl

中文:
定理 snd_sup
  条件: (s t : Nonempty整数erval α)
  结论: (s ⊔ t).snd = s.snd ⊔ t.snd
  证明: rfl
-/
theorem snd_sup (s t : NonemptyInterval α) : (s ⊔ t).snd = s.snd ⊔ t.snd :=
  rfl

end Lattice

end NonemptyInterval

/--
Definition of `Interval` / `Interval` 的定义

English:
definition Interval
  signature: (α : Type*) [LE α]
  body: WithBot (NonemptyInterval α)
deriving Inhabited, LE, OrderBot

中文:
定义 区间
  签名: (α : 类型) [LE α]
  定义体: WithBot (NonemptyInterval α)
deriving Inhabited, LE, OrderBot

Depends on / 依赖: NonemptyInterval, WithBot
-/
def Interval (α : Type*) [LE α] :=
  WithBot (NonemptyInterval α)
deriving Inhabited, LE, OrderBot

namespace Interval

section LE

variable [LE α]

/--
Definition of `coe` / `coe` 的定义

English:
definition coe
  signature: (x : NonemptyInterval α)
  body: (x : WithBot _)

中文:
定义 coe
  签名: (x : Nonempty整数erval α)
  定义体: (x : WithBot _)
-/
@[coe] def coe (x : NonemptyInterval α) : Interval α := (x : WithBot _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (NonemptyInterval α) (Interval α)
  body: ⟨coe⟩

中文:
实例 :
  签名: Coe (Nonempty整数erval α) (区间 α)
  定义体: ⟨coe⟩
-/
instance : Coe (NonemptyInterval α) (Interval α) :=
  ⟨coe⟩

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: : CanLift (Interval α) (NonemptyInterval α) (↑) fun r => r != ⊥
  body: WithBot.canLift

中文:
实例 canLift
  签名: : CanLift (区间 α) (Nonempty整数erval α) (↑) fun r => r != ⊥
  定义体: WithBot.canLift

Depends on / 依赖: WithBot, WithBot.canLift, canLift, fg_def, fg_def.mp, fg_def.mpr, span_union
-/
instance canLift : CanLift (Interval α) (NonemptyInterval α) (↑) fun r => r != ⊥ :=
  WithBot.canLift

/-- Recursor for `Interval` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/--
Definition of `recBotCoe` / `recBotCoe` 的定义

English:
definition recBotCoe
  signature: {C : Interval α -> Sort*} (bot : C ⊥) (coe : forall a : NonemptyInterval α, C a)
  body: WithBot.recBotCoe bot coe

中文:
定义 recBotCoe
  签名: {C : 区间 α -> 类型层*} (bot : C ⊥) (coe : 对任意 a : Nonempty整数erval α, C a)
  定义体: WithBot.recBotCoe bot coe

Depends on / 依赖: WithBot, WithBot.recBotCoe, recBotCoe
-/
def recBotCoe {C : Interval α -> Sort*} (bot : C ⊥) (coe : forall a : NonemptyInterval α, C a) :
    forall n : Interval α, C n :=
  WithBot.recBotCoe bot coe

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective ((↑) : NonemptyInterval α -> Interval α)
  proof: WithBot.coe_injective

@[norm_cast]

中文:
定理 coe_injective
  结论: 单射 ((↑) : Nonempty整数erval α -> 区间 α)
  证明: WithBot.coe_injective

@[norm_cast]

Depends on / 依赖: WithBot, WithBot.coe_injective, coe_injective
-/
theorem coe_injective : Injective ((↑) : NonemptyInterval α -> Interval α) :=
  WithBot.coe_injective

@[norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {s t : NonemptyInterval α}
  statement: (s : Interval α) = t ↔ s = t
  proof: WithBot.coe_inj

protected

中文:
定理 coe_inj
  条件: {s t : Nonempty整数erval α}
  结论: (s : 区间 α) = t ↔ s = t
  证明: WithBot.coe_inj

protected

Depends on / 依赖: WithBot, WithBot.coe_inj, coe_inj
-/
theorem coe_inj {s t : NonemptyInterval α} : (s : Interval α) = t ↔ s = t :=
  WithBot.coe_inj

protected
/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : Interval α -> Prop}
  statement: (forall s, p s) ↔ p ⊥ ∧ forall s : NonemptyInterval α, p s
  proof: Option.forall

protected

中文:
定理 «对任意»
  条件: {p : 区间 α -> 命题}
  结论: (对任意 s, p s) ↔ p ⊥ ∧ 对任意 s : Nonempty整数erval α, p s
  证明: Option.forall

protected
-/
theorem «forall» {p : Interval α -> Prop} : (forall s, p s) ↔ p ⊥ ∧ forall s : NonemptyInterval α, p s :=
  Option.forall

protected
/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {p : Interval α -> Prop}
  statement: (exists s, p s) ↔ p ⊥ ∨ exists s : NonemptyInterval α, p s
  proof: Option.exists

中文:
定理 «存在»
  条件: {p : 区间 α -> 命题}
  结论: (存在 s, p s) ↔ p ⊥ ∨ 存在 s : Nonempty整数erval α, p s
  证明: Option.exists
-/
theorem «exists» {p : Interval α -> Prop} : (exists s, p s) ↔ p ⊥ ∨ exists s : NonemptyInterval α, p s :=
  Option.exists

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Unique (Interval α)
  body: inferInstanceAs Unique (Option _)

中文:
实例 [是空
  签名: α] : 唯一 (区间 α)
  定义体: inferInstanceAs Unique (Option _)

Depends on / 依赖: Unique
-/
instance [IsEmpty α] : Unique (Interval α) :=
inferInstanceAs Unique (Option _)

/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : Interval α ≃ Interval αᵒᵈ
  body: NonemptyInterval.dual.withBotCongr

中文:
定义 dual
  签名: : 区间 α ≃ 区间 αᵒᵈ
  定义体: NonemptyInterval.dual.withBotCongr

Depends on / 依赖: NonemptyInterval, NonemptyInterval.dual.withBotCongr, fg_def, fg_def.mp, fg_def.mpr, ht.image, span_image, span_t, withBotCongr
-/
def dual : Interval α ≃ Interval αᵒᵈ :=
  NonemptyInterval.dual.withBotCongr

end LE

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (Interval α)
  body: inferInstanceAs Preorder (WithBot _)

中文:
实例 :
  签名: 预序 (区间 α)
  定义体: inferInstanceAs Preorder (WithBot _)

Depends on / 依赖: Preorder, WithBot
-/
instance : Preorder (Interval α) :=
inferInstanceAs Preorder (WithBot _)

/--
Definition of `pure` / `pure` 的定义

English:
definition pure
  signature: (a : α)
  body: NonemptyInterval.pure a

中文:
定义 pure
  签名: (a : α)
  定义体: NonemptyInterval.pure a

Depends on / 依赖: NonemptyInterval, NonemptyInterval.pure
-/
def pure (a : α) : Interval α :=
  NonemptyInterval.pure a

/--
theorem `pure_injective` / 定理 `pure_injective`

English:
theorem pure_injective
  statement: Injective (pure : α -> Interval α)
  proof: coe_injective.comp NonemptyInterval.pure_injective

@[simp]

中文:
定理 pure_injective
  结论: 单射 (pure : α -> 区间 α)
  证明: coe_injective.comp NonemptyInterval.pure_injective

@[simp]

Depends on / 依赖: NonemptyInterval, NonemptyInterval.pure_injective, coe_injective, coe_injective.comp, pure_injective
-/
theorem pure_injective : Injective (pure : α -> Interval α) :=
  coe_injective.comp NonemptyInterval.pure_injective

@[simp]
/--
theorem `dual_pure` / 定理 `dual_pure`

English:
theorem dual_pure
  given: (a : α)
  statement: dual (pure a) = pure (toDual a)
  proof: rfl

@[simp]

中文:
定理 dual_pure
  条件: (a : α)
  结论: dual (pure a) = pure (toDual a)
  证明: rfl

@[simp]
-/
theorem dual_pure (a : α) : dual (pure a) = pure (toDual a) :=
  rfl

@[simp]
/--
theorem `dual_bot` / 定理 `dual_bot`

English:
theorem dual_bot
  statement: dual (⊥ : Interval α) = ⊥
  proof: rfl

@[simp]

中文:
定理 dual_bot
  结论: dual (⊥ : 区间 α) = ⊥
  证明: rfl

@[simp]
-/
theorem dual_bot : dual (⊥ : Interval α) = ⊥ :=
  rfl

@[simp]
/--
theorem `pure_ne_bot` / 定理 `pure_ne_bot`

English:
theorem pure_ne_bot
  given: {a : α}
  statement: pure a != ⊥
  proof: WithBot.coe_ne_bot

@[simp]

中文:
定理 pure_ne_bot
  条件: {a : α}
  结论: pure a != ⊥
  证明: WithBot.coe_ne_bot

@[simp]

Depends on / 依赖: WithBot, WithBot.coe_ne_bot, coe_ne_bot
-/
theorem pure_ne_bot {a : α} : pure a != ⊥ :=
  WithBot.coe_ne_bot

@[simp]
/--
theorem `bot_ne_pure` / 定理 `bot_ne_pure`

English:
theorem bot_ne_pure
  given: {a : α}
  statement: ⊥ != pure a
  proof: WithBot.bot_ne_coe

中文:
定理 bot_ne_pure
  条件: {a : α}
  结论: ⊥ != pure a
  证明: WithBot.bot_ne_coe

Depends on / 依赖: WithBot, WithBot.bot_ne_coe, bot_ne_coe
-/
theorem bot_ne_pure {a : α} : ⊥ != pure a :=
  WithBot.bot_ne_coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nontrivial (Interval α)
  body: Option.nontrivial

中文:
实例 [非空
  签名: α] : 非平凡 (区间 α)
  定义体: Option.nontrivial

Depends on / 依赖: Option.nontrivial, e.le, le_antisymm, nontrivial, restrictScalars_injective, restrictScalars_le, span_le, span_le.mp, span_le_restrictScalars
-/
instance [Nonempty α] : Nontrivial (Interval α) :=
  Option.nontrivial

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α ->o β)
  body: WithBot.map (NonemptyInterval.map f)

@[simp]

中文:
定义 map
  签名: (f : α ->o β)
  定义体: WithBot.map (NonemptyInterval.map f)

@[simp]

Depends on / 依赖: NonemptyInterval, NonemptyInterval.map, WithBot, WithBot.map
-/
def map (f : α ->o β) : Interval α -> Interval β :=
  WithBot.map (NonemptyInterval.map f)

@[simp]
/--
theorem `map_pure` / 定理 `map_pure`

English:
theorem map_pure
  given: (f : α ->o β) (a : α)
  statement: (pure a).map f = pure (f a)
  proof: rfl

@[simp]

中文:
定理 map_pure
  条件: (f : α ->o β) (a : α)
  结论: (pure a).map f = pure (f a)
  证明: rfl

@[simp]
-/
theorem map_pure (f : α ->o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : β ->o γ) (f : α ->o β) (s : Interval α)
  statement: (s.map f).map g = s.map (g.comp f)
  proof: Option.map_map _ _ _

@[simp]

中文:
定理 map_map
  条件: (g : β ->o γ) (f : α ->o β) (s : 区间 α)
  结论: (s.map f).map g = s.map (g.comp f)
  证明: Option.map_map _ _ _

@[simp]

Depends on / 依赖: Option.map_map, map_map
-/
theorem map_map (g : β ->o γ) (f : α ->o β) (s : Interval α) : (s.map f).map g = s.map (g.comp f) :=
  Option.map_map _ _ _

@[simp]
/--
theorem `dual_map` / 定理 `dual_map`

English:
theorem dual_map
  given: (f : α ->o β) (s : Interval α)
  statement: dual (s.map f) = s.dual.map f.dual
  proof: by
  cases s
  · rfl
  · exact WithBot.map_comm rfl _

@[simp, norm_cast]

中文:
定理 dual_map
  条件: (f : α ->o β) (s : 区间 α)
  结论: dual (s.map f) = s.dual.map f.dual
  证明: by
  cases s
  · rfl
  · exact WithBot.map_comm rfl _

@[simp, norm_cast]

Depends on / 依赖: Finite, Finset, Finset.coe_univ, Finset.univ, Module, Module.Finite, WithBot, WithBot.map_comm, coe_univ, map_comm, nonempty_fintype, of_finite, span_univ
-/
theorem dual_map (f : α ->o β) (s : Interval α) : dual (s.map f) = s.dual.map f.dual := by
  cases s
  · rfl
  · exact WithBot.map_comm rfl _

@[simp, norm_cast]
/--
lemma `coe_le_coe` / 引理 `coe_le_coe`

English:
lemma coe_le_coe
  given: {s t : NonemptyInterval α}
  statement: (s : Interval α) <= t ↔ s <= t
  proof: WithBot.coe_le_coe

中文:
引理 coe_le_coe
  条件: {s t : Nonempty整数erval α}
  结论: (s : 区间 α) <= t ↔ s <= t
  证明: WithBot.coe_le_coe

Depends on / 依赖: WithBot, WithBot.coe_le_coe, coe_le_coe
-/
lemma coe_le_coe {s t : NonemptyInterval α} : (s : Interval α) <= t ↔ s <= t :=
  WithBot.coe_le_coe

variable [BoundedOrder α]

/--
Instance `boundedOrder` / 实例 `boundedOrder`

English:
instance boundedOrder
  signature: : BoundedOrder (Interval α)
  body: inferInstanceAs BoundedOrder (WithBot _)

@[simp]

中文:
实例 boundedOrder
  签名: : 有界序 (区间 α)
  定义体: inferInstanceAs BoundedOrder (WithBot _)

@[simp]

Depends on / 依赖: BoundedOrder, WithBot
-/
instance boundedOrder : BoundedOrder (Interval α) :=
inferInstanceAs BoundedOrder (WithBot _)

@[simp]
/--
theorem `dual_top` / 定理 `dual_top`

English:
theorem dual_top
  statement: dual (⊤ : Interval α) = ⊤
  proof: rfl

中文:
定理 dual_top
  结论: dual (⊤ : 区间 α) = ⊤
  证明: rfl
-/
theorem dual_top : dual (⊤ : Interval α) = ⊤ :=
  rfl

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {s t : Interval α} {a b : α}

/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: : PartialOrder (Interval α)
  body: inferInstanceAs PartialOrder (WithBot _)

中文:
实例 partialOrder
  签名: : 偏序 (区间 α)
  定义体: inferInstanceAs PartialOrder (WithBot _)

Depends on / 依赖: PartialOrder, WithBot
-/
instance partialOrder : PartialOrder (Interval α) :=
inferInstanceAs PartialOrder (WithBot _)

/--
Definition of `coeHom` / `coeHom` 的定义

English:
definition coeHom
  signature: : Interval α ↪o Set α
  body: OrderEmbedding.ofMapLEIff
    (fun s =>
      match s with
      | ⊥ => ∅
      | some s => s)
    fun s t =>
    match s, t with
    | ⊥, _ => iff_of_true bot_le bot_le
    | some s, ⊥ =>
      iff_of_false (fun h => s.coe_nonempty.ne_empty <| le_bot_iff.1 h) (WithBot.not_coe_le_bot _)
    | some _

中文:
定义 coeHom
  签名: : 区间 α ↪o 集合 α
  定义体: OrderEmbedding.ofMapLEIff
    (fun s =>
      match s with
      | ⊥ => ∅
      | some s => s)
    fun s t =>
    match s, t with
    | ⊥, _ => iff_of_true bot_le bot_le
    | some s, ⊥ =>
      iff_of_false (fun h => s.coe_nonempty.ne_empty <| le_bot_iff.1 h) (WithBot.not_coe_le_bot _)
    | some _

Depends on / 依赖: NonemptyInterval, NonemptyInterval.coeHom, OrderEmbedding, OrderEmbedding.ofMapLEIff, WithBot, WithBot.coe_le_coe.symm, WithBot.not_coe_le_bot, bot_le, coeHom, coe_le_coe, coe_nonempty, iff_of_false, iff_of_true, le_bot_iff, le_iff_le, le_iff_le.trans, ne_empty, not_coe_le_bot, ofMapLEIff, s.coe_nonempty.ne_empty
-/
def coeHom : Interval α ↪o Set α :=
  OrderEmbedding.ofMapLEIff
    (fun s =>
      match s with
      | ⊥ => ∅
      | some s => s)
    fun s t =>
    match s, t with
    | ⊥, _ => iff_of_true bot_le bot_le
    | some s, ⊥ =>
      iff_of_false (fun h => s.coe_nonempty.ne_empty <| le_bot_iff.1 h) (WithBot.not_coe_le_bot _)
    | some _, some _ => (@NonemptyInterval.coeHom α _).le_iff_le.trans WithBot.coe_le_coe.symm

/--
Instance `setLike` / 实例 `setLike`

English:
instance setLike
  signature: : SetLike (Interval α) α where
  body: coeHom
  coe_injective := coeHom.injective

@[norm_cast]

中文:
实例 setLike
  签名: : 集合状 (区间 α) α where
  定义体: coeHom
  coe_injective := coeHom.injective

@[norm_cast]

Depends on / 依赖: coeHom
-/
instance setLike : SetLike (Interval α) α where
  coe := coeHom
  coe_injective := coeHom.injective

@[norm_cast]
/--
theorem `coe_subset_coe` / 定理 `coe_subset_coe`

English:
theorem coe_subset_coe
  statement: (s : Set α) subseteq t ↔ s <= t
  proof: (@coeHom α _).le_iff_le

@[norm_cast]

中文:
定理 coe_subset_coe
  结论: (s : 集合 α) subseteq t ↔ s <= t
  证明: (@coeHom α _).le_iff_le

@[norm_cast]

Depends on / 依赖: coeHom, le_iff_le
-/
theorem coe_subset_coe : (s : Set α) subseteq t ↔ s <= t :=
  (@coeHom α _).le_iff_le

@[norm_cast]
/--
theorem `coe_sSubset_coe` / 定理 `coe_sSubset_coe`

English:
theorem coe_sSubset_coe
  statement: (s : Set α) ⊂ t ↔ s < t
  proof: (@coeHom α _).lt_iff_lt

@[simp, norm_cast]

中文:
定理 coe_sSubset_coe
  结论: (s : 集合 α) ⊂ t ↔ s < t
  证明: (@coeHom α _).lt_iff_lt

@[simp, norm_cast]

Depends on / 依赖: coeHom, lt_iff_lt
-/
theorem coe_sSubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt

@[simp, norm_cast]
/--
theorem `coe_pure` / 定理 `coe_pure`

English:
theorem coe_pure
  given: (a : α)
  statement: (pure a : Set α) = {a}
  proof: Icc_self _

@[simp, norm_cast]

中文:
定理 coe_pure
  条件: (a : α)
  结论: (pure a : 集合 α) = {a}
  证明: Icc_self _

@[simp, norm_cast]

Depends on / 依赖: Icc_self
-/
theorem coe_pure (a : α) : (pure a : Set α) = {a} :=
  Icc_self _

@[simp, norm_cast]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (s : NonemptyInterval α)
  statement: ((s : Interval α) : Set α) = s
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_coe
  条件: (s : Nonempty整数erval α)
  结论: ((s : 区间 α) : 集合 α) = s
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_coe (s : NonemptyInterval α) : ((s : Interval α) : Set α) = s :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : Interval α) : Set α) = ∅
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_bot
  结论: ((⊥ : 区间 α) : 集合 α) = ∅
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_bot : ((⊥ : Interval α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  given: [BoundedOrder α]
  statement: ((⊤ : Interval α) : Set α) = univ
  proof: Icc_bot_top

@[simp, norm_cast]

中文:
定理 coe_top
  条件: [有界序 α]
  结论: ((⊤ : 区间 α) : 集合 α) = univ
  证明: Icc_bot_top

@[simp, norm_cast]

Depends on / 依赖: Icc_bot_top
-/
theorem coe_top [BoundedOrder α] : ((⊤ : Interval α) : Set α) = univ :=
  Icc_bot_top

@[simp, norm_cast]
/--
theorem `coe_dual` / 定理 `coe_dual`

English:
theorem coe_dual
  given: (s : Interval α)
  statement: (dual s : Set αᵒᵈ) = ofDual ⁻¹' s
  proof: by
  cases s with
  | bot => rfl
  | coe s₀ => exact NonemptyInterval.coe_dual s₀

中文:
定理 coe_dual
  条件: (s : 区间 α)
  结论: (dual s : 集合 αᵒᵈ) = ofDual ⁻¹' s
  证明: by
  cases s with
  | bot => rfl
  | coe s₀ => exact NonemptyInterval.coe_dual s₀

Depends on / 依赖: NonemptyInterval, NonemptyInterval.coe_dual, coe_dual
-/
theorem coe_dual (s : Interval α) : (dual s : Set αᵒᵈ) = ofDual ⁻¹' s := by
  cases s with
  | bot => rfl
  | coe s₀ => exact NonemptyInterval.coe_dual s₀

/--
theorem `subset_coe_map` / 定理 `subset_coe_map`

English:
theorem subset_coe_map
  given: (f : α ->o β)
  statement: forall s : Interval α, f '' s subseteq s.map f

中文:
定理 subset_coe_map
  条件: (f : α ->o β)
  结论: 对任意 s : 区间 α, f '' s subseteq s.map f
-/
theorem subset_coe_map (f : α ->o β) : forall s : Interval α, f '' s subseteq s.map f
  | ⊥ => by simp
  | (s : NonemptyInterval α) => s.subset_coe_map _

@[simp]
/--
theorem `mem_pure` / 定理 `mem_pure`

English:
theorem mem_pure
  statement: b in pure a ↔ b = a
  proof: by rw [← SetLike.mem_coe, coe_pure, mem_singleton_iff]

中文:
定理 mem_pure
  结论: b in pure a ↔ b = a
  证明: by rw [← SetLike.mem_coe, coe_pure, mem_singleton_iff]

Depends on / 依赖: SetLike, SetLike.mem_coe, coe_pure, mem_coe, mem_singleton_iff
-/
theorem mem_pure : b in pure a ↔ b = a := by rw [← SetLike.mem_coe, coe_pure, mem_singleton_iff]

/--
theorem `mem_pure_self` / 定理 `mem_pure_self`

English:
theorem mem_pure_self
  given: (a : α)
  statement: a in pure a
  proof: mem_pure.2 rfl

中文:
定理 mem_pure_self
  条件: (a : α)
  结论: a in pure a
  证明: mem_pure.2 rfl

Depends on / 依赖: mem_pure
-/
theorem mem_pure_self (a : α) : a in pure a :=
  mem_pure.2 rfl

end PartialOrder

section Lattice

variable [Lattice α]

/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: : SemilatticeSup (Interval α)
  body: inferInstanceAs SemilatticeSup (WithBot _)

中文:
实例 semilatticeSup
  签名: : SemilatticeSup (区间 α)
  定义体: inferInstanceAs SemilatticeSup (WithBot _)

Depends on / 依赖: SemilatticeSup, WithBot
-/
instance semilatticeSup : SemilatticeSup (Interval α) :=
inferInstanceAs SemilatticeSup (WithBot _)

section Decidable

variable [DecidableLE α]

/--
Instance `lattice` / 实例 `lattice`

English:
instance lattice
  signature: : Lattice (Interval α)
  body: { Interval.semilatticeSup with
    inf := fun s t =>
      match s, t with
      | ⊥, _ => ⊥
      | _, ⊥ => ⊥
      | some s, some t =>
        if h : s.fst <= t.snd ∧ t.fst <= s.snd then
          coe ⟨⟨s.fst ⊔ t.fst, s.snd ⊓ t.snd⟩,
sup_le (le_inf s.fst_le_snd h.1) le_inf h.2 t.fst_le_snd⟩
      

中文:
实例 lattice
  签名: : 格 (区间 α)
  定义体: { Interval.semilatticeSup with
    inf := fun s t =>
      match s, t with
      | ⊥, _ => ⊥
      | _, ⊥ => ⊥
      | some s, some t =>
        if h : s.fst <= t.snd ∧ t.fst <= s.snd then
          coe ⟨⟨s.fst ⊔ t.fst, s.snd ⊓ t.snd⟩,
sup_le (le_inf s.fst_le_snd h.1) le_inf h.2 t.fst_le_snd⟩
      

Depends on / 依赖: Interval, Interval.semilatticeSup, WithBot, WithBot.coe_le_coe, bot_le, coe_le_coe, fst_le_snd, inf_le_left, inf_le_right, le_inf, le_sup_left, s.fst, s.fst_le_snd, s.snd, semilatticeSup, split_ifs, sup_le, t.fst, t.fst_le_snd, t.snd
-/
instance lattice : Lattice (Interval α) :=
  { Interval.semilatticeSup with
    inf := fun s t =>
      match s, t with
      | ⊥, _ => ⊥
      | _, ⊥ => ⊥
      | some s, some t =>
        if h : s.fst <= t.snd ∧ t.fst <= s.snd then
          coe ⟨⟨s.fst ⊔ t.fst, s.snd ⊓ t.snd⟩,
sup_le (le_inf s.fst_le_snd h.1) le_inf h.2 t.fst_le_snd⟩
        else ⊥
    inf_le_left := fun s t =>
      match s, t with
      | ⊥, ⊥ => bot_le
      | ⊥, some _ => bot_le
      | some _, ⊥ => bot_le
      | some s, some t => by
        change dite _ _ _ <= _
        split_ifs
        · exact WithBot.coe_le_coe.2 ⟨le_sup_left, inf_le_left⟩
        · exact bot_le
    inf_le_right := fun s t =>
      match s, t with
      | ⊥, ⊥ => bot_le
      | ⊥, some _ => bot_le
      | some _, ⊥ => bot_le
      | some s, some t => by
        change dite _ _ _ <= _
        split_ifs
        · exact WithBot.coe_le_coe.2 ⟨le_sup_right, inf_le_right⟩
        · exact bot_le
    le_inf := fun s t c =>
      match s, t, c with
      | ⊥, _, _ => fun _ _ => bot_le
      | (s : NonemptyInterval α), t, c => fun hb hc => by
        lift t to NonemptyInterval α using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hb
        lift c to NonemptyInterval α using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hc
        change _ <= dite _ _ _
        simp only [Interval.coe_le_coe] at hb hc ⊢
        rw [dif_pos]; rw [Interval.coe_le_coe]
        · exact ⟨sup_le hb.1 hc.1, le_inf hb.2 hc.2⟩
        -- Porting note: had to add the next 6 lines including the changes because
        -- it seems that lean cannot automatically turn `NonemptyInterval.toDualProd s`
        -- into `s.toProd` anymore.
        rcases hb with ⟨hb₁, hb₂⟩
        rcases hc with ⟨hc₁, hc₂⟩
        change t.toProd.fst <= s.toProd.fst at hb₁
        change s.toProd.snd <= t.toProd.snd at hb₂
        change c.toProd.fst <= s.toProd.fst at hc₁
        change s.toProd.snd <= c.toProd.snd at hc₂
        -- Porting note: originally it just had `hb.1` etc. in this next line
exact ⟨hb₁.trans s.fst_le_snd.trans hc₂, hc₁.trans s.fst_le_snd.trans hb₂⟩ }

/--
lemma `inf_coe` / 引理 `inf_coe`

English:
lemma inf_coe
  given: (s t : NonemptyInterval α)
  proof: rfl

@[simp, norm_cast]

中文:
引理 inf_coe
  条件: (s t : Nonempty整数erval α)
  证明: rfl

@[simp, norm_cast]
-/
lemma inf_coe (s t : NonemptyInterval α) :
    (s : Interval α) ⊓ t = if h : s.fst <= t.snd ∧ t.fst <= s.snd then
      coe ⟨⟨s.fst ⊔ t.fst, s.snd ⊓ t.snd⟩,
sup_le (le_inf s.fst_le_snd h.1) le_inf h.2 t.fst_le_snd⟩
      else ⊥ := rfl

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  statement: forall s t : Interval α, (↑(s ⊓ t) : Set α) = ↑s inter ↑t

中文:
定理 coe_inf
  结论: 对任意 s t : 区间 α, (↑(s ⊓ t) : 集合 α) = ↑s inter ↑t
-/
theorem coe_inf : forall s t : Interval α, (↑(s ⊓ t) : Set α) = ↑s inter ↑t
  | ⊥, _ => by
    rw [bot_inf_eq]
    exact (empty_inter _).symm
  | (s : NonemptyInterval α), ⊥ => by
    rw [inf_bot_eq]
    exact (inter_empty _).symm
  | (s : NonemptyInterval α), (t : NonemptyInterval α) => by
    simp only [coe_coe, NonemptyInterval.coe_def, Icc_inter_Icc, inf_coe]
    split_ifs with h
    · simp only [coe_coe, NonemptyInterval.coe_def]
    · refine (Icc_eq_empty <| mt ?_ h).symm
exact fun h => ⟨le_sup_left.trans h.trans inf_le_right,
le_sup_right.trans h.trans inf_le_left⟩

end Decidable

@[simp, norm_cast]
/--
theorem `disjoint_coe` / 定理 `disjoint_coe`

English:
theorem disjoint_coe
  given: (s t : Interval α)
  statement: Disjoint (s : Set α) t ↔ Disjoint s t
  proof: by
  classical
    rw [disjoint_iff_inf_le]; rw [disjoint_iff_inf_le]; rw [← coe_subset_coe]; rw [coe_inf]
    rfl

中文:
定理 disjoint_coe
  条件: (s t : 区间 α)
  结论: Disjoint (s : 集合 α) t ↔ Disjoint s t
  证明: by
  classical
    rw [disjoint_iff_inf_le]; rw [disjoint_iff_inf_le]; rw [← coe_subset_coe]; rw [coe_inf]
    rfl

Depends on / 依赖: classical, coe_inf, coe_subset_coe, disjoint_iff_inf_le
-/
theorem disjoint_coe (s t : Interval α) : Disjoint (s : Set α) t ↔ Disjoint s t := by
  classical
    rw [disjoint_iff_inf_le]; rw [disjoint_iff_inf_le]; rw [← coe_subset_coe]; rw [coe_inf]
    rfl

end Lattice

end Interval

namespace NonemptyInterval

section Preorder

variable [Preorder α] {s t : NonemptyInterval α} {a : α}

@[simp, norm_cast]
/--
theorem `coe_pure_interval` / 定理 `coe_pure_interval`

English:
theorem coe_pure_interval
  given: (a : α)
  statement: (pure a : Interval α) = Interval.pure a
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_pure_interval
  条件: (a : α)
  结论: (pure a : 区间 α) = 区间.pure a
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_pure_interval (a : α) : (pure a : Interval α) = Interval.pure a :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_eq_pure` / 定理 `coe_eq_pure`

English:
theorem coe_eq_pure
  statement: (s : Interval α) = Interval.pure a ↔ s = pure a
  proof: by
  rw [← Interval.coe_inj]; rw [coe_pure_interval]

@[simp, norm_cast]

中文:
定理 coe_eq_pure
  结论: (s : 区间 α) = 区间.pure a ↔ s = pure a
  证明: by
  rw [← Interval.coe_inj]; rw [coe_pure_interval]

@[simp, norm_cast]

Depends on / 依赖: Interval, Interval.coe_inj, coe_inj, coe_pure_interval
-/
theorem coe_eq_pure : (s : Interval α) = Interval.pure a ↔ s = pure a := by
  rw [← Interval.coe_inj]; rw [coe_pure_interval]

@[simp, norm_cast]
/--
theorem `coe_top_interval` / 定理 `coe_top_interval`

English:
theorem coe_top_interval
  given: [BoundedOrder α]
  statement: ((⊤ : NonemptyInterval α) : Interval α) = ⊤
  proof: rfl

中文:
定理 coe_top_interval
  条件: [有界序 α]
  结论: ((⊤ : Nonempty整数erval α) : 区间 α) = ⊤
  证明: rfl
-/
theorem coe_top_interval [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Interval α) = ⊤ :=
  rfl

end Preorder

@[simp, norm_cast]
/--
theorem `mem_coe_interval` / 定理 `mem_coe_interval`

English:
theorem mem_coe_interval
  given: [PartialOrder α] {s : NonemptyInterval α} {x : α}
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 mem_coe_interval
  条件: [偏序 α] {s : Nonempty整数erval α} {x : α}
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe_interval [PartialOrder α] {s : NonemptyInterval α} {x : α} :
    x in (s : Interval α) ↔ x in s :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_sup_interval` / 定理 `coe_sup_interval`

English:
theorem coe_sup_interval
  given: [Lattice α] (s t : NonemptyInterval α)
  proof: rfl

中文:
定理 coe_sup_interval
  条件: [格 α] (s t : Nonempty整数erval α)
  证明: rfl
-/
theorem coe_sup_interval [Lattice α] (s t : NonemptyInterval α) :
    (↑(s ⊔ t) : Interval α) = ↑s ⊔ ↑t :=
  rfl

end NonemptyInterval

namespace Interval

section CompleteLattice

variable [CompleteLattice α]

open scoped Classical in
/--
Instance `completeLattice` / 实例 `completeLattice`

English:
instance completeLattice
  signature: [DecidableLE α]
  body: fun S =>
    if h : S subseteq {⊥} then ⊥
    else
      coe
        ⟨⟨⨅ (s : NonemptyInterval α) (_ : ↑s in S), s.fst,
            ⨆ (s : NonemptyInterval α) (_ : ↑s in S), s.snd⟩, by
          obtain ⟨s, hs, ha⟩ := not_subset.1 h
          lift s to NonemptyInterval α using ha
          exact iInf

中文:
实例 completeLattice
  签名: [DecidableLE α]
  定义体: fun S =>
    if h : S subseteq {⊥} then ⊥
    else
      coe
        ⟨⟨⨅ (s : NonemptyInterval α) (_ : ↑s in S), s.fst,
            ⨆ (s : NonemptyInterval α) (_ : ↑s in S), s.snd⟩, by
          obtain ⟨s, hs, ha⟩ := not_subset.1 h
          lift s to NonemptyInterval α using ha
          exact iInf
-/
noncomputable instance completeLattice [DecidableLE α] : CompleteLattice (Interval α) where
  sSup := fun S =>
    if h : S subseteq {⊥} then ⊥
    else
      coe
        ⟨⟨⨅ (s : NonemptyInterval α) (_ : ↑s in S), s.fst,
            ⨆ (s : NonemptyInterval α) (_ : ↑s in S), s.snd⟩, by
          obtain ⟨s, hs, ha⟩ := not_subset.1 h
          lift s to NonemptyInterval α using ha
          exact iInf₂_le_of_le s hs (le_iSup₂_of_le s hs s.fst_le_snd)⟩
  isLUB_sSup _ := by
    constructor
    · intro s ha
      split_ifs with h
      · exact (h ha).le
      cases s
      · exact bot_le
      · -- Porting note: This case was
        -- `exact WithBot.some_le_some.2 ⟨iInf₂_le _ ha, le_iSup₂_of_le _ ha le_rfl⟩`
        -- but there seems to be a defEq-problem at `iInf₂_le` that lean cannot resolve yet.
        apply Interval.coe_le_coe.2
        constructor
        · apply iInf₂_le
          exact ha
        · exact le_iSup₂_of_le _ ha le_rfl
    · intro s ha
      split_ifs with h
      · exact bot_le
      obtain ⟨b, hs, hb⟩ := not_subset.1 h
      lift s to NonemptyInterval α using ne_bot_of_le_ne_bot hb (ha hs)
      exact
        Interval.coe_le_coe.2
          ⟨le_iInf₂ fun c hc => (WithBot.coe_le_coe.1 <| ha hc).1,
            iSup₂_le fun c hc => (WithBot.coe_le_coe.1 <| ha hc).2⟩
  sInf := fun S =>
    if h :
        ⊥ ∉ S ∧
          forall ⦃s : NonemptyInterval α⦄,
            ↑s in S -> forall ⦃t : NonemptyInterval α⦄, ↑t in S -> s.fst <= t.snd then
      coe
        ⟨⟨⨆ (s : NonemptyInterval α) (_ : ↑s in S), s.fst,
            ⨅ (s : NonemptyInterval α) (_ : ↑s in S), s.snd⟩,
iSup₂_le fun s hs => le_iInf₂ h.2 hs⟩
    else ⊥
  isGLB_sInf s₁ := by
    constructor
    · intro s ha
      split_ifs with h
      · lift s to NonemptyInterval α using ne_of_mem_of_not_mem ha h.1
        -- Porting note: Lean failed to figure out the function `f` by itself,
        -- so I added it through manually
        let f := fun (s : NonemptyInterval α) (_ : ↑s in s₁) => s.toProd.fst
        exact WithBot.coe_le_coe.2 ⟨le_iSup₂ (f := f) s ha, iInf₂_le s ha⟩
      · exact bot_le
    · intro s ha
      cases s with
      | bot => exact bot_le
      | coe s =>
        split_ifs with h
        · exact WithBot.coe_le_coe.2
            ⟨iSup₂_le fun t hb => (WithBot.coe_le_coe.1 <| ha hb).1,
              le_iInf₂ fun t hb => (WithBot.coe_le_coe.1 <| ha hb).2⟩
        · rw [not_and_or, not_not] at h
          rcases h with h | h
          · exact ha h
          · cases h fun b hb c hc => (WithBot.coe_le_coe.1 <| ha hb).1.trans
              (s.fst_le_snd.trans (WithBot.coe_le_coe.1 <| ha hc).2)

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: [DecidableLE α] (S : Set (Interval α))
  statement: ↑(sInf S) = ⋂ s in S, (s : Set α)
  proof: by
  classical
  change ((dite _ _ _ : Interval α) : Set α) = ⋂ (s : Interval α) (_ : s in S), (s : Set α)
  split_ifs with h
  · ext
    simp [Interval.forall, h.1, ← forall_and, ← NonemptyInterval.mem_def]
  simp_rw [not_and_or, Classical.not_not] at h
  rcases h with h | h
  · refine (eq_empty_of

中文:
定理 coe_sInf
  条件: [DecidableLE α] (S : 集合 (区间 α))
  结论: ↑(sInf S) = ⋂ s in S, (s : 集合 α)
  证明: by
  classical
  change ((dite _ _ _ : Interval α) : Set α) = ⋂ (s : Interval α) (_ : s in S), (s : Set α)
  split_ifs with h
  · ext
    simp [Interval.forall, h.1, ← forall_and, ← NonemptyInterval.mem_def]
  simp_rw [not_and_or, Classical.not_not] at h
  rcases h with h | h
  · refine (eq_empty_of

Depends on / 依赖: Classical, Classical.not_not, Interval, Interval.forall, NonemptyInterval, NonemptyInterval.mem_def, Subset, Subset.rfl, classical, eq_empty_of_subset_empty, forall_and, mem_def, not_and_or, not_nonempty_iff_eq_empty, not_not, simp_rw, split_ifs
-/
theorem coe_sInf [DecidableLE α] (S : Set (Interval α)) : ↑(sInf S) = ⋂ s in S, (s : Set α) := by
  classical
  change ((dite _ _ _ : Interval α) : Set α) = ⋂ (s : Interval α) (_ : s in S), (s : Set α)
  split_ifs with h
  · ext
    simp [Interval.forall, h.1, ← forall_and, ← NonemptyInterval.mem_def]
  simp_rw [not_and_or, Classical.not_not] at h
  rcases h with h | h
  · refine (eq_empty_of_subset_empty ?_).symm
    exact iInter₂_subset_of_subset _ h Subset.rfl
  · refine (not_nonempty_iff_eq_empty.1 ?_).symm
    rintro ⟨x, hx⟩
    rw [mem_iInter₂] at hx
    exact h fun s ha t hb => (hx _ ha).1.trans (hx _ hb).2

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: [DecidableLE α] (f : ι -> Interval α)
  proof: by simp [iInf]

@[norm_cast]

中文:
定理 coe_iInf
  条件: [DecidableLE α] (f : ι -> 区间 α)
  证明: by simp [iInf]

@[norm_cast]
-/
theorem coe_iInf [DecidableLE α] (f : ι -> Interval α) :
    ↑(⨅ i, f i) = ⋂ i, (f i : Set α) := by simp [iInf]

@[norm_cast]
/--
theorem `coe_iInf₂` / 定理 `coe_iInf₂`

English:
theorem coe_iInf₂
  given: [DecidableLE α] (f : forall i, κ i -> Interval α)
  proof: by simp_rw [coe_iInf]

中文:
定理 coe_iInf₂
  条件: [DecidableLE α] (f : 对任意 i, κ i -> 区间 α)
  证明: by simp_rw [coe_iInf]

Depends on / 依赖: coe_iInf, simp_rw
-/
theorem coe_iInf₂ [DecidableLE α] (f : forall i, κ i -> Interval α) :
    ↑(⨅ (i) (j), f i j) = ⋂ (i) (j), (f i j : Set α) := by simp_rw [coe_iInf]

end CompleteLattice

end Interval
