/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Order.Disjoint
public import Mathlib.Order.RelIso.Basic
public import Mathlib.Tactic.Monotonicity.Attr
public import Mathlib.Tactic.PPWithUniv

/-!
# Order homomorphisms

This file defines order homomorphisms, which are bundled monotone functions. A preorder
homomorphism `f : α →o β` is a function `α → β` along with a proof that `∀ x y, x ≤ y → f x ≤ f y`.

## Main definitions

In this file we define the following bundled monotone maps:
* `OrderHom α β` a.k.a. `α →o β`: Preorder homomorphism.
  An `OrderHom α β` is a function `f : α → β` such that `a₁ ≤ a₂ → f a₁ ≤ f a₂`
* `OrderEmbedding α β` a.k.a. `α ↪o β`: Relation embedding.
  An `OrderEmbedding α β` is an embedding `f : α ↪ β` such that `a ≤ b ↔ f a ≤ f b`.
  Defined as an abbreviation of `@RelEmbedding α β (≤) (≤)`.
* `OrderIso`: Relation isomorphism.
  An `OrderIso α β` is an equivalence `f : α ≃ β` such that `a ≤ b ↔ f a ≤ f b`.
  Defined as an abbreviation of `@RelIso α β (≤) (≤)`.

We also define many `OrderHom`s. In some cases we define two versions, one with `ₘ` suffix and
one without it (e.g., `OrderHom.compₘ` and `OrderHom.comp`). This means that the former
function is a "more bundled" version of the latter. We can't just drop the "less bundled" version
because the more bundled version usually does not work with dot notation.

* `OrderHom.id`: identity map as `α →o α`;
* `OrderHom.curry`: an order isomorphism between `α × β →o γ` and `α →o β →o γ`;
* `OrderHom.comp`: composition of two bundled monotone maps;
* `OrderHom.compₘ`: composition of bundled monotone maps as a bundled monotone map;
* `OrderHom.const`: constant function as a bundled monotone map;
* `OrderHom.prod`: combine `α →o β` and `α →o γ` into `α →o β × γ`;
* `OrderHom.prodₘ`: a more bundled version of `OrderHom.prod`;
* `OrderHom.prodIso`: order isomorphism between `α →o β × γ` and `(α →o β) × (α →o γ)`;
* `OrderHom.diag`: diagonal embedding of `α` into `α × α` as a bundled monotone map;
* `OrderHom.onDiag`: restrict a monotone map `α →o α →o β` to the diagonal;
* `OrderHom.fst`: projection `Prod.fst : α × β → α` as a bundled monotone map;
* `OrderHom.snd`: projection `Prod.snd : α × β → β` as a bundled monotone map;
* `OrderHom.prodMap`: `Prod.map f g` as a bundled monotone map;
* `Pi.evalOrderHom`: evaluation of a function at a point `Function.eval i` as a bundled
  monotone map;
* `OrderHom.coeFnHom`: coercion to function as a bundled monotone map;
* `OrderHom.apply`: application of an `OrderHom` at a point as a bundled monotone map;
* `OrderHom.pi`: combine a family of monotone maps `f i : α →o π i` into a monotone map
  `α →o Π i, π i`;
* `OrderHom.piIso`: order isomorphism between `α →o Π i, π i` and `Π i, α →o π i`;
* `OrderHom.subtype.val`: embedding `Subtype.val : Subtype p → α` as a bundled monotone map;
* `OrderHom.dual`: reinterpret a monotone map `α →o β` as a monotone map `αᵒᵈ →o βᵒᵈ`;
* `OrderHom.dualIso`: order isomorphism between `α →o β` and `(αᵒᵈ →o βᵒᵈ)ᵒᵈ`;
* `OrderHom.compl`: order isomorphism `α ≃o αᵒᵈ` given by taking complements in a
  Boolean algebra;

We also define two functions to convert other bundled maps to `α →o β`:

* `OrderEmbedding.toOrderHom`: convert `α ↪o β` to `α →o β`;
* `RelHom.toOrderHom`: convert a `RelHom` between strict orders to an `OrderHom`.

## Tags

monotone map, bundled morphism
-/

@[expose] public section

-- Developments relating order homs and sets belong in `Order.Hom.Set` or later.
assert_not_imported Mathlib.Data.Set.Basic

open OrderDual

variable {F α β γ δ : Type*}

/--
Definition of `OrderHom` / `OrderHom` 的定义

English:
structure OrderHom
  parameters: (α β : Type*) [Preorder α] [Preorder β]
  axioms and operations (2):
    - toFun : α -> β
    - monotone' : Monotone toFun

中文:
结构 OrderHom
  参数: (α β : 类型) [Preorder α] [Preorder β]
  公理与运算 (2 个):
    - toFun : α -> β
    - monotone' : Monotone toFun
-/
structure OrderHom (α β : Type*) [Preorder α] [Preorder β] where
  /-- The underlying function of an `OrderHom`. -/
  toFun : α -> β
  /-- The underlying function of an `OrderHom` is monotone. -/
  monotone' : Monotone toFun

/-- Notation for an `OrderHom`. -/
infixr:25 " ->o " => OrderHom

/--
Definition of `OrderEmbedding` / `OrderEmbedding` 的定义

English:
abbreviation OrderEmbedding
  signature: (α β : Type*) [LE α] [LE β]
  body: @RelEmbedding α β (· <= ·) (· <= ·)

to_dual_insert_cast_fun OrderEmbedding :=
  fun i => ⟨i.1, by rw [forall_comm]; exact @i.2⟩,
  fun i => ⟨i.1, by rw [forall_comm]; exact @i.2⟩

中文:
缩写 OrderEmbedding
  签名: (α β : 类型) [LE α] [LE β]
  定义体: @RelEmbedding α β (· <= ·) (· <= ·)

to_dual_insert_cast_fun OrderEmbedding :=
  fun i => ⟨i.1, by rw [forall_comm]; exact @i.2⟩,
  fun i => ⟨i.1, by rw [forall_comm]; exact @i.2⟩

Depends on / 依赖: RelEmbedding
-/
abbrev OrderEmbedding (α β : Type*) [LE α] [LE β] :=
  @RelEmbedding α β (· <= ·) (· <= ·)

to_dual_insert_cast_fun OrderEmbedding :=
  fun i => ⟨i.1, by rw [forall_comm]; exact @i.2⟩,
  fun i => ⟨i.1, by rw [forall_comm]; exact @i.2⟩

/-- Notation for an `OrderEmbedding`. -/
infixl:25 " ↪o " => OrderEmbedding

/--
Definition of `OrderIso` / `OrderIso` 的定义

English:
abbreviation OrderIso
  signature: (α β : Type*) [LE α] [LE β]
  body: @RelIso α β (· <= ·) (· <= ·)

to_dual_insert_cast_fun OrderIso :=
  fun i => ⟨i.1, by rw [forall_comm]; exact @i.2⟩,
  fun i => ⟨i.1, by rw [forall_comm]; exact @i.2⟩

中文:
缩写 OrderIso
  签名: (α β : 类型) [LE α] [LE β]
  定义体: @RelIso α β (· <= ·) (· <= ·)

to_dual_insert_cast_fun OrderIso :=
  fun i => ⟨i.1, by rw [forall_comm]; exact @i.2⟩,
  fun i => ⟨i.1, by rw [forall_comm]; exact @i.2⟩

Depends on / 依赖: RelIso
-/
abbrev OrderIso (α β : Type*) [LE α] [LE β] :=
  @RelIso α β (· <= ·) (· <= ·)

to_dual_insert_cast_fun OrderIso :=
  fun i => ⟨i.1, by rw [forall_comm]; exact @i.2⟩,
  fun i => ⟨i.1, by rw [forall_comm]; exact @i.2⟩

/-- Notation for an `OrderIso`. -/
infixl:25 " ≃o " => OrderIso

-- These instances are here just to make `to_dual` work correctly
instance (α β : Type*) [LE α] [LE β] : FunLike (α ↪o β) α β := RelEmbedding.instFunLike
instance (α β : Type*) [LE α] [LE β] : FunLike (α ≃o β) α β := RelIso.instFunLike

section

/--
Definition of `OrderHomClass` / `OrderHomClass` 的定义

English:
abbreviation OrderHomClass
  signature: (F : Type*) (α β : outParam Type*) [LE α] [LE β] [FunLike F α β]
  body: RelHomClass F ((· <= ·) : α -> α -> Prop) ((· <= ·) : β -> β -> Prop)

to_dual_insert_cast OrderHomClass := by grind only [RelHomClass]

中文:
缩写 OrderHomClass
  签名: (F : 类型) (α β : outParam 类型) [LE α] [LE β] [FunLike F α β]
  定义体: RelHomClass F ((· <= ·) : α -> α -> Prop) ((· <= ·) : β -> β -> Prop)

to_dual_insert_cast OrderHomClass := by grind only [RelHomClass]

Depends on / 依赖: RelHomClass
-/
abbrev OrderHomClass (F : Type*) (α β : outParam Type*) [LE α] [LE β] [FunLike F α β] :=
  RelHomClass F ((· <= ·) : α -> α -> Prop) ((· <= ·) : β -> β -> Prop)

to_dual_insert_cast OrderHomClass := by grind only [RelHomClass]

/--
Definition of `OrderIsoClass` / `OrderIsoClass` 的定义

English:
class OrderIsoClass
  parameters: (F : Type*) (α β : outParam Type*) [LE α] [LE β] [EquivLike F α β]
  axioms and operations (1):
    - map_le_map_iff((f : F) {a b : α}) : f a <= f b ↔ a <= b

中文:
类 OrderIsoClass
  参数: (F : 类型) (α β : outParam 类型) [LE α] [LE β] [EquivLike F α β]
  公理与运算 (1 个):
    - map_le_map_iff((f : F) {a b : α}) : f a <= f b ↔ a <= b
-/
class OrderIsoClass (F : Type*) (α β : outParam Type*) [LE α] [LE β] [EquivLike F α β] :
    Prop where
  /-- An order isomorphism respects `≤`. -/
  map_le_map_iff (f : F) {a b : α} : f a <= f b ↔ a <= b

attribute [to_dual self] OrderIsoClass.map_le_map_iff

end

export OrderIsoClass (map_le_map_iff)

attribute [simp] map_le_map_iff

/-- Turn an element of a type `F` satisfying `OrderIsoClass F α β` into an actual
`OrderIso`. This is declared as the default coercion from `F` to `α ≃o β`. -/
@[coe]
/--
Definition of `OrderIsoClass.toOrderIso` / `OrderIsoClass.toOrderIso` 的定义

English:
definition OrderIsoClass.toOrderIso
  signature: [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] (f : F)
  body: { EquivLike.toEquiv f with map_rel_iff' := map_le_map_iff f }

中文:
定义 OrderIsoClass.toOrderIso
  签名: [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] (f : F)
  定义体: { EquivLike.toEquiv f with map_rel_iff' := map_le_map_iff f }

Depends on / 依赖: EquivLike, EquivLike.toEquiv, map_le_map_iff, map_rel_iff, toEquiv
-/
def OrderIsoClass.toOrderIso [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] (f : F) :
    α ≃o β :=
  { EquivLike.toEquiv f with map_rel_iff' := map_le_map_iff f }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] : CoeTC F (α ≃o β)
  body: ⟨OrderIsoClass.toOrderIso⟩

中文:
实例 [LE
  签名: α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] : CoeTC F (α ≃o β)
  定义体: ⟨OrderIsoClass.toOrderIso⟩
-/
instance [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] : CoeTC F (α ≃o β) :=
  ⟨OrderIsoClass.toOrderIso⟩

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toOrderHomClass [LE α] [LE β]
    [EquivLike F α β] [OrderIsoClass F α β] : OrderHomClass F α β :=
  { EquivLike.toEmbeddingLike (E := F) with
    map_rel := fun f _ _ => (map_le_map_iff f).2 }

namespace OrderHomClass

variable [Preorder α] [Preorder β] [FunLike F α β] [OrderHomClass F α β]

/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  given: (f : F)
  statement: Monotone f
  proof: fun _ _ => map_rel f

@[gcongr]

中文:
定理 monotone
  条件: (f : F)
  结论: Monotone f
  证明: fun _ _ => map_rel f

@[gcongr]
-/
protected theorem monotone (f : F) : Monotone f := fun _ _ => map_rel f

@[gcongr]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (f : F)
  statement: Monotone f
  proof: fun _ _ => map_rel f

中文:
定理 mono
  条件: (f : F)
  结论: Monotone f
  证明: fun _ _ => map_rel f
-/
protected theorem mono (f : F) : Monotone f := fun _ _ => map_rel f

/-- Turn an element of a type `F` satisfying `OrderHomClass F α β` into an actual
`OrderHom`. This is declared as the default coercion from `F` to `α →o β`. -/
@[coe]
/--
Definition of `toOrderHom` / `toOrderHom` 的定义

English:
definition toOrderHom
  signature: (f : F)
  body: f
  monotone' := OrderHomClass.monotone f

中文:
定义 toOrderHom
  签名: (f : F)
  定义体: f
  monotone' := OrderHomClass.monotone f
-/
def toOrderHom (f : F) : α ->o β where
  toFun := f
  monotone' := OrderHomClass.monotone f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC F (α ->o β)
  body: ⟨toOrderHom⟩

中文:
实例 :
  签名: CoeTC F (α ->o β)
  定义体: ⟨toOrderHom⟩

Depends on / 依赖: toOrderHom
-/
instance : CoeTC F (α ->o β) :=
  ⟨toOrderHom⟩

end OrderHomClass

section OrderIsoClass

section LE

variable [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β]

@[to_dual (attr := simp) le_map_inv_iff]
/--
theorem `map_inv_le_iff` / 定理 `map_inv_le_iff`

English:
theorem map_inv_le_iff
  given: (f : F) {a : α} {b : β}
  statement: EquivLike.inv f b <= a ↔ b <= f a
  proof: by
  convert! (map_le_map_iff f).symm
  exact (EquivLike.right_inv f _).symm

@[to_dual self]

中文:
定理 map_inv_le_iff
  条件: (f : F) {a : α} {b : β}
  结论: EquivLike.inv f b <= a ↔ b <= f a
  证明: by
  convert! (map_le_map_iff f).symm
  exact (EquivLike.right_inv f _).symm

@[to_dual self]

Depends on / 依赖: EquivLike, EquivLike.right_inv, convert, map_le_map_iff, right_inv
-/
theorem map_inv_le_iff (f : F) {a : α} {b : β} : EquivLike.inv f b <= a ↔ b <= f a := by
  convert! (map_le_map_iff f).symm
  exact (EquivLike.right_inv f _).symm

@[to_dual self]
/--
theorem `map_inv_le_map_inv_iff` / 定理 `map_inv_le_map_inv_iff`

English:
theorem map_inv_le_map_inv_iff
  given: (f : F) {a b : β}
  proof: by
  simp

中文:
定理 map_inv_le_map_inv_iff
  条件: (f : F) {a b : β}
  证明: by
  simp
-/
theorem map_inv_le_map_inv_iff (f : F) {a b : β} :
    EquivLike.inv f b <= EquivLike.inv f a ↔ b <= a := by
  simp

end LE

variable [Preorder α] [Preorder β] [EquivLike F α β] [OrderIsoClass F α β]

@[to_dual self]
/--
theorem `map_lt_map_iff` / 定理 `map_lt_map_iff`

English:
theorem map_lt_map_iff
  given: (f : F) {a b : α}
  statement: f a < f b ↔ a < b
  proof: lt_iff_lt_of_le_iff_le' (map_le_map_iff f) (map_le_map_iff f)

@[to_dual (attr := simp) lt_map_inv_iff]

中文:
定理 map_lt_map_iff
  条件: (f : F) {a b : α}
  结论: f a < f b ↔ a < b
  证明: lt_iff_lt_of_le_iff_le' (map_le_map_iff f) (map_le_map_iff f)

@[to_dual (attr := simp) lt_map_inv_iff]

Depends on / 依赖: lt_iff_lt_of_le_iff_le, map_le_map_iff
-/
theorem map_lt_map_iff (f : F) {a b : α} : f a < f b ↔ a < b :=
  lt_iff_lt_of_le_iff_le' (map_le_map_iff f) (map_le_map_iff f)

@[to_dual (attr := simp) lt_map_inv_iff]
/--
theorem `map_inv_lt_iff` / 定理 `map_inv_lt_iff`

English:
theorem map_inv_lt_iff
  given: (f : F) {a : α} {b : β}
  statement: EquivLike.inv f b < a ↔ b < f a
  proof: by
  rw [← map_lt_map_iff f]
  simp only [EquivLike.apply_inv_apply]

@[to_dual self]

中文:
定理 map_inv_lt_iff
  条件: (f : F) {a : α} {b : β}
  结论: EquivLike.inv f b < a ↔ b < f a
  证明: by
  rw [← map_lt_map_iff f]
  simp only [EquivLike.apply_inv_apply]

@[to_dual self]

Depends on / 依赖: EquivLike, EquivLike.apply_inv_apply, apply_inv_apply, map_lt_map_iff
-/
theorem map_inv_lt_iff (f : F) {a : α} {b : β} : EquivLike.inv f b < a ↔ b < f a := by
  rw [← map_lt_map_iff f]
  simp only [EquivLike.apply_inv_apply]

@[to_dual self]
/--
theorem `map_inv_lt_map_inv_iff` / 定理 `map_inv_lt_map_inv_iff`

English:
theorem map_inv_lt_map_inv_iff
  given: (f : F) {a b : β}
  proof: by
  simp

中文:
定理 map_inv_lt_map_inv_iff
  条件: (f : F) {a b : β}
  证明: by
  simp
-/
theorem map_inv_lt_map_inv_iff (f : F) {a b : β} :
    EquivLike.inv f b < EquivLike.inv f a ↔ b < a := by
  simp

end OrderIsoClass

namespace OrderHom

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (α ->o β) α β
  body: toFun
  coe_injective f g h := by cases f; cases g; congr

中文:
实例 :
  签名: FunLike (α ->o β) α β
  定义体: toFun
  coe_injective f g h := by cases f; cases g; congr
-/
instance : FunLike (α ->o β) α β where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderHomClass (α ->o β) α β
  body: f.monotone' h

中文:
实例 :
  签名: OrderHomClass (α ->o β) α β
  定义体: f.monotone' h

Depends on / 依赖: f.monotone, monotone
-/
instance : OrderHomClass (α ->o β) α β where
  map_rel f _ _ h := f.monotone' h

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : α -> β) (hf : Monotone f)
  statement: ⇑(mk f hf) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : α -> β) (hf : Monotone f)
  结论: ⇑(mk f hf) = f
  证明: rfl
-/
@[simp] theorem coe_mk (f : α -> β) (hf : Monotone f) : ⇑(mk f hf) = f := rfl

/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  given: (f : α ->o β)
  statement: Monotone f
  proof: f.monotone'

中文:
定理 monotone
  条件: (f : α ->o β)
  结论: Monotone f
  证明: f.monotone'
-/
protected theorem monotone (f : α ->o β) : Monotone f :=
  f.monotone'

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (f : α ->o β)
  statement: Monotone f
  proof: f.monotone

中文:
定理 mono
  条件: (f : α ->o β)
  结论: Monotone f
  证明: f.monotone
-/
protected theorem mono (f : α ->o β) : Monotone f :=
  f.monotone

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (f : α ->o β)
  body: f

中文:
定义 Simps.coe
  签名: (f : α ->o β)
  定义体: f
-/
def Simps.coe (f : α ->o β) : α -> β := f

/- TODO: all other DFunLike classes use `apply` instead of `coe`
for the projection names. Maybe we should change this. -/
initialize_simps_projections OrderHom (toFun -> coe)

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : α ->o β)
  statement: f.toFun = f
  proof: rfl

中文:
定理 toFun_eq_coe
  条件: (f : α ->o β)
  结论: f.toFun = f
  证明: rfl
-/
@[simp] theorem toFun_eq_coe (f : α ->o β) : f.toFun = f := rfl

-- See library note [partially-applied ext lemmas]
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (f g : α ->o β) (h : (f : α -> β) = g)
  statement: f = g
  proof: DFunLike.coe_injective h

中文:
定理 ext
  条件: (f g : α ->o β) (h : (f : α -> β) = g)
  结论: f = g
  证明: DFunLike.coe_injective h

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g :=
  DFunLike.coe_injective h

/--
theorem `coe_eq` / 定理 `coe_eq`

English:
theorem coe_eq
  given: (f : α ->o β)
  statement: OrderHomClass.toOrderHom f = f
  proof: rfl

中文:
定理 coe_eq
  条件: (f : α ->o β)
  结论: OrderHomClass.toOrderHom f = f
  证明: rfl
-/
@[simp] theorem coe_eq (f : α ->o β) : OrderHomClass.toOrderHom f = f := rfl

/--
theorem `_root_.OrderHomClass.coe_coe` / 定理 `_root_.OrderHomClass.coe_coe`

English:
theorem _root_.OrderHomClass.coe_coe
  given: {F} [FunLike F α β] [OrderHomClass F α β] (f : F)
  proof: rfl

中文:
定理 _root_.OrderHomClass.coe_coe
  条件: {F} [FunLike F α β] [OrderHomClass F α β] (f : F)
  证明: rfl
-/
@[simp] theorem _root_.OrderHomClass.coe_coe {F} [FunLike F α β] [OrderHomClass F α β] (f : F) :
    ⇑(f : α ->o β) = f :=
  rfl

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: : CanLift (α -> β) (α ->o β) (↑) Monotone where
  body: ⟨⟨f, h⟩, rfl⟩

中文:
实例 canLift
  签名: : CanLift (α -> β) (α ->o β) (↑) Monotone where
  定义体: ⟨⟨f, h⟩, rfl⟩
-/
protected instance canLift : CanLift (α -> β) (α ->o β) (↑) Monotone where
  prf f h := ⟨⟨f, h⟩, rfl⟩

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : α ->o β) (f' : α -> β) (h : f' = f)
  body: ⟨f', h.symm.subst f.monotone'⟩

@[simp]

中文:
定义 copy
  签名: (f : α ->o β) (f' : α -> β) (h : f' = f)
  定义体: ⟨f', h.symm.subst f.monotone'⟩

@[simp]
-/
protected def copy (f : α ->o β) (f' : α -> β) (h : f' = f) : α ->o β :=
  ⟨f', h.symm.subst f.monotone'⟩

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : α ->o β) (f' : α -> β) (h : f' = f)
  statement: (f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : α ->o β) (f' : α -> β) (h : f' = f)
  结论: (f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : α ->o β) (f' : α -> β) (h : f' = f) : (f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : α ->o β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : α ->o β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : α ->o β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

instance {α : Type*} (β : Type*) [PartialOrder α] [PartialOrder β] [DecidableEq (α -> β)] :
    DecidableEq (α ->o β) := fun a b =>
  decidable_of_iff (a.toFun = b.toFun) OrderHom.ext_iff.symm

/-- The identity function as bundled monotone function. -/
@[simps -fullyApplied]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : α ->o α
  body: ⟨_root_.id, monotone_id⟩

中文:
定义 id
  签名: : α ->o α
  定义体: ⟨_root_.id, monotone_id⟩

Depends on / 依赖: _root_, _root_.id, monotone_id
-/
def id : α ->o α :=
  ⟨_root_.id, monotone_id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (α ->o α)
  body: ⟨id⟩

中文:
实例 :
  签名: Inhabited (α ->o α)
  定义体: ⟨id⟩
-/
instance : Inhabited (α ->o α) :=
  ⟨id⟩

variable (α β) in
/--
Definition of `equivRelHom` / `equivRelHom` 的定义

English:
definition equivRelHom
  signature: : (α ->o β) ≃ @RelHom α β (· <= ·) (· <= ·) where
  body: ⟨f, @f.monotone⟩
  invFun f := ⟨f, @f.map_rel⟩
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 equivRelHom
  签名: : (α ->o β) ≃ @RelHom α β (· <= ·) (· <= ·) where
  定义体: ⟨f, @f.monotone⟩
  invFun f := ⟨f, @f.map_rel⟩
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: f.monotone, monotone
-/
def equivRelHom : (α ->o β) ≃ @RelHom α β (· <= ·) (· <= ·) where
  toFun f := ⟨f, @f.monotone⟩
  invFun f := ⟨f, @f.map_rel⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (α ->o β)
  body: @Preorder.lift (α ->o β) (α -> β) _ DFunLike.coe

中文:
实例 :
  签名: Preorder (α ->o β)
  定义体: @Preorder.lift (α ->o β) (α -> β) _ DFunLike.coe

Depends on / 依赖: DFunLike, DFunLike.coe, Preorder, Preorder.lift
-/
instance : Preorder (α ->o β) :=
  @Preorder.lift (α ->o β) (α -> β) _ DFunLike.coe

instance {β : Type*} [PartialOrder β] : PartialOrder (α ->o β) :=
  @PartialOrder.lift (α ->o β) (α -> β) _ toFun ext

@[to_dual self]
/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {f g : α ->o β}
  statement: f <= g ↔ forall x, f x <= g x
  proof: Iff.rfl

@[simp, norm_cast, to_dual self]

中文:
定理 le_def
  条件: {f g : α ->o β}
  结论: f <= g ↔ 对任意 x, f x <= g x
  证明: Iff.rfl

@[simp, norm_cast, to_dual self]

Depends on / 依赖: Iff.rfl
-/
theorem le_def {f g : α ->o β} : f <= g ↔ forall x, f x <= g x :=
  Iff.rfl

@[simp, norm_cast, to_dual self]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  given: {f g : α ->o β}
  statement: (f : α -> β) <= g ↔ f <= g
  proof: Iff.rfl

@[simp, to_dual self]

中文:
定理 coe_le_coe
  条件: {f g : α ->o β}
  结论: (f : α -> β) <= g ↔ f <= g
  证明: Iff.rfl

@[simp, to_dual self]

Depends on / 依赖: Iff.rfl
-/
theorem coe_le_coe {f g : α ->o β} : (f : α -> β) <= g ↔ f <= g :=
  Iff.rfl

@[simp, to_dual self]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: {f g : α -> β} {hf hg}
  statement: mk f hf <= mk g hg ↔ f <= g
  proof: Iff.rfl

@[mono, to_dual self]

中文:
定理 mk_le_mk
  条件: {f g : α -> β} {hf hg}
  结论: mk f hf <= mk g hg ↔ f <= g
  证明: Iff.rfl

@[mono, to_dual self]

Depends on / 依赖: Iff.rfl
-/
theorem mk_le_mk {f g : α -> β} {hf hg} : mk f hf <= mk g hg ↔ f <= g :=
  Iff.rfl

@[mono, to_dual self]
/--
theorem `apply_mono` / 定理 `apply_mono`

English:
theorem apply_mono
  given: {f g : α ->o β} {x y : α} (h₁ : f <= g) (h₂ : x <= y)
  statement: f x <= g y
  proof: (h₁ x).trans g.mono h₂

中文:
定理 apply_mono
  条件: {f g : α ->o β} {x y : α} (h₁ : f <= g) (h₂ : x <= y)
  结论: f x <= g y
  证明: (h₁ x).trans g.mono h₂

Depends on / 依赖: g.mono
-/
theorem apply_mono {f g : α ->o β} {x y : α} (h₁ : f <= g) (h₂ : x <= y) : f x <= g y :=
(h₁ x).trans g.mono h₂

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: : (α × β ->o γ) ≃o (α ->o β ->o γ) where
  body: ⟨fun x => ⟨Function.curry f x, fun _ _ h => f.mono ⟨le_rfl, h⟩⟩, fun _ _ h _ =>
    f.mono ⟨h, le_rfl⟩⟩
  invFun f := ⟨Function.uncurry fun x => f x, fun x y h => (f.mono h.1 x.2).trans ((f y.1).mono h.2)⟩
  map_rel_iff' := by simp [le_def]

@[simp]

中文:
定义 curry
  签名: : (α × β ->o γ) ≃o (α ->o β ->o γ) where
  定义体: ⟨fun x => ⟨Function.curry f x, fun _ _ h => f.mono ⟨le_rfl, h⟩⟩, fun _ _ h _ =>
    f.mono ⟨h, le_rfl⟩⟩
  invFun f := ⟨Function.uncurry fun x => f x, fun x y h => (f.mono h.1 x.2).trans ((f y.1).mono h.2)⟩
  map_rel_iff' := by simp [le_def]

@[simp]

Depends on / 依赖: Function, Function.curry, f.mono, le_rfl
-/
def curry : (α × β ->o γ) ≃o (α ->o β ->o γ) where
  toFun f := ⟨fun x => ⟨Function.curry f x, fun _ _ h => f.mono ⟨le_rfl, h⟩⟩, fun _ _ h _ =>
    f.mono ⟨h, le_rfl⟩⟩
  invFun f := ⟨Function.uncurry fun x => f x, fun x y h => (f.mono h.1 x.2).trans ((f y.1).mono h.2)⟩
  map_rel_iff' := by simp [le_def]

@[simp]
/--
theorem `curry_apply` / 定理 `curry_apply`

English:
theorem curry_apply
  given: (f : α × β ->o γ) (x : α) (y : β)
  statement: curry f x y = f (x, y)
  proof: rfl

@[simp]

中文:
定理 curry_apply
  条件: (f : α × β ->o γ) (x : α) (y : β)
  结论: curry f x y = f (x, y)
  证明: rfl

@[simp]
-/
theorem curry_apply (f : α × β ->o γ) (x : α) (y : β) : curry f x y = f (x, y) :=
  rfl

@[simp]
/--
theorem `curry_symm_apply` / 定理 `curry_symm_apply`

English:
theorem curry_symm_apply
  given: (f : α ->o β ->o γ) (x : α × β)
  statement: curry.symm f x = f x.1 x.2
  proof: rfl

中文:
定理 curry_symm_apply
  条件: (f : α ->o β ->o γ) (x : α × β)
  结论: curry.symm f x = f x.1 x.2
  证明: rfl
-/
theorem curry_symm_apply (f : α ->o β ->o γ) (x : α × β) : curry.symm f x = f x.1 x.2 :=
  rfl

/-- The composition of two bundled monotone functions. -/
@[simps -fullyApplied]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : β ->o γ) (f : α ->o β)
  body: ⟨g ∘ f, g.mono.comp f.mono⟩

@[mono, to_dual self]

中文:
定义 comp
  签名: (g : β ->o γ) (f : α ->o β)
  定义体: ⟨g ∘ f, g.mono.comp f.mono⟩

@[mono, to_dual self]

Depends on / 依赖: f.mono, g.mono.comp
-/
def comp (g : β ->o γ) (f : α ->o β) : α ->o γ :=
  ⟨g ∘ f, g.mono.comp f.mono⟩

@[mono, to_dual self]
/--
theorem `comp_mono` / 定理 `comp_mono`

English:
theorem comp_mono
  given: ⦃g₁ g₂
  statement: β ->o γ⦄ (hg : g₁ <= g₂) ⦃f₁ f₂ : α ->o β⦄ (hf : f₁ <= f₂) :
  proof: fun _ => (hg _).trans (g₂.mono <| hf _)

中文:
定理 comp_mono
  条件: ⦃g₁ g₂
  结论: β ->o γ⦄ (hg : g₁ <= g₂) ⦃f₁ f₂ : α ->o β⦄ (hf : f₁ <= f₂) :
  证明: fun _ => (hg _).trans (g₂.mono <| hf _)
-/
theorem comp_mono ⦃g₁ g₂ : β ->o γ⦄ (hg : g₁ <= g₂) ⦃f₁ f₂ : α ->o β⦄ (hf : f₁ <= f₂) :
    g₁.comp f₁ <= g₂.comp f₂ := fun _ => (hg _).trans (g₂.mono <| hf _)

/--
lemma `mk_comp_mk` / 引理 `mk_comp_mk`

English:
lemma mk_comp_mk
  given: (g : β -> γ) (f : α -> β) (hg hf)
  proof: rfl

中文:
引理 mk_comp_mk
  条件: (g : β -> γ) (f : α -> β) (hg hf)
  证明: rfl
-/
@[simp] lemma mk_comp_mk (g : β -> γ) (f : α -> β) (hg hf) :
    comp ⟨g, hg⟩ ⟨f, hf⟩ = ⟨g ∘ f, hg.comp hf⟩ := rfl

/-- The composition of two bundled monotone functions, a fully bundled version. -/
@[simps! -fullyApplied]
/--
Definition of `compₘ` / `compₘ` 的定义

English:
definition compₘ
  signature: : (β ->o γ) ->o (α ->o β) ->o α ->o γ
  body: curry ⟨fun f : (β ->o γ) × (α ->o β) => f.1.comp f.2, fun _ _ h => comp_mono h.1 h.2⟩

@[simp]

中文:
定义 compₘ
  签名: : (β ->o γ) ->o (α ->o β) ->o α ->o γ
  定义体: curry ⟨fun f : (β ->o γ) × (α ->o β) => f.1.comp f.2, fun _ _ h => comp_mono h.1 h.2⟩

@[simp]

Depends on / 依赖: comp_mono
-/
def compₘ : (β ->o γ) ->o (α ->o β) ->o α ->o γ :=
  curry ⟨fun f : (β ->o γ) × (α ->o β) => f.1.comp f.2, fun _ _ h => comp_mono h.1 h.2⟩

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : α ->o β)
  statement: comp f id = f
  proof: by
  ext
  rfl

@[simp]

中文:
定理 comp_id
  条件: (f : α ->o β)
  结论: comp f id = f
  证明: by
  ext
  rfl

@[simp]
-/
theorem comp_id (f : α ->o β) : comp f id = f := by
  ext
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : α ->o β)
  statement: comp id f = f
  proof: by
  ext
  rfl

中文:
定理 id_comp
  条件: (f : α ->o β)
  结论: comp id f = f
  证明: by
  ext
  rfl
-/
theorem id_comp (f : α ->o β) : comp id f = f := by
  ext
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : γ ->o δ) (g : β ->o γ) (h : α ->o β)
  statement: (f.comp g).comp h = f.comp (g.comp h)
  proof: rfl

中文:
定理 comp_assoc
  条件: (f : γ ->o δ) (g : β ->o γ) (h : α ->o β)
  结论: (f.comp g).comp h = f.comp (g.comp h)
  证明: rfl
-/
theorem comp_assoc (f : γ ->o δ) (g : β ->o γ) (h : α ->o β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

/-- Constant function bundled as an `OrderHom`. -/
@[simps -fullyApplied]
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (α : Type*) [Preorder α] {β : Type*} [Preorder β]
  body: ⟨Function.const α b, fun _ _ _ => le_rfl⟩
  monotone' _ _ h _ := h

@[simp]

中文:
定义 const
  签名: (α : 类型) [Preorder α] {β : 类型} [Preorder β]
  定义体: ⟨Function.const α b, fun _ _ _ => le_rfl⟩
  monotone' _ _ h _ := h

@[simp]

Depends on / 依赖: Function, Function.const, le_rfl
-/
def const (α : Type*) [Preorder α] {β : Type*} [Preorder β] : β ->o α ->o β where
  toFun b := ⟨Function.const α b, fun _ _ _ => le_rfl⟩
  monotone' _ _ h _ := h

@[simp]
/--
theorem `const_comp` / 定理 `const_comp`

English:
theorem const_comp
  given: (f : α ->o β) (c : γ)
  statement: (const β c).comp f = const α c
  proof: rfl

@[simp]

中文:
定理 const_comp
  条件: (f : α ->o β) (c : γ)
  结论: (const β c).comp f = const α c
  证明: rfl

@[simp]
-/
theorem const_comp (f : α ->o β) (c : γ) : (const β c).comp f = const α c :=
  rfl

@[simp]
/--
theorem `comp_const` / 定理 `comp_const`

English:
theorem comp_const
  given: (γ : Type*) [Preorder γ] (f : α ->o β) (c : α)
  proof: rfl

中文:
定理 comp_const
  条件: (γ : 类型) [Preorder γ] (f : α ->o β) (c : α)
  证明: rfl
-/
theorem comp_const (γ : Type*) [Preorder γ] (f : α ->o β) (c : α) :
    f.comp (const γ c) = const γ (f c) :=
  rfl

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`OrderHom`. -/
@[simps]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : α ->o β) (g : α ->o γ)
  body: ⟨fun x => (f x, g x), fun _ _ h => ⟨f.mono h, g.mono h⟩⟩

@[mono, to_dual self]

中文:
定义 prod
  签名: (f : α ->o β) (g : α ->o γ)
  定义体: ⟨fun x => (f x, g x), fun _ _ h => ⟨f.mono h, g.mono h⟩⟩

@[mono, to_dual self]
-/
protected def prod (f : α ->o β) (g : α ->o γ) : α ->o β × γ :=
  ⟨fun x => (f x, g x), fun _ _ h => ⟨f.mono h, g.mono h⟩⟩

@[mono, to_dual self]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: {f₁ f₂ : α ->o β} (hf : f₁ <= f₂) {g₁ g₂ : α ->o γ} (hg : g₁ <= g₂)
  proof: fun _ => Prod.le_def.2 ⟨hf _, hg _⟩

中文:
定理 prod_mono
  条件: {f₁ f₂ : α ->o β} (hf : f₁ <= f₂) {g₁ g₂ : α ->o γ} (hg : g₁ <= g₂)
  证明: fun _ => Prod.le_def.2 ⟨hf _, hg _⟩

Depends on / 依赖: Prod.le_def, le_def
-/
theorem prod_mono {f₁ f₂ : α ->o β} (hf : f₁ <= f₂) {g₁ g₂ : α ->o γ} (hg : g₁ <= g₂) :
    f₁.prod g₁ <= f₂.prod g₂ := fun _ => Prod.le_def.2 ⟨hf _, hg _⟩

/--
theorem `comp_prod_comp_same` / 定理 `comp_prod_comp_same`

English:
theorem comp_prod_comp_same
  given: (f₁ f₂ : β ->o γ) (g : α ->o β)
  proof: rfl

中文:
定理 comp_prod_comp_same
  条件: (f₁ f₂ : β ->o γ) (g : α ->o β)
  证明: rfl
-/
theorem comp_prod_comp_same (f₁ f₂ : β ->o γ) (g : α ->o β) :
    (f₁.comp g).prod (f₂.comp g) = (f₁.prod f₂).comp g :=
  rfl

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`OrderHom`. This is a fully bundled version. -/
@[simps!]
/--
Definition of `prodₘ` / `prodₘ` 的定义

English:
definition prodₘ
  signature: : (α ->o β) ->o (α ->o γ) ->o α ->o β × γ
  body: curry ⟨fun f : (α ->o β) × (α ->o γ) => f.1.prod f.2, fun _ _ h => prod_mono h.1 h.2⟩

中文:
定义 prodₘ
  签名: : (α ->o β) ->o (α ->o γ) ->o α ->o β × γ
  定义体: curry ⟨fun f : (α ->o β) × (α ->o γ) => f.1.prod f.2, fun _ _ h => prod_mono h.1 h.2⟩

Depends on / 依赖: prod_mono
-/
def prodₘ : (α ->o β) ->o (α ->o γ) ->o α ->o β × γ :=
  curry ⟨fun f : (α ->o β) × (α ->o γ) => f.1.prod f.2, fun _ _ h => prod_mono h.1 h.2⟩

/-- Diagonal embedding of `α` into `α × α` as an `OrderHom`. -/
@[simps!]
/--
Definition of `diag` / `diag` 的定义

English:
definition diag
  signature: : α ->o α × α
  body: id.prod id

中文:
定义 diag
  签名: : α ->o α × α
  定义体: id.prod id

Depends on / 依赖: id.prod
-/
def diag : α ->o α × α :=
  id.prod id

/-- Restriction of `f : α →o α →o β` to the diagonal. -/
@[simps! +simpRhs]
/--
Definition of `onDiag` / `onDiag` 的定义

English:
definition onDiag
  signature: (f : α ->o α ->o β)
  body: (curry.symm f).comp diag

中文:
定义 onDiag
  签名: (f : α ->o α ->o β)
  定义体: (curry.symm f).comp diag

Depends on / 依赖: curry.symm
-/
def onDiag (f : α ->o α ->o β) : α ->o β :=
  (curry.symm f).comp diag

/-- `Prod.fst` as an `OrderHom`. -/
@[simps]
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : α × β ->o α
  body: ⟨Prod.fst, fun _ _ h => h.1⟩

中文:
定义 fst
  签名: : α × β ->o α
  定义体: ⟨Prod.fst, fun _ _ h => h.1⟩

Depends on / 依赖: Prod.fst
-/
def fst : α × β ->o α :=
  ⟨Prod.fst, fun _ _ h => h.1⟩

/-- `Prod.snd` as an `OrderHom`. -/
@[simps]
/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : α × β ->o β
  body: ⟨Prod.snd, fun _ _ h => h.2⟩

@[simp]

中文:
定义 snd
  签名: : α × β ->o β
  定义体: ⟨Prod.snd, fun _ _ h => h.2⟩

@[simp]

Depends on / 依赖: Prod.snd
-/
def snd : α × β ->o β :=
  ⟨Prod.snd, fun _ _ h => h.2⟩

@[simp]
/--
theorem `fst_prod_snd` / 定理 `fst_prod_snd`

English:
theorem fst_prod_snd
  statement: (fst : α × β ->o α).prod snd = id
  proof: by
  ext ⟨x, y⟩ : 2
  rfl

@[simp]

中文:
定理 fst_prod_snd
  结论: (fst : α × β ->o α).prod snd = id
  证明: by
  ext ⟨x, y⟩ : 2
  rfl

@[simp]
-/
theorem fst_prod_snd : (fst : α × β ->o α).prod snd = id := by
  ext ⟨x, y⟩ : 2
  rfl

@[simp]
/--
theorem `fst_comp_prod` / 定理 `fst_comp_prod`

English:
theorem fst_comp_prod
  given: (f : α ->o β) (g : α ->o γ)
  statement: fst.comp (f.prod g) = f
  proof: ext _ _ rfl

@[simp]

中文:
定理 fst_comp_prod
  条件: (f : α ->o β) (g : α ->o γ)
  结论: fst.comp (f.prod g) = f
  证明: ext _ _ rfl

@[simp]
-/
theorem fst_comp_prod (f : α ->o β) (g : α ->o γ) : fst.comp (f.prod g) = f :=
  ext _ _ rfl

@[simp]
/--
theorem `snd_comp_prod` / 定理 `snd_comp_prod`

English:
theorem snd_comp_prod
  given: (f : α ->o β) (g : α ->o γ)
  statement: snd.comp (f.prod g) = g
  proof: ext _ _ rfl

中文:
定理 snd_comp_prod
  条件: (f : α ->o β) (g : α ->o γ)
  结论: snd.comp (f.prod g) = g
  证明: ext _ _ rfl
-/
theorem snd_comp_prod (f : α ->o β) (g : α ->o γ) : snd.comp (f.prod g) = g :=
  ext _ _ rfl

/-- Order isomorphism between the space of monotone maps to `β × γ` and the product of the spaces
of monotone maps to `β` and `γ`. -/
@[simps]
/--
Definition of `prodIso` / `prodIso` 的定义

English:
definition prodIso
  signature: : (α ->o β × γ) ≃o (α ->o β) × (α ->o γ) where
  body: (fst.comp f, snd.comp f)
  invFun f := f.1.prod f.2
  map_rel_iff' := forall_and.symm

中文:
定义 prodIso
  签名: : (α ->o β × γ) ≃o (α ->o β) × (α ->o γ) where
  定义体: (fst.comp f, snd.comp f)
  invFun f := f.1.prod f.2
  map_rel_iff' := forall_and.symm

Depends on / 依赖: fst.comp, snd.comp
-/
def prodIso : (α ->o β × γ) ≃o (α ->o β) × (α ->o γ) where
  toFun f := (fst.comp f, snd.comp f)
  invFun f := f.1.prod f.2
  map_rel_iff' := forall_and.symm

/-- `Prod.map` of two `OrderHom`s as an `OrderHom` -/
@[simps]
/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: (f : α ->o β) (g : γ ->o δ)
  body: ⟨Prod.map f g, fun _ _ h => ⟨f.mono h.1, g.mono h.2⟩⟩

中文:
定义 prodMap
  签名: (f : α ->o β) (g : γ ->o δ)
  定义体: ⟨Prod.map f g, fun _ _ h => ⟨f.mono h.1, g.mono h.2⟩⟩

Depends on / 依赖: Prod.map, f.mono, g.mono
-/
def prodMap (f : α ->o β) (g : γ ->o δ) : α × γ ->o β × δ :=
  ⟨Prod.map f g, fun _ _ h => ⟨f.mono h.1, g.mono h.2⟩⟩

variable {ι : Type*} {π : ι -> Type*} [forall i, Preorder (π i)]

/-- Evaluation of an unbundled function at a point (`Function.eval`) as an `OrderHom`. -/
@[simps -fullyApplied]
/--
Definition of `_root_.Pi.evalOrderHom` / `_root_.Pi.evalOrderHom` 的定义

English:
definition _root_.Pi.evalOrderHom
  signature: (i : ι)
  body: ⟨Function.eval i, Function.monotone_eval i⟩

中文:
定义 _root_.Pi.evalOrderHom
  签名: (i : ι)
  定义体: ⟨Function.eval i, Function.monotone_eval i⟩

Depends on / 依赖: Function, Function.eval, Function.monotone_eval, monotone_eval
-/
def _root_.Pi.evalOrderHom (i : ι) : (forall j, π j) ->o π i :=
  ⟨Function.eval i, Function.monotone_eval i⟩

/-- The "forgetful functor" from `α →o β` to `α → β` that takes the underlying function,
is monotone. -/
@[simps -fullyApplied]
/--
Definition of `coeFnHom` / `coeFnHom` 的定义

English:
definition coeFnHom
  signature: : (α ->o β) ->o α -> β where
  body: f
  monotone' _ _ h := h

中文:
定义 coeFnHom
  签名: : (α ->o β) ->o α -> β where
  定义体: f
  monotone' _ _ h := h
-/
def coeFnHom : (α ->o β) ->o α -> β where
  toFun f := f
  monotone' _ _ h := h

/-- Function application `fun f => f a` (for fixed `a`) is a monotone function from the
monotone function space `α →o β` to `β`. See also `Pi.evalOrderHom`. -/
@[simps! -fullyApplied]
/--
Definition of `apply` / `apply` 的定义

English:
definition apply
  signature: (x : α)
  body: (Pi.evalOrderHom x).comp coeFnHom

中文:
定义 apply
  签名: (x : α)
  定义体: (Pi.evalOrderHom x).comp coeFnHom

Depends on / 依赖: Pi.evalOrderHom, coeFnHom, evalOrderHom
-/
def apply (x : α) : (α ->o β) ->o β :=
  (Pi.evalOrderHom x).comp coeFnHom

/-- Construct a bundled monotone map `α →o Π i, π i` from a family of monotone maps
`f i : α →o π i`. -/
@[simps]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (f : forall i, α ->o π i)
  body: ⟨fun x i => f i x, fun _ _ h i => (f i).mono h⟩

中文:
定义 pi
  签名: (f : 对任意 i, α ->o π i)
  定义体: ⟨fun x i => f i x, fun _ _ h i => (f i).mono h⟩
-/
def pi (f : forall i, α ->o π i) : α ->o forall i, π i :=
  ⟨fun x i => f i x, fun _ _ h i => (f i).mono h⟩

/-- Order isomorphism between bundled monotone maps `α →o Π i, π i` and families of bundled monotone
maps `Π i, α →o π i`. -/
@[simps]
/--
Definition of `piIso` / `piIso` 的定义

English:
definition piIso
  signature: : (α ->o forall i, π i) ≃o forall i, α ->o π i where
  body: (Pi.evalOrderHom i).comp f
  invFun := pi
  map_rel_iff' := forall_comm

中文:
定义 piIso
  签名: : (α ->o 对任意 i, π i) ≃o 对任意 i, α ->o π i where
  定义体: (Pi.evalOrderHom i).comp f
  invFun := pi
  map_rel_iff' := forall_comm

Depends on / 依赖: Pi.evalOrderHom, evalOrderHom
-/
def piIso : (α ->o forall i, π i) ≃o forall i, α ->o π i where
  toFun f i := (Pi.evalOrderHom i).comp f
  invFun := pi
  map_rel_iff' := forall_comm

/-- `Subtype.val` as a bundled monotone function. -/
@[simps -fullyApplied]
/--
Definition of `Subtype.val` / `Subtype.val` 的定义

English:
definition Subtype.val
  signature: (p : α -> Prop)
  body: ⟨_root_.Subtype.val, fun _ _ h => h⟩

中文:
定义 Subtype.val
  签名: (p : α -> 命题)
  定义体: ⟨_root_.Subtype.val, fun _ _ h => h⟩

Depends on / 依赖: Subtype, _root_, _root_.Subtype.val
-/
def Subtype.val (p : α -> Prop) : Subtype p ->o α :=
  ⟨_root_.Subtype.val, fun _ _ h => h⟩

/-- `Subtype.impEmbedding` as an order embedding. -/
@[simps!]
/--
Definition of `_root_.Subtype.orderEmbedding` / `_root_.Subtype.orderEmbedding` 的定义

English:
definition _root_.Subtype.orderEmbedding
  signature: {p q : α -> Prop} (h : forall a, p a -> q a)
  body: { Subtype.impEmbedding _ _ h with
    map_rel_iff' := by aesop }

中文:
定义 _root_.Subtype.orderEmbedding
  签名: {p q : α -> 命题} (h : 对任意 a, p a -> q a)
  定义体: { Subtype.impEmbedding _ _ h with
    map_rel_iff' := by aesop }

Depends on / 依赖: Subtype, Subtype.impEmbedding, impEmbedding, map_rel_iff
-/
def _root_.Subtype.orderEmbedding {p q : α -> Prop} (h : forall a, p a -> q a) :
    {x // p x} ↪o {x // q x} :=
  { Subtype.impEmbedding _ _ h with
    map_rel_iff' := by aesop }

/--
Instance `unique` / 实例 `unique`

English:
instance unique
  signature: [Subsingleton α]
  body: OrderHom.id
  uniq _ := ext _ _ (Subsingleton.elim _ _)

中文:
实例 unique
  签名: [Subsingleton α]
  定义体: OrderHom.id
  uniq _ := ext _ _ (Subsingleton.elim _ _)

Depends on / 依赖: OrderHom, OrderHom.id
-/
instance unique [Subsingleton α] : Unique (α ->o α) where
  default := OrderHom.id
  uniq _ := ext _ _ (Subsingleton.elim _ _)

/--
theorem `orderHom_eq_id` / 定理 `orderHom_eq_id`

English:
theorem orderHom_eq_id
  given: [Subsingleton α] (g : α ->o α)
  statement: g = OrderHom.id
  proof: Subsingleton.elim _ _

中文:
定理 orderHom_eq_id
  条件: [Subsingleton α] (g : α ->o α)
  结论: g = OrderHom.id
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem orderHom_eq_id [Subsingleton α] (g : α ->o α) : g = OrderHom.id :=
  Subsingleton.elim _ _

/-- Reinterpret a bundled monotone function as a monotone function between dual orders. -/
@[simps]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : (α ->o β) ≃ (αᵒᵈ ->o βᵒᵈ) where
  body: ⟨(OrderDual.toDual : β -> βᵒᵈ) ∘ (f : α -> β) ∘
    (OrderDual.ofDual : αᵒᵈ -> α), f.mono.dual⟩
  invFun f := ⟨OrderDual.ofDual ∘ f ∘ OrderDual.toDual, f.mono.dual⟩

@[simp]

中文:
定义 dual
  签名: : (α ->o β) ≃ (αᵒᵈ ->o βᵒᵈ) where
  定义体: ⟨(OrderDual.toDual : β -> βᵒᵈ) ∘ (f : α -> β) ∘
    (OrderDual.ofDual : αᵒᵈ -> α), f.mono.dual⟩
  invFun f := ⟨OrderDual.ofDual ∘ f ∘ OrderDual.toDual, f.mono.dual⟩

@[simp]
-/
protected def dual : (α ->o β) ≃ (αᵒᵈ ->o βᵒᵈ) where
  toFun f := ⟨(OrderDual.toDual : β -> βᵒᵈ) ∘ (f : α -> β) ∘
    (OrderDual.ofDual : αᵒᵈ -> α), f.mono.dual⟩
  invFun f := ⟨OrderDual.ofDual ∘ f ∘ OrderDual.toDual, f.mono.dual⟩

@[simp]
/--
theorem `dual_id` / 定理 `dual_id`

English:
theorem dual_id
  statement: (OrderHom.id : α ->o α).dual = OrderHom.id
  proof: rfl

@[simp]

中文:
定理 dual_id
  结论: (OrderHom.id : α ->o α).dual = OrderHom.id
  证明: rfl

@[simp]
-/
theorem dual_id : (OrderHom.id : α ->o α).dual = OrderHom.id :=
  rfl

@[simp]
/--
theorem `dual_comp` / 定理 `dual_comp`

English:
theorem dual_comp
  given: (g : β ->o γ) (f : α ->o β)
  proof: rfl

@[simp]

中文:
定理 dual_comp
  条件: (g : β ->o γ) (f : α ->o β)
  证明: rfl

@[simp]
-/
theorem dual_comp (g : β ->o γ) (f : α ->o β) :
    (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
/--
theorem `symm_dual_id` / 定理 `symm_dual_id`

English:
theorem symm_dual_id
  statement: OrderHom.dual.symm OrderHom.id = (OrderHom.id : α ->o α)
  proof: rfl

@[simp]

中文:
定理 symm_dual_id
  结论: OrderHom.dual.symm OrderHom.id = (OrderHom.id : α ->o α)
  证明: rfl

@[simp]
-/
theorem symm_dual_id : OrderHom.dual.symm OrderHom.id = (OrderHom.id : α ->o α) :=
  rfl

@[simp]
/--
theorem `symm_dual_comp` / 定理 `symm_dual_comp`

English:
theorem symm_dual_comp
  given: (g : βᵒᵈ ->o γᵒᵈ) (f : αᵒᵈ ->o βᵒᵈ)
  proof: rfl

中文:
定理 symm_dual_comp
  条件: (g : βᵒᵈ ->o γᵒᵈ) (f : αᵒᵈ ->o βᵒᵈ)
  证明: rfl
-/
theorem symm_dual_comp (g : βᵒᵈ ->o γᵒᵈ) (f : αᵒᵈ ->o βᵒᵈ) :
    OrderHom.dual.symm (g.comp f) = (OrderHom.dual.symm g).comp (OrderHom.dual.symm f) :=
  rfl

/--
Definition of `dualIso` / `dualIso` 的定义

English:
definition dualIso
  signature: (α β : Type*) [Preorder α] [Preorder β]
  body: OrderHom.dual.trans OrderDual.toDual
  map_rel_iff' := Iff.rfl

中文:
定义 dualIso
  签名: (α β : 类型) [Preorder α] [Preorder β]
  定义体: OrderHom.dual.trans OrderDual.toDual
  map_rel_iff' := Iff.rfl

Depends on / 依赖: OrderDual, OrderDual.toDual, OrderHom, OrderHom.dual.trans, toDual
-/
def dualIso (α β : Type*) [Preorder α] [Preorder β] : (α ->o β) ≃o (αᵒᵈ ->o βᵒᵈ)ᵒᵈ where
  toEquiv := OrderHom.dual.trans OrderDual.toDual
  map_rel_iff' := Iff.rfl

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `ULift α →o ULift β` in a
higher universe. -/
@[simps!]
/--
Definition of `uliftMap` / `uliftMap` 的定义

English:
definition uliftMap
  signature: (f : α ->o β)
  body: ⟨fun i => ⟨f i.down⟩, fun _ _ h => f.monotone h⟩

中文:
定义 uliftMap
  签名: (f : α ->o β)
  定义体: ⟨fun i => ⟨f i.down⟩, fun _ _ h => f.monotone h⟩

Depends on / 依赖: f.monotone, i.down, monotone
-/
def uliftMap (f : α ->o β) : ULift α ->o ULift β :=
  ⟨fun i => ⟨f i.down⟩, fun _ _ h => f.monotone h⟩

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `α →o ULift β` in a
higher universe. -/
@[simps!]
/--
Definition of `uliftRightMap` / `uliftRightMap` 的定义

English:
definition uliftRightMap
  signature: (f : α ->o β)
  body: ⟨fun i => ⟨f i⟩, fun _ _ h => f.monotone h⟩

中文:
定义 uliftRightMap
  签名: (f : α ->o β)
  定义体: ⟨fun i => ⟨f i⟩, fun _ _ h => f.monotone h⟩

Depends on / 依赖: f.monotone, monotone
-/
def uliftRightMap (f : α ->o β) : α ->o ULift β :=
  ⟨fun i => ⟨f i⟩, fun _ _ h => f.monotone h⟩

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `ULift α →o β` in a
higher universe. -/
@[simps!]
/--
Definition of `uliftLeftMap` / `uliftLeftMap` 的定义

English:
definition uliftLeftMap
  signature: (f : α ->o β)
  body: ⟨fun i => f i.down, fun _ _ h => f.monotone h⟩

@[simp]

中文:
定义 uliftLeftMap
  签名: (f : α ->o β)
  定义体: ⟨fun i => f i.down, fun _ _ h => f.monotone h⟩

@[simp]

Depends on / 依赖: f.monotone, i.down, monotone
-/
def uliftLeftMap (f : α ->o β) : ULift α ->o β :=
  ⟨fun i => f i.down, fun _ _ h => f.monotone h⟩

@[simp]
/--
theorem `uliftLeftMap_uliftRightMap_eq` / 定理 `uliftLeftMap_uliftRightMap_eq`

English:
theorem uliftLeftMap_uliftRightMap_eq
  given: (f : α ->o β)
  statement: f.uliftLeftMap.uliftRightMap = f.uliftMap
  proof: rfl

@[simp]

中文:
定理 uliftLeftMap_uliftRightMap_eq
  条件: (f : α ->o β)
  结论: f.uliftLeftMap.uliftRightMap = f.uliftMap
  证明: rfl

@[simp]
-/
theorem uliftLeftMap_uliftRightMap_eq (f : α ->o β) : f.uliftLeftMap.uliftRightMap = f.uliftMap :=
  rfl

@[simp]
/--
theorem `uliftRightMap_uliftLeftMap_eq` / 定理 `uliftRightMap_uliftLeftMap_eq`

English:
theorem uliftRightMap_uliftLeftMap_eq
  given: (f : α ->o β)
  statement: f.uliftRightMap.uliftLeftMap = f.uliftMap
  proof: rfl

中文:
定理 uliftRightMap_uliftLeftMap_eq
  条件: (f : α ->o β)
  结论: f.uliftRightMap.uliftLeftMap = f.uliftMap
  证明: rfl
-/
theorem uliftRightMap_uliftLeftMap_eq (f : α ->o β) : f.uliftRightMap.uliftLeftMap = f.uliftMap :=
  rfl

end OrderHom

/--
Definition of `RelEmbedding.orderEmbeddingOfLTEmbedding` / `RelEmbedding.orderEmbeddingOfLTEmbedding` 的定义

English:
definition RelEmbedding.orderEmbeddingOfLTEmbedding
  signature: [PartialOrder α] [PartialOrder β]
  body: { f with
    map_rel_iff' := by
      simp [le_iff_lt_or_eq, f.map_rel_iff, f.injective.eq_iff] }

@[simp]

中文:
定义 RelEmbedding.orderEmbeddingOfLTEmbedding
  签名: [PartialOrder α] [PartialOrder β]
  定义体: { f with
    map_rel_iff' := by
      simp [le_iff_lt_or_eq, f.map_rel_iff, f.injective.eq_iff] }

@[simp]

Depends on / 依赖: eq_iff, f.injective.eq_iff, f.map_rel_iff, injective, le_iff_lt_or_eq, map_rel_iff
-/
def RelEmbedding.orderEmbeddingOfLTEmbedding [PartialOrder α] [PartialOrder β]
    (f : ((· < ·) : α -> α -> Prop) ↪r ((· < ·) : β -> β -> Prop)) : α ↪o β :=
  { f with
    map_rel_iff' := by
      simp [le_iff_lt_or_eq, f.map_rel_iff, f.injective.eq_iff] }

@[simp]
/--
theorem `RelEmbedding.orderEmbeddingOfLTEmbedding_apply` / 定理 `RelEmbedding.orderEmbeddingOfLTEmbedding_apply`

English:
theorem RelEmbedding.orderEmbeddingOfLTEmbedding_apply
  statement: [PartialOrder α] [PartialOrder β]
  proof: rfl

中文:
定理 RelEmbedding.orderEmbeddingOfLTEmbedding_apply
  结论: [PartialOrder α] [PartialOrder β]
  证明: rfl
-/
theorem RelEmbedding.orderEmbeddingOfLTEmbedding_apply [PartialOrder α] [PartialOrder β]
    {f : ((· < ·) : α -> α -> Prop) ↪r ((· < ·) : β -> β -> Prop)} {x : α} :
    RelEmbedding.orderEmbeddingOfLTEmbedding f x = f x :=
  rfl

namespace OrderEmbedding

section LE

variable [LE α] [LE β] [LE γ] [LE δ]

variable (α) in
/--
Definition of `id` / `id` 的定义

English:
abbreviation id
  signature: : α ↪o α
  body: RelEmbedding.refl (· <= ·)

@[simp]

中文:
缩写 id
  签名: : α ↪o α
  定义体: RelEmbedding.refl (· <= ·)

@[simp]

Depends on / 依赖: RelEmbedding, RelEmbedding.refl
-/
abbrev id : α ↪o α :=
  RelEmbedding.refl (· <= ·)

@[simp]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(id α) = _root_.id
  proof: rfl

@[simp]

中文:
定理 coe_id
  结论: ⇑(id α) = _root_.id
  证明: rfl

@[simp]
-/
theorem coe_id : ⇑(id α) = _root_.id :=
  rfl

@[simp]
/--
theorem `id_toEmbedding` / 定理 `id_toEmbedding`

English:
theorem id_toEmbedding
  statement: (id α).toEmbedding = Function.Embedding.refl α
  proof: rfl

中文:
定理 id_toEmbedding
  结论: (id α).toEmbedding = Function.Embedding.refl α
  证明: rfl
-/
theorem id_toEmbedding : (id α).toEmbedding = Function.Embedding.refl α :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
abbreviation comp
  signature: (f : α ↪o β) (g : β ↪o γ)
  body: RelEmbedding.trans f g

@[simp]

中文:
缩写 comp
  签名: (f : α ↪o β) (g : β ↪o γ)
  定义体: RelEmbedding.trans f g

@[simp]

Depends on / 依赖: RelEmbedding, RelEmbedding.trans
-/
abbrev comp (f : α ↪o β) (g : β ↪o γ) : α ↪o γ :=
  RelEmbedding.trans f g

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : α ↪o β) (g : β ↪o γ)
  statement: f.comp g = g ∘ f
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : α ↪o β) (g : β ↪o γ)
  结论: f.comp g = g ∘ f
  证明: rfl

@[simp]
-/
theorem coe_comp (f : α ↪o β) (g : β ↪o γ) : f.comp g = g ∘ f :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : α ↪o β)
  statement: (id α).comp f = f
  proof: by
  ext
  rfl

@[simp]

中文:
定理 id_comp
  条件: (f : α ↪o β)
  结论: (id α).comp f = f
  证明: by
  ext
  rfl

@[simp]
-/
theorem id_comp (f : α ↪o β) : (id α).comp f = f := by
  ext
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : α ↪o β)
  statement: f.comp (id β) = f
  proof: by
  ext
  rfl

中文:
定理 comp_id
  条件: (f : α ↪o β)
  结论: f.comp (id β) = f
  证明: by
  ext
  rfl
-/
theorem comp_id (f : α ↪o β) : f.comp (id β) = f := by
  ext
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : α ↪o β) (g : β ↪o γ) (h : γ ↪o δ)
  proof: rfl

中文:
定理 comp_assoc
  条件: (f : α ↪o β) (g : β ↪o γ) (h : γ ↪o δ)
  证明: rfl
-/
theorem comp_assoc (f : α ↪o β) (g : β ↪o γ) (h : γ ↪o δ) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

end LE

section Preorder

variable [Preorder α] [Preorder β] (f : α ↪o β)

/-- `<` is preserved by order embeddings of preorders. -/
@[to_dual gtEmbedding /-- `>` is preserved by order embeddings of preorders. -/]
/--
Definition of `ltEmbedding` / `ltEmbedding` 的定义

English:
definition ltEmbedding
  signature: : ((· < ·) : α -> α -> Prop) ↪r ((· < ·) : β -> β -> Prop)
  body: { f with map_rel_iff' := by simp [lt_iff_le_not_ge, f.map_rel_iff] }

@[to_dual (attr := simp) gtEmbedding_apply]

中文:
定义 ltEmbedding
  签名: : ((· < ·) : α -> α -> 命题) ↪r ((· < ·) : β -> β -> 命题)
  定义体: { f with map_rel_iff' := by simp [lt_iff_le_not_ge, f.map_rel_iff] }

@[to_dual (attr := simp) gtEmbedding_apply]

Depends on / 依赖: f.map_rel_iff, lt_iff_le_not_ge, map_rel_iff
-/
def ltEmbedding : ((· < ·) : α -> α -> Prop) ↪r ((· < ·) : β -> β -> Prop) :=
  { f with map_rel_iff' := by simp [lt_iff_le_not_ge, f.map_rel_iff] }

@[to_dual (attr := simp) gtEmbedding_apply]
/--
theorem `ltEmbedding_apply` / 定理 `ltEmbedding_apply`

English:
theorem ltEmbedding_apply
  given: (x : α)
  statement: f.ltEmbedding x = f x
  proof: rfl

@[simp, to_dual self]

中文:
定理 ltEmbedding_apply
  条件: (x : α)
  结论: f.ltEmbedding x = f x
  证明: rfl

@[simp, to_dual self]
-/
theorem ltEmbedding_apply (x : α) : f.ltEmbedding x = f x :=
  rfl

@[simp, to_dual self]
/--
theorem `le_iff_le` / 定理 `le_iff_le`

English:
theorem le_iff_le
  given: {a b}
  statement: f a <= f b ↔ a <= b
  proof: f.map_rel_iff

@[simp, to_dual self]

中文:
定理 le_iff_le
  条件: {a b}
  结论: f a <= f b ↔ a <= b
  证明: f.map_rel_iff

@[simp, to_dual self]

Depends on / 依赖: f.map_rel_iff, map_rel_iff
-/
theorem le_iff_le {a b} : f a <= f b ↔ a <= b :=
  f.map_rel_iff

@[simp, to_dual self]
/--
theorem `lt_iff_lt` / 定理 `lt_iff_lt`

English:
theorem lt_iff_lt
  given: {a b}
  statement: f a < f b ↔ a < b
  proof: f.ltEmbedding.map_rel_iff

中文:
定理 lt_iff_lt
  条件: {a b}
  结论: f a < f b ↔ a < b
  证明: f.ltEmbedding.map_rel_iff

Depends on / 依赖: f.ltEmbedding.map_rel_iff, ltEmbedding, map_rel_iff
-/
theorem lt_iff_lt {a b} : f a < f b ↔ a < b :=
  f.ltEmbedding.map_rel_iff

/--
theorem `eq_iff_eq` / 定理 `eq_iff_eq`

English:
theorem eq_iff_eq
  given: {a b}
  statement: f a = f b ↔ a = b
  proof: f.injective.eq_iff

中文:
定理 eq_iff_eq
  条件: {a b}
  结论: f a = f b ↔ a = b
  证明: f.injective.eq_iff

Depends on / 依赖: eq_iff, f.injective.eq_iff, injective
-/
theorem eq_iff_eq {a b} : f a = f b ↔ a = b :=
  f.injective.eq_iff

/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  statement: Monotone f
  proof: OrderHomClass.monotone f

中文:
定理 monotone
  结论: Monotone f
  证明: OrderHomClass.monotone f
-/
protected theorem monotone : Monotone f :=
  OrderHomClass.monotone f

/--
theorem `strictMono` / 定理 `strictMono`

English:
theorem strictMono
  statement: StrictMono f
  proof: fun _ _ => f.lt_iff_lt.2

中文:
定理 strictMono
  结论: StrictMono f
  证明: fun _ _ => f.lt_iff_lt.2
-/
protected theorem strictMono : StrictMono f := fun _ _ => f.lt_iff_lt.2

/--
theorem `acc` / 定理 `acc`

English:
theorem acc
  given: (a : α)
  statement: Acc (· < ·) (f a) -> Acc (· < ·) a
  proof: f.ltEmbedding.acc a

@[to_dual none]

中文:
定理 acc
  条件: (a : α)
  结论: Acc (· < ·) (f a) -> Acc (· < ·) a
  证明: f.ltEmbedding.acc a

@[to_dual none]
-/
protected theorem acc (a : α) : Acc (· < ·) (f a) -> Acc (· < ·) a :=
  f.ltEmbedding.acc a

@[to_dual none]
/--
theorem `wellFounded` / 定理 `wellFounded`

English:
theorem wellFounded
  given: (f : α ↪o β)
  proof: f.ltEmbedding.wellFounded

中文:
定理 wellFounded
  条件: (f : α ↪o β)
  证明: f.ltEmbedding.wellFounded
-/
protected theorem wellFounded (f : α ↪o β) :
    WellFounded ((· < ·) : β -> β -> Prop) -> WellFounded ((· < ·) : α -> α -> Prop) :=
  f.ltEmbedding.wellFounded

/--
theorem `isWellOrder` / 定理 `isWellOrder`

English:
theorem isWellOrder
  given: [IsWellOrder β (· < ·)] (f : α ↪o β)
  statement: IsWellOrder α (· < ·)
  proof: f.ltEmbedding.isWellOrder

中文:
定理 isWellOrder
  条件: [IsWellOrder β (· < ·)] (f : α ↪o β)
  结论: IsWellOrder α (· < ·)
  证明: f.ltEmbedding.isWellOrder
-/
protected theorem isWellOrder [IsWellOrder β (· < ·)] (f : α ↪o β) : IsWellOrder α (· < ·) :=
  f.ltEmbedding.isWellOrder

/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : αᵒᵈ ↪o βᵒᵈ
  body: ⟨f.toEmbedding, f.map_rel_iff⟩

中文:
定义 dual
  签名: : αᵒᵈ ↪o βᵒᵈ
  定义体: ⟨f.toEmbedding, f.map_rel_iff⟩
-/
protected def dual : αᵒᵈ ↪o βᵒᵈ :=
  ⟨f.toEmbedding, f.map_rel_iff⟩

/-- A preorder which embeds into a well-founded preorder is itself well-founded. -/
@[to_dual /-- A preorder which embeds into a preorder in which `(· > ·)` is well-founded
also has `(· > ·)` well-founded. -/]
/--
theorem `wellFoundedLT` / 定理 `wellFoundedLT`

English:
theorem wellFoundedLT
  given: [WellFoundedLT β] (f : α ↪o β)
  statement: WellFoundedLT α where
  proof: f.wellFounded IsWellFounded.wf

中文:
定理 wellFoundedLT
  条件: [WellFoundedLT β] (f : α ↪o β)
  结论: WellFoundedLT α where
  证明: f.wellFounded IsWellFounded.wf
-/
protected theorem wellFoundedLT [WellFoundedLT β] (f : α ↪o β) : WellFoundedLT α where
  wf := f.wellFounded IsWellFounded.wf

/-- To define an order embedding from a partial order to a preorder it suffices to give a function
together with a proof that it satisfies `f a ≤ f b ↔ a ≤ b`.
-/
@[to_dual self]
/--
Definition of `ofMapLEIff` / `ofMapLEIff` 的定义

English:
definition ofMapLEIff
  signature: {α β} [PartialOrder α] [Preorder β] (f : α -> β) (hf : forall a b, f a <= f b ↔ a <= b)
  body: RelEmbedding.ofMapRelIff f hf

@[simp, to_dual self]

中文:
定义 ofMapLEIff
  签名: {α β} [PartialOrder α] [Preorder β] (f : α -> β) (hf : 对任意 a b, f a <= f b ↔ a <= b)
  定义体: RelEmbedding.ofMapRelIff f hf

@[simp, to_dual self]

Depends on / 依赖: RelEmbedding, RelEmbedding.ofMapRelIff, ofMapRelIff
-/
def ofMapLEIff {α β} [PartialOrder α] [Preorder β] (f : α -> β) (hf : forall a b, f a <= f b ↔ a <= b) :
    α ↪o β :=
  RelEmbedding.ofMapRelIff f hf

@[simp, to_dual self]
/--
theorem `coe_ofMapLEIff` / 定理 `coe_ofMapLEIff`

English:
theorem coe_ofMapLEIff
  given: {α β} [PartialOrder α] [Preorder β] {f : α -> β} (h)
  proof: rfl

中文:
定理 coe_ofMapLEIff
  条件: {α β} [PartialOrder α] [Preorder β] {f : α -> β} (h)
  证明: rfl
-/
theorem coe_ofMapLEIff {α β} [PartialOrder α] [Preorder β] {f : α -> β} (h) :
    ⇑(ofMapLEIff f h) = f :=
  rfl

/--
Definition of `ofStrictMono` / `ofStrictMono` 的定义

English:
definition ofStrictMono
  signature: {α β} [LinearOrder α] [Preorder β] (f : α -> β) (h : StrictMono f)
  body: ofMapLEIff f fun _ _ => h.le_iff_le

@[simp, grind =]

中文:
定义 ofStrictMono
  签名: {α β} [LinearOrder α] [Preorder β] (f : α -> β) (h : StrictMono f)
  定义体: ofMapLEIff f fun _ _ => h.le_iff_le

@[simp, grind =]

Depends on / 依赖: h.le_iff_le, le_iff_le, ofMapLEIff
-/
def ofStrictMono {α β} [LinearOrder α] [Preorder β] (f : α -> β) (h : StrictMono f) : α ↪o β :=
  ofMapLEIff f fun _ _ => h.le_iff_le

@[simp, grind =]
/--
theorem `coe_ofStrictMono` / 定理 `coe_ofStrictMono`

English:
theorem coe_ofStrictMono
  given: {α β} [LinearOrder α] [Preorder β] {f : α -> β} (h : StrictMono f)
  proof: rfl

中文:
定理 coe_ofStrictMono
  条件: {α β} [LinearOrder α] [Preorder β] {f : α -> β} (h : StrictMono f)
  证明: rfl
-/
theorem coe_ofStrictMono {α β} [LinearOrder α] [Preorder β] {f : α -> β} (h : StrictMono f) :
    ⇑(ofStrictMono f h) = f :=
  rfl

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (p : α -> Prop)
  body: ⟨Function.Embedding.subtype p, Iff.rfl⟩

@[simp]

中文:
定义 subtype
  签名: (p : α -> 命题)
  定义体: ⟨Function.Embedding.subtype p, Iff.rfl⟩

@[simp]

Depends on / 依赖: Embedding, Function, Function.Embedding.subtype, Iff.rfl, subtype
-/
def subtype (p : α -> Prop) : Subtype p ↪o α :=
  ⟨Function.Embedding.subtype p, Iff.rfl⟩

@[simp]
/--
theorem `subtype_apply` / 定理 `subtype_apply`

English:
theorem subtype_apply
  given: {p : α -> Prop} (x : Subtype p)
  statement: subtype p x = x
  proof: rfl

中文:
定理 subtype_apply
  条件: {p : α -> 命题} (x : Subtype p)
  结论: subtype p x = x
  证明: rfl
-/
theorem subtype_apply {p : α -> Prop} (x : Subtype p) : subtype p x = x :=
  rfl

/--
theorem `subtype_injective` / 定理 `subtype_injective`

English:
theorem subtype_injective
  given: (p : α -> Prop)
  statement: Function.Injective (subtype p)
  proof: Subtype.coe_injective

@[simp]

中文:
定理 subtype_injective
  条件: (p : α -> 命题)
  结论: Function.Injective (subtype p)
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem subtype_injective (p : α -> Prop) : Function.Injective (subtype p) :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  given: (p : α -> Prop)
  statement: ⇑(subtype p) = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  条件: (p : α -> 命题)
  结论: ⇑(subtype p) = Subtype.val
  证明: rfl
-/
theorem coe_subtype (p : α -> Prop) : ⇑(subtype p) = Subtype.val :=
  rfl

/-- Convert an `OrderEmbedding` to an `OrderHom`. -/
@[simps -fullyApplied]
/--
Definition of `toOrderHom` / `toOrderHom` 的定义

English:
definition toOrderHom
  signature: {X Y : Type*} [Preorder X] [Preorder Y] (f : X ↪o Y)
  body: f
  monotone' := f.monotone

中文:
定义 toOrderHom
  签名: {X Y : 类型} [Preorder X] [Preorder Y] (f : X ↪o Y)
  定义体: f
  monotone' := f.monotone
-/
def toOrderHom {X Y : Type*} [Preorder X] [Preorder Y] (f : X ↪o Y) : X ->o Y where
  toFun := f
  monotone' := f.monotone

/--
Definition of `ofIsEmpty` / `ofIsEmpty` 的定义

English:
definition ofIsEmpty
  signature: [IsEmpty α]
  body: isEmptyElim
  inj' := isEmptyElim
  map_rel_iff' {a} := isEmptyElim a

@[simp, norm_cast]

中文:
定义 ofIsEmpty
  签名: [IsEmpty α]
  定义体: isEmptyElim
  inj' := isEmptyElim
  map_rel_iff' {a} := isEmptyElim a

@[simp, norm_cast]
-/
@[simps] def ofIsEmpty [IsEmpty α] : α ↪o β where
  toFun := isEmptyElim
  inj' := isEmptyElim
  map_rel_iff' {a} := isEmptyElim a

@[simp, norm_cast]
/--
lemma `coe_ofIsEmpty` / 引理 `coe_ofIsEmpty`

English:
lemma coe_ofIsEmpty
  given: [IsEmpty α]
  statement: (ofIsEmpty : α ↪o β) = (isEmptyElim : α -> β)
  proof: rfl

中文:
引理 coe_ofIsEmpty
  条件: [IsEmpty α]
  结论: (ofIsEmpty : α ↪o β) = (isEmptyElim : α -> β)
  证明: rfl
-/
lemma coe_ofIsEmpty [IsEmpty α] : (ofIsEmpty : α ↪o β) = (isEmptyElim : α -> β) := rfl

end Preorder

end OrderEmbedding

section Disjoint

variable [PartialOrder α] [PartialOrder β] (f : OrderEmbedding α β)

/--
lemma `Disjoint.of_orderEmbedding` / 引理 `Disjoint.of_orderEmbedding`

English:
lemma Disjoint.of_orderEmbedding
  given: [OrderBot α] [OrderBot β] {a₁ a₂ : α}
  proof: by
  intro h x h₁ h₂
  rw [← f.le_iff_le] at h₁ h₂ ⊢
  calc
    f x <= ⊥ := h h₁ h₂
    _ <= f ⊥ := bot_le

中文:
引理 Disjoint.of_orderEmbedding
  条件: [OrderBot α] [OrderBot β] {a₁ a₂ : α}
  证明: by
  intro h x h₁ h₂
  rw [← f.le_iff_le] at h₁ h₂ ⊢
  calc
    f x <= ⊥ := h h₁ h₂
    _ <= f ⊥ := bot_le

Depends on / 依赖: bot_le, f.le_iff_le, le_iff_le
-/
lemma Disjoint.of_orderEmbedding [OrderBot α] [OrderBot β] {a₁ a₂ : α} :
    Disjoint (f a₁) (f a₂) -> Disjoint a₁ a₂ := by
  intro h x h₁ h₂
  rw [← f.le_iff_le] at h₁ h₂ ⊢
  calc
    f x <= ⊥ := h h₁ h₂
    _ <= f ⊥ := bot_le

/--
lemma `Codisjoint.of_orderEmbedding` / 引理 `Codisjoint.of_orderEmbedding`

English:
lemma Codisjoint.of_orderEmbedding
  given: [OrderTop α] [OrderTop β] {a₁ a₂ : α}
  proof: Disjoint.of_orderEmbedding (α := αᵒᵈ) (β := βᵒᵈ) f.dual

中文:
引理 Codisjoint.of_orderEmbedding
  条件: [OrderTop α] [OrderTop β] {a₁ a₂ : α}
  证明: Disjoint.of_orderEmbedding (α := αᵒᵈ) (β := βᵒᵈ) f.dual

Depends on / 依赖: Disjoint, Disjoint.of_orderEmbedding, f.dual, of_orderEmbedding
-/
lemma Codisjoint.of_orderEmbedding [OrderTop α] [OrderTop β] {a₁ a₂ : α} :
    Codisjoint (f a₁) (f a₂) -> Codisjoint a₁ a₂ :=
  Disjoint.of_orderEmbedding (α := αᵒᵈ) (β := βᵒᵈ) f.dual

/--
lemma `IsCompl.of_orderEmbedding` / 引理 `IsCompl.of_orderEmbedding`

English:
lemma IsCompl.of_orderEmbedding
  given: [BoundedOrder α] [BoundedOrder β] {a₁ a₂ : α}
  proof: fun ⟨hd, hcd⟩ =>
  ⟨Disjoint.of_orderEmbedding f hd, Codisjoint.of_orderEmbedding f hcd⟩

中文:
引理 IsCompl.of_orderEmbedding
  条件: [BoundedOrder α] [BoundedOrder β] {a₁ a₂ : α}
  证明: fun ⟨hd, hcd⟩ =>
  ⟨Disjoint.of_orderEmbedding f hd, Codisjoint.of_orderEmbedding f hcd⟩
-/
lemma IsCompl.of_orderEmbedding [BoundedOrder α] [BoundedOrder β] {a₁ a₂ : α} :
    IsCompl (f a₁) (f a₂) -> IsCompl a₁ a₂ := fun ⟨hd, hcd⟩ =>
  ⟨Disjoint.of_orderEmbedding f hd, Codisjoint.of_orderEmbedding f hcd⟩

end Disjoint

section RelHom

variable [PartialOrder α] [Preorder β]

namespace RelHom

variable (f : ((· < ·) : α -> α -> Prop) ->r ((· < ·) : β -> β -> Prop))

/-- A bundled expression of the fact that a map between partial orders that is strictly monotone
is weakly monotone. -/
@[simps -fullyApplied]
/--
Definition of `toOrderHom` / `toOrderHom` 的定义

English:
definition toOrderHom
  signature: : α ->o β where
  body: f
  monotone' := StrictMono.monotone fun _ _ => f.map_rel

中文:
定义 toOrderHom
  签名: : α ->o β where
  定义体: f
  monotone' := StrictMono.monotone fun _ _ => f.map_rel
-/
def toOrderHom : α ->o β where
  toFun := f
  monotone' := StrictMono.monotone fun _ _ => f.map_rel

end RelHom

/--
theorem `RelEmbedding.toOrderHom_injective` / 定理 `RelEmbedding.toOrderHom_injective`

English:
theorem RelEmbedding.toOrderHom_injective
  proof: fun _ _ h => f.injective h

中文:
定理 RelEmbedding.toOrderHom_injective
  证明: fun _ _ h => f.injective h

Depends on / 依赖: f.injective, injective
-/
theorem RelEmbedding.toOrderHom_injective
    (f : ((· < ·) : α -> α -> Prop) ↪r ((· < ·) : β -> β -> Prop)) :
    Function.Injective (f : ((· < ·) : α -> α -> Prop) ->r ((· < ·) : β -> β -> Prop)).toOrderHom :=
  fun _ _ h => f.injective h

end RelHom

namespace OrderIso

section LE

variable [LE α] [LE β] [LE γ] [LE δ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (α ≃o β) α β
  body: inferInstance

中文:
实例 :
  签名: EquivLike (α ≃o β) α β
  定义体: inferInstance
-/
instance : EquivLike (α ≃o β) α β :=
  inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderIsoClass (α ≃o β) α β
  body: f.map_rel_iff'

@[simp]

中文:
实例 :
  签名: OrderIsoClass (α ≃o β) α β
  定义体: f.map_rel_iff'

@[simp]

Depends on / 依赖: f.map_rel_iff, map_rel_iff
-/
instance : OrderIsoClass (α ≃o β) α β where
  map_le_map_iff f _ _ := f.map_rel_iff'

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : α ≃o β}
  statement: f.toFun = f
  proof: rfl

中文:
定理 toFun_eq_coe
  条件: {f : α ≃o β}
  结论: f.toFun = f
  证明: rfl
-/
theorem toFun_eq_coe {f : α ≃o β} : f.toFun = f :=
  rfl

-- See note [partially-applied ext lemmas]
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : α ≃o β} (h : (f : α -> β) = g)
  statement: f = g
  proof: DFunLike.coe_injective h

中文:
定理 ext
  条件: {f g : α ≃o β} (h : (f : α -> β) = g)
  结论: f = g
  证明: DFunLike.coe_injective h

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g :=
  DFunLike.coe_injective h

/--
Definition of `toOrderEmbedding` / `toOrderEmbedding` 的定义

English:
definition toOrderEmbedding
  signature: (e : α ≃o β)
  body: e.toRelEmbedding

@[simp]

中文:
定义 toOrderEmbedding
  签名: (e : α ≃o β)
  定义体: e.toRelEmbedding

@[simp]

Depends on / 依赖: e.toRelEmbedding, toRelEmbedding
-/
def toOrderEmbedding (e : α ≃o β) : α ↪o β :=
  e.toRelEmbedding

@[simp]
/--
theorem `coe_toOrderEmbedding` / 定理 `coe_toOrderEmbedding`

English:
theorem coe_toOrderEmbedding
  given: (e : α ≃o β)
  statement: ⇑e.toOrderEmbedding = e
  proof: rfl

中文:
定理 coe_toOrderEmbedding
  条件: (e : α ≃o β)
  结论: ⇑e.toOrderEmbedding = e
  证明: rfl
-/
theorem coe_toOrderEmbedding (e : α ≃o β) : ⇑e.toOrderEmbedding = e :=
  rfl

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (e : α ≃o β)
  statement: Function.Bijective e
  proof: e.toEquiv.bijective

中文:
定理 bijective
  条件: (e : α ≃o β)
  结论: Function.Bijective e
  证明: e.toEquiv.bijective
-/
protected theorem bijective (e : α ≃o β) : Function.Bijective e :=
  e.toEquiv.bijective

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : α ≃o β)
  statement: Function.Injective e
  proof: e.toEquiv.injective

中文:
定理 injective
  条件: (e : α ≃o β)
  结论: Function.Injective e
  证明: e.toEquiv.injective
-/
protected theorem injective (e : α ≃o β) : Function.Injective e :=
  e.toEquiv.injective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : α ≃o β)
  statement: Function.Surjective e
  proof: e.toEquiv.surjective

中文:
定理 surjective
  条件: (e : α ≃o β)
  结论: Function.Surjective e
  证明: e.toEquiv.surjective
-/
protected theorem surjective (e : α ≃o β) : Function.Surjective e :=
  e.toEquiv.surjective

/--
theorem `apply_eq_iff_eq` / 定理 `apply_eq_iff_eq`

English:
theorem apply_eq_iff_eq
  given: (e : α ≃o β) {x y : α}
  statement: e x = e y ↔ x = y
  proof: e.toEquiv.apply_eq_iff_eq

中文:
定理 apply_eq_iff_eq
  条件: (e : α ≃o β) {x y : α}
  结论: e x = e y ↔ x = y
  证明: e.toEquiv.apply_eq_iff_eq

Depends on / 依赖: apply_eq_iff_eq, e.toEquiv.apply_eq_iff_eq, toEquiv
-/
theorem apply_eq_iff_eq (e : α ≃o β) {x y : α} : e x = e y ↔ x = y :=
  e.toEquiv.apply_eq_iff_eq

/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (α : Type*) [LE α]
  body: RelIso.refl (· <= ·)

@[simp]

中文:
定义 refl
  签名: (α : 类型) [LE α]
  定义体: RelIso.refl (· <= ·)

@[simp]

Depends on / 依赖: RelIso, RelIso.refl
-/
def refl (α : Type*) [LE α] : α ≃o α :=
  RelIso.refl (· <= ·)

@[simp]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: ⇑(refl α) = id
  proof: rfl

@[simp]

中文:
定理 coe_refl
  结论: ⇑(refl α) = id
  证明: rfl

@[simp]
-/
theorem coe_refl : ⇑(refl α) = id :=
  rfl

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (x : α)
  statement: refl α x = x
  proof: rfl

@[simp]

中文:
定理 refl_apply
  条件: (x : α)
  结论: refl α x = x
  证明: rfl

@[simp]
-/
theorem refl_apply (x : α) : refl α x = x :=
  rfl

@[simp]
/--
theorem `refl_toEquiv` / 定理 `refl_toEquiv`

English:
theorem refl_toEquiv
  statement: (refl α).toEquiv = Equiv.refl α
  proof: rfl

中文:
定理 refl_toEquiv
  结论: (refl α).toEquiv = Equiv.refl α
  证明: rfl
-/
theorem refl_toEquiv : (refl α).toEquiv = Equiv.refl α :=
  rfl

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : α ≃o β)
  body: RelIso.symm e

中文:
定义 symm
  签名: (e : α ≃o β)
  定义体: RelIso.symm e

Depends on / 依赖: RelIso, RelIso.symm
-/
def symm (e : α ≃o β) : β ≃o α := RelIso.symm e

/--
lemma `symm_mk` / 引理 `symm_mk`

English:
lemma symm_mk
  given: (e : α ≃ β) (map_rel_iff')
  proof: rfl

@[simp]

中文:
引理 symm_mk
  条件: (e : α ≃ β) (map_rel_iff')
  证明: rfl

@[simp]
-/
@[simp] lemma symm_mk (e : α ≃ β) (map_rel_iff') :
    symm (.mk e map_rel_iff') = .mk e.symm (by simp [← map_rel_iff']) := rfl

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : α ≃o β) (x : β)
  statement: e (e.symm x) = x
  proof: e.toEquiv.apply_symm_apply x

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : α ≃o β) (x : β)
  结论: e (e.symm x) = x
  证明: e.toEquiv.apply_symm_apply x

@[simp]

Depends on / 依赖: apply_symm_apply, e.toEquiv.apply_symm_apply, toEquiv
-/
theorem apply_symm_apply (e : α ≃o β) (x : β) : e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply x

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : α ≃o β) (x : α)
  statement: e.symm (e x) = x
  proof: e.toEquiv.symm_apply_apply x

@[simp]

中文:
定理 symm_apply_apply
  条件: (e : α ≃o β) (x : α)
  结论: e.symm (e x) = x
  证明: e.toEquiv.symm_apply_apply x

@[simp]

Depends on / 依赖: e.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
theorem symm_apply_apply (e : α ≃o β) (x : α) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[simp]
/--
theorem `symm_refl` / 定理 `symm_refl`

English:
theorem symm_refl
  given: (α : Type*) [LE α]
  statement: (refl α).symm = refl α
  proof: rfl

中文:
定理 symm_refl
  条件: (α : 类型) [LE α]
  结论: (refl α).symm = refl α
  证明: rfl
-/
theorem symm_refl (α : Type*) [LE α] : (refl α).symm = refl α :=
  rfl

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : α ≃o β) {x : α} {y : β}
  statement: e.symm y = x ↔ y = e x
  proof: e.toEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: (e : α ≃o β) {x : α} {y : β}
  结论: e.symm y = x ↔ y = e x
  证明: e.toEquiv.symm_apply_eq

Depends on / 依赖: e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.symm y = x ↔ y = e x :=
  e.toEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : α ≃o β) {x : α} {y : β}
  statement: x = e.symm y ↔ e x = y
  proof: e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]

中文:
定理 eq_symm_apply
  条件: (e : α ≃o β) {x : α} {y : β}
  结论: x = e.symm y ↔ e x = y
  证明: e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
theorem eq_symm_apply (e : α ≃o β) {x : α} {y : β} : x = e.symm y ↔ e x = y :=
  e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]
/--
theorem `apply_eq_iff_eq_symm_apply` / 定理 `apply_eq_iff_eq_symm_apply`

English:
theorem apply_eq_iff_eq_symm_apply
  given: (e : α ≃o β) (x : α) (y : β)
  statement: e x = y ↔ x = e.symm y
  proof: e.eq_symm_apply.symm

@[simp]

中文:
定理 apply_eq_iff_eq_symm_apply
  条件: (e : α ≃o β) (x : α) (y : β)
  结论: e x = y ↔ x = e.symm y
  证明: e.eq_symm_apply.symm

@[simp]

Depends on / 依赖: e.eq_symm_apply.symm, eq_symm_apply
-/
theorem apply_eq_iff_eq_symm_apply (e : α ≃o β) (x : α) (y : β) : e x = y ↔ x = e.symm y :=
  e.eq_symm_apply.symm

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : α ≃o β)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : α ≃o β)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : α ≃o β) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (OrderIso.symm : (α ≃o β) -> β ≃o α)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  结论: Function.Bijective (OrderIso.symm : (α ≃o β) -> β ≃o α)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (OrderIso.symm : (α ≃o β) -> β ≃o α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
theorem `symm_injective` / 定理 `symm_injective`

English:
theorem symm_injective
  statement: Function.Injective (symm : α ≃o β -> β ≃o α)
  proof: symm_bijective.injective

@[simp]

中文:
定理 symm_injective
  结论: Function.Injective (symm : α ≃o β -> β ≃o α)
  证明: symm_bijective.injective

@[simp]

Depends on / 依赖: injective, symm_bijective, symm_bijective.injective
-/
theorem symm_injective : Function.Injective (symm : α ≃o β -> β ≃o α) :=
  symm_bijective.injective

@[simp]
/--
theorem `toEquiv_symm` / 定理 `toEquiv_symm`

English:
theorem toEquiv_symm
  given: (e : α ≃o β)
  statement: e.symm.toEquiv = e.toEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toEquiv_symm
  条件: (e : α ≃o β)
  结论: e.symm.toEquiv = e.toEquiv.symm
  证明: rfl

@[simp]
-/
theorem toEquiv_symm (e : α ≃o β) : e.symm.toEquiv = e.toEquiv.symm :=
  rfl

@[simp]
/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  given: (e : α ≃o β)
  statement: ⇑e.toEquiv = e
  proof: rfl

@[simp]

中文:
定理 coe_toEquiv
  条件: (e : α ≃o β)
  结论: ⇑e.toEquiv = e
  证明: rfl

@[simp]
-/
theorem coe_toEquiv (e : α ≃o β) : ⇑e.toEquiv = e := rfl

@[simp]
/--
theorem `coe_symm_toEquiv` / 定理 `coe_symm_toEquiv`

English:
theorem coe_symm_toEquiv
  given: (e : α ≃o β)
  statement: ⇑e.toEquiv.symm = e.symm
  proof: rfl

中文:
定理 coe_symm_toEquiv
  条件: (e : α ≃o β)
  结论: ⇑e.toEquiv.symm = e.symm
  证明: rfl
-/
theorem coe_symm_toEquiv (e : α ≃o β) : ⇑e.toEquiv.symm = e.symm := rfl

/-- Composition of two order isomorphisms is an order isomorphism. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e : α ≃o β) (e' : β ≃o γ)
  body: RelIso.trans e e'

@[simp]

中文:
定义 trans
  签名: (e : α ≃o β) (e' : β ≃o γ)
  定义体: RelIso.trans e e'

@[simp]

Depends on / 依赖: RelIso, RelIso.trans
-/
def trans (e : α ≃o β) (e' : β ≃o γ) : α ≃o γ :=
  RelIso.trans e e'

@[simp]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (e : α ≃o β) (e' : β ≃o γ)
  statement: ⇑(e.trans e') = e' ∘ e
  proof: rfl

@[simp]

中文:
定理 coe_trans
  条件: (e : α ≃o β) (e' : β ≃o γ)
  结论: ⇑(e.trans e') = e' ∘ e
  证明: rfl

@[simp]
-/
theorem coe_trans (e : α ≃o β) (e' : β ≃o γ) : ⇑(e.trans e') = e' ∘ e :=
  rfl

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e : α ≃o β) (e' : β ≃o γ) (x : α)
  statement: e.trans e' x = e' (e x)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: (e : α ≃o β) (e' : β ≃o γ) (x : α)
  结论: e.trans e' x = e' (e x)
  证明: rfl

@[simp]
-/
theorem trans_apply (e : α ≃o β) (e' : β ≃o γ) (x : α) : e.trans e' x = e' (e x) :=
  rfl

@[simp]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  given: (e : α ≃o β)
  statement: (refl α).trans e = e
  proof: by
  ext x
  rfl

@[simp]

中文:
定理 refl_trans
  条件: (e : α ≃o β)
  结论: (refl α).trans e = e
  证明: by
  ext x
  rfl

@[simp]
-/
theorem refl_trans (e : α ≃o β) : (refl α).trans e = e := by
  ext x
  rfl

@[simp]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  given: (e : α ≃o β)
  statement: e.trans (refl β) = e
  proof: by
  ext x
  rfl

@[simp]

中文:
定理 trans_refl
  条件: (e : α ≃o β)
  结论: e.trans (refl β) = e
  证明: by
  ext x
  rfl

@[simp]
-/
theorem trans_refl (e : α ≃o β) : e.trans (refl β) = e := by
  ext x
  rfl

@[simp]
/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (e₁ : α ≃o β) (e₂ : β ≃o γ) (c : γ)
  proof: rfl

中文:
定理 symm_trans_apply
  条件: (e₁ : α ≃o β) (e₂ : β ≃o γ) (c : γ)
  证明: rfl
-/
theorem symm_trans_apply (e₁ : α ≃o β) (e₂ : β ≃o γ) (c : γ) :
    (e₁.trans e₂).symm c = e₁.symm (e₂.symm c) :=
  rfl

/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: (e₁ : α ≃o β) (e₂ : β ≃o γ)
  statement: (e₁.trans e₂).symm = e₂.symm.trans e₁.symm
  proof: rfl

@[simp]

中文:
定理 symm_trans
  条件: (e₁ : α ≃o β) (e₂ : β ≃o γ)
  结论: (e₁.trans e₂).symm = e₂.symm.trans e₁.symm
  证明: rfl

@[simp]
-/
theorem symm_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

@[simp]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (e : α ≃o β)
  statement: e.trans e.symm = OrderIso.refl α
  proof: RelIso.self_trans_symm e

@[simp]

中文:
定理 self_trans_symm
  条件: (e : α ≃o β)
  结论: e.trans e.symm = OrderIso.refl α
  证明: RelIso.self_trans_symm e

@[simp]

Depends on / 依赖: RelIso, RelIso.self_trans_symm, self_trans_symm
-/
theorem self_trans_symm (e : α ≃o β) : e.trans e.symm = OrderIso.refl α :=
  RelIso.self_trans_symm e

@[simp]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (e : α ≃o β)
  statement: e.symm.trans e = OrderIso.refl β
  proof: RelIso.symm_trans_self e

中文:
定理 symm_trans_self
  条件: (e : α ≃o β)
  结论: e.symm.trans e = OrderIso.refl β
  证明: RelIso.symm_trans_self e

Depends on / 依赖: RelIso, RelIso.symm_trans_self, symm_trans_self
-/
theorem symm_trans_self (e : α ≃o β) : e.symm.trans e = OrderIso.refl β :=
  RelIso.symm_trans_self e

/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: (f : α ≃o β) (g : β ≃o γ) (h : γ ≃o δ)
  proof: rfl

中文:
定理 trans_assoc
  条件: (f : α ≃o β) (g : β ≃o γ) (h : γ ≃o δ)
  证明: rfl
-/
theorem trans_assoc (f : α ≃o β) (g : β ≃o γ) (h : γ ≃o δ) :
    (f.trans g).trans h = f.trans (g.trans h) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- An order isomorphism between the domains and codomains of two prosets of
order homomorphisms gives an order isomorphism between the two function prosets. -/
@[simps apply symm_apply]
/--
Definition of `arrowCongr` / `arrowCongr` 的定义

English:
definition arrowCongr
  signature: {α β γ δ} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
  body: .comp g .comp p f.symm
invFun p := .comp g.symm .comp p f
left_inv p := DFunLike.coe_injective by
    change (g.symm ∘ g) ∘ p ∘ (f.symm ∘ f) = p
    simp only [← OrderIso.coe_trans, Function.id_comp,
               OrderIso.self_trans_symm, OrderIso.coe_refl, Function.comp_id]
right_inv p := DFunLik

中文:
定义 arrowCongr
  签名: {α β γ δ} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
  定义体: .comp g .comp p f.symm
invFun p := .comp g.symm .comp p f
left_inv p := DFunLike.coe_injective by
    change (g.symm ∘ g) ∘ p ∘ (f.symm ∘ f) = p
    simp only [← OrderIso.coe_trans, Function.id_comp,
               OrderIso.self_trans_symm, OrderIso.coe_refl, Function.comp_id]
right_inv p := DFunLik

Depends on / 依赖: f.symm
-/
def arrowCongr {α β γ δ} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
    (f : α ≃o γ) (g : β ≃o δ) : (α ->o β) ≃o (γ ->o δ) where
toFun p := .comp g .comp p f.symm
invFun p := .comp g.symm .comp p f
left_inv p := DFunLike.coe_injective by
    change (g.symm ∘ g) ∘ p ∘ (f.symm ∘ f) = p
    simp only [← OrderIso.coe_trans, Function.id_comp,
               OrderIso.self_trans_symm, OrderIso.coe_refl, Function.comp_id]
right_inv p := DFunLike.coe_injective by
    change (g ∘ g.symm) ∘ p ∘ (f ∘ f.symm) = p
    simp only [← OrderIso.coe_trans, Function.id_comp,
               OrderIso.symm_trans_self, OrderIso.coe_refl, Function.comp_id]
  map_rel_iff' {p q} := by
    simp only [Equiv.coe_fn_mk, OrderHom.le_def, OrderHom.comp_coe,
               OrderHomClass.coe_coe, Function.comp_apply, map_le_map_iff]
    exact Iff.symm f.forall_congr_left

/-- If `α` and `β` are order-isomorphic then the two orders of order-homomorphisms
from `α` and `β` to themselves are order-isomorphic. -/
@[simps! apply symm_apply]
/--
Definition of `conj` / `conj` 的定义

English:
definition conj
  signature: {α β} [Preorder α] [Preorder β] (f : α ≃o β)
  body: arrowCongr f f

中文:
定义 conj
  签名: {α β} [Preorder α] [Preorder β] (f : α ≃o β)
  定义体: arrowCongr f f

Depends on / 依赖: arrowCongr
-/
def conj {α β} [Preorder α] [Preorder β] (f : α ≃o β) : (α ->o α) ≃ (β ->o β) :=
  arrowCongr f f

/--
Definition of `orderEmbeddingCongr` / `orderEmbeddingCongr` 的定义

English:
abbreviation orderEmbeddingCongr
  signature: (f : α ≃o γ) (g : β ≃o δ)
  body: RelIso.relEmbeddingCongr f g

@[simp]

中文:
缩写 orderEmbeddingCongr
  签名: (f : α ≃o γ) (g : β ≃o δ)
  定义体: RelIso.relEmbeddingCongr f g

@[simp]

Depends on / 依赖: RelIso, RelIso.relEmbeddingCongr, relEmbeddingCongr
-/
abbrev orderEmbeddingCongr (f : α ≃o γ) (g : β ≃o δ) : (α ↪o β) ≃ (γ ↪o δ) :=
  RelIso.relEmbeddingCongr f g

@[simp]
/--
theorem `orderEmbeddingCongr_apply` / 定理 `orderEmbeddingCongr_apply`

English:
theorem orderEmbeddingCongr_apply
  given: (f : α ≃o γ) (g : β ≃o δ) (h : α ↪o β)
  proof: rfl

@[simp]

中文:
定理 orderEmbeddingCongr_apply
  条件: (f : α ≃o γ) (g : β ≃o δ) (h : α ↪o β)
  证明: rfl

@[simp]
-/
theorem orderEmbeddingCongr_apply (f : α ≃o γ) (g : β ≃o δ) (h : α ↪o β) :
    orderEmbeddingCongr f g h = .trans (.trans f.symm h) g :=
  rfl

@[simp]
/--
theorem `orderEmbeddingCongr_symm_apply` / 定理 `orderEmbeddingCongr_symm_apply`

English:
theorem orderEmbeddingCongr_symm_apply
  given: (f : α ≃o γ) (g : β ≃o δ) (h : γ ↪o δ)
  proof: rfl

中文:
定理 orderEmbeddingCongr_symm_apply
  条件: (f : α ≃o γ) (g : β ≃o δ) (h : γ ↪o δ)
  证明: rfl
-/
theorem orderEmbeddingCongr_symm_apply (f : α ≃o γ) (g : β ≃o δ) (h : γ ↪o δ) :
    (orderEmbeddingCongr f g).symm h = .trans (.trans f h) g.symm :=
  rfl

/--
Definition of `orderIsoCongr` / `orderIsoCongr` 的定义

English:
abbreviation orderIsoCongr
  signature: (f : α ≃o γ) (g : β ≃o δ)
  body: RelIso.relIsoCongr f g

@[simp]

中文:
缩写 orderIsoCongr
  签名: (f : α ≃o γ) (g : β ≃o δ)
  定义体: RelIso.relIsoCongr f g

@[simp]

Depends on / 依赖: RelIso, RelIso.relIsoCongr, relIsoCongr
-/
abbrev orderIsoCongr (f : α ≃o γ) (g : β ≃o δ) : (α ≃o β) ≃ (γ ≃o δ) :=
  RelIso.relIsoCongr f g

@[simp]
/--
theorem `orderIsoCongr_apply` / 定理 `orderIsoCongr_apply`

English:
theorem orderIsoCongr_apply
  given: (f : α ≃o γ) (g : β ≃o δ) (h : α ≃o β)
  proof: rfl

@[simp]

中文:
定理 orderIsoCongr_apply
  条件: (f : α ≃o γ) (g : β ≃o δ) (h : α ≃o β)
  证明: rfl

@[simp]
-/
theorem orderIsoCongr_apply (f : α ≃o γ) (g : β ≃o δ) (h : α ≃o β) :
    orderIsoCongr f g h = .trans (.trans f.symm h) g :=
  rfl

@[simp]
/--
theorem `orderIsoCongr_symm_apply` / 定理 `orderIsoCongr_symm_apply`

English:
theorem orderIsoCongr_symm_apply
  given: (f : α ≃o γ) (g : β ≃o δ) (h : γ ≃o δ)
  proof: rfl

中文:
定理 orderIsoCongr_symm_apply
  条件: (f : α ≃o γ) (g : β ≃o δ) (h : γ ≃o δ)
  证明: rfl
-/
theorem orderIsoCongr_symm_apply (f : α ≃o γ) (g : β ≃o δ) (h : γ ≃o δ) :
    (orderIsoCongr f g).symm h = .trans (.trans f h) g.symm :=
  rfl

/-- A surjective order embedding is an order isomorphism. -/
@[simps!]
/--
Definition of `ofSurjective` / `ofSurjective` 的定义

English:
definition ofSurjective
  signature: (f : α ↪o β) (hf : Function.Surjective f)
  body: RelIso.ofSurjective f hf

中文:
定义 ofSurjective
  签名: (f : α ↪o β) (hf : Function.Surjective f)
  定义体: RelIso.ofSurjective f hf

Depends on / 依赖: RelIso, RelIso.ofSurjective, ofSurjective
-/
noncomputable def ofSurjective (f : α ↪o β) (hf : Function.Surjective f) : α ≃o β :=
  RelIso.ofSurjective f hf

/-- Surjective order embeddings are equivalent to order isomorphisms. -/
@[simps apply symm_apply]
/--
Definition of `equivEmbeddingSurjective` / `equivEmbeddingSurjective` 的定义

English:
definition equivEmbeddingSurjective
  signature: :
  body: ⟨f, f.surjective⟩
  invFun f := ofSurjective f f.prop
  left_inv _ := by ext; rfl
  right_inv _ := rfl

中文:
定义 equivEmbeddingSurjective
  签名: :
  定义体: ⟨f, f.surjective⟩
  invFun f := ofSurjective f f.prop
  left_inv _ := by ext; rfl
  right_inv _ := rfl

Depends on / 依赖: f.surjective, surjective
-/
noncomputable def equivEmbeddingSurjective :
    α ≃o β ≃ { f : α ↪o β // Function.Surjective f } where
  toFun f := ⟨f, f.surjective⟩
  invFun f := ofSurjective f f.prop
  left_inv _ := by ext; rfl
  right_inv _ := rfl

/--
Definition of `prodComm` / `prodComm` 的定义

English:
definition prodComm
  signature: : α × β ≃o β × α where
  body: Equiv.prodComm α β
  map_rel_iff' := Prod.swap_le_swap

中文:
定义 prodComm
  签名: : α × β ≃o β × α where
  定义体: Equiv.prodComm α β
  map_rel_iff' := Prod.swap_le_swap

Depends on / 依赖: Equiv.prodComm, prodComm
-/
def prodComm : α × β ≃o β × α where
  toEquiv := Equiv.prodComm α β
  map_rel_iff' := Prod.swap_le_swap

set_option backward.isDefEq.respectTransparency false in
/-- `Equiv.prodAssoc` promoted to an order isomorphism. -/
@[simps! (attr := grind =)]
/--
Definition of `prodAssoc` / `prodAssoc` 的定义

English:
definition prodAssoc
  signature: (α β γ : Type*) [LE α] [LE β] [LE γ]
  body: .prodAssoc α β γ
  map_rel_iff' := @fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ => by simp [Equiv.prodAssoc, and_assoc]

@[simp]

中文:
定义 prodAssoc
  签名: (α β γ : 类型) [LE α] [LE β] [LE γ]
  定义体: .prodAssoc α β γ
  map_rel_iff' := @fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ => by simp [Equiv.prodAssoc, and_assoc]

@[simp]

Depends on / 依赖: prodAssoc
-/
def prodAssoc (α β γ : Type*) [LE α] [LE β] [LE γ] :
    (α × β) × γ ≃o α × (β × γ) where
  toEquiv := .prodAssoc α β γ
  map_rel_iff' := @fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ => by simp [Equiv.prodAssoc, and_assoc]

@[simp]
/--
theorem `coe_prodComm` / 定理 `coe_prodComm`

English:
theorem coe_prodComm
  statement: ⇑(prodComm : α × β ≃o β × α) = Prod.swap
  proof: rfl

@[simp]

中文:
定理 coe_prodComm
  结论: ⇑(prodComm : α × β ≃o β × α) = Prod.swap
  证明: rfl

@[simp]
-/
theorem coe_prodComm : ⇑(prodComm : α × β ≃o β × α) = Prod.swap :=
  rfl

@[simp]
/--
theorem `prodComm_symm` / 定理 `prodComm_symm`

English:
theorem prodComm_symm
  statement: (prodComm : α × β ≃o β × α).symm = prodComm
  proof: rfl

中文:
定理 prodComm_symm
  结论: (prodComm : α × β ≃o β × α).symm = prodComm
  证明: rfl
-/
theorem prodComm_symm : (prodComm : α × β ≃o β × α).symm = prodComm :=
  rfl

variable (α)

/--
Definition of `dualDual` / `dualDual` 的定义

English:
definition dualDual
  signature: : α ≃o αᵒᵈᵒᵈ
  body: refl α

@[simp]

中文:
定义 dualDual
  签名: : α ≃o αᵒᵈᵒᵈ
  定义体: refl α

@[simp]
-/
def dualDual : α ≃o αᵒᵈᵒᵈ :=
  refl α

@[simp]
/--
theorem `coe_dualDual` / 定理 `coe_dualDual`

English:
theorem coe_dualDual
  statement: ⇑(dualDual α) = toDual ∘ toDual
  proof: rfl

@[simp]

中文:
定理 coe_dualDual
  结论: ⇑(dualDual α) = toDual ∘ toDual
  证明: rfl

@[simp]
-/
theorem coe_dualDual : ⇑(dualDual α) = toDual ∘ toDual :=
  rfl

@[simp]
/--
theorem `coe_dualDual_symm` / 定理 `coe_dualDual_symm`

English:
theorem coe_dualDual_symm
  statement: ⇑(dualDual α).symm = ofDual ∘ ofDual
  proof: rfl

中文:
定理 coe_dualDual_symm
  结论: ⇑(dualDual α).symm = ofDual ∘ ofDual
  证明: rfl
-/
theorem coe_dualDual_symm : ⇑(dualDual α).symm = ofDual ∘ ofDual :=
  rfl

variable {α}

@[simp]
/--
theorem `dualDual_apply` / 定理 `dualDual_apply`

English:
theorem dualDual_apply
  given: (a : α)
  statement: dualDual α a = toDual (toDual a)
  proof: rfl

@[simp]

中文:
定理 dualDual_apply
  条件: (a : α)
  结论: dualDual α a = toDual (toDual a)
  证明: rfl

@[simp]
-/
theorem dualDual_apply (a : α) : dualDual α a = toDual (toDual a) :=
  rfl

@[simp]
/--
theorem `dualDual_symm_apply` / 定理 `dualDual_symm_apply`

English:
theorem dualDual_symm_apply
  given: (a : αᵒᵈᵒᵈ)
  statement: (dualDual α).symm a = ofDual (ofDual a)
  proof: rfl

中文:
定理 dualDual_symm_apply
  条件: (a : αᵒᵈᵒᵈ)
  结论: (dualDual α).symm a = ofDual (ofDual a)
  证明: rfl
-/
theorem dualDual_symm_apply (a : αᵒᵈᵒᵈ) : (dualDual α).symm a = ofDual (ofDual a) :=
  rfl

end LE

open Set

section LE

variable [LE α] [LE β]

@[gcongr, to_dual self]
/--
theorem `le_iff_le` / 定理 `le_iff_le`

English:
theorem le_iff_le
  given: (e : α ≃o β) {x y : α}
  statement: e x <= e y ↔ x <= y
  proof: e.map_rel_iff

@[to_dual symm_apply_le]

中文:
定理 le_iff_le
  条件: (e : α ≃o β) {x y : α}
  结论: e x <= e y ↔ x <= y
  证明: e.map_rel_iff

@[to_dual symm_apply_le]

Depends on / 依赖: e.map_rel_iff, map_rel_iff
-/
theorem le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <= y :=
  e.map_rel_iff

@[to_dual symm_apply_le]
/--
theorem `le_symm_apply` / 定理 `le_symm_apply`

English:
theorem le_symm_apply
  given: (e : α ≃o β) {x : α} {y : β}
  statement: x <= e.symm y ↔ e x <= y
  proof: e.rel_symm_apply

中文:
定理 le_symm_apply
  条件: (e : α ≃o β) {x : α} {y : β}
  结论: x <= e.symm y ↔ e x <= y
  证明: e.rel_symm_apply

Depends on / 依赖: e.rel_symm_apply, rel_symm_apply
-/
theorem le_symm_apply (e : α ≃o β) {x : α} {y : β} : x <= e.symm y ↔ e x <= y :=
  e.rel_symm_apply

end LE

variable [Preorder α] [Preorder β]

/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  given: (e : α ≃o β)
  statement: Monotone e
  proof: e.toOrderEmbedding.monotone

中文:
定理 monotone
  条件: (e : α ≃o β)
  结论: Monotone e
  证明: e.toOrderEmbedding.monotone
-/
protected theorem monotone (e : α ≃o β) : Monotone e :=
  e.toOrderEmbedding.monotone

/--
theorem `strictMono` / 定理 `strictMono`

English:
theorem strictMono
  given: (e : α ≃o β)
  statement: StrictMono e
  proof: e.toOrderEmbedding.strictMono

@[simp, gcongr, to_dual self]

中文:
定理 strictMono
  条件: (e : α ≃o β)
  结论: StrictMono e
  证明: e.toOrderEmbedding.strictMono

@[simp, gcongr, to_dual self]
-/
protected theorem strictMono (e : α ≃o β) : StrictMono e :=
  e.toOrderEmbedding.strictMono

@[simp, gcongr, to_dual self]
/--
theorem `lt_iff_lt` / 定理 `lt_iff_lt`

English:
theorem lt_iff_lt
  given: (e : α ≃o β) {x y : α}
  statement: e x < e y ↔ x < y
  proof: e.toOrderEmbedding.lt_iff_lt

@[to_dual symm_apply_lt]

中文:
定理 lt_iff_lt
  条件: (e : α ≃o β) {x y : α}
  结论: e x < e y ↔ x < y
  证明: e.toOrderEmbedding.lt_iff_lt

@[to_dual symm_apply_lt]

Depends on / 依赖: e.toOrderEmbedding.lt_iff_lt, lt_iff_lt, toOrderEmbedding
-/
theorem lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y :=
  e.toOrderEmbedding.lt_iff_lt

@[to_dual symm_apply_lt]
/--
theorem `lt_symm_apply` / 定理 `lt_symm_apply`

English:
theorem lt_symm_apply
  given: (e : α ≃o β) {x : α} {y : β}
  statement: x < e.symm y ↔ e x < y
  proof: by
  rw [← e.lt_iff_lt]; rw [e.apply_symm_apply]

中文:
定理 lt_symm_apply
  条件: (e : α ≃o β) {x : α} {y : β}
  结论: x < e.symm y ↔ e x < y
  证明: by
  rw [← e.lt_iff_lt]; rw [e.apply_symm_apply]

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply, e.lt_iff_lt, lt_iff_lt
-/
theorem lt_symm_apply (e : α ≃o β) {x : α} {y : β} : x < e.symm y ↔ e x < y := by
  rw [← e.lt_iff_lt]; rw [e.apply_symm_apply]

/-- Converts an `OrderIso` into a `RelIso (<) (<)`. -/
@[to_dual /-- Converts an `OrderIso` into a `RelIso (>) (>)`. -/]
/--
Definition of `toRelIsoLT` / `toRelIsoLT` 的定义

English:
definition toRelIsoLT
  signature: (e : α ≃o β)
  body: ⟨e.toEquiv, lt_iff_lt e⟩

@[to_dual (attr := simp)]

中文:
定义 toRelIsoLT
  签名: (e : α ≃o β)
  定义体: ⟨e.toEquiv, lt_iff_lt e⟩

@[to_dual (attr := simp)]

Depends on / 依赖: e.toEquiv, lt_iff_lt, toEquiv
-/
def toRelIsoLT (e : α ≃o β) : ((· < ·) : α -> α -> Prop) ≃r ((· < ·) : β -> β -> Prop) :=
  ⟨e.toEquiv, lt_iff_lt e⟩

@[to_dual (attr := simp)]
/--
theorem `toRelIsoLT_apply` / 定理 `toRelIsoLT_apply`

English:
theorem toRelIsoLT_apply
  given: (e : α ≃o β) (x : α)
  statement: e.toRelIsoLT x = e x
  proof: rfl

@[to_dual]

中文:
定理 toRelIsoLT_apply
  条件: (e : α ≃o β) (x : α)
  结论: e.toRelIsoLT x = e x
  证明: rfl

@[to_dual]
-/
theorem toRelIsoLT_apply (e : α ≃o β) (x : α) : e.toRelIsoLT x = e x :=
  rfl

@[to_dual]
/--
theorem `toRelIsoLT_symm` / 定理 `toRelIsoLT_symm`

English:
theorem toRelIsoLT_symm
  given: (e : α ≃o β)
  statement: e.symm.toRelIsoLT = e.toRelIsoLT.symm
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 toRelIsoLT_symm
  条件: (e : α ≃o β)
  结论: e.symm.toRelIsoLT = e.toRelIsoLT.symm
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem toRelIsoLT_symm (e : α ≃o β) : e.symm.toRelIsoLT = e.toRelIsoLT.symm :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `coe_toRelIsoLT` / 定理 `coe_toRelIsoLT`

English:
theorem coe_toRelIsoLT
  given: (e : α ≃o β)
  statement: ⇑e.toRelIsoLT = e
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_toRelIsoLT
  条件: (e : α ≃o β)
  结论: ⇑e.toRelIsoLT = e
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_toRelIsoLT (e : α ≃o β) : ⇑e.toRelIsoLT = e := rfl

@[to_dual (attr := simp)]
/--
theorem `coe_symm_toRelIsoLT` / 定理 `coe_symm_toRelIsoLT`

English:
theorem coe_symm_toRelIsoLT
  given: (e : α ≃o β)
  statement: ⇑e.toRelIsoLT.symm = e.symm
  proof: rfl

中文:
定理 coe_symm_toRelIsoLT
  条件: (e : α ≃o β)
  结论: ⇑e.toRelIsoLT.symm = e.symm
  证明: rfl
-/
theorem coe_symm_toRelIsoLT (e : α ≃o β) : ⇑e.toRelIsoLT.symm = e.symm := rfl

/--
Definition of `ofRelIsoLT` / `ofRelIsoLT` 的定义

English:
definition ofRelIsoLT
  signature: {α β} [PartialOrder α] [PartialOrder β]
  body: ⟨e.toEquiv, by simp [le_iff_eq_or_lt, e.map_rel_iff, e.injective.eq_iff]⟩

@[simp]

中文:
定义 ofRelIsoLT
  签名: {α β} [PartialOrder α] [PartialOrder β]
  定义体: ⟨e.toEquiv, by simp [le_iff_eq_or_lt, e.map_rel_iff, e.injective.eq_iff]⟩

@[simp]

Depends on / 依赖: e.injective.eq_iff, e.map_rel_iff, e.toEquiv, eq_iff, injective, le_iff_eq_or_lt, map_rel_iff, toEquiv
-/
def ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α -> α -> Prop) ≃r ((· < ·) : β -> β -> Prop)) : α ≃o β :=
  ⟨e.toEquiv, by simp [le_iff_eq_or_lt, e.map_rel_iff, e.injective.eq_iff]⟩

@[simp]
/--
theorem `ofRelIsoLT_apply` / 定理 `ofRelIsoLT_apply`

English:
theorem ofRelIsoLT_apply
  statement: {α β} [PartialOrder α] [PartialOrder β]
  proof: rfl

@[simp]

中文:
定理 ofRelIsoLT_apply
  结论: {α β} [PartialOrder α] [PartialOrder β]
  证明: rfl

@[simp]
-/
theorem ofRelIsoLT_apply {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α -> α -> Prop) ≃r ((· < ·) : β -> β -> Prop)) (x : α) : ofRelIsoLT e x = e x :=
  rfl

@[simp]
/--
theorem `ofRelIsoLT_symm` / 定理 `ofRelIsoLT_symm`

English:
theorem ofRelIsoLT_symm
  statement: {α β} [PartialOrder α] [PartialOrder β]
  proof: rfl

@[simp]

中文:
定理 ofRelIsoLT_symm
  结论: {α β} [PartialOrder α] [PartialOrder β]
  证明: rfl

@[simp]
-/
theorem ofRelIsoLT_symm {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α -> α -> Prop) ≃r ((· < ·) : β -> β -> Prop)) :
    (ofRelIsoLT e).symm = ofRelIsoLT e.symm :=
  rfl

@[simp]
/--
theorem `ofRelIsoLT_toRelIsoLT` / 定理 `ofRelIsoLT_toRelIsoLT`

English:
theorem ofRelIsoLT_toRelIsoLT
  given: {α β} [PartialOrder α] [PartialOrder β] (e : α ≃o β)
  proof: by
  ext
  simp

@[simp]

中文:
定理 ofRelIsoLT_toRelIsoLT
  条件: {α β} [PartialOrder α] [PartialOrder β] (e : α ≃o β)
  证明: by
  ext
  simp

@[simp]
-/
theorem ofRelIsoLT_toRelIsoLT {α β} [PartialOrder α] [PartialOrder β] (e : α ≃o β) :
    ofRelIsoLT (toRelIsoLT e) = e := by
  ext
  simp

@[simp]
/--
theorem `toRelIsoLT_ofRelIsoLT` / 定理 `toRelIsoLT_ofRelIsoLT`

English:
theorem toRelIsoLT_ofRelIsoLT
  statement: {α β} [PartialOrder α] [PartialOrder β]
  proof: by
  ext
  simp

中文:
定理 toRelIsoLT_ofRelIsoLT
  结论: {α β} [PartialOrder α] [PartialOrder β]
  证明: by
  ext
  simp
-/
theorem toRelIsoLT_ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α -> α -> Prop) ≃r ((· < ·) : β -> β -> Prop)) : toRelIsoLT (ofRelIsoLT e) = e := by
  ext
  simp

/--
Definition of `ofCmpEqCmp` / `ofCmpEqCmp` 的定义

English:
definition ofCmpEqCmp
  signature: {α β} [LinearOrder α] [LinearOrder β] (f : α -> β) (g : β -> α)
  body: have gf : forall a : α, a = g (f a) := by
    intro
    rw [← cmp_eq_eq_iff]; rw [h]; rw [cmp_self_eq_eq]
  { toFun := f, invFun := g, left_inv := fun a => (gf a).symm,
    right_inv := by
      intro
      rw [← cmp_eq_eq_iff]; rw [← h]; rw [cmp_self_eq_eq],
    map_rel_iff' := by
      intro a b
 

中文:
定义 ofCmpEqCmp
  签名: {α β} [LinearOrder α] [LinearOrder β] (f : α -> β) (g : β -> α)
  定义体: have gf : forall a : α, a = g (f a) := by
    intro
    rw [← cmp_eq_eq_iff]; rw [h]; rw [cmp_self_eq_eq]
  { toFun := f, invFun := g, left_inv := fun a => (gf a).symm,
    right_inv := by
      intro
      rw [← cmp_eq_eq_iff]; rw [← h]; rw [cmp_self_eq_eq],
    map_rel_iff' := by
      intro a b
 

Depends on / 依赖: cmp_eq_eq_iff, cmp_self_eq_eq, convert, invFun, le_iff_le_of_cmp_eq_cmp, left_inv, map_rel_iff, right_inv
-/
def ofCmpEqCmp {α β} [LinearOrder α] [LinearOrder β] (f : α -> β) (g : β -> α)
    (h : forall (a : α) (b : β), cmp a (g b) = cmp (f a) b) : α ≃o β :=
  have gf : forall a : α, a = g (f a) := by
    intro
    rw [← cmp_eq_eq_iff]; rw [h]; rw [cmp_self_eq_eq]
  { toFun := f, invFun := g, left_inv := fun a => (gf a).symm,
    right_inv := by
      intro
      rw [← cmp_eq_eq_iff]; rw [← h]; rw [cmp_self_eq_eq],
    map_rel_iff' := by
      intro a b
      apply le_iff_le_of_cmp_eq_cmp
      convert! (h a (f b)).symm
      apply gf }

/-- To show that `f : α →o β` and `g : β →o α` make up an order isomorphism it is enough to show
that `g` is the inverse of `f`. -/
@[simps apply]
/--
Definition of `ofHomInv` / `ofHomInv` 的定义

English:
definition ofHomInv
  signature: (f : α ->o β) (g : β ->o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id)
  body: f
  invFun := g
  left_inv := DFunLike.congr_fun h₂
  right_inv := DFunLike.congr_fun h₁
  map_rel_iff' :=
    { mp h := by simpa [h₂] using show g.comp f _ <= g.comp f _ from map_rel g h
      mpr h := f.monotone h }

@[simp]

中文:
定义 ofHomInv
  签名: (f : α ->o β) (g : β ->o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id)
  定义体: f
  invFun := g
  left_inv := DFunLike.congr_fun h₂
  right_inv := DFunLike.congr_fun h₁
  map_rel_iff' :=
    { mp h := by simpa [h₂] using show g.comp f _ <= g.comp f _ from map_rel g h
      mpr h := f.monotone h }

@[simp]
-/
def ofHomInv (f : α ->o β) (g : β ->o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id) :
    α ≃o β where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₂
  right_inv := DFunLike.congr_fun h₁
  map_rel_iff' :=
    { mp h := by simpa [h₂] using show g.comp f _ <= g.comp f _ from map_rel g h
      mpr h := f.monotone h }

@[simp]
/--
theorem `ofHomInv_symm_apply` / 定理 `ofHomInv_symm_apply`

English:
theorem ofHomInv_symm_apply
  statement: (f : α ->o β) (g : β ->o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id)
  proof: rfl

中文:
定理 ofHomInv_symm_apply
  结论: (f : α ->o β) (g : β ->o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id)
  证明: rfl
-/
theorem ofHomInv_symm_apply (f : α ->o β) (g : β ->o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id)
    (a : β) : (ofHomInv f g h₁ h₂).symm a = g a := rfl

/-- Order isomorphism between `α → β` and `β`, where `α` has a unique element. -/
@[simps! toEquiv apply]
/--
Definition of `funUnique` / `funUnique` 的定义

English:
definition funUnique
  signature: (α β : Type*) [Unique α] [Preorder β]
  body: Equiv.funUnique α β
  map_rel_iff' := by simp [Pi.le_def, Unique.forall_iff]

@[simp]

中文:
定义 funUnique
  签名: (α β : 类型) [Unique α] [Preorder β]
  定义体: Equiv.funUnique α β
  map_rel_iff' := by simp [Pi.le_def, Unique.forall_iff]

@[simp]

Depends on / 依赖: Equiv.funUnique, funUnique
-/
def funUnique (α β : Type*) [Unique α] [Preorder β] : (α -> β) ≃o β where
  toEquiv := Equiv.funUnique α β
  map_rel_iff' := by simp [Pi.le_def, Unique.forall_iff]

@[simp]
/--
theorem `funUnique_symm_apply` / 定理 `funUnique_symm_apply`

English:
theorem funUnique_symm_apply
  given: {α β : Type*} [Unique α] [Preorder β]
  proof: rfl

中文:
定理 funUnique_symm_apply
  条件: {α β : 类型} [Unique α] [Preorder β]
  证明: rfl
-/
theorem funUnique_symm_apply {α β : Type*} [Unique α] [Preorder β] :
    ((funUnique α β).symm : β -> α -> β) = Function.const α :=
  rfl

/-- The order isomorphism `α ≃o β` when `α` and `β` are preordered types
containing unique elements. -/
@[simps!]
/--
Definition of `ofUnique` / `ofUnique` 的定义

English:
definition ofUnique
  body: Equiv.ofUnique α β
  map_rel_iff' := by simp

中文:
定义 ofUnique
  定义体: Equiv.ofUnique α β
  map_rel_iff' := by simp

Depends on / 依赖: Equiv.ofUnique, ofUnique
-/
noncomputable def ofUnique
    (α β : Type*) [Unique α] [Unique β] [Preorder α] [Preorder β] :
    α ≃o β where
  toEquiv := Equiv.ofUnique α β
  map_rel_iff' := by simp

/--
Definition of `ofIsEmpty` / `ofIsEmpty` 的定义

English:
definition ofIsEmpty
  signature: (α β : Type*) [Preorder α] [Preorder β] [IsEmpty α] [IsEmpty β]
  body: ⟨Equiv.equivOfIsEmpty α β, @isEmptyElim _ _ _⟩

中文:
定义 ofIsEmpty
  签名: (α β : 类型) [Preorder α] [Preorder β] [IsEmpty α] [IsEmpty β]
  定义体: ⟨Equiv.equivOfIsEmpty α β, @isEmptyElim _ _ _⟩

Depends on / 依赖: Equiv.equivOfIsEmpty, equivOfIsEmpty, isEmptyElim
-/
def ofIsEmpty (α β : Type*) [Preorder α] [Preorder β] [IsEmpty α] [IsEmpty β] : α ≃o β :=
  ⟨Equiv.equivOfIsEmpty α β, @isEmptyElim _ _ _⟩

end OrderIso

namespace Equiv

variable [Preorder α] [Preorder β]

/--
Definition of `toOrderIso` / `toOrderIso` 的定义

English:
definition toOrderIso
  signature: (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm)
  body: ⟨e, ⟨fun h => by simpa only [e.symm_apply_apply] using h₂ h, fun h => h₁ h⟩⟩

@[simp]

中文:
定义 toOrderIso
  签名: (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm)
  定义体: ⟨e, ⟨fun h => by simpa only [e.symm_apply_apply] using h₂ h, fun h => h₁ h⟩⟩

@[simp]

Depends on / 依赖: e.symm_apply_apply, symm_apply_apply
-/
def toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) : α ≃o β :=
  ⟨e, ⟨fun h => by simpa only [e.symm_apply_apply] using h₂ h, fun h => h₁ h⟩⟩

@[simp]
/--
theorem `coe_toOrderIso` / 定理 `coe_toOrderIso`

English:
theorem coe_toOrderIso
  given: (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm)
  proof: rfl

@[simp]

中文:
定理 coe_toOrderIso
  条件: (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm)
  证明: rfl

@[simp]
-/
theorem coe_toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) :
    ⇑(e.toOrderIso h₁ h₂) = e :=
  rfl

@[simp]
/--
theorem `toOrderIso_toEquiv` / 定理 `toOrderIso_toEquiv`

English:
theorem toOrderIso_toEquiv
  given: (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm)
  proof: rfl

中文:
定理 toOrderIso_toEquiv
  条件: (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm)
  证明: rfl
-/
theorem toOrderIso_toEquiv (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) :
    (e.toOrderIso h₁ h₂).toEquiv = e :=
  rfl

end Equiv

namespace StrictMono

variable [LinearOrder α] [Preorder β]
variable (f : α -> β) (h_mono : StrictMono f)

/-- A strictly monotone function with a right inverse is an order isomorphism. -/
@[simps -fullyApplied]
/--
Definition of `orderIsoOfRightInverse` / `orderIsoOfRightInverse` 的定义

English:
definition orderIsoOfRightInverse
  signature: (g : β -> α) (hg : Function.RightInverse g f)
  body: { OrderEmbedding.ofStrictMono f h_mono with
    toFun := f,
    invFun := g,
left_inv := fun _ => h_mono.injective hg _,
    right_inv := hg }

中文:
定义 orderIsoOfRightInverse
  签名: (g : β -> α) (hg : Function.RightInverse g f)
  定义体: { OrderEmbedding.ofStrictMono f h_mono with
    toFun := f,
    invFun := g,
left_inv := fun _ => h_mono.injective hg _,
    right_inv := hg }

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, h_mono, h_mono.injective, injective, invFun, left_inv, ofStrictMono, right_inv
-/
def orderIsoOfRightInverse (g : β -> α) (hg : Function.RightInverse g f) : α ≃o β :=
  { OrderEmbedding.ofStrictMono f h_mono with
    toFun := f,
    invFun := g,
left_inv := fun _ => h_mono.injective hg _,
    right_inv := hg }

end StrictMono

/--
Definition of `OrderIso.dual` / `OrderIso.dual` 的定义

English:
definition OrderIso.dual
  signature: [LE α] [LE β] (f : α ≃o β)
  body: ⟨f.toEquiv, f.le_iff_le⟩

中文:
定义 OrderIso.dual
  签名: [LE α] [LE β] (f : α ≃o β)
  定义体: ⟨f.toEquiv, f.le_iff_le⟩
-/
protected def OrderIso.dual [LE α] [LE β] (f : α ≃o β) : αᵒᵈ ≃o βᵒᵈ :=
  ⟨f.toEquiv, f.le_iff_le⟩

section
variable [LE α] [LE β] (f : α ≃o β)

/--
lemma `OrderIso.dual_apply` / 引理 `OrderIso.dual_apply`

English:
lemma OrderIso.dual_apply
  given: (x)
  statement: f.dual x = .toDual (f x.ofDual)
  proof: rfl

中文:
引理 OrderIso.dual_apply
  条件: (x)
  结论: f.dual x = .toDual (f x.ofDual)
  证明: rfl
-/
@[simp] lemma OrderIso.dual_apply (x) : f.dual x = .toDual (f x.ofDual) := rfl

/--
lemma `OrderIso.dual_symm_apply` / 引理 `OrderIso.dual_symm_apply`

English:
lemma OrderIso.dual_symm_apply
  given: (x)
  statement: f.dual.symm x = .toDual (f.symm x.ofDual)
  proof: rfl

中文:
引理 OrderIso.dual_symm_apply
  条件: (x)
  结论: f.dual.symm x = .toDual (f.symm x.ofDual)
  证明: rfl
-/
@[simp] lemma OrderIso.dual_symm_apply (x) : f.dual.symm x = .toDual (f.symm x.ofDual) := rfl

/--
lemma `OrderIso.symm_dual` / 引理 `OrderIso.symm_dual`

English:
lemma OrderIso.symm_dual
  statement: f.symm.dual = f.dual.symm
  proof: rfl

中文:
引理 OrderIso.symm_dual
  结论: f.symm.dual = f.dual.symm
  证明: rfl
-/
@[simp] lemma OrderIso.symm_dual : f.symm.dual = f.dual.symm := rfl

end

section LatticeIsos

@[to_dual]
/--
theorem `OrderIso.map_bot'` / 定理 `OrderIso.map_bot'`

English:
theorem OrderIso.map_bot'
  statement: [LE α] [PartialOrder β] (f : α ≃o β) {x : α} {y : β} (hx : forall x', x <= x')
  proof: by
  refine le_antisymm ?_ (hy _)
  rw [← f.apply_symm_apply y]; rw [f.le_iff_le]
  apply hx

@[to_dual]

中文:
定理 OrderIso.map_bot'
  结论: [LE α] [PartialOrder β] (f : α ≃o β) {x : α} {y : β} (hx : 对任意 x', x <= x')
  证明: by
  refine le_antisymm ?_ (hy _)
  rw [← f.apply_symm_apply y]; rw [f.le_iff_le]
  apply hx

@[to_dual]

Depends on / 依赖: apply_symm_apply, f.apply_symm_apply, f.le_iff_le, le_antisymm, le_iff_le
-/
theorem OrderIso.map_bot' [LE α] [PartialOrder β] (f : α ≃o β) {x : α} {y : β} (hx : forall x', x <= x')
    (hy : forall y', y <= y') : f x = y := by
  refine le_antisymm ?_ (hy _)
  rw [← f.apply_symm_apply y]; rw [f.le_iff_le]
  apply hx

@[to_dual]
/--
theorem `OrderIso.map_bot` / 定理 `OrderIso.map_bot`

English:
theorem OrderIso.map_bot
  given: [LE α] [PartialOrder β] [OrderBot α] [OrderBot β] (f : α ≃o β)
  statement: f ⊥ = ⊥
  proof: f.map_bot' (fun _ => bot_le) fun _ => bot_le

@[to_dual le_map_sup]

中文:
定理 OrderIso.map_bot
  条件: [LE α] [PartialOrder β] [OrderBot α] [OrderBot β] (f : α ≃o β)
  结论: f ⊥ = ⊥
  证明: f.map_bot' (fun _ => bot_le) fun _ => bot_le

@[to_dual le_map_sup]

Depends on / 依赖: bot_le, f.map_bot, map_bot
-/
theorem OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] [OrderBot β] (f : α ≃o β) : f ⊥ = ⊥ :=
  f.map_bot' (fun _ => bot_le) fun _ => bot_le

@[to_dual le_map_sup]
/--
theorem `OrderEmbedding.map_inf_le` / 定理 `OrderEmbedding.map_inf_le`

English:
theorem OrderEmbedding.map_inf_le
  given: [SemilatticeInf α] [SemilatticeInf β] (f : α ↪o β) (x y : α)
  proof: f.monotone.map_inf_le x y

@[to_dual]

中文:
定理 OrderEmbedding.map_inf_le
  条件: [SemilatticeInf α] [SemilatticeInf β] (f : α ↪o β) (x y : α)
  证明: f.monotone.map_inf_le x y

@[to_dual]

Depends on / 依赖: f.monotone.map_inf_le, map_inf_le, monotone
-/
theorem OrderEmbedding.map_inf_le [SemilatticeInf α] [SemilatticeInf β] (f : α ↪o β) (x y : α) :
    f (x ⊓ y) <= f x ⊓ f y :=
  f.monotone.map_inf_le x y

@[to_dual]
/--
theorem `OrderIso.map_inf` / 定理 `OrderIso.map_inf`

English:
theorem OrderIso.map_inf
  given: [SemilatticeInf α] [SemilatticeInf β] (f : α ≃o β) (x y : α)
  proof: by
  refine (f.toOrderEmbedding.map_inf_le x y).antisymm ?_
  apply f.symm.le_iff_le.1
  simpa using f.symm.toOrderEmbedding.map_inf_le (f x) (f y)

@[to_dual]

中文:
定理 OrderIso.map_inf
  条件: [SemilatticeInf α] [SemilatticeInf β] (f : α ≃o β) (x y : α)
  证明: by
  refine (f.toOrderEmbedding.map_inf_le x y).antisymm ?_
  apply f.symm.le_iff_le.1
  simpa using f.symm.toOrderEmbedding.map_inf_le (f x) (f y)

@[to_dual]

Depends on / 依赖: antisymm, f.symm.le_iff_le, f.symm.toOrderEmbedding.map_inf_le, f.toOrderEmbedding.map_inf_le, le_iff_le, map_inf_le, toOrderEmbedding
-/
theorem OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β] (f : α ≃o β) (x y : α) :
    f (x ⊓ y) = f x ⊓ f y := by
  refine (f.toOrderEmbedding.map_inf_le x y).antisymm ?_
  apply f.symm.le_iff_le.1
  simpa using f.symm.toOrderEmbedding.map_inf_le (f x) (f y)

@[to_dual]
/--
theorem `OrderIso.isMax_apply` / 定理 `OrderIso.isMax_apply`

English:
theorem OrderIso.isMax_apply
  given: {α β : Type*} [Preorder α] [Preorder β] (f : α ≃o β) {x : α}
  proof: by
  refine ⟨f.strictMono.isMax_of_apply, ?_⟩
  conv_lhs => rw [← f.symm_apply_apply x]
  exact f.symm.strictMono.isMax_of_apply

中文:
定理 OrderIso.isMax_apply
  条件: {α β : 类型} [Preorder α] [Preorder β] (f : α ≃o β) {x : α}
  证明: by
  refine ⟨f.strictMono.isMax_of_apply, ?_⟩
  conv_lhs => rw [← f.symm_apply_apply x]
  exact f.symm.strictMono.isMax_of_apply

Depends on / 依赖: conv_lhs, f.strictMono.isMax_of_apply, f.symm.strictMono.isMax_of_apply, f.symm_apply_apply, isMax_of_apply, strictMono, symm_apply_apply
-/
theorem OrderIso.isMax_apply {α β : Type*} [Preorder α] [Preorder β] (f : α ≃o β) {x : α} :
    IsMax (f x) ↔ IsMax x := by
  refine ⟨f.strictMono.isMax_of_apply, ?_⟩
  conv_lhs => rw [← f.symm_apply_apply x]
  exact f.symm.strictMono.isMax_of_apply

/--
theorem `Disjoint.map_orderIso` / 定理 `Disjoint.map_orderIso`

English:
theorem Disjoint.map_orderIso
  statement: [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
  proof: by
  rw [disjoint_iff_inf_le]; rw [← f.map_inf]; rw [← f.map_bot]
  exact f.monotone ha.le_bot

中文:
定理 Disjoint.map_orderIso
  结论: [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
  证明: by
  rw [disjoint_iff_inf_le]; rw [← f.map_inf]; rw [← f.map_bot]
  exact f.monotone ha.le_bot

Depends on / 依赖: disjoint_iff_inf_le, f.map_bot, f.map_inf, f.monotone, ha.le_bot, le_bot, map_bot, map_inf, monotone
-/
theorem Disjoint.map_orderIso [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
    {a b : α} (f : α ≃o β) (ha : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [disjoint_iff_inf_le]; rw [← f.map_inf]; rw [← f.map_bot]
  exact f.monotone ha.le_bot

/-- Note that this goal could also be stated `(Codisjoint on f) a b` -/
@[to_dual existing] -- We can remove this use of `existing` once we get https://github.com/leanprover-community/mathlib4/pull/32438
/--
theorem `Codisjoint.map_orderIso` / 定理 `Codisjoint.map_orderIso`

English:
theorem Codisjoint.map_orderIso
  statement: [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β]
  proof: by
  rw [codisjoint_iff_le_sup]; rw [← f.map_sup]; rw [← f.map_top]
  exact f.monotone ha.top_le

@[to_dual (attr := simp)]

中文:
定理 Codisjoint.map_orderIso
  结论: [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β]
  证明: by
  rw [codisjoint_iff_le_sup]; rw [← f.map_sup]; rw [← f.map_top]
  exact f.monotone ha.top_le

@[to_dual (attr := simp)]

Depends on / 依赖: codisjoint_iff_le_sup, f.map_sup, f.map_top, f.monotone, ha.top_le, map_sup, map_top, monotone, top_le
-/
theorem Codisjoint.map_orderIso [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β]
    {a b : α} (f : α ≃o β) (ha : Codisjoint a b) : Codisjoint (f a) (f b) := by
  rw [codisjoint_iff_le_sup]; rw [← f.map_sup]; rw [← f.map_top]
  exact f.monotone ha.top_le

@[to_dual (attr := simp)]
/--
theorem `disjoint_map_orderIso_iff` / 定理 `disjoint_map_orderIso_iff`

English:
theorem disjoint_map_orderIso_iff
  statement: [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
  proof: ⟨fun h => f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_orderIso f.symm,
   fun h => h.map_orderIso f⟩

中文:
定理 disjoint_map_orderIso_iff
  结论: [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
  证明: ⟨fun h => f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_orderIso f.symm,
   fun h => h.map_orderIso f⟩

Depends on / 依赖: f.symm, f.symm_apply_apply, h.map_orderIso, map_orderIso, symm_apply_apply
-/
theorem disjoint_map_orderIso_iff [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
    {a b : α} (f : α ≃o β) : Disjoint (f a) (f b) ↔ Disjoint a b :=
  ⟨fun h => f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_orderIso f.symm,
   fun h => h.map_orderIso f⟩

section BoundedOrder

variable [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] (f : α ≃o β)

/--
theorem `OrderIso.isCompl` / 定理 `OrderIso.isCompl`

English:
theorem OrderIso.isCompl
  given: {x y : α} (h : IsCompl x y)
  statement: IsCompl (f x) (f y)
  proof: ⟨h.1.map_orderIso _, h.2.map_orderIso _⟩

中文:
定理 OrderIso.isCompl
  条件: {x y : α} (h : IsCompl x y)
  结论: IsCompl (f x) (f y)
  证明: ⟨h.1.map_orderIso _, h.2.map_orderIso _⟩

Depends on / 依赖: map_orderIso
-/
theorem OrderIso.isCompl {x y : α} (h : IsCompl x y) : IsCompl (f x) (f y) :=
  ⟨h.1.map_orderIso _, h.2.map_orderIso _⟩

/--
theorem `OrderIso.isCompl_iff` / 定理 `OrderIso.isCompl_iff`

English:
theorem OrderIso.isCompl_iff
  given: {x y : α}
  statement: IsCompl x y ↔ IsCompl (f x) (f y)
  proof: ⟨f.isCompl, fun h => f.symm_apply_apply x ▸ f.symm_apply_apply y ▸ f.symm.isCompl h⟩

中文:
定理 OrderIso.isCompl_iff
  条件: {x y : α}
  结论: IsCompl x y ↔ IsCompl (f x) (f y)
  证明: ⟨f.isCompl, fun h => f.symm_apply_apply x ▸ f.symm_apply_apply y ▸ f.symm.isCompl h⟩

Depends on / 依赖: f.isCompl, f.symm.isCompl, f.symm_apply_apply, isCompl, symm_apply_apply
-/
theorem OrderIso.isCompl_iff {x y : α} : IsCompl x y ↔ IsCompl (f x) (f y) :=
  ⟨f.isCompl, fun h => f.symm_apply_apply x ▸ f.symm_apply_apply y ▸ f.symm.isCompl h⟩

/--
theorem `OrderIso.complementedLattice` / 定理 `OrderIso.complementedLattice`

English:
theorem OrderIso.complementedLattice
  given: [ComplementedLattice α] (f : α ≃o β)
  statement: ComplementedLattice β
  proof: ⟨fun x => by
    obtain ⟨y, hy⟩ := exists_isCompl (f.symm x)
    rw [← f.symm_apply_apply y] at hy
    exact ⟨f y, f.symm.isCompl_iff.2 hy⟩⟩

中文:
定理 OrderIso.complementedLattice
  条件: [ComplementedLattice α] (f : α ≃o β)
  结论: ComplementedLattice β
  证明: ⟨fun x => by
    obtain ⟨y, hy⟩ := exists_isCompl (f.symm x)
    rw [← f.symm_apply_apply y] at hy
    exact ⟨f y, f.symm.isCompl_iff.2 hy⟩⟩

Depends on / 依赖: exists_isCompl, f.symm, f.symm.isCompl_iff, f.symm_apply_apply, isCompl_iff, symm_apply_apply
-/
theorem OrderIso.complementedLattice [ComplementedLattice α] (f : α ≃o β) : ComplementedLattice β :=
  ⟨fun x => by
    obtain ⟨y, hy⟩ := exists_isCompl (f.symm x)
    rw [← f.symm_apply_apply y] at hy
    exact ⟨f y, f.symm.isCompl_iff.2 hy⟩⟩

/--
theorem `OrderIso.complementedLattice_iff` / 定理 `OrderIso.complementedLattice_iff`

English:
theorem OrderIso.complementedLattice_iff
  given: (f : α ≃o β)
  proof: ⟨by intro; exact f.complementedLattice,
   by intro; exact f.symm.complementedLattice⟩

中文:
定理 OrderIso.complementedLattice_iff
  条件: (f : α ≃o β)
  证明: ⟨by intro; exact f.complementedLattice,
   by intro; exact f.symm.complementedLattice⟩

Depends on / 依赖: ENat.eq_top_iff_forall_ge, Ideal.mem_span_singleton, Ideal.one_eq_top, Ideal.span_singleton_pow, SModEq, SModEq.zero, addVal_eq_top_iff, addVal_le_iff_dvd, addVal_pow, complementedLattice, eq_top_iff_forall_ge, exists_irreducible, f.complementedLattice, f.symm.complementedLattice, maximalIdeal_eq, mem_span_singleton, mul_one, one_eq_top, smul_eq_mul, span_singleton_pow
-/
theorem OrderIso.complementedLattice_iff (f : α ≃o β) :
    ComplementedLattice α ↔ ComplementedLattice β :=
  ⟨by intro; exact f.complementedLattice,
   by intro; exact f.symm.complementedLattice⟩

end BoundedOrder

end LatticeIsos

section DenselyOrdered

-- could live in a more upstream file, but hard to find a good place
/--
lemma `StrictMono.denselyOrdered_range` / 引理 `StrictMono.denselyOrdered_range`

English:
lemma StrictMono.denselyOrdered_range
  statement: {X Y : Type*} [LinearOrder X] [DenselyOrdered X] [Preorder Y]
  proof: by
  constructor
  simpa [← exists_and_left, ← exists_and_right, exists_comm, hf.lt_iff_lt]
    using fun _ _ => exists_between

中文:
引理 StrictMono.denselyOrdered_range
  结论: {X Y : 类型} [LinearOrder X] [DenselyOrdered X] [Preorder Y]
  证明: by
  constructor
  simpa [← exists_and_left, ← exists_and_right, exists_comm, hf.lt_iff_lt]
    using fun _ _ => exists_between

Depends on / 依赖: exists_and_left, exists_and_right, exists_between, exists_comm, hf.lt_iff_lt, lt_iff_lt
-/
lemma StrictMono.denselyOrdered_range {X Y : Type*} [LinearOrder X] [DenselyOrdered X] [Preorder Y]
    {f : X -> Y} (hf : StrictMono f) :
    DenselyOrdered (Set.range f) := by
  constructor
  simpa [← exists_and_left, ← exists_and_right, exists_comm, hf.lt_iff_lt]
    using fun _ _ => exists_between

/--
lemma `denselyOrdered_iff_of_orderIsoClass` / 引理 `denselyOrdered_iff_of_orderIsoClass`

English:
lemma denselyOrdered_iff_of_orderIsoClass
  statement: {X Y F : Type*} [Preorder X] [Preorder Y]
  proof: by
  constructor
  · intro H
    refine ⟨fun a b h => ?_⟩
    obtain ⟨c, hc⟩ := exists_between ((map_inv_lt_map_inv_iff f).mpr h)
    exact ⟨f c, by simpa using hc⟩
  · intro H
    refine ⟨fun a b h => ?_⟩
    obtain ⟨c, hc⟩ := exists_between ((map_lt_map_iff f).mpr h)
    exact ⟨EquivLike.inv f c, 

中文:
引理 denselyOrdered_iff_of_orderIsoClass
  结论: {X Y F : 类型} [Preorder X] [Preorder Y]
  证明: by
  constructor
  · intro H
    refine ⟨fun a b h => ?_⟩
    obtain ⟨c, hc⟩ := exists_between ((map_inv_lt_map_inv_iff f).mpr h)
    exact ⟨f c, by simpa using hc⟩
  · intro H
    refine ⟨fun a b h => ?_⟩
    obtain ⟨c, hc⟩ := exists_between ((map_lt_map_iff f).mpr h)
    exact ⟨EquivLike.inv f c, 

Depends on / 依赖: EquivLike, EquivLike.inv, exists_between, map_inv_lt_map_inv_iff, map_lt_map_iff
-/
lemma denselyOrdered_iff_of_orderIsoClass {X Y F : Type*} [Preorder X] [Preorder Y]
    [EquivLike F X Y] [OrderIsoClass F X Y] (f : F) :
    DenselyOrdered X ↔ DenselyOrdered Y := by
  constructor
  · intro H
    refine ⟨fun a b h => ?_⟩
    obtain ⟨c, hc⟩ := exists_between ((map_inv_lt_map_inv_iff f).mpr h)
    exact ⟨f c, by simpa using hc⟩
  · intro H
    refine ⟨fun a b h => ?_⟩
    obtain ⟨c, hc⟩ := exists_between ((map_lt_map_iff f).mpr h)
    exact ⟨EquivLike.inv f c, by simpa using hc⟩

/--
lemma `denselyOrdered_iff_of_strictAnti` / 引理 `denselyOrdered_iff_of_strictAnti`

English:
lemma denselyOrdered_iff_of_strictAnti
  statement: {X Y F : Type*} [LinearOrder X] [Preorder Y]
  proof: by
  rw [← denselyOrdered_orderDual]
  let e : Xᵒᵈ ≃o Y := ⟨OrderDual.ofDual.trans (f : X ≃ Y), ?_⟩
  · exact denselyOrdered_iff_of_orderIsoClass e
  · simp only [Equiv.trans_apply, EquivLike.coe_coe, OrderDual.forall, OrderDual.ofDual_toDual,
      OrderDual.toDual_le_toDual]
    intro a b
    rw [

中文:
引理 denselyOrdered_iff_of_strictAnti
  结论: {X Y F : 类型} [LinearOrder X] [Preorder Y]
  证明: by
  rw [← denselyOrdered_orderDual]
  let e : Xᵒᵈ ≃o Y := ⟨OrderDual.ofDual.trans (f : X ≃ Y), ?_⟩
  · exact denselyOrdered_iff_of_orderIsoClass e
  · simp only [Equiv.trans_apply, EquivLike.coe_coe, OrderDual.forall, OrderDual.ofDual_toDual,
      OrderDual.toDual_le_toDual]
    intro a b
    rw [

Depends on / 依赖: Equiv.trans_apply, EquivLike, EquivLike.coe_coe, OrderDual, OrderDual.forall, OrderDual.ofDual.trans, OrderDual.ofDual_toDual, OrderDual.toDual_le_toDual, coe_coe, denselyOrdered_iff_of_orderIsoClass, denselyOrdered_orderDual, hf.le_iff_ge, le_iff_ge, ofDual, ofDual_toDual, toDual_le_toDual, trans_apply
-/
lemma denselyOrdered_iff_of_strictAnti {X Y F : Type*} [LinearOrder X] [Preorder Y]
    [EquivLike F X Y] (f : F) (hf : StrictAnti f) :
    DenselyOrdered X ↔ DenselyOrdered Y := by
  rw [← denselyOrdered_orderDual]
  let e : Xᵒᵈ ≃o Y := ⟨OrderDual.ofDual.trans (f : X ≃ Y), ?_⟩
  · exact denselyOrdered_iff_of_orderIsoClass e
  · simp only [Equiv.trans_apply, EquivLike.coe_coe, OrderDual.forall, OrderDual.ofDual_toDual,
      OrderDual.toDual_le_toDual]
    intro a b
    rw [hf.le_iff_ge]

end DenselyOrdered

universe v u in
/-- The bijection `ULift.{v} α ≃ α` as an isomorphism of orders. -/
@[pp_with_univ, simps!]
/--
Definition of `ULift.orderIso` / `ULift.orderIso` 的定义

English:
definition ULift.orderIso
  signature: {α : Type u} [Preorder α]
  body: Equiv.ulift.toOrderIso (fun _ _ => id) (fun _ _ => id)

中文:
定义 ULift.orderIso
  签名: {α : 类型u} [Preorder α]
  定义体: Equiv.ulift.toOrderIso (fun _ _ => id) (fun _ _ => id)

Depends on / 依赖: Equiv.ulift.toOrderIso, toOrderIso
-/
def ULift.orderIso {α : Type u} [Preorder α] :
    ULift.{v} α ≃o α :=
  Equiv.ulift.toOrderIso (fun _ _ => id) (fun _ _ => id)
