/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic

/-!
# Order dual

This file defines `OrderDual α`, a type synonym reversing the meaning of all inequalities,
with notation `αᵒᵈ`.

## Notation

`αᵒᵈ` is notation for `OrderDual α`.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`. Instead, explicit
coercions should be inserted:
* `OrderDual.toDual : α → αᵒᵈ` and `OrderDual.ofDual : αᵒᵈ → α`
-/

@[expose] public section

assert_not_exists Lex

variable {α : Type*}

/--
Definition of `OrderDual` / `OrderDual` 的定义

English:
definition OrderDual
  signature: (α : Type*)
  body: α

@[inherit_doc]
notation:max α "ᵒᵈ" => OrderDual α

中文:
定义 OrderDual
  签名: (α : 类型)
  定义体: α

@[inherit_doc]
notation:max α "ᵒᵈ" => OrderDual α
-/
def OrderDual (α : Type*) : Type _ :=
  α

@[inherit_doc]
notation:max α "ᵒᵈ" => OrderDual α

namespace OrderDual

instance (α : Type*) [h : Nonempty α] : Nonempty αᵒᵈ :=
  h

instance (α : Type*) [h : Subsingleton α] : Subsingleton αᵒᵈ :=
  h

instance (α : Type*) [h : LE α] : LE αᵒᵈ :=
  ⟨fun a b => h.le b a⟩

instance (α : Type*) [h : LT α] : LT αᵒᵈ :=
  ⟨fun a b => h.lt b a⟩

instance (α : Type*) [h : Ord α] : Ord αᵒᵈ :=
  ⟨fun a b => h.compare b a⟩

@[to_dual]
instance (α : Type*) [h : Min α] : Max αᵒᵈ :=
  ⟨fun a b => h.min a b⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: α] [T
  body: T.trans _ _ _ hbc hab

中文:
实例 [LE
  签名: α] [T
  定义体: T.trans _ _ _ hbc hab

Depends on / 依赖: T.trans
-/
instance [LE α] [T : IsTrans α LE.le] : IsTrans αᵒᵈ LE.le where
  trans _ _ _ hab hbc := T.trans _ _ _ hbc hab

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: α] [T
  body: T.trans _ _ _ hbc hab

中文:
实例 [LT
  签名: α] [T
  定义体: T.trans _ _ _ hbc hab

Depends on / 依赖: T.trans
-/
instance [LT α] [T : IsTrans α LT.lt] : IsTrans αᵒᵈ LT.lt where
  trans _ _ _ hab hbc := T.trans _ _ _ hbc hab

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: α] [T
  body: by rw [eq_comm]; exact T.trichotomous b a

中文:
实例 [LT
  签名: α] [T
  定义体: by rw [eq_comm]; exact T.trichotomous b a

Depends on / 依赖: T.trichotomous, eq_comm, trichotomous
-/
instance [LT α] [T : @Std.Trichotomous α LT.lt] : @Std.Trichotomous αᵒᵈ LT.lt where
  trichotomous a b := by rw [eq_comm]; exact T.trichotomous b a

instance (α : Type*) [Preorder α] : Preorder αᵒᵈ where
  le_refl _ := le_refl _
  le_trans _ _ _ hab hbc := hbc.trans hab
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge

instance (α : Type*) [PartialOrder α] : PartialOrder αᵒᵈ where
  le_antisymm a b hab hba := @le_antisymm α _ a b hba hab

instance (α : Type*) [DecidableEq α] : DecidableEq αᵒᵈ := ‹DecidableEq α›

instance (α : Type*) [LT α] [h : DecidableLT α] : DecidableLT (αᵒᵈ) :=
  fun a b => h b a

instance (α : Type*) [LE α] [h : DecidableLE α] : DecidableLE (αᵒᵈ) :=
  fun a b => h b a

set_option backward.isDefEq.respectTransparency false in
instance (α : Type*) [LinearOrder α] : LinearOrder αᵒᵈ where
  le_total a b := le_total (α := α) b a
  min_def := max_def' (α := α)
  max_def := min_def' (α := α)
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  toDecidableEq := inferInstance
  compare_eq_compareOfLessAndEq a b := by
    simp only [compare, LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq, eq_comm]
    rfl

set_option linter.style.setOption false in
set_option backward.inferInstanceAs.wrap.reuseSubInstances false in -- otherwise we get an identity!
/-- The opposite linear order to a given linear order -/
@[instance_reducible, deprecated "This declaration shouldn't have existed" (since := "2026-04-08")]
/--
Definition of `_root_.LinearOrder.swap` / `_root_.LinearOrder.swap` 的定义

English:
definition _root_.LinearOrder.swap
  signature: (α : Type*) (_ : LinearOrder α)
  body: inferInstanceAs LinearOrder (OrderDual α)

中文:
定义 _root_.LinearOrder.swap
  签名: (α : 类型) (_ : LinearOrder α)
  定义体: inferInstanceAs LinearOrder (OrderDual α)

Depends on / 依赖: LinearOrder, OrderDual, mem_sInf, mem_sInf.mpr, smul_mem
-/
def _root_.LinearOrder.swap (α : Type*) (_ : LinearOrder α) : LinearOrder α :=
inferInstanceAs LinearOrder (OrderDual α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Inhabited α] : Inhabited αᵒᵈ
  body: ⟨h.default⟩

中文:
实例 [h
  签名: : Inhabited α] : Inhabited αᵒᵈ
  定义体: ⟨h.default⟩

Depends on / 依赖: h.default
-/
instance [h : Inhabited α] : Inhabited αᵒᵈ := ⟨h.default⟩

/--
theorem `Ord.dual_dual` / 定理 `Ord.dual_dual`

English:
theorem Ord.dual_dual
  given: (α : Type*) [H : Ord α]
  statement: OrderDual.instOrd αᵒᵈ = H
  proof: rfl

中文:
定理 Ord.dual_dual
  条件: (α : 类型) [H : Ord α]
  结论: OrderDual.instOrd αᵒᵈ = H
  证明: rfl
-/
theorem Ord.dual_dual (α : Type*) [H : Ord α] : OrderDual.instOrd αᵒᵈ = H :=
  rfl

/--
theorem `Preorder.dual_dual` / 定理 `Preorder.dual_dual`

English:
theorem Preorder.dual_dual
  given: (α : Type*) [H : Preorder α]
  statement: OrderDual.instPreorder αᵒᵈ = H
  proof: rfl

中文:
定理 Preorder.dual_dual
  条件: (α : 类型) [H : Preorder α]
  结论: OrderDual.instPreorder αᵒᵈ = H
  证明: rfl
-/
theorem Preorder.dual_dual (α : Type*) [H : Preorder α] : OrderDual.instPreorder αᵒᵈ = H :=
  rfl

/--
theorem `instPartialOrder.dual_dual` / 定理 `instPartialOrder.dual_dual`

English:
theorem instPartialOrder.dual_dual
  given: (α : Type*) [H : PartialOrder α]
  proof: rfl

中文:
定理 instPartialOrder.dual_dual
  条件: (α : 类型) [H : PartialOrder α]
  证明: rfl
-/
theorem instPartialOrder.dual_dual (α : Type*) [H : PartialOrder α] :
    OrderDual.instPartialOrder αᵒᵈ = H :=
  rfl

/--
theorem `instLinearOrder.dual_dual` / 定理 `instLinearOrder.dual_dual`

English:
theorem instLinearOrder.dual_dual
  given: (α : Type*) [H : LinearOrder α]
  proof: rfl

中文:
定理 instLinearOrder.dual_dual
  条件: (α : 类型) [H : LinearOrder α]
  证明: rfl
-/
theorem instLinearOrder.dual_dual (α : Type*) [H : LinearOrder α] :
    OrderDual.instLinearOrder αᵒᵈ = H :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Nontrivial α] : Nontrivial αᵒᵈ
  body: h

中文:
实例 [h
  签名: : Nontrivial α] : Nontrivial αᵒᵈ
  定义体: h
-/
instance [h : Nontrivial α] : Nontrivial αᵒᵈ := h
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Unique α] : Unique αᵒᵈ where
  body: h.uniq

中文:
实例 [h
  签名: : Unique α] : Unique αᵒᵈ where
  定义体: h.uniq

Depends on / 依赖: h.uniq
-/
instance [h : Unique α] : Unique αᵒᵈ where
  uniq := h.uniq

/--
Definition of `toDual` / `toDual` 的定义

English:
definition toDual
  signature: : α ≃ αᵒᵈ
  body: Equiv.refl _

中文:
定义 toDual
  签名: : α ≃ αᵒᵈ
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def toDual : α ≃ αᵒᵈ :=
  Equiv.refl _

/--
Definition of `ofDual` / `ofDual` 的定义

English:
definition ofDual
  signature: : αᵒᵈ ≃ α
  body: Equiv.refl _

中文:
定义 ofDual
  签名: : αᵒᵈ ≃ α
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def ofDual : αᵒᵈ ≃ α :=
  Equiv.refl _

/--
theorem `toDual_symm_eq` / 定理 `toDual_symm_eq`

English:
theorem toDual_symm_eq
  statement: (@toDual α).symm = ofDual
  proof: rfl

中文:
定理 toDual_symm_eq
  结论: (@toDual α).symm = ofDual
  证明: rfl
-/
@[simp] theorem toDual_symm_eq : (@toDual α).symm = ofDual := rfl
/--
theorem `ofDual_symm_eq` / 定理 `ofDual_symm_eq`

English:
theorem ofDual_symm_eq
  statement: (@ofDual α).symm = toDual
  proof: rfl

中文:
定理 ofDual_symm_eq
  结论: (@ofDual α).symm = toDual
  证明: rfl
-/
@[simp] theorem ofDual_symm_eq : (@ofDual α).symm = toDual := rfl
/--
theorem `toDual_ofDual` / 定理 `toDual_ofDual`

English:
theorem toDual_ofDual
  given: (a : αᵒᵈ)
  statement: toDual (ofDual a) = a
  proof: rfl

中文:
定理 toDual_ofDual
  条件: (a : αᵒᵈ)
  结论: toDual (ofDual a) = a
  证明: rfl
-/
@[simp] theorem toDual_ofDual (a : αᵒᵈ) : toDual (ofDual a) = a := rfl
/--
theorem `ofDual_toDual` / 定理 `ofDual_toDual`

English:
theorem ofDual_toDual
  given: (a : α)
  statement: ofDual (toDual a) = a
  proof: rfl

中文:
定理 ofDual_toDual
  条件: (a : α)
  结论: ofDual (toDual a) = a
  证明: rfl
-/
@[simp] theorem ofDual_toDual (a : α) : ofDual (toDual a) = a := rfl

/--
theorem `toDual_trans_ofDual` / 定理 `toDual_trans_ofDual`

English:
theorem toDual_trans_ofDual
  statement: (toDual (α := α)).trans ofDual = Equiv.refl _
  proof: rfl

中文:
定理 toDual_trans_ofDual
  结论: (toDual (α := α)).trans ofDual = Equiv.refl _
  证明: rfl
-/
@[simp] theorem toDual_trans_ofDual : (toDual (α := α)).trans ofDual = Equiv.refl _ := rfl
/--
theorem `ofDual_trans_toDual` / 定理 `ofDual_trans_toDual`

English:
theorem ofDual_trans_toDual
  statement: (ofDual (α := α)).trans toDual = Equiv.refl _
  proof: rfl

中文:
定理 ofDual_trans_toDual
  结论: (ofDual (α := α)).trans toDual = Equiv.refl _
  证明: rfl
-/
@[simp] theorem ofDual_trans_toDual : (ofDual (α := α)).trans toDual = Equiv.refl _ := rfl
/--
theorem `toDual_comp_ofDual` / 定理 `toDual_comp_ofDual`

English:
theorem toDual_comp_ofDual
  statement: (toDual (α := α)) ∘ ofDual = id
  proof: rfl

中文:
定理 toDual_comp_ofDual
  结论: (toDual (α := α)) ∘ ofDual = id
  证明: rfl
-/
@[simp] theorem toDual_comp_ofDual : (toDual (α := α)) ∘ ofDual = id := rfl
/--
theorem `ofDual_comp_toDual` / 定理 `ofDual_comp_toDual`

English:
theorem ofDual_comp_toDual
  statement: (ofDual (α := α)) ∘ toDual = id
  proof: rfl

中文:
定理 ofDual_comp_toDual
  结论: (ofDual (α := α)) ∘ toDual = id
  证明: rfl
-/
@[simp] theorem ofDual_comp_toDual : (ofDual (α := α)) ∘ toDual = id := rfl

/--
theorem `toDual_inj` / 定理 `toDual_inj`

English:
theorem toDual_inj
  given: {a b : α}
  statement: toDual a = toDual b ↔ a = b
  proof: by simp

中文:
定理 toDual_inj
  条件: {a b : α}
  结论: toDual a = toDual b ↔ a = b
  证明: by simp
-/
theorem toDual_inj {a b : α} : toDual a = toDual b ↔ a = b := by simp
/--
theorem `ofDual_inj` / 定理 `ofDual_inj`

English:
theorem ofDual_inj
  given: {a b : αᵒᵈ}
  statement: ofDual a = ofDual b ↔ a = b
  proof: by simp

中文:
定理 ofDual_inj
  条件: {a b : αᵒᵈ}
  结论: ofDual a = ofDual b ↔ a = b
  证明: by simp
-/
theorem ofDual_inj {a b : αᵒᵈ} : ofDual a = ofDual b ↔ a = b := by simp

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {a b : αᵒᵈ} (h : ofDual a = ofDual b)
  statement: a = b
  proof: h

@[to_dual self, simp]

中文:
引理 ext
  条件: {a b : αᵒᵈ} (h : ofDual a = ofDual b)
  结论: a = b
  证明: h

@[to_dual self, simp]
-/
@[ext] lemma ext {a b : αᵒᵈ} (h : ofDual a = ofDual b) : a = b := h

@[to_dual self, simp]
/--
theorem `toDual_le_toDual` / 定理 `toDual_le_toDual`

English:
theorem toDual_le_toDual
  given: [LE α] {a b : α}
  statement: toDual a <= toDual b ↔ b <= a
  proof: .rfl

@[to_dual self, simp]

中文:
定理 toDual_le_toDual
  条件: [LE α] {a b : α}
  结论: toDual a <= toDual b ↔ b <= a
  证明: .rfl

@[to_dual self, simp]
-/
theorem toDual_le_toDual [LE α] {a b : α} : toDual a <= toDual b ↔ b <= a := .rfl

@[to_dual self, simp]
/--
theorem `toDual_lt_toDual` / 定理 `toDual_lt_toDual`

English:
theorem toDual_lt_toDual
  given: [LT α] {a b : α}
  statement: toDual a < toDual b ↔ b < a
  proof: .rfl

@[to_dual self, simp]

中文:
定理 toDual_lt_toDual
  条件: [LT α] {a b : α}
  结论: toDual a < toDual b ↔ b < a
  证明: .rfl

@[to_dual self, simp]
-/
theorem toDual_lt_toDual [LT α] {a b : α} : toDual a < toDual b ↔ b < a := .rfl

@[to_dual self, simp]
/--
theorem `ofDual_le_ofDual` / 定理 `ofDual_le_ofDual`

English:
theorem ofDual_le_ofDual
  given: [LE α] {a b : αᵒᵈ}
  statement: ofDual a <= ofDual b ↔ b <= a
  proof: .rfl

@[to_dual self, simp]

中文:
定理 ofDual_le_ofDual
  条件: [LE α] {a b : αᵒᵈ}
  结论: ofDual a <= ofDual b ↔ b <= a
  证明: .rfl

@[to_dual self, simp]
-/
theorem ofDual_le_ofDual [LE α] {a b : αᵒᵈ} : ofDual a <= ofDual b ↔ b <= a := .rfl

@[to_dual self, simp]
/--
theorem `ofDual_lt_ofDual` / 定理 `ofDual_lt_ofDual`

English:
theorem ofDual_lt_ofDual
  given: [LT α] {a b : αᵒᵈ}
  statement: ofDual a < ofDual b ↔ b < a
  proof: .rfl

@[to_dual toDual_le]

中文:
定理 ofDual_lt_ofDual
  条件: [LT α] {a b : αᵒᵈ}
  结论: ofDual a < ofDual b ↔ b < a
  证明: .rfl

@[to_dual toDual_le]
-/
theorem ofDual_lt_ofDual [LT α] {a b : αᵒᵈ} : ofDual a < ofDual b ↔ b < a := .rfl

@[to_dual toDual_le]
/--
theorem `le_toDual` / 定理 `le_toDual`

English:
theorem le_toDual
  given: [LE α] {a : αᵒᵈ} {b : α}
  statement: a <= toDual b ↔ b <= ofDual a
  proof: .rfl

@[to_dual toDual_lt]

中文:
定理 le_toDual
  条件: [LE α] {a : αᵒᵈ} {b : α}
  结论: a <= toDual b ↔ b <= ofDual a
  证明: .rfl

@[to_dual toDual_lt]
-/
theorem le_toDual [LE α] {a : αᵒᵈ} {b : α} : a <= toDual b ↔ b <= ofDual a := .rfl

@[to_dual toDual_lt]
/--
theorem `lt_toDual` / 定理 `lt_toDual`

English:
theorem lt_toDual
  given: [LT α] {a : αᵒᵈ} {b : α}
  statement: a < toDual b ↔ b < ofDual a
  proof: .rfl

中文:
定理 lt_toDual
  条件: [LT α] {a : αᵒᵈ} {b : α}
  结论: a < toDual b ↔ b < ofDual a
  证明: .rfl
-/
theorem lt_toDual [LT α] {a : αᵒᵈ} {b : α} : a < toDual b ↔ b < ofDual a := .rfl

/-- Recursor for `αᵒᵈ`. -/
@[elab_as_elim]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {motive : αᵒᵈ -> Sort*} (toDual : forall a : α, motive (toDual a))
  body: toDual

中文:
定义 rec
  签名: {motive : αᵒᵈ -> Sort*} (toDual : 对任意 a : α, motive (toDual a))
  定义体: toDual
-/
protected def rec {motive : αᵒᵈ -> Sort*} (toDual : forall a : α, motive (toDual a)) :
    forall a : αᵒᵈ, motive a := toDual

/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : αᵒᵈ -> Prop}
  statement: (forall a, p a) ↔ forall a, p (toDual a)
  proof: .rfl

中文:
定理 «forall»
  条件: {p : αᵒᵈ -> 命题}
  结论: (对任意 a, p a) ↔ 对任意 a, p (toDual a)
  证明: .rfl
-/
@[simp] protected theorem «forall» {p : αᵒᵈ -> Prop} : (forall a, p a) ↔ forall a, p (toDual a) := .rfl
/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {p : αᵒᵈ -> Prop}
  statement: (exists a, p a) ↔ exists a, p (toDual a)
  proof: .rfl

@[to_dual self] alias ⟨_, _root_.LE.le.dual⟩ := toDual_le_toDual
@[to_dual self] alias ⟨_, _root_.LT.lt.dual⟩ := toDual_lt_toDual
@[to_dual self] alias ⟨_, _root_.LE.le.ofDual⟩ := ofDual_le_ofDual
@[to_dual self] alias ⟨_, _root_.LT.lt.ofDual⟩ := ofDual_lt_ofDual

中文:
定理 «exists»
  条件: {p : αᵒᵈ -> 命题}
  结论: (存在 a, p a) ↔ 存在 a, p (toDual a)
  证明: .rfl

@[to_dual self] alias ⟨_, _root_.LE.le.dual⟩ := toDual_le_toDual
@[to_dual self] alias ⟨_, _root_.LT.lt.dual⟩ := toDual_lt_toDual
@[to_dual self] alias ⟨_, _root_.LE.le.ofDual⟩ := ofDual_le_ofDual
@[to_dual self] alias ⟨_, _root_.LT.lt.ofDual⟩ := ofDual_lt_ofDual
-/
@[simp] protected theorem «exists» {p : αᵒᵈ -> Prop} : (exists a, p a) ↔ exists a, p (toDual a) := .rfl

@[to_dual self] alias ⟨_, _root_.LE.le.dual⟩ := toDual_le_toDual
@[to_dual self] alias ⟨_, _root_.LT.lt.dual⟩ := toDual_lt_toDual
@[to_dual self] alias ⟨_, _root_.LE.le.ofDual⟩ := ofDual_le_ofDual
@[to_dual self] alias ⟨_, _root_.LT.lt.ofDual⟩ := ofDual_lt_ofDual

end OrderDual


/--
Instance `OrderDual.denselyOrdered` / 实例 `OrderDual.denselyOrdered`

English:
instance OrderDual.denselyOrdered
  signature: (α : Type*) [LT α] [h : DenselyOrdered α]
  body: ⟨fun _ _ ha => (@exists_between α _ h _ _ ha).imp fun _ => And.symm⟩

@[simp]

中文:
实例 OrderDual.denselyOrdered
  签名: (α : 类型) [LT α] [h : DenselyOrdered α]
  定义体: ⟨fun _ _ ha => (@exists_between α _ h _ _ ha).imp fun _ => And.symm⟩

@[simp]

Depends on / 依赖: And.symm, exists_between
-/
instance OrderDual.denselyOrdered (α : Type*) [LT α] [h : DenselyOrdered α] :
    DenselyOrdered αᵒᵈ :=
  ⟨fun _ _ ha => (@exists_between α _ h _ _ ha).imp fun _ => And.symm⟩

@[simp]
/--
theorem `denselyOrdered_orderDual` / 定理 `denselyOrdered_orderDual`

English:
theorem denselyOrdered_orderDual
  given: [LT α]
  statement: DenselyOrdered αᵒᵈ ↔ DenselyOrdered α
  proof: ⟨by convert! @OrderDual.denselyOrdered αᵒᵈ _, @OrderDual.denselyOrdered α _⟩

中文:
定理 denselyOrdered_orderDual
  条件: [LT α]
  结论: DenselyOrdered αᵒᵈ ↔ DenselyOrdered α
  证明: ⟨by convert! @OrderDual.denselyOrdered αᵒᵈ _, @OrderDual.denselyOrdered α _⟩

Depends on / 依赖: OrderDual, OrderDual.denselyOrdered, convert, denselyOrdered
-/
theorem denselyOrdered_orderDual [LT α] : DenselyOrdered αᵒᵈ ↔ DenselyOrdered α :=
  ⟨by convert! @OrderDual.denselyOrdered αᵒᵈ _, @OrderDual.denselyOrdered α _⟩

/-! ### Pushing order definitions through `Equiv` -/

namespace Equiv

variable {β : Type*} (e : α ≃ β)

/--
Definition of `top` / `top` 的定义

English:
abbreviation top
  signature: [Top β]
  body: e.symm ⊤

中文:
缩写 top
  签名: [Top β]
  定义体: e.symm ⊤
-/
protected abbrev top [Top β] : Top α where
  top := e.symm ⊤

/--
lemma `top_def` / 引理 `top_def`

English:
lemma top_def
  given: [Top β]
  proof: e.top
    ⊤ = e.symm ⊤ := rfl

中文:
引理 top_def
  条件: [Top β]
  证明: e.top
    ⊤ = e.symm ⊤ := rfl

Depends on / 依赖: e.top
-/
lemma top_def [Top β] :
    letI := e.top
    ⊤ = e.symm ⊤ := rfl

/--
Definition of `bot` / `bot` 的定义

English:
abbreviation bot
  signature: [Bot β]
  body: e.symm ⊥

中文:
缩写 bot
  签名: [Bot β]
  定义体: e.symm ⊥
-/
protected abbrev bot [Bot β] : Bot α where
  bot := e.symm ⊥

/--
lemma `bot_def` / 引理 `bot_def`

English:
lemma bot_def
  given: [Bot β]
  proof: e.bot
    ⊥ = e.symm ⊥ := rfl

中文:
引理 bot_def
  条件: [Bot β]
  证明: e.bot
    ⊥ = e.symm ⊥ := rfl

Depends on / 依赖: e.bot
-/
lemma bot_def [Bot β] :
    letI := e.bot
    ⊥ = e.symm ⊥ := rfl

/--
Definition of `compl` / `compl` 的定义

English:
abbreviation compl
  signature: [Compl β]
  body: e.symm (e a)ᶜ

中文:
缩写 compl
  签名: [Compl β]
  定义体: e.symm (e a)ᶜ
-/
protected abbrev compl [Compl β] : Compl α where
  compl a := e.symm (e a)ᶜ

/--
lemma `compl_def` / 引理 `compl_def`

English:
lemma compl_def
  given: [Compl β] (a : α)
  proof: e.compl
    aᶜ = e.symm (e a)ᶜ := rfl

中文:
引理 compl_def
  条件: [Compl β] (a : α)
  证明: e.compl
    aᶜ = e.symm (e a)ᶜ := rfl

Depends on / 依赖: e.compl
-/
lemma compl_def [Compl β] (a : α) :
    letI := e.compl
    aᶜ = e.symm (e a)ᶜ := rfl

/--
Definition of `sdiff` / `sdiff` 的定义

English:
abbreviation sdiff
  signature: [SDiff β]
  body: e.symm (e a \ e b)

中文:
缩写 sdiff
  签名: [SDiff β]
  定义体: e.symm (e a \ e b)
-/
protected abbrev sdiff [SDiff β] : SDiff α where
  sdiff a b := e.symm (e a \ e b)

/--
lemma `sdiff_def` / 引理 `sdiff_def`

English:
lemma sdiff_def
  given: [SDiff β] (a b : α)
  proof: e.sdiff
    a \ b = e.symm (e a \ e b) := rfl

中文:
引理 sdiff_def
  条件: [SDiff β] (a b : α)
  证明: e.sdiff
    a \ b = e.symm (e a \ e b) := rfl

Depends on / 依赖: e.sdiff
-/
lemma sdiff_def [SDiff β] (a b : α) :
    letI := e.sdiff
    a \ b = e.symm (e a \ e b) := rfl

/--
Definition of `himp` / `himp` 的定义

English:
abbreviation himp
  signature: [HImp β]
  body: e.symm (e a ⇨ e b)

中文:
缩写 himp
  签名: [HImp β]
  定义体: e.symm (e a ⇨ e b)
-/
protected abbrev himp [HImp β] : HImp α where
  himp a b := e.symm (e a ⇨ e b)

/--
lemma `himp_def` / 引理 `himp_def`

English:
lemma himp_def
  given: [HImp β] (a b : α)
  proof: e.himp
    a ⇨ b = e.symm (e a ⇨ e b) := rfl

中文:
引理 himp_def
  条件: [HImp β] (a b : α)
  证明: e.himp
    a ⇨ b = e.symm (e a ⇨ e b) := rfl

Depends on / 依赖: e.himp
-/
lemma himp_def [HImp β] (a b : α) :
    letI := e.himp
    a ⇨ b = e.symm (e a ⇨ e b) := rfl

/--
Definition of `hnot` / `hnot` 的定义

English:
abbreviation hnot
  signature: [HNot β]
  body: e.symm (￢e a)

中文:
缩写 hnot
  签名: [HNot β]
  定义体: e.symm (￢e a)
-/
protected abbrev hnot [HNot β] : HNot α where
  hnot a := e.symm (￢e a)

/--
lemma `hnot_def` / 引理 `hnot_def`

English:
lemma hnot_def
  given: [HNot β] (a : α)
  proof: e.hnot
    ￢a = e.symm (￢e a) := rfl

中文:
引理 hnot_def
  条件: [HNot β] (a : α)
  证明: e.hnot
    ￢a = e.symm (￢e a) := rfl

Depends on / 依赖: e.hnot
-/
lemma hnot_def [HNot β] (a : α) :
    letI := e.hnot
    ￢a = e.symm (￢e a) := rfl

end Equiv
