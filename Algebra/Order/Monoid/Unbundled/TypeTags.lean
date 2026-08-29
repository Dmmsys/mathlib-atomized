/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Order.BoundedOrder.Basic

/-! # Ordered monoid structures on `Multiplicative α` and `Additive α`. -/

public section

variable {α : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: α] : LE (Multiplicative α)
  body: inferInstanceAs LE α

中文:
实例 [LE
  签名: α] : LE (Multiplicative α)
  定义体: inferInstanceAs LE α
-/
instance [LE α] : LE (Multiplicative α) :=
inferInstanceAs LE α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: α] : LE (Additive α)
  body: inferInstanceAs LE α

中文:
实例 [LE
  签名: α] : LE (Additive α)
  定义体: inferInstanceAs LE α
-/
instance [LE α] : LE (Additive α) :=
inferInstanceAs LE α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: α] : LT (Multiplicative α)
  body: inferInstanceAs LT α

中文:
实例 [LT
  签名: α] : LT (Multiplicative α)
  定义体: inferInstanceAs LT α
-/
instance [LT α] : LT (Multiplicative α) :=
inferInstanceAs LT α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: α] : LT (Additive α)
  body: inferInstanceAs LT α

中文:
实例 [LT
  签名: α] : LT (Additive α)
  定义体: inferInstanceAs LT α
-/
instance [LT α] : LT (Additive α) :=
inferInstanceAs LT α

/--
Instance `Multiplicative.preorder` / 实例 `Multiplicative.preorder`

English:
instance Multiplicative.preorder
  signature: [Preorder α]
  body: inferInstanceAs Preorder α

中文:
实例 Multiplicative.preorder
  签名: [Preorder α]
  定义体: inferInstanceAs Preorder α

Depends on / 依赖: Preorder
-/
instance Multiplicative.preorder [Preorder α] : Preorder (Multiplicative α) :=
inferInstanceAs Preorder α

/--
Instance `Additive.preorder` / 实例 `Additive.preorder`

English:
instance Additive.preorder
  signature: [Preorder α]
  body: inferInstanceAs Preorder α

中文:
实例 Additive.preorder
  签名: [Preorder α]
  定义体: inferInstanceAs Preorder α

Depends on / 依赖: Preorder
-/
instance Additive.preorder [Preorder α] : Preorder (Additive α) :=
inferInstanceAs Preorder α

/--
Instance `Multiplicative.partialOrder` / 实例 `Multiplicative.partialOrder`

English:
instance Multiplicative.partialOrder
  signature: [PartialOrder α]
  body: inferInstanceAs PartialOrder α

中文:
实例 Multiplicative.partialOrder
  签名: [PartialOrder α]
  定义体: inferInstanceAs PartialOrder α

Depends on / 依赖: PartialOrder
-/
instance Multiplicative.partialOrder [PartialOrder α] : PartialOrder (Multiplicative α) :=
inferInstanceAs PartialOrder α

/--
Instance `Additive.partialOrder` / 实例 `Additive.partialOrder`

English:
instance Additive.partialOrder
  signature: [PartialOrder α]
  body: inferInstanceAs PartialOrder α

中文:
实例 Additive.partialOrder
  签名: [PartialOrder α]
  定义体: inferInstanceAs PartialOrder α

Depends on / 依赖: PartialOrder
-/
instance Additive.partialOrder [PartialOrder α] : PartialOrder (Additive α) :=
inferInstanceAs PartialOrder α

/--
Instance `Multiplicative.linearOrder` / 实例 `Multiplicative.linearOrder`

English:
instance Multiplicative.linearOrder
  signature: [LinearOrder α]
  body: inferInstanceAs LinearOrder α

中文:
实例 Multiplicative.linearOrder
  签名: [LinearOrder α]
  定义体: inferInstanceAs LinearOrder α

Depends on / 依赖: LinearOrder
-/
instance Multiplicative.linearOrder [LinearOrder α] : LinearOrder (Multiplicative α) :=
inferInstanceAs LinearOrder α

/--
Instance `Additive.linearOrder` / 实例 `Additive.linearOrder`

English:
instance Additive.linearOrder
  signature: [LinearOrder α]
  body: inferInstanceAs LinearOrder α

中文:
实例 Additive.linearOrder
  签名: [LinearOrder α]
  定义体: inferInstanceAs LinearOrder α

Depends on / 依赖: LinearOrder
-/
instance Additive.linearOrder [LinearOrder α] : LinearOrder (Additive α) :=
inferInstanceAs LinearOrder α

/--
Instance `Multiplicative.orderBot` / 实例 `Multiplicative.orderBot`

English:
instance Multiplicative.orderBot
  signature: [LE α] [OrderBot α]
  body: inferInstanceAs OrderBot α

中文:
实例 Multiplicative.orderBot
  签名: [LE α] [OrderBot α]
  定义体: inferInstanceAs OrderBot α

Depends on / 依赖: OrderBot
-/
instance Multiplicative.orderBot [LE α] [OrderBot α] : OrderBot (Multiplicative α) :=
inferInstanceAs OrderBot α

/--
Instance `Additive.orderBot` / 实例 `Additive.orderBot`

English:
instance Additive.orderBot
  signature: [LE α] [OrderBot α]
  body: inferInstanceAs OrderBot α

中文:
实例 Additive.orderBot
  签名: [LE α] [OrderBot α]
  定义体: inferInstanceAs OrderBot α

Depends on / 依赖: OrderBot
-/
instance Additive.orderBot [LE α] [OrderBot α] : OrderBot (Additive α) :=
inferInstanceAs OrderBot α

/--
Instance `Multiplicative.orderTop` / 实例 `Multiplicative.orderTop`

English:
instance Multiplicative.orderTop
  signature: [LE α] [OrderTop α]
  body: inferInstanceAs OrderTop α

中文:
实例 Multiplicative.orderTop
  签名: [LE α] [OrderTop α]
  定义体: inferInstanceAs OrderTop α

Depends on / 依赖: OrderTop
-/
instance Multiplicative.orderTop [LE α] [OrderTop α] : OrderTop (Multiplicative α) :=
inferInstanceAs OrderTop α

/--
Instance `Additive.orderTop` / 实例 `Additive.orderTop`

English:
instance Additive.orderTop
  signature: [LE α] [OrderTop α]
  body: inferInstanceAs OrderTop α

中文:
实例 Additive.orderTop
  签名: [LE α] [OrderTop α]
  定义体: inferInstanceAs OrderTop α

Depends on / 依赖: OrderTop
-/
instance Additive.orderTop [LE α] [OrderTop α] : OrderTop (Additive α) :=
inferInstanceAs OrderTop α

/--
Instance `Multiplicative.boundedOrder` / 实例 `Multiplicative.boundedOrder`

English:
instance Multiplicative.boundedOrder
  signature: [LE α] [BoundedOrder α]
  body: inferInstanceAs BoundedOrder α

中文:
实例 Multiplicative.boundedOrder
  签名: [LE α] [BoundedOrder α]
  定义体: inferInstanceAs BoundedOrder α

Depends on / 依赖: BoundedOrder
-/
instance Multiplicative.boundedOrder [LE α] [BoundedOrder α] : BoundedOrder (Multiplicative α) :=
inferInstanceAs BoundedOrder α

/--
Instance `Additive.boundedOrder` / 实例 `Additive.boundedOrder`

English:
instance Additive.boundedOrder
  signature: [LE α] [BoundedOrder α]
  body: inferInstanceAs BoundedOrder α

中文:
实例 Additive.boundedOrder
  签名: [LE α] [BoundedOrder α]
  定义体: inferInstanceAs BoundedOrder α

Depends on / 依赖: BoundedOrder
-/
instance Additive.boundedOrder [LE α] [BoundedOrder α] : BoundedOrder (Additive α) :=
inferInstanceAs BoundedOrder α

/--
Instance `Multiplicative.existsMulOfLe` / 实例 `Multiplicative.existsMulOfLe`

English:
instance Multiplicative.existsMulOfLe
  signature: [Add α] [LE α] [ExistsAddOfLE α]
  body: ⟨@exists_add_of_le α _ _ _⟩

中文:
实例 Multiplicative.existsMulOfLe
  签名: [Add α] [LE α] [ExistsAddOfLE α]
  定义体: ⟨@exists_add_of_le α _ _ _⟩

Depends on / 依赖: exists_add_of_le
-/
instance Multiplicative.existsMulOfLe [Add α] [LE α] [ExistsAddOfLE α] :
    ExistsMulOfLE (Multiplicative α) :=
  ⟨@exists_add_of_le α _ _ _⟩

/--
Instance `Additive.existsAddOfLe` / 实例 `Additive.existsAddOfLe`

English:
instance Additive.existsAddOfLe
  signature: [Mul α] [LE α] [ExistsMulOfLE α]
  body: ⟨@exists_mul_of_le α _ _ _⟩

中文:
实例 Additive.existsAddOfLe
  签名: [Mul α] [LE α] [ExistsMulOfLE α]
  定义体: ⟨@exists_mul_of_le α _ _ _⟩

Depends on / 依赖: exists_mul_of_le
-/
instance Additive.existsAddOfLe [Mul α] [LE α] [ExistsMulOfLE α] : ExistsAddOfLE (Additive α) :=
  ⟨@exists_mul_of_le α _ _ _⟩

namespace Additive
section Preorder
variable [Preorder α]

@[simp]
/--
theorem `ofMul_le` / 定理 `ofMul_le`

English:
theorem ofMul_le
  given: {a b : α}
  statement: ofMul a <= ofMul b ↔ a <= b
  proof: Iff.rfl

@[simp]

中文:
定理 ofMul_le
  条件: {a b : α}
  结论: ofMul a <= ofMul b ↔ a <= b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem ofMul_le {a b : α} : ofMul a <= ofMul b ↔ a <= b :=
  Iff.rfl

@[simp]
/--
theorem `ofMul_lt` / 定理 `ofMul_lt`

English:
theorem ofMul_lt
  given: {a b : α}
  statement: ofMul a < ofMul b ↔ a < b
  proof: Iff.rfl

@[simp]

中文:
定理 ofMul_lt
  条件: {a b : α}
  结论: ofMul a < ofMul b ↔ a < b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem ofMul_lt {a b : α} : ofMul a < ofMul b ↔ a < b :=
  Iff.rfl

@[simp]
/--
theorem `toMul_le` / 定理 `toMul_le`

English:
theorem toMul_le
  given: {a b : Additive α}
  statement: a.toMul <= b.toMul ↔ a <= b
  proof: Iff.rfl

@[simp]

中文:
定理 toMul_le
  条件: {a b : Additive α}
  结论: a.toMul <= b.toMul ↔ a <= b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem toMul_le {a b : Additive α} : a.toMul <= b.toMul ↔ a <= b :=
  Iff.rfl

@[simp]
/--
theorem `toMul_lt` / 定理 `toMul_lt`

English:
theorem toMul_lt
  given: {a b : Additive α}
  statement: a.toMul < b.toMul ↔ a < b
  proof: Iff.rfl

@[gcongr] alias ⟨_, toMul_mono⟩ := toMul_le
@[gcongr] alias ⟨_, ofMul_mono⟩ := ofMul_le
@[gcongr] alias ⟨_, toMul_strictMono⟩ := toMul_lt
@[gcongr] alias ⟨_, ofMul_strictMono⟩ := ofMul_lt

中文:
定理 toMul_lt
  条件: {a b : Additive α}
  结论: a.toMul < b.toMul ↔ a < b
  证明: Iff.rfl

@[gcongr] alias ⟨_, toMul_mono⟩ := toMul_le
@[gcongr] alias ⟨_, ofMul_mono⟩ := ofMul_le
@[gcongr] alias ⟨_, toMul_strictMono⟩ := toMul_lt
@[gcongr] alias ⟨_, ofMul_strictMono⟩ := ofMul_lt

Depends on / 依赖: Iff.rfl
-/
theorem toMul_lt {a b : Additive α} : a.toMul < b.toMul ↔ a < b :=
  Iff.rfl

@[gcongr] alias ⟨_, toMul_mono⟩ := toMul_le
@[gcongr] alias ⟨_, ofMul_mono⟩ := ofMul_le
@[gcongr] alias ⟨_, toMul_strictMono⟩ := toMul_lt
@[gcongr] alias ⟨_, ofMul_strictMono⟩ := ofMul_lt

end Preorder

section OrderTop
variable [LE α] [OrderTop α]

/--
lemma `ofMul_top` / 引理 `ofMul_top`

English:
lemma ofMul_top
  statement: ofMul (⊤ : α) = ⊤
  proof: rfl

中文:
引理 ofMul_top
  结论: ofMul (⊤ : α) = ⊤
  证明: rfl
-/
@[simp] lemma ofMul_top : ofMul (⊤ : α) = ⊤ := rfl
/--
lemma `toMul_top` / 引理 `toMul_top`

English:
lemma toMul_top
  statement: toMul ⊤ = (⊤ : α)
  proof: rfl

中文:
引理 toMul_top
  结论: toMul ⊤ = (⊤ : α)
  证明: rfl
-/
@[simp] lemma toMul_top : toMul ⊤ = (⊤ : α) := rfl

/--
lemma `ofMul_eq_top` / 引理 `ofMul_eq_top`

English:
lemma ofMul_eq_top
  given: {a : α}
  statement: ofMul a = ⊤ ↔ a = ⊤
  proof: .rfl

中文:
引理 ofMul_eq_top
  条件: {a : α}
  结论: ofMul a = ⊤ ↔ a = ⊤
  证明: .rfl
-/
@[simp] lemma ofMul_eq_top {a : α} : ofMul a = ⊤ ↔ a = ⊤ := .rfl
/--
lemma `toMul_eq_top` / 引理 `toMul_eq_top`

English:
lemma toMul_eq_top
  given: {a : Additive α}
  statement: toMul a = ⊤ ↔ a = ⊤
  proof: .rfl

中文:
引理 toMul_eq_top
  条件: {a : Additive α}
  结论: toMul a = ⊤ ↔ a = ⊤
  证明: .rfl
-/
@[simp] lemma toMul_eq_top {a : Additive α} : toMul a = ⊤ ↔ a = ⊤ := .rfl

end OrderTop

section OrderBot
variable [LE α] [OrderBot α]

/--
lemma `ofMul_bot` / 引理 `ofMul_bot`

English:
lemma ofMul_bot
  statement: ofMul (⊥ : α) = ⊥
  proof: rfl

中文:
引理 ofMul_bot
  结论: ofMul (⊥ : α) = ⊥
  证明: rfl
-/
@[simp] lemma ofMul_bot : ofMul (⊥ : α) = ⊥ := rfl
/--
lemma `toMul_bot` / 引理 `toMul_bot`

English:
lemma toMul_bot
  statement: toMul ⊥ = (⊥ : α)
  proof: rfl

中文:
引理 toMul_bot
  结论: toMul ⊥ = (⊥ : α)
  证明: rfl
-/
@[simp] lemma toMul_bot : toMul ⊥ = (⊥ : α) := rfl

/--
lemma `ofMul_eq_bot` / 引理 `ofMul_eq_bot`

English:
lemma ofMul_eq_bot
  given: {a : α}
  statement: ofMul a = ⊥ ↔ a = ⊥
  proof: .rfl

中文:
引理 ofMul_eq_bot
  条件: {a : α}
  结论: ofMul a = ⊥ ↔ a = ⊥
  证明: .rfl
-/
@[simp] lemma ofMul_eq_bot {a : α} : ofMul a = ⊥ ↔ a = ⊥ := .rfl
/--
lemma `toMul_eq_bot` / 引理 `toMul_eq_bot`

English:
lemma toMul_eq_bot
  given: {a : Additive α}
  statement: toMul a = ⊥ ↔ a = ⊥
  proof: .rfl

中文:
引理 toMul_eq_bot
  条件: {a : Additive α}
  结论: toMul a = ⊥ ↔ a = ⊥
  证明: .rfl
-/
@[simp] lemma toMul_eq_bot {a : Additive α} : toMul a = ⊥ ↔ a = ⊥ := .rfl

end OrderBot
end Additive

namespace Multiplicative
section Preorder
variable [Preorder α]

@[simp]
/--
theorem `ofAdd_le` / 定理 `ofAdd_le`

English:
theorem ofAdd_le
  given: {a b : α}
  statement: ofAdd a <= ofAdd b ↔ a <= b
  proof: Iff.rfl

@[simp]

中文:
定理 ofAdd_le
  条件: {a b : α}
  结论: ofAdd a <= ofAdd b ↔ a <= b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem ofAdd_le {a b : α} : ofAdd a <= ofAdd b ↔ a <= b :=
  Iff.rfl

@[simp]
/--
theorem `ofAdd_lt` / 定理 `ofAdd_lt`

English:
theorem ofAdd_lt
  given: {a b : α}
  statement: ofAdd a < ofAdd b ↔ a < b
  proof: Iff.rfl

@[simp]

中文:
定理 ofAdd_lt
  条件: {a b : α}
  结论: ofAdd a < ofAdd b ↔ a < b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem ofAdd_lt {a b : α} : ofAdd a < ofAdd b ↔ a < b :=
  Iff.rfl

@[simp]
/--
theorem `toAdd_le` / 定理 `toAdd_le`

English:
theorem toAdd_le
  given: {a b : Multiplicative α}
  statement: a.toAdd <= b.toAdd ↔ a <= b
  proof: Iff.rfl

@[simp]

中文:
定理 toAdd_le
  条件: {a b : Multiplicative α}
  结论: a.toAdd <= b.toAdd ↔ a <= b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem toAdd_le {a b : Multiplicative α} : a.toAdd <= b.toAdd ↔ a <= b :=
  Iff.rfl

@[simp]
/--
theorem `toAdd_lt` / 定理 `toAdd_lt`

English:
theorem toAdd_lt
  given: {a b : Multiplicative α}
  statement: a.toAdd < b.toAdd ↔ a < b
  proof: Iff.rfl

@[gcongr] alias ⟨_, toAdd_mono⟩ := toAdd_le
@[gcongr] alias ⟨_, ofAdd_mono⟩ := ofAdd_le
@[gcongr] alias ⟨_, toAdd_strictMono⟩ := toAdd_lt
@[gcongr] alias ⟨_, ofAdd_strictMono⟩ := ofAdd_lt

中文:
定理 toAdd_lt
  条件: {a b : Multiplicative α}
  结论: a.toAdd < b.toAdd ↔ a < b
  证明: Iff.rfl

@[gcongr] alias ⟨_, toAdd_mono⟩ := toAdd_le
@[gcongr] alias ⟨_, ofAdd_mono⟩ := ofAdd_le
@[gcongr] alias ⟨_, toAdd_strictMono⟩ := toAdd_lt
@[gcongr] alias ⟨_, ofAdd_strictMono⟩ := ofAdd_lt

Depends on / 依赖: Iff.rfl
-/
theorem toAdd_lt {a b : Multiplicative α} : a.toAdd < b.toAdd ↔ a < b :=
  Iff.rfl

@[gcongr] alias ⟨_, toAdd_mono⟩ := toAdd_le
@[gcongr] alias ⟨_, ofAdd_mono⟩ := ofAdd_le
@[gcongr] alias ⟨_, toAdd_strictMono⟩ := toAdd_lt
@[gcongr] alias ⟨_, ofAdd_strictMono⟩ := ofAdd_lt

end Preorder

section OrderTop
variable [LE α] [OrderTop α]

/--
lemma `ofAdd_top` / 引理 `ofAdd_top`

English:
lemma ofAdd_top
  statement: ofAdd (⊤ : α) = ⊤
  proof: rfl

中文:
引理 ofAdd_top
  结论: ofAdd (⊤ : α) = ⊤
  证明: rfl
-/
@[simp] lemma ofAdd_top : ofAdd (⊤ : α) = ⊤ := rfl
/--
lemma `toAdd_top` / 引理 `toAdd_top`

English:
lemma toAdd_top
  statement: toAdd ⊤ = (⊤ : α)
  proof: rfl

中文:
引理 toAdd_top
  结论: toAdd ⊤ = (⊤ : α)
  证明: rfl
-/
@[simp] lemma toAdd_top : toAdd ⊤ = (⊤ : α) := rfl

/--
lemma `ofAdd_eq_top` / 引理 `ofAdd_eq_top`

English:
lemma ofAdd_eq_top
  given: {a : α}
  statement: ofAdd a = ⊤ ↔ a = ⊤
  proof: .rfl

中文:
引理 ofAdd_eq_top
  条件: {a : α}
  结论: ofAdd a = ⊤ ↔ a = ⊤
  证明: .rfl
-/
@[simp] lemma ofAdd_eq_top {a : α} : ofAdd a = ⊤ ↔ a = ⊤ := .rfl
/--
lemma `toAdd_eq_top` / 引理 `toAdd_eq_top`

English:
lemma toAdd_eq_top
  given: {a : Multiplicative α}
  statement: toAdd a = ⊤ ↔ a = ⊤
  proof: .rfl

中文:
引理 toAdd_eq_top
  条件: {a : Multiplicative α}
  结论: toAdd a = ⊤ ↔ a = ⊤
  证明: .rfl
-/
@[simp] lemma toAdd_eq_top {a : Multiplicative α} : toAdd a = ⊤ ↔ a = ⊤ := .rfl

end OrderTop

section OrderBot
variable [LE α] [OrderBot α]

/--
lemma `ofAdd_bot` / 引理 `ofAdd_bot`

English:
lemma ofAdd_bot
  statement: ofAdd (⊥ : α) = ⊥
  proof: rfl

中文:
引理 ofAdd_bot
  结论: ofAdd (⊥ : α) = ⊥
  证明: rfl
-/
@[simp] lemma ofAdd_bot : ofAdd (⊥ : α) = ⊥ := rfl
/--
lemma `toAdd_bot` / 引理 `toAdd_bot`

English:
lemma toAdd_bot
  statement: toAdd ⊥ = (⊥ : α)
  proof: rfl

中文:
引理 toAdd_bot
  结论: toAdd ⊥ = (⊥ : α)
  证明: rfl
-/
@[simp] lemma toAdd_bot : toAdd ⊥ = (⊥ : α) := rfl

/--
lemma `ofAdd_eq_bot` / 引理 `ofAdd_eq_bot`

English:
lemma ofAdd_eq_bot
  given: {a : α}
  statement: ofAdd a = ⊥ ↔ a = ⊥
  proof: .rfl

中文:
引理 ofAdd_eq_bot
  条件: {a : α}
  结论: ofAdd a = ⊥ ↔ a = ⊥
  证明: .rfl
-/
@[simp] lemma ofAdd_eq_bot {a : α} : ofAdd a = ⊥ ↔ a = ⊥ := .rfl
/--
lemma `toAdd_eq_bot` / 引理 `toAdd_eq_bot`

English:
lemma toAdd_eq_bot
  given: {a : Multiplicative α}
  statement: toAdd a = ⊥ ↔ a = ⊥
  proof: .rfl

中文:
引理 toAdd_eq_bot
  条件: {a : Multiplicative α}
  结论: toAdd a = ⊥ ↔ a = ⊥
  证明: .rfl
-/
@[simp] lemma toAdd_eq_bot {a : Multiplicative α} : toAdd a = ⊥ ↔ a = ⊥ := .rfl

end OrderBot

end Multiplicative
