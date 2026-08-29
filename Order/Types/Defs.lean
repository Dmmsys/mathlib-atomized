/-
Copyright (c) 2025 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy
-/
module

public import Mathlib.Order.Hom.Basic

/-!
# Order types

Order types are defined as the quotient of linear orders under order isomorphism.
They are preordered by order embeddings.

## Main definitions

* `OrderType`: the type of order types (in a given universe)
* `OrderType.type α`: given a type `α` with a linear order, this is the corresponding OrderType,

A preorder with a bottom element is registered on order types, where `⊥` is
`0`, the order type corresponding to the empty type.

## Notation

The following are notations in the `OrderType` namespace:

* `ω` is a notation for the order type of `ℕ` with its natural order.

## References

* <https://en.wikipedia.org/wiki/Order_type>
* [Dauben, J. W., Georg Cantor: His Mathematics and Philosophy of the Infinite. Princeton,
  NJ: Princeton University Press, 1990.][dauben_1990]
* [Enderton, Herbert B., Elements of Set Theory. United Kingdom: Academic Press,
  1977.][enderton_1977]

## Tags

order type, order isomorphism, linear order
-/

public noncomputable section

open Function Set Equiv Order

universe u v
variable {α β : Type u} [LinearOrder α] [LinearOrder β] {δ : Sort v}

/-- Equivalence relation on linear orders on arbitrary types in universe `u`, given by order
isomorphism. -/
@[instance_reducible]
/--
Definition of `OrderType.instSetoid` / `OrderType.instSetoid` 的定义

English:
definition OrderType.instSetoid
  signature: : Setoid LinOrd where
  body: fun lin_ord₁ lin_ord₂ => Nonempty (lin_ord₁ ≃o lin_ord₂)
  iseqv := ⟨fun _ => ⟨.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

中文:
定义 序型.instSetoid
  签名: : 集合等价关系 线性序 where
  定义体: fun lin_ord₁ lin_ord₂ => Nonempty (lin_ord₁ ≃o lin_ord₂)
  iseqv := ⟨fun _ => ⟨.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

Depends on / 依赖: Nonempty
-/
def OrderType.instSetoid : Setoid LinOrd where
  r := fun lin_ord₁ lin_ord₂ => Nonempty (lin_ord₁ ≃o lin_ord₂)
  iseqv := ⟨fun _ => ⟨.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

/-- `OrderType.{u}` is the type of linear orders in `Type u`, up to order isomorphism. -/
@[pp_with_univ]
/--
Definition of `OrderType` / `OrderType` 的定义

English:
definition OrderType
  signature: : Type (u + 1)
  body: Quotient OrderType.instSetoid

中文:
定义 序型
  签名: : 类型 (u + 1)
  定义体: Quotient OrderType.instSetoid

Depends on / 依赖: OrderType, OrderType.instSetoid, Quotient, instSetoid
-/
def OrderType : Type (u + 1) :=
  Quotient OrderType.instSetoid

namespace OrderType

/--
Definition of `ToType` / `ToType` 的定义

English:
definition ToType
  signature: (o : OrderType)
  body: o.out.carrier

中文:
定义 ToType
  签名: (o : 序型)
  定义体: o.out.carrier

Depends on / 依赖: carrier, o.out.carrier
-/
def ToType (o : OrderType) : Type u :=
  o.out.carrier

/-- The instance for some arbitrary linear order on `Type u` , order isomorphic within
order type `o`. -/
@[no_expose]
instance (o : OrderType) : LinearOrder o.ToType :=
  o.out.str

/-! ### Basic properties of the order type -/

/--
Definition of `type` / `type` 的定义

English:
definition type
  signature: (α : Type u) [LinearOrder α]
  body: ⟦⟨α⟩⟧

中文:
定义 type
  签名: (α : 类型u) [线性序 α]
  定义体: ⟦⟨α⟩⟧
-/
def type (α : Type u) [LinearOrder α] : OrderType :=
  ⟦⟨α⟩⟧

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero OrderType
  body: type PEmpty

中文:
实例 :
  签名: 零 序型
  定义体: type PEmpty

Depends on / 依赖: PEmpty
-/
instance : Zero OrderType where
  zero := type PEmpty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited OrderType
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 序型
  定义体: ⟨0⟩
-/
instance : Inhabited OrderType :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One OrderType
  body: type PUnit

@[simp]

中文:
实例 :
  签名: 幺 序型
  定义体: type PUnit

@[simp]
-/
instance : One OrderType where
  one := type PUnit

@[simp]
/--
theorem `type_toType` / 定理 `type_toType`

English:
theorem type_toType
  given: (o : OrderType)
  statement: type o.ToType = o
  proof: surjInv_eq Quot.exists_rep o

中文:
定理 type_toType
  条件: (o : 序型)
  结论: type o.ToType = o
  证明: surjInv_eq Quot.exists_rep o

Depends on / 依赖: Quot.exists_rep, exists_rep, surjInv_eq
-/
theorem type_toType (o : OrderType) : type o.ToType = o := surjInv_eq Quot.exists_rep o

/--
theorem `type_eq_type` / 定理 `type_eq_type`

English:
theorem type_eq_type
  statement: type α = type β ↔ Nonempty (α ≃o β)
  proof: Quotient.eq'

中文:
定理 type_eq_type
  结论: type α = type β ↔ 非空 (α ≃o β)
  证明: Quotient.eq'

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem type_eq_type : type α = type β ↔ Nonempty (α ≃o β) :=
  Quotient.eq'

/--
theorem `type_congr` / 定理 `type_congr`

English:
theorem type_congr
  given: (h : α ≃o β)
  statement: type α = type β
  proof: type_eq_type.2 ⟨h⟩

alias _root_.OrderIso.type_congr := type_congr

@[simp]

中文:
定理 type_congr
  条件: (h : α ≃o β)
  结论: type α = type β
  证明: type_eq_type.2 ⟨h⟩

alias _root_.OrderIso.type_congr := type_congr

@[simp]

Depends on / 依赖: type_eq_type
-/
theorem type_congr (h : α ≃o β) : type α = type β :=
  type_eq_type.2 ⟨h⟩

alias _root_.OrderIso.type_congr := type_congr

@[simp]
/--
theorem `type_of_isEmpty` / 定理 `type_of_isEmpty`

English:
theorem type_of_isEmpty
  given: [IsEmpty α]
  statement: type α = 0
  proof: type_congr .ofIsEmpty α PEmpty

中文:
定理 type_of_isEmpty
  条件: [是空 α]
  结论: type α = 0
  证明: type_congr .ofIsEmpty α PEmpty

Depends on / 依赖: PEmpty, ofIsEmpty, type_congr
-/
theorem type_of_isEmpty [IsEmpty α] : type α = 0 :=
type_congr .ofIsEmpty α PEmpty

/--
theorem `type_eq_zero` / 定理 `type_eq_zero`

English:
theorem type_eq_zero
  statement: type α = 0 ↔ IsEmpty α where
  proof: let ⟨s⟩ := type_eq_type.1 h
    s.toEquiv.isEmpty
  mpr := @type_of_isEmpty α _

中文:
定理 type_eq_zero
  结论: type α = 0 ↔ 是空 α where
  证明: let ⟨s⟩ := type_eq_type.1 h
    s.toEquiv.isEmpty
  mpr := @type_of_isEmpty α _

Depends on / 依赖: isEmpty, s.toEquiv.isEmpty, toEquiv, type_eq_type, type_of_isEmpty
-/
theorem type_eq_zero : type α = 0 ↔ IsEmpty α where
  mp h :=
    let ⟨s⟩ := type_eq_type.1 h
    s.toEquiv.isEmpty
  mpr := @type_of_isEmpty α _

/--
theorem `type_ne_zero_iff` / 定理 `type_ne_zero_iff`

English:
theorem type_ne_zero_iff
  statement: type α != 0 ↔ Nonempty α
  proof: by simp [type_eq_zero]

@[simp]

中文:
定理 type_ne_zero_iff
  结论: type α != 0 ↔ 非空 α
  证明: by simp [type_eq_zero]

@[simp]

Depends on / 依赖: type_eq_zero
-/
theorem type_ne_zero_iff : type α != 0 ↔ Nonempty α := by simp [type_eq_zero]

@[simp]
/--
theorem `type_ne_zero` / 定理 `type_ne_zero`

English:
theorem type_ne_zero
  given: [h : Nonempty α]
  statement: type α != 0
  proof: type_ne_zero_iff.2 h

@[simp]

中文:
定理 type_ne_zero
  条件: [h : 非空 α]
  结论: type α != 0
  证明: type_ne_zero_iff.2 h

@[simp]

Depends on / 依赖: type_ne_zero_iff
-/
theorem type_ne_zero [h : Nonempty α] : type α != 0 :=
  type_ne_zero_iff.2 h

@[simp]
/--
theorem `type_of_unique` / 定理 `type_of_unique`

English:
theorem type_of_unique
  given: [Nonempty α] [Subsingleton α]
  statement: type α = 1
  proof: by
  cases nonempty_unique α
  exact (OrderIso.ofUnique α _).type_congr

中文:
定理 type_of_unique
  条件: [非空 α] [子单例 α]
  结论: type α = 1
  证明: by
  cases nonempty_unique α
  exact (OrderIso.ofUnique α _).type_congr

Depends on / 依赖: OrderIso, OrderIso.ofUnique, nonempty_unique, ofUnique, type_congr
-/
theorem type_of_unique [Nonempty α] [Subsingleton α] : type α = 1 := by
  cases nonempty_unique α
  exact (OrderIso.ofUnique α _).type_congr

/--
theorem `type_eq_one` / 定理 `type_eq_one`

English:
theorem type_eq_one
  statement: type α = 1 ↔ Nonempty (Unique α)
  proof: ⟨fun h => let ⟨s⟩ := type_eq_type.1 h; ⟨s.toEquiv.unique⟩,
    fun ⟨_⟩ => type_of_unique⟩

@[simp]

中文:
定理 type_eq_one
  结论: type α = 1 ↔ 非空 (唯一 α)
  证明: ⟨fun h => let ⟨s⟩ := type_eq_type.1 h; ⟨s.toEquiv.unique⟩,
    fun ⟨_⟩ => type_of_unique⟩

@[simp]

Depends on / 依赖: s.toEquiv.unique, toEquiv, type_eq_type, type_of_unique, unique
-/
theorem type_eq_one : type α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h => let ⟨s⟩ := type_eq_type.1 h; ⟨s.toEquiv.unique⟩,
    fun ⟨_⟩ => type_of_unique⟩

@[simp]
/--
theorem `isEmpty_toType_iff` / 定理 `isEmpty_toType_iff`

English:
theorem isEmpty_toType_iff
  given: {o : OrderType}
  statement: IsEmpty o.ToType ↔ o = 0
  proof: by
  rw [← @type_eq_zero o.ToType]; rw [type_toType]

@[simp]

中文:
定理 isEmpty_toType_iff
  条件: {o : 序型}
  结论: 是空 o.ToType ↔ o = 0
  证明: by
  rw [← @type_eq_zero o.ToType]; rw [type_toType]

@[simp]
-/
private theorem isEmpty_toType_iff {o : OrderType} : IsEmpty o.ToType ↔ o = 0 := by
  rw [← @type_eq_zero o.ToType]; rw [type_toType]

@[simp]
/--
theorem `nonempty_toType_iff` / 定理 `nonempty_toType_iff`

English:
theorem nonempty_toType_iff
  given: {o : OrderType}
  statement: Nonempty o.ToType ↔ o != 0
  proof: by
  rw [← @type_ne_zero_iff o.ToType]; rw [type_toType]

中文:
定理 nonempty_toType_iff
  条件: {o : 序型}
  结论: 非空 o.ToType ↔ o != 0
  证明: by
  rw [← @type_ne_zero_iff o.ToType]; rw [type_toType]
-/
private theorem nonempty_toType_iff {o : OrderType} : Nonempty o.ToType ↔ o != 0 := by
  rw [← @type_ne_zero_iff o.ToType]; rw [type_toType]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial OrderType.{u}
  body: ⟨⟨1, 0, type_ne_zero⟩⟩

中文:
实例 :
  签名: 非平凡 序型.{u}
  定义体: ⟨⟨1, 0, type_ne_zero⟩⟩

Depends on / 依赖: type_ne_zero
-/
instance : Nontrivial OrderType.{u} :=
  ⟨⟨1, 0, type_ne_zero⟩⟩

/-- `Quotient.inductionOn` specialized to `OrderType`. -/
@[elab_as_elim]
/--
theorem `inductionOn` / 定理 `inductionOn`

English:
theorem inductionOn
  statement: {C : OrderType -> Prop} (o : OrderType)
  proof: Quot.inductionOn o (fun α => H α)

中文:
定理 inductionOn
  结论: {C : 序型 -> 命题} (o : 序型)
  证明: Quot.inductionOn o (fun α => H α)

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem inductionOn {C : OrderType -> Prop} (o : OrderType)
    (H : forall α [LinearOrder α], C (type α)) : C o :=
  Quot.inductionOn o (fun α => H α)

/-- `Quotient.inductionOn₂` specialized to `OrderType`. -/
@[elab_as_elim]
/--
theorem `inductionOn₂` / 定理 `inductionOn₂`

English:
theorem inductionOn₂
  statement: {C : OrderType -> OrderType -> Prop} (o₁ o₂ : OrderType)
  proof: Quotient.inductionOn₂ o₁ o₂ fun α β => H α β

中文:
定理 inductionOn₂
  结论: {C : 序型 -> 序型 -> 命题} (o₁ o₂ : 序型)
  证明: Quotient.inductionOn₂ o₁ o₂ fun α β => H α β

Depends on / 依赖: Quotient, Quotient.inductionOn
-/
theorem inductionOn₂ {C : OrderType -> OrderType -> Prop} (o₁ o₂ : OrderType)
    (H : forall α [LinearOrder α] β [LinearOrder β], C (type α) (type β)) : C o₁ o₂ :=
  Quotient.inductionOn₂ o₁ o₂ fun α β => H α β

/-- `Quotient.inductionOn₃` specialized to `OrderType`. -/
@[elab_as_elim]
/--
theorem `inductionOn₃` / 定理 `inductionOn₃`

English:
theorem inductionOn₃
  statement: {C : OrderType -> OrderType -> OrderType -> Prop} (o₁ o₂ o₃ : OrderType)
  proof: Quotient.inductionOn₃ o₁ o₂ o₃ fun α β γ =>
    H α β γ

中文:
定理 inductionOn₃
  结论: {C : 序型 -> 序型 -> 序型 -> 命题} (o₁ o₂ o₃ : 序型)
  证明: Quotient.inductionOn₃ o₁ o₂ o₃ fun α β γ =>
    H α β γ

Depends on / 依赖: Quotient, Quotient.inductionOn
-/
theorem inductionOn₃ {C : OrderType -> OrderType -> OrderType -> Prop} (o₁ o₂ o₃ : OrderType)
    (H : forall α [LinearOrder α] β [LinearOrder β] γ [LinearOrder γ],
      C (type α) (type β) (type γ)) : C o₁ o₂ o₃ :=
  Quotient.inductionOn₃ o₁ o₂ o₃ fun α β γ =>
    H α β γ

/--
Definition of `liftOn` / `liftOn` 的定义

English:
definition liftOn
  signature: (o : OrderType) (f : forall (α) [LinearOrder α], δ)
  body: Quotient.liftOn o (fun w => f w)
    fun w₁ w₂ h => c w₁ w₂ (Quotient.sound h)

中文:
定义 liftOn
  签名: (o : 序型) (f : 对任意 (α) [线性序 α], δ)
  定义体: Quotient.liftOn o (fun w => f w)
    fun w₁ w₂ h => c w₁ w₂ (Quotient.sound h)

Depends on / 依赖: Quotient, Quotient.liftOn, Quotient.sound, liftOn
-/
def liftOn (o : OrderType) (f : forall (α) [LinearOrder α], δ)
    (c : forall (α) [LinearOrder α] (β) [LinearOrder β],
      type α = type β -> f α = f β) : δ :=
  Quotient.liftOn o (fun w => f w)
    fun w₁ w₂ h => c w₁ w₂ (Quotient.sound h)

/--
Definition of `liftOn₂` / `liftOn₂` 的定义

English:
definition liftOn₂
  signature: (o₁ o₂ : OrderType) (f : forall (α) [LinearOrder α] (β) [LinearOrder β], δ)
  body: Quotient.liftOn₂ o₁ o₂ (fun w v => f w v)
    fun w₁ w₂ v₁ v₂ hw hv => c w₁ w₂ v₁ v₂ (Quotient.sound hw) (Quotient.sound hv)

@[simp]

中文:
定义 liftOn₂
  签名: (o₁ o₂ : 序型) (f : 对任意 (α) [线性序 α] (β) [线性序 β], δ)
  定义体: Quotient.liftOn₂ o₁ o₂ (fun w v => f w v)
    fun w₁ w₂ v₁ v₂ hw hv => c w₁ w₂ v₁ v₂ (Quotient.sound hw) (Quotient.sound hv)

@[simp]

Depends on / 依赖: Quotient, Quotient.liftOn, Quotient.sound
-/
def liftOn₂ (o₁ o₂ : OrderType) (f : forall (α) [LinearOrder α] (β) [LinearOrder β], δ)
    (c : forall (α₁) [LinearOrder α₁] (β₁) [LinearOrder β₁] (α₂) [LinearOrder α₂] (β₂) [LinearOrder β₂],
      type α₁ = type α₂ -> type β₁ = type β₂ -> f α₁ β₁ = f α₂ β₂) : δ :=
  Quotient.liftOn₂ o₁ o₂ (fun w v => f w v)
    fun w₁ w₂ v₁ v₂ hw hv => c w₁ w₂ v₁ v₂ (Quotient.sound hw) (Quotient.sound hv)

@[simp]
/--
theorem `liftOn_type` / 定理 `liftOn_type`

English:
theorem liftOn_type
  statement: (f : forall (α) [LinearOrder α], δ)
  proof: by rfl

@[simp]

中文:
定理 liftOn_type
  结论: (f : 对任意 (α) [线性序 α], δ)
  证明: by rfl

@[simp]
-/
theorem liftOn_type (f : forall (α) [LinearOrder α], δ)
    (c : forall (α) [LinearOrder α] (β) [LinearOrder β],
      type α = type β -> f α = f β) {γ} [LinearOrder γ] :
    liftOn (type γ) f c = f γ := by rfl

@[simp]
/--
theorem `liftOn₂_type` / 定理 `liftOn₂_type`

English:
theorem liftOn₂_type
  statement: {α : Type u} {β : Type v} {δ : Type*} [LinearOrder α] [LinearOrder β]
  proof: by rfl

中文:
定理 liftOn₂_type
  结论: {α : 类型u} {β : 类型v} {δ : 类型} [线性序 α] [线性序 β]
  证明: by rfl
-/
theorem liftOn₂_type {α : Type u} {β : Type v} {δ : Type*} [LinearOrder α] [LinearOrder β]
     (f : forall (α) [LinearOrder α] (β) [LinearOrder β], δ)
     (c : forall (α₁) [LinearOrder α₁] (β₁) [LinearOrder β₁] (α₂) [LinearOrder α₂] (β₂) [LinearOrder β₂],
       type α₁ = type α₂ -> type β₁ = type β₂ -> f α₁ β₁ = f α₂ β₂) :
    liftOn₂ (type α) (type β) f c = f α β := by rfl

/-! ### The order on `OrderType` -/

/--
The order is defined so that `type α ≤ type β` iff there exists an order embedding `α ↪o β`.
-/
@[no_expose]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder OrderType
  body: Quotient.liftOn₂ o₁ o₂ (fun r s => Nonempty (r ↪o s))
    fun _ _ _ _ ⟨f⟩ ⟨g⟩ => propext
      ⟨fun ⟨h⟩ => ⟨(f.symm.toOrderEmbedding.trans h).trans g.toOrderEmbedding⟩, fun ⟨h⟩ =>
        ⟨(f.toOrderEmbedding.trans h).trans g.symm.toOrderEmbedding⟩⟩
  le_refl o := inductionOn o fun α _ => ⟨(OrderIso.refl _).toOrderEmbedding⟩
  le_trans o₁ o₂ o₃ := inductionOn₃ o₁ o₂ o₃ fun _ _ _ _ _ _ ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩

中文:
实例 :
  签名: 预序 序型
  定义体: Quotient.liftOn₂ o₁ o₂ (fun r s => Nonempty (r ↪o s))
    fun _ _ _ _ ⟨f⟩ ⟨g⟩ => propext
      ⟨fun ⟨h⟩ => ⟨(f.symm.toOrderEmbedding.trans h).trans g.toOrderEmbedding⟩, fun ⟨h⟩ =>
        ⟨(f.toOrderEmbedding.trans h).trans g.symm.toOrderEmbedding⟩⟩
  le_refl o := inductionOn o fun α _ => ⟨(OrderIso.refl _).toOrderEmbedding⟩
  le_trans o₁ o₂ o₃ := inductionOn₃ o₁ o₂ o₃ fun _ _ _ _ _ _ ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩

Depends on / 依赖: Nonempty, OrderIso, OrderIso.refl, Quotient, Quotient.liftOn, f.symm.toOrderEmbedding.trans, f.toOrderEmbedding.trans, f.trans, g.symm.toOrderEmbedding, g.toOrderEmbedding, inductionOn, le_refl, le_trans, propext, toOrderEmbedding
-/
instance : Preorder OrderType where
  le o₁ o₂ :=
    Quotient.liftOn₂ o₁ o₂ (fun r s => Nonempty (r ↪o s))
    fun _ _ _ _ ⟨f⟩ ⟨g⟩ => propext
      ⟨fun ⟨h⟩ => ⟨(f.symm.toOrderEmbedding.trans h).trans g.toOrderEmbedding⟩, fun ⟨h⟩ =>
        ⟨(f.toOrderEmbedding.trans h).trans g.symm.toOrderEmbedding⟩⟩
  le_refl o := inductionOn o fun α _ => ⟨(OrderIso.refl _).toOrderEmbedding⟩
  le_trans o₁ o₂ o₃ := inductionOn₃ o₁ o₂ o₃ fun _ _ _ _ _ _ ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NeZero (1 : OrderType)
  body: ⟨type_ne_zero⟩

中文:
实例 :
  签名: NeZero (1 : 序型)
  定义体: ⟨type_ne_zero⟩

Depends on / 依赖: type_ne_zero
-/
instance : NeZero (1 : OrderType) :=
  ⟨type_ne_zero⟩

/--
theorem `type_le_type_iff` / 定理 `type_le_type_iff`

English:
theorem type_le_type_iff
  statement: type α <= type β ↔ Nonempty (α ↪o β)
  proof: .rfl

中文:
定理 type_le_type_iff
  结论: type α <= type β ↔ 非空 (α ↪o β)
  证明: .rfl
-/
theorem type_le_type_iff : type α <= type β ↔ Nonempty (α ↪o β) :=
  .rfl

/--
theorem `type_le_type` / 定理 `type_le_type`

English:
theorem type_le_type
  given: (h : α ↪o β)
  statement: type α <= type β
  proof: ⟨h⟩

中文:
定理 type_le_type
  条件: (h : α ↪o β)
  结论: type α <= type β
  证明: ⟨h⟩
-/
theorem type_le_type (h : α ↪o β) : type α <= type β :=
  ⟨h⟩

/--
theorem `type_lt_type` / 定理 `type_lt_type`

English:
theorem type_lt_type
  given: (h : α ↪o β) (hne : IsEmpty (β ↪o α))
  statement: type α < type β
  proof: ⟨⟨h⟩, not_nonempty_iff.mpr hne⟩

alias _root_.OrderEmbedding.type_le_type := type_le_type

@[simp]

中文:
定理 type_lt_type
  条件: (h : α ↪o β) (hne : 是空 (β ↪o α))
  结论: type α < type β
  证明: ⟨⟨h⟩, not_nonempty_iff.mpr hne⟩

alias _root_.OrderEmbedding.type_le_type := type_le_type

@[simp]

Depends on / 依赖: not_nonempty_iff, not_nonempty_iff.mpr
-/
theorem type_lt_type (h : α ↪o β) (hne : IsEmpty (β ↪o α)) : type α < type β :=
  ⟨⟨h⟩, not_nonempty_iff.mpr hne⟩

alias _root_.OrderEmbedding.type_le_type := type_le_type

@[simp]
/--
theorem `zero_le` / 定理 `zero_le`

English:
theorem zero_le
  given: (o : OrderType)
  statement: 0 <= o
  proof: inductionOn o fun _ => OrderEmbedding.ofIsEmpty.type_le_type

中文:
定理 zero_le
  条件: (o : 序型)
  结论: 0 <= o
  证明: inductionOn o fun _ => OrderEmbedding.ofIsEmpty.type_le_type
-/
protected theorem zero_le (o : OrderType) : 0 <= o :=
  inductionOn o fun _ => OrderEmbedding.ofIsEmpty.type_le_type

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot OrderType
  body: 0
  bot_le := OrderType.zero_le

@[simp]

中文:
实例 :
  签名: 有底序 序型
  定义体: 0
  bot_le := OrderType.zero_le

@[simp]
-/
instance : OrderBot OrderType where
  bot := 0
  bot_le := OrderType.zero_le

@[simp]
/--
theorem `bot_eq_zero` / 定理 `bot_eq_zero`

English:
theorem bot_eq_zero
  statement: (⊥ : OrderType) = 0
  proof: rfl

@[simp]

中文:
定理 bot_eq_zero
  结论: (⊥ : 序型) = 0
  证明: rfl

@[simp]
-/
theorem bot_eq_zero : (⊥ : OrderType) = 0 :=
  rfl

@[simp]
/--
theorem `not_lt_zero` / 定理 `not_lt_zero`

English:
theorem not_lt_zero
  given: {o : OrderType}
  statement: ¬o < 0
  proof: not_lt_bot

@[simp]

中文:
定理 not_lt_zero
  条件: {o : 序型}
  结论: ¬o < 0
  证明: not_lt_bot

@[simp]
-/
protected theorem not_lt_zero {o : OrderType} : ¬o < 0 :=
  not_lt_bot

@[simp]
/--
theorem `pos_iff_ne_zero` / 定理 `pos_iff_ne_zero`

English:
theorem pos_iff_ne_zero
  given: {o : OrderType}
  statement: 0 < o ↔ o != 0 where
  proof: ne_bot_of_gt
  mpr ho := by
    have := nonempty_toType_iff.2 ho
    rw [← type_toType o]
    exact ⟨⟨Function.Embedding.ofIsEmpty, nofun⟩, fun ⟨f⟩ => IsEmpty.elim inferInstance f.toFun⟩

中文:
定理 pos_iff_ne_zero
  条件: {o : 序型}
  结论: 0 < o ↔ o != 0 where
  证明: ne_bot_of_gt
  mpr ho := by
    have := nonempty_toType_iff.2 ho
    rw [← type_toType o]
    exact ⟨⟨Function.Embedding.ofIsEmpty, nofun⟩, fun ⟨f⟩ => IsEmpty.elim inferInstance f.toFun⟩

Depends on / 依赖: ne_bot_of_gt
-/
theorem pos_iff_ne_zero {o : OrderType} : 0 < o ↔ o != 0 where
  mp := ne_bot_of_gt
  mpr ho := by
    have := nonempty_toType_iff.2 ho
    rw [← type_toType o]
    exact ⟨⟨Function.Embedding.ofIsEmpty, nofun⟩, fun ⟨f⟩ => IsEmpty.elim inferInstance f.toFun⟩

/-- The universe lift operation on order types. You can specify the universes explicitly with
  `lift.{u, v} : OrderType.{v} → OrderType.{max v u}` -/
@[pp_with_univ]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (o : OrderType.{v})
  body: o.liftOn (fun α _ => type (ULift α)) fun _α _ _β _ e =>
    ((ULift.orderIso.trans (type_eq_type.mp e).some).trans ULift.orderIso.symm).type_congr

@[simp]

中文:
定义 lift
  签名: (o : 序型.{v})
  定义体: o.liftOn (fun α _ => type (ULift α)) fun _α _ _β _ e =>
    ((ULift.orderIso.trans (type_eq_type.mp e).some).trans ULift.orderIso.symm).type_congr

@[simp]

Depends on / 依赖: ULift.orderIso.symm, ULift.orderIso.trans, liftOn, o.liftOn, orderIso, type_congr, type_eq_type, type_eq_type.mp
-/
def lift (o : OrderType.{v}) : OrderType.{max v u} :=
  o.liftOn (fun α _ => type (ULift α)) fun _α _ _β _ e =>
    ((ULift.orderIso.trans (type_eq_type.mp e).some).trans ULift.orderIso.symm).type_congr

@[simp]
/--
theorem `type_ulift` / 定理 `type_ulift`

English:
theorem type_ulift
  statement: type (ULift.{v, u} α) = lift.{v} (type α)
  proof: (rfl)

中文:
定理 type_ulift
  结论: type (类型层提升.{v, u} α) = lift.{v} (type α)
  证明: (rfl)
-/
theorem type_ulift : type (ULift.{v, u} α) = lift.{v} (type α) := (rfl)

/--
theorem `lift_id'` / 定理 `lift_id'`

English:
theorem lift_id'
  given: (o : OrderType.{max u v})
  statement: lift.{u} o = o
  proof: inductionOn o fun _ => type_congr ULift.orderIso

中文:
定理 lift_id'
  条件: (o : 序型.{最大值 u v})
  结论: lift.{u} o = o
  证明: inductionOn o fun _ => type_congr ULift.orderIso

Depends on / 依赖: ULift.orderIso, inductionOn, orderIso, type_congr
-/
theorem lift_id' (o : OrderType.{max u v}) : lift.{u} o = o :=
  inductionOn o fun _ => type_congr ULift.orderIso

/-- An order type lifted to the same universe equals itself. -/
@[simp]
/--
theorem `lift_id` / 定理 `lift_id`

English:
theorem lift_id
  given: (o : OrderType)
  statement: lift.{u, u} o = o
  proof: lift_id'.{u, u} o

中文:
定理 lift_id
  条件: (o : 序型)
  结论: lift.{u, u} o = o
  证明: lift_id'.{u, u} o

Depends on / 依赖: lift_id
-/
theorem lift_id (o : OrderType) : lift.{u, u} o = o :=
  lift_id'.{u, u} o

/-- An order type lifted to the zero universe equals itself. -/
@[simp]
/--
theorem `lift_uzero` / 定理 `lift_uzero`

English:
theorem lift_uzero
  given: (o : OrderType.{u})
  statement: lift.{0} o = o
  proof: lift_id'.{0, u} o

@[simp]

中文:
定理 lift_uzero
  条件: (o : 序型.{u})
  结论: lift.{0} o = o
  证明: lift_id'.{0, u} o

@[simp]

Depends on / 依赖: lift_id
-/
theorem lift_uzero (o : OrderType.{u}) : lift.{0} o = o :=
  lift_id'.{0, u} o

@[simp]
/--
theorem `lift_lift.` / 定理 `lift_lift.`

English:
theorem lift_lift.{u_1}
  given: (o : OrderType.{u_1})
  statement: lift.{u} (lift.{v} o) = lift.{max v u} o
  proof: inductionOn o fun _ =>
    (ULift.orderIso.trans <| ULift.orderIso.trans ULift.orderIso.symm).type_congr

中文:
定理 lift_lift.{u_1}
  条件: (o : 序型.{u_1})
  结论: lift.{u} (lift.{v} o) = lift.{最大值 v u} o
  证明: inductionOn o fun _ =>
    (ULift.orderIso.trans <| ULift.orderIso.trans ULift.orderIso.symm).type_congr

Depends on / 依赖: ULift.orderIso.symm, ULift.orderIso.trans, inductionOn, orderIso, type_congr
-/
theorem lift_lift.{u_1} (o : OrderType.{u_1}) : lift.{u} (lift.{v} o) = lift.{max v u} o :=
  inductionOn o fun _ =>
    (ULift.orderIso.trans <| ULift.orderIso.trans ULift.orderIso.symm).type_congr

/--
theorem `lift_type_eq_iff` / 定理 `lift_type_eq_iff`

English:
theorem lift_type_eq_iff
  statement: lift (type α) = lift (type β) ↔ Nonempty (α ≃o β)
  proof: by
refine ⟨fun h => ?_, fun ⟨h⟩ => congrArg lift type_congr h⟩
  rw [← type_ulift]; rw [← type_ulift]; rw [type_eq_type] at h
  exact ⟨(ULift.orderIso.symm.trans h.some).trans ULift.orderIso⟩

中文:
定理 lift_type_eq_iff
  结论: lift (type α) = lift (type β) ↔ 非空 (α ≃o β)
  证明: by
refine ⟨fun h => ?_, fun ⟨h⟩ => congrArg lift type_congr h⟩
  rw [← type_ulift]; rw [← type_ulift]; rw [type_eq_type] at h
  exact ⟨(ULift.orderIso.symm.trans h.some).trans ULift.orderIso⟩

Depends on / 依赖: ULift.orderIso, ULift.orderIso.symm.trans, h.some, orderIso, type_congr, type_eq_type, type_ulift
-/
theorem lift_type_eq_iff : lift (type α) = lift (type β) ↔ Nonempty (α ≃o β) := by
refine ⟨fun h => ?_, fun ⟨h⟩ => congrArg lift type_congr h⟩
  rw [← type_ulift]; rw [← type_ulift]; rw [type_eq_type] at h
  exact ⟨(ULift.orderIso.symm.trans h.some).trans ULift.orderIso⟩

/--
theorem `lift_type_le_iff` / 定理 `lift_type_le_iff`

English:
theorem lift_type_le_iff
  statement: lift (type α) <= lift (type β) ↔ Nonempty (α ↪o β)
  proof: by
refine ⟨fun h => ?_, fun ⟨h⟩ => type_le_type (ULift.orderIso.toOrderEmbedding.trans h).trans
    ULift.orderIso.symm.toOrderEmbedding⟩
  rw [← type_ulift]; rw [← type_ulift]; rw [type_le_type_iff] at h
  exact ⟨(ULift.orderIso.symm.toOrderEmbedding.trans h.some).trans ULift.orderIso.toOrderEmbedding⟩

中文:
定理 lift_type_le_iff
  结论: lift (type α) <= lift (type β) ↔ 非空 (α ↪o β)
  证明: by
refine ⟨fun h => ?_, fun ⟨h⟩ => type_le_type (ULift.orderIso.toOrderEmbedding.trans h).trans
    ULift.orderIso.symm.toOrderEmbedding⟩
  rw [← type_ulift]; rw [← type_ulift]; rw [type_le_type_iff] at h
  exact ⟨(ULift.orderIso.symm.toOrderEmbedding.trans h.some).trans ULift.orderIso.toOrderEmbedding⟩

Depends on / 依赖: ULift.orderIso.symm.toOrderEmbedding, ULift.orderIso.symm.toOrderEmbedding.trans, ULift.orderIso.toOrderEmbedding, ULift.orderIso.toOrderEmbedding.trans, h.some, orderIso, toOrderEmbedding, type_le_type, type_le_type_iff, type_ulift
-/
theorem lift_type_le_iff : lift (type α) <= lift (type β) ↔ Nonempty (α ↪o β) := by
refine ⟨fun h => ?_, fun ⟨h⟩ => type_le_type (ULift.orderIso.toOrderEmbedding.trans h).trans
    ULift.orderIso.symm.toOrderEmbedding⟩
  rw [← type_ulift]; rw [← type_ulift]; rw [type_le_type_iff] at h
  exact ⟨(ULift.orderIso.symm.toOrderEmbedding.trans h.some).trans ULift.orderIso.toOrderEmbedding⟩

/-- `ω` is the first infinite order type, defined as the order type of `ℕ`. -/
@[expose]
/--
Definition of `omega0` / `omega0` 的定义

English:
definition omega0
  signature: : OrderType
  body: lift type Nat

@[inherit_doc]
scoped notation "ω" => OrderType.omega0
recommended_spelling "omega0" for "ω" in [omega0, «termω»]

@[simp]

中文:
定义 omega0
  签名: : 序型
  定义体: lift type Nat

@[inherit_doc]
scoped notation "ω" => OrderType.omega0
recommended_spelling "omega0" for "ω" in [omega0, «termω»]

@[simp]
-/
def omega0 : OrderType := lift type Nat

@[inherit_doc]
scoped notation "ω" => OrderType.omega0
recommended_spelling "omega0" for "ω" in [omega0, «termω»]

@[simp]
/--
theorem `type_nat` / 定理 `type_nat`

English:
theorem type_nat
  statement: type Nat = omega0
  proof: type_congr ⟨Equiv.ulift.symm, @fun _ _ => by
  simp only [ulift_symm_apply, ULift.up_le]⟩

中文:
定理 type_nat
  结论: type 自然数 = omega0
  证明: type_congr ⟨Equiv.ulift.symm, @fun _ _ => by
  simp only [ulift_symm_apply, ULift.up_le]⟩

Depends on / 依赖: Equiv.ulift.symm, ULift.up_le, type_congr, ulift_symm_apply, up_le
-/
theorem type_nat : type Nat = omega0 := type_congr ⟨Equiv.ulift.symm, @fun _ _ => by
  simp only [ulift_symm_apply, ULift.up_le]⟩

end OrderType
