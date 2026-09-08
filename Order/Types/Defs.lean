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
/-
**OrderType.instSetoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderType.instSetoid : Setoid LinOrd where r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence relation on linear orders on arbitrary types in universe `u`, given 
by order
isomorphism.
-/
def OrderType.instSetoid : Setoid LinOrd where
  r := fun lin_ord₁ lin_ord₂ ↦ Nonempty (lin_ord₁ ≃o lin_ord₂)
  iseqv := ⟨fun _ ↦ ⟨.refl _⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ ↦ ⟨e₁.trans e₂⟩⟩

/-- `OrderType.{u}` is the type of linear orders in `Type u`, up to order isomorphism. -/
@[pp_with_univ]
/-
**OrderType** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderType : Type (u + 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderType.{u}` is the type of linear orders in `Type u`, up to order isomorphis
m.
-/
def OrderType : Type (u + 1) :=
  Quotient OrderType.instSetoid

namespace OrderType

/-- A "canonical" type order-isomorphic to the order type `o`, living in the same universe.
This is defined through the axiom of choice. -/
/-
**OrderType.ToType** 是 Mathlib 中的一个定义，位于命名空间 `OrderType`。
形式化陈述：ToType (o : OrderType) : Type u
参数：o : OrderType。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A "canonical" type order-isomorphic to the order type `o`, living in the same un
iverse.
This is defined through the axiom of choice.
-/
def ToType (o : OrderType) : Type u :=
  o.out.carrier

/-- The instance for some arbitrary linear order on `Type u` , order isomorphic within
order type `o`. -/
@[no_expose]
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The instance for some arbitrary linear order on `Type u` , order isomorphic with
in
order type `o`.
-/
instance (o : OrderType) : LinearOrder o.ToType :=
  o.out.str

/-! ### Basic properties of the order type -/

/-- The order type of the linear order on `α`. -/
/-
**OrderType.type** 是 Mathlib 中的一个定义，位于命名空间 `OrderType`。
形式化陈述：type (α : Type u) [LinearOrder α] : OrderType
参数：α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order type of the linear order on `α`.
-/
def type (α : Type u) [LinearOrder α] : OrderType :=
  ⟦⟨α⟩⟧
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero OrderType where
  zero := type PEmpty
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited OrderType :=
  ⟨0⟩
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One OrderType where
  one := type PUnit

@[simp]
/-
**OrderType.type_toType** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_toType (o : OrderType) : type o.ToType = o
参数：o : OrderType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
-/
theorem type_toType (o : OrderType) : type o.ToType = o := surjInv_eq Quot.exists_rep o
/-
**OrderType.type_eq_type** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_eq_type : type α = type β ↔ Nonempty (α ≃o β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b
-/
theorem type_eq_type : type α = type β ↔ Nonempty (α ≃o β) :=
  Quotient.eq'
/-
**OrderType.type_congr** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_congr (h : α ≃o β) : type α = type β
参数：h : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderType.type_eq_type`：type_eq_type : type α = type β ↔ Nonempty (α ≃o 
β)
-/
theorem type_congr (h : α ≃o β) : type α = type β :=
  type_eq_type.2 ⟨h⟩

alias _root_.OrderIso.type_congr := type_congr

@[simp]
/-
**OrderType.type_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_of_isEmpty [IsEmpty α] : type α = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderType.type_congr`：type_congr (h : α ≃o β) : type α = type β
-/
theorem type_of_isEmpty [IsEmpty α] : type α = 0 :=
  type_congr <| .ofIsEmpty α PEmpty
/-
**OrderType.type_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_eq_zero : type α = 0 ↔ IsEmpty α where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OrderType.type_eq_type`：type_eq_type : type α = type β ↔ Nonempty (α ≃o 
β)
· 使用定理 `Equiv.isEmpty`：∀ {α : Sort u_1} {β : Sort u_4} (e : α ≃ β) [IsEmpty β], 
IsEmpty α
· 使用定理 `OrderType.type_of_isEmpty`：type_of_isEmpty [IsEmpty α] : type α = 0
-/
theorem type_eq_zero : type α = 0 ↔ IsEmpty α where
  mp h :=
    let ⟨s⟩ := type_eq_type.1 h
    s.toEquiv.isEmpty
  mpr := @type_of_isEmpty α _
/-
**OrderType.type_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_ne_zero_iff : type α != 0 ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem type_ne_zero_iff : type α ≠ 0 ↔ Nonempty α := by simp [type_eq_zero]

@[simp]
/-
**OrderType.type_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_ne_zero [h : Nonempty α] : type α != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderType.type_ne_zero_iff`：type_ne_zero_iff : type α != 0 ↔ Nonempty α
-/
theorem type_ne_zero [h : Nonempty α] : type α ≠ 0 :=
  type_ne_zero_iff.2 h

@[simp]
/-
**OrderType.type_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_of_unique [Nonempty α] [Subsingleton α] : type α = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_unique`：nonempty_unique (α : Sort u) [Subsingleton α] [Nonempty
 α] : Nonempty (Unique α)
· 使用定理 `OrderIso.type_congr`：∀ {α β : Type u} [inst : LinearOrder α] [inst_1 : L
inearOrder β] (h : α ≃o β), OrderType.type α = OrderType.type β
-/
theorem type_of_unique [Nonempty α] [Subsingleton α] : type α = 1 := by
  cases nonempty_unique α
  exact (OrderIso.ofUnique α _).type_congr
/-
**OrderType.type_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_eq_one : type α = 1 ↔ Nonempty (Unique α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OrderType.type_eq_type`：type_eq_type : type α = type β ↔ Nonempty (α ≃o 
β)
· 使用定理 `OrderType.type_of_unique`：type_of_unique [Nonempty α] [Subsingleton α] :
 type α = 1
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem type_eq_one : type α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h ↦ let ⟨s⟩ := type_eq_type.1 h; ⟨s.toEquiv.unique⟩,
    fun ⟨_⟩ ↦ type_of_unique⟩

@[simp]
/-
**OrderType.isEmpty_toType_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem isEmpty_toType_iff {o : OrderType} : IsEmpty o.ToType ↔ o = 0 := by
  rw [← @type_eq_zero o.ToType, type_toType]

@[simp]
/-
**OrderType.nonempty_toType_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem nonempty_toType_iff {o : OrderType} : Nonempty o.ToType ↔ o ≠ 0 := by
  rw [← @type_ne_zero_iff o.ToType, type_toType]
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial OrderType.{u} :=
  ⟨⟨1, 0, type_ne_zero⟩⟩

/-- `Quotient.inductionOn` specialized to `OrderType`. -/
@[elab_as_elim]
/-
**OrderType.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：inductionOn {C : OrderType -> Prop} (o : OrderType) (H : forall α [LinearO
rder α], C (type α)) : C o
参数：o : OrderType；H : forall α [LinearOrder α], C (type α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q

--- 原说明 ---
`Quotient.inductionOn` specialized to `OrderType`.
-/
theorem inductionOn {C : OrderType → Prop} (o : OrderType)
    (H : ∀ α [LinearOrder α], C (type α)) : C o :=
  Quot.inductionOn o (fun α ↦ H α)

/-- `Quotient.inductionOn₂` specialized to `OrderType`. -/
@[elab_as_elim]
/-
**OrderType.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：inductionOn {C : OrderType -> Prop} (o : OrderType) (H : forall α [LinearO
rder α], C (type α)) : C o
参数：o : OrderType；H : forall α [LinearOrder α], C (type α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q

--- 原说明 ---
`Quotient.inductionOn₂` specialized to `OrderType`.
-/
theorem inductionOn₂ {C : OrderType → OrderType → Prop} (o₁ o₂ : OrderType)
    (H : ∀ α [LinearOrder α] β [LinearOrder β], C (type α) (type β)) : C o₁ o₂ :=
  Quotient.inductionOn₂ o₁ o₂ fun α β ↦ H α β

/-- `Quotient.inductionOn₃` specialized to `OrderType`. -/
@[elab_as_elim]
/-
**OrderType.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：inductionOn {C : OrderType -> Prop} (o : OrderType) (H : forall α [LinearO
rder α], C (type α)) : C o
参数：o : OrderType；H : forall α [LinearOrder α], C (type α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q

--- 原说明 ---
`Quotient.inductionOn₃` specialized to `OrderType`.
-/
theorem inductionOn₃ {C : OrderType → OrderType → OrderType → Prop} (o₁ o₂ o₃ : OrderType)
    (H : ∀ α [LinearOrder α] β [LinearOrder β] γ [LinearOrder γ],
      C (type α) (type β) (type γ)) : C o₁ o₂ o₃ :=
  Quotient.inductionOn₃ o₁ o₂ o₃ fun α β γ ↦
    H α β γ

/-- To define a function on `OrderType`, it suffices to define it on all linear orders.
-/
/-
**OrderType.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `OrderType`。
形式化陈述：liftOn (o : OrderType) (f : forall (α) [LinearOrder α], δ) (c : forall (α)
 [LinearOrder α] (β) [LinearOrder β], type α = type β -> f α = f β) : δ
参数：o : OrderType；f : forall (α) [LinearOrder α], δ；c : forall (α) [LinearOrder α
] (β) [LinearOrder β], type α = type β -> f α = f β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To define a function on `OrderType`, it suffices to define it on all linear orde
rs.
-/
def liftOn (o : OrderType) (f : ∀ (α) [LinearOrder α], δ)
    (c : ∀ (α) [LinearOrder α] (β) [LinearOrder β],
      type α = type β → f α = f β) : δ :=
  Quotient.liftOn o (fun w ↦ f w)
    fun w₁ w₂ h ↦ c w₁ w₂ (Quotient.sound h)

/-- `Quotient.liftOn₂` specialized to `OrderType`. -/
/-
**OrderType.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `OrderType`。
形式化陈述：liftOn (o : OrderType) (f : forall (α) [LinearOrder α], δ) (c : forall (α)
 [LinearOrder α] (β) [LinearOrder β], type α = type β -> f α = f β) : δ
参数：o : OrderType；f : forall (α) [LinearOrder α], δ；c : forall (α) [LinearOrder α
] (β) [LinearOrder β], type α = type β -> f α = f β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Quotient.liftOn₂` specialized to `OrderType`.
-/
def liftOn₂ (o₁ o₂ : OrderType) (f : ∀ (α) [LinearOrder α] (β) [LinearOrder β], δ)
    (c : ∀ (α₁) [LinearOrder α₁] (β₁) [LinearOrder β₁] (α₂) [LinearOrder α₂] (β₂) [LinearOrder β₂],
      type α₁ = type α₂ → type β₁ = type β₂ → f α₁ β₁ = f α₂ β₂) : δ :=
  Quotient.liftOn₂ o₁ o₂ (fun w v ↦ f w v)
    fun w₁ w₂ v₁ v₂ hw hv ↦ c w₁ w₂ v₁ v₂ (Quotient.sound hw) (Quotient.sound hv)

@[simp]
/-
**OrderType.liftOn_type** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：liftOn_type (f : forall (α) [LinearOrder α], δ) (c : forall (α) [LinearOrd
er α] (β) [LinearOrder β], type α = type β -> f α = f β) {γ} [LinearOrder γ] : l
iftOn (type γ) f c = f γ
参数：f : forall (α) [LinearOrder α], δ；c : forall (α) [LinearOrder α] (β) [LinearO
rder β], type α = type β -> f α = f β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftOn_type (f : ∀ (α) [LinearOrder α], δ)
    (c : ∀ (α) [LinearOrder α] (β) [LinearOrder β],
      type α = type β → f α = f β) {γ} [LinearOrder γ] :
    liftOn (type γ) f c = f γ := by rfl

@[simp]
/-
**OrderType.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `OrderType`。
形式化陈述：liftOn (o : OrderType) (f : forall (α) [LinearOrder α], δ) (c : forall (α)
 [LinearOrder α] (β) [LinearOrder β], type α = type β -> f α = f β) : δ
参数：o : OrderType；f : forall (α) [LinearOrder α], δ；c : forall (α) [LinearOrder α
] (β) [LinearOrder β], type α = type β -> f α = f β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftOn₂_type {α : Type u} {β : Type v} {δ : Type*} [LinearOrder α] [LinearOrder β]
     (f : ∀ (α) [LinearOrder α] (β) [LinearOrder β], δ)
     (c : ∀ (α₁) [LinearOrder α₁] (β₁) [LinearOrder β₁] (α₂) [LinearOrder α₂] (β₂) [LinearOrder β₂],
       type α₁ = type α₂ → type β₁ = type β₂ → f α₁ β₁ = f α₂ β₂) :
    liftOn₂ (type α) (type β) f c = f α β := by rfl

/-! ### The order on `OrderType` -/

/--
The order is defined so that `type α ≤ type β` iff there exists an order embedding `α ↪o β`.
-/
@[no_expose]
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order is defined so that `type α ≤ type β` iff there exists an order embeddi
ng `α ↪o β`.
-/
instance : Preorder OrderType where
  le o₁ o₂ :=
    Quotient.liftOn₂ o₁ o₂ (fun r s ↦ Nonempty (r ↪o s))
    fun _ _ _ _ ⟨f⟩ ⟨g⟩ ↦ propext
      ⟨fun ⟨h⟩ ↦ ⟨(f.symm.toOrderEmbedding.trans h).trans g.toOrderEmbedding⟩, fun ⟨h⟩ ↦
        ⟨(f.toOrderEmbedding.trans h).trans g.symm.toOrderEmbedding⟩⟩
  le_refl o := inductionOn o fun α _ ↦ ⟨(OrderIso.refl _).toOrderEmbedding⟩
  le_trans o₁ o₂ o₃ := inductionOn₃ o₁ o₂ o₃ fun _ _ _ _ _ _ ⟨f⟩ ⟨g⟩ ↦ ⟨f.trans g⟩
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NeZero (1 : OrderType) :=
  ⟨type_ne_zero⟩
/-
**OrderType.type_le_type_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_le_type_iff : type α <= type β ↔ Nonempty (α ↪o β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem type_le_type_iff : type α ≤ type β ↔ Nonempty (α ↪o β) :=
  .rfl
/-
**OrderType.type_le_type** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_le_type (h : α ↪o β) : type α <= type β
参数：h : α ↪o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem type_le_type (h : α ↪o β) : type α ≤ type β :=
  ⟨h⟩
/-
**OrderType.type_lt_type** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_lt_type (h : α ↪o β) (hne : IsEmpty (β ↪o α)) : type α < type β
参数：h : α ↪o β；hne : IsEmpty (β ↪o α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
-/
theorem type_lt_type (h : α ↪o β) (hne : IsEmpty (β ↪o α)) : type α < type β :=
  ⟨⟨h⟩, not_nonempty_iff.mpr hne⟩

alias _root_.OrderEmbedding.type_le_type := type_le_type

@[simp]
/-
**OrderType.zero_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：∀ (o : OrderType.{u_1}), 0 ≤ o
参数：o : OrderType.{u_1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderType.inductionOn`：inductionOn {C : OrderType -> Prop} (o : OrderTyp
e) (H : forall α [LinearOrder α], C (type α)) : C o
· 使用定理 `OrderEmbedding.type_le_type`：∀ {α β : Type u} [inst : LinearOrder α] [in
st_1 : LinearOrder β] (h : α ↪o β), OrderType.type α ≤ OrderType.type β
-/
protected theorem zero_le (o : OrderType) : 0 ≤ o :=
  inductionOn o fun _ ↦ OrderEmbedding.ofIsEmpty.type_le_type
/-
**OrderType.** 是 Mathlib 中的一个实例，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot OrderType where
  bot := 0
  bot_le := OrderType.zero_le

@[simp]
/-
**OrderType.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：bot_eq_zero : (⊥ : OrderType) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_eq_zero : (⊥ : OrderType) = 0 :=
  rfl

@[simp]
/-
**OrderType.not_lt_zero** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：∀ {o : OrderType.{u_1}}, ¬o < 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
-/
protected theorem not_lt_zero {o : OrderType} : ¬o < 0 :=
  not_lt_bot

@[simp]
/-
**OrderType.pos_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：pos_iff_ne_zero {o : OrderType} : 0 < o ↔ o != 0 where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.Order.Types.Defs.0.OrderType.nonempty_toType_iff`：∀ {o 
: OrderType.{u_1}}, Nonempty o.ToType ↔ o ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderType.type_toType`：type_toType (o : OrderType) : type o.ToType = o
· 使用定理 `instIsEmptyForallOfNonempty`：∀ {α : Sort u} {p : α → Sort v} [∀ (x : α),
 IsEmpty (p x)] [h : Nonempty α], IsEmpty ((x : α) → p x)
-/
theorem pos_iff_ne_zero {o : OrderType} : 0 < o ↔ o ≠ 0 where
  mp := ne_bot_of_gt
  mpr ho := by
    have := nonempty_toType_iff.2 ho
    rw [← type_toType o]
    exact ⟨⟨Function.Embedding.ofIsEmpty, nofun⟩, fun ⟨f⟩ ↦ IsEmpty.elim inferInstance f.toFun⟩

/-- The universe lift operation on order types. You can specify the universes explicitly with
  `lift.{u, v} : OrderType.{v} → OrderType.{max v u}` -/
@[pp_with_univ]
/-
**OrderType.lift** 是 Mathlib 中的一个定义，位于命名空间 `OrderType`。
形式化陈述：lift (o : OrderType.{v}) : OrderType.{max v u}
参数：o : OrderType.{v}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universe lift operation on order types. You can specify the universes explic
itly with
  `lift.{u, v} : OrderType.{v} → OrderType.{max v u}`
-/
def lift (o : OrderType.{v}) : OrderType.{max v u} :=
  o.liftOn (fun α _ ↦ type (ULift α)) fun _α _ _β _ e ↦
    ((ULift.orderIso.trans (type_eq_type.mp e).some).trans ULift.orderIso.symm).type_congr

@[simp]
/-
**OrderType.type_ulift** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_ulift : type (ULift.{v, u} α) = lift.{v} (type α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem type_ulift : type (ULift.{v, u} α) = lift.{v} (type α) := (rfl)

/-- An order type lifted to a lower or equal universe equals itself. -/
/-
**OrderType.lift_id'** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：lift_id' (o : OrderType.{max u v}) : lift.{u} o = o
参数：o : OrderType.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderType.inductionOn`：inductionOn {C : OrderType -> Prop} (o : OrderTyp
e) (H : forall α [LinearOrder α], C (type α)) : C o
· 使用定理 `OrderType.type_congr`：type_congr (h : α ≃o β) : type α = type β

--- 原说明 ---
An order type lifted to a lower or equal universe equals itself.
-/
theorem lift_id' (o : OrderType.{max u v}) : lift.{u} o = o :=
  inductionOn o fun _ ↦ type_congr ULift.orderIso

/-- An order type lifted to the same universe equals itself. -/
@[simp]
/-
**OrderType.lift_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：lift_id (o : OrderType) : lift.{u, u} o = o
参数：o : OrderType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderType.lift_id'`：lift_id' (o : OrderType.{max u v}) : lift.{u} o = o

--- 原说明 ---
An order type lifted to the same universe equals itself.
-/
theorem lift_id (o : OrderType) : lift.{u, u} o = o :=
  lift_id'.{u, u} o

/-- An order type lifted to the zero universe equals itself. -/
@[simp]
/-
**OrderType.lift_uzero** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：lift_uzero (o : OrderType.{u}) : lift.{0} o = o
参数：o : OrderType.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderType.lift_id'`：lift_id' (o : OrderType.{max u v}) : lift.{u} o = o

--- 原说明 ---
An order type lifted to the zero universe equals itself.
-/
theorem lift_uzero (o : OrderType.{u}) : lift.{0} o = o :=
  lift_id'.{0, u} o

@[simp]
/-
**OrderType.lift_lift.** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_lift.{u_1} (o : OrderType.{u_1}) : lift.{u} (lift.{v} o) = lift.{max v u} o :=
  inductionOn o fun _ ↦
    (ULift.orderIso.trans <| ULift.orderIso.trans ULift.orderIso.symm).type_congr
/-
**OrderType.lift_type_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：lift_type_eq_iff : lift (type α) = lift (type β) ↔ Nonempty (α ≃o β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderType.type_eq_type`：type_eq_type : type α = type β ↔ Nonempty (α ≃o 
β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderType.type_ulift`：type_ulift : type (ULift.{v, u} α) = lift.{v} (typ
e α)
· 使用定理 `OrderType.type_congr`：type_congr (h : α ≃o β) : type α = type β
-/
theorem lift_type_eq_iff : lift (type α) = lift (type β) ↔ Nonempty (α ≃o β) := by
  refine ⟨fun h ↦ ?_, fun ⟨h⟩ ↦ congrArg lift <| type_congr h⟩
  rw [← type_ulift, ← type_ulift, type_eq_type] at h
  exact ⟨(ULift.orderIso.symm.trans h.some).trans ULift.orderIso⟩
/-
**OrderType.lift_type_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：lift_type_le_iff : lift (type α) <= lift (type β) ↔ Nonempty (α ↪o β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderType.type_le_type_iff`：type_le_type_iff : type α <= type β ↔ Nonemp
ty (α ↪o β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderType.type_ulift`：type_ulift : type (ULift.{v, u} α) = lift.{v} (typ
e α)
· 使用定理 `OrderType.type_le_type`：type_le_type (h : α ↪o β) : type α <= type β
-/
theorem lift_type_le_iff : lift (type α) ≤ lift (type β) ↔ Nonempty (α ↪o β) := by
  refine ⟨fun h ↦ ?_, fun ⟨h⟩ ↦ type_le_type <| (ULift.orderIso.toOrderEmbedding.trans h).trans
    ULift.orderIso.symm.toOrderEmbedding⟩
  rw [← type_ulift, ← type_ulift, type_le_type_iff] at h
  exact ⟨(ULift.orderIso.symm.toOrderEmbedding.trans h.some).trans ULift.orderIso.toOrderEmbedding⟩

/-- `ω` is the first infinite order type, defined as the order type of `ℕ`. -/
@[expose]
/-
**OrderType.omega0** 是 Mathlib 中的一个定义，位于命名空间 `OrderType`。
形式化陈述：omega0 : OrderType
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ω` is the first infinite order type, defined as the order type of `ℕ`.
-/
def omega0 : OrderType := lift <| type ℕ

@[inherit_doc]
scoped notation "ω" => OrderType.omega0
recommended_spelling "omega0" for "ω" in [omega0, «termω»]

@[simp]
/-
**OrderType.type_nat** 是 Mathlib 中的一个定理，位于命名空间 `OrderType`。
形式化陈述：type_nat : type Nat = omega0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderType.type_congr`：type_congr (h : α ≃o β) : type α = type β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.ulift_symm_apply`：∀ {α : Type v}, ⇑Equiv.ulift.symm = ULift.up
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem type_nat : type ℕ = omega0 := type_congr ⟨Equiv.ulift.symm, @fun _ _ ↦ by
  simp only [ulift_symm_apply, ULift.up_le]⟩

end OrderType

