/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Cofinality.Basic
public import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Cofinality of an ordinal

This file contains the definition of the cofinality `Ordinal.cof o` of an ordinal. This is the
cofinality of the ordinal `o` when viewed as a linear order.

## Main statements

* `Cardinal.lt_power_cof_ord`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ℵ₀`.

## Implementation notes

* We do not separately define the cofinality of a cardinal. If `c` is a cardinal number, you can
  write its cofinality as `c.ord.cof`.
-/

public noncomputable section

open Function Cardinal Set Order
open scoped Ordinal

universe u v w

variable {α γ : Type u} {β : Type v}

/-
**Order.cof_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Order.cof_int : cof Int = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.cof_eq_aleph0`：cof_eq_aleph0 [NoMaxOrder α] [Nonempty α] [Countabl
e α] : cof α = ℵ₀
· 使用定理 `LinearOrderedAddCommGroup.to_noMaxOrder`：∀ {α : Type u} [inst : AddCommG
roup α] [inst_1 : LinearOrder α] [IsOrderedAddMonoid α] [Nontrivial α], NoMaxOrd
er α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Order.cof_int : cof ℤ = ℵ₀ := by simp

/-! ### Cofinality of ordinals -/

-- TODO: generalize to `OrderType`
namespace Ordinal

/-- The cofinality on an ordinal is the `Order.cof` of any isomorphic linear order.

In particular, `cof 0 = 0` and `cof (succ o) = 1`. -/
/-
**Ordinal.cof** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：cof (o : Ordinal.{u}) : Cardinal.{u}
参数：o : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofinality on an ordinal is the `Order.cof` of any isomorphic linear order.

In particular, `cof 0 = 0` and `cof (succ o) = 1`.
-/
def cof (o : Ordinal.{u}) : Cardinal.{u} :=
  o.liftOnWellOrder (fun α _ _ ↦ Order.cof α) fun _ _ _ _ _ _ h ↦
    let ⟨f⟩ := type_eq.1 h
    (OrderIso.ofRelIsoLT f).cof_congr

@[simp]
/-
**Ordinal.cof_type** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_type (α : Type*) [LinearOrder α] [WellFoundedLT α] : (typeLT α).cof = 
Order.cof α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.liftOnWellOrder_type`：liftOnWellOrder_type {δ : Sort v} (f : for
all (α) [LinearOrder α] [WellFoundedLT α], δ) (c : forall (α) [LinearOrder α] [W
ellFoundedLT α] (β…
-/
theorem cof_type (α : Type*) [LinearOrder α] [WellFoundedLT α] :
    (typeLT α).cof = Order.cof α :=
  liftOnWellOrder_type ..

@[deprecated (since := "2026-02-18")] alias cof_type_lt := cof_type

@[simp]
/-
**Ordinal.cof_toType** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_toType (o : Ordinal) : Order.cof o.ToType = o.cof
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `Ordinal.cof_type`：cof_type (α : Type*) [LinearOrder α] [WellFoundedLT α]
 : (typeLT α).cof = Order.cof α
-/
theorem cof_toType (o : Ordinal) : Order.cof o.ToType = o.cof := by
  conv_rhs => rw [← type_toType o, cof_type]

@[deprecated (since := "2026-02-18")] alias cof_eq_cof_toType := cof_toType
@[deprecated (since := "2026-02-18")] alias le_cof_type := le_cof_iff
@[deprecated (since := "2026-02-18")] alias cof_type_le := cof_le
@[deprecated (since := "2026-02-18")] alias lt_cof_type := cof_le
@[deprecated (since := "2026-02-18")] alias cof_eq := Order.cof_eq

@[simp]
/-
**Ordinal.lift_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_cof (o : Ordinal.{u}) : Cardinal.lift.{v} (cof o) = cof (Ordinal.lift
.{v} o)
参数：o : Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOnWellOrder`：inductionOnWellOrder {motive : Ordinal -> 
Prop} (o : Ordinal) (type : forall (α) [LinearOrder α] [WellFoundedLT α], motive
 (typeLT α)) : mot…
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.cof_type`：cof_type (α : Type*) [LinearOrder α] [WellFoundedLT α]
 : (typeLT α).cof = Order.cof α
· 使用定理 `instWellFoundedLTULift`：∀ {α : Type u_1} [inst : LT α] [h : WellFoundedL
T α], WellFoundedLT (ULift.{u_4, u_1} α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_lt_ulift`：type_lt_ulift [LinearOrder α] [WellFoundedLT α] :
 typeLT (ULift α) = lift.{v} (typeLT α)
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `OrderIso.lift_cof_congr`：OrderIso.lift_cof_congr (f : α ≃o β) : Cardinal
.lift.{v} (Order.cof α) = Cardinal.lift.{u} (Order.cof β)
-/
theorem lift_cof (o : Ordinal.{u}) : Cardinal.lift.{v} (cof o) = cof (Ordinal.lift.{v} o) := by
  cases o using inductionOnWellOrder with | type α
  rw [cof_type, ← type_lt_ulift, cof_type, ← Cardinal.lift_id'.{u, v} (Order.cof (ULift _)),
    ← Cardinal.lift_umax, ← ULift.orderIso.lift_cof_congr]
/-
**Ordinal._root_.Order.cof_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Order.cof_Iio [LinearOrder α] [WellFoundedLT α] (x : α) :
    Order.cof (Iio x) = cof (typein (α := α) (· < ·) x) :=
  (cof_type _).symm

@[simp]
/-
**Ordinal.cof_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_Iio (o : Ordinal.{u}) : Order.cof (Iio o) = cof (lift.{u + 1} o)
参数：o : Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.cof_Iio`：∀ {α : Type u} [inst : LinearOrder α] [inst_1 : WellFound
edLT α] (x : α),   Order.cof ↑(Set.Iio x) = ((Ordinal.typein fun x1 x2 => x1 < x
2).…
· 使用定理 `Ordinal.typein_ordinal`：typein_ordinal (o : Ordinal.{u}) : typein LT.lt 
o = lift.{u + 1} o
-/
theorem cof_Iio (o : Ordinal.{u}) : Order.cof (Iio o) = cof (lift.{u + 1} o) := by
  rw [Order.cof_Iio, typein_ordinal]
/-
**Ordinal.cof_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_le_card (o : Ordinal) : cof o <= card o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.cof_toType`：cof_toType (o : Ordinal) : Order.cof o.ToType = o.co
f
· 使用定理 `Cardinal.mk_toType`：∀ (o : Ordinal.{u_1}), Cardinal.mk o.ToType = o.card
· 使用定理 `Order.cof_le_cardinalMk`：cof_le_cardinalMk : cof α <= #α
-/
theorem cof_le_card (o : Ordinal) : cof o ≤ card o := by
  simpa using cof_le_cardinalMk o.ToType
/-
**Ordinal.cof_ord_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_ord_le (c : Cardinal) : c.ord.cof <= c
参数：c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `Ordinal.cof_le_card`：cof_le_card (o : Ordinal) : cof o <= card o
-/
theorem cof_ord_le (c : Cardinal) : c.ord.cof ≤ c := by
  simpa using cof_le_card c.ord
/-
**Ordinal.ord_cof_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：ord_cof_le (o : Ordinal) : o.cof.ord <= o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.ord_le_ord`：ord_le_ord {c₁ c₂} : ord c₁ <= ord c₂ ↔ c₁ <= c₂
· 使用定理 `Ordinal.cof_le_card`：cof_le_card (o : Ordinal) : cof o <= card o
· 使用定理 `Cardinal.ord_card_le`：ord_card_le (o : Ordinal) : o.card.ord <= o
-/
theorem ord_cof_le (o : Ordinal) : o.cof.ord ≤ o :=
  (ord_le_ord.2 (cof_le_card o)).trans (ord_card_le o)

@[simp]
/-
**Ordinal.cof_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_eq_zero {o} : cof o = 0 ↔ o = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.cof_toType`：cof_toType (o : Ordinal) : Order.cof o.ToType = o.co
f
· 使用定理 `Order.cof_eq_zero_iff`：cof_eq_zero_iff : cof α = 0 ↔ IsEmpty α
· 使用定理 `Ordinal.isEmpty_toType_iff`：isEmpty_toType_iff {o : Ordinal} : IsEmpty o
.ToType ↔ o = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cof_eq_zero {o} : cof o = 0 ↔ o = 0 := by
  rw [← cof_toType, cof_eq_zero_iff, isEmpty_toType_iff]

@[deprecated cof_eq_zero (since := "2026-02-18")]
/-
**Ordinal.cof_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_ne_zero {o} : cof o != 0 ↔ o != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ordinal.cof_eq_zero`：cof_eq_zero {o} : cof o = 0 ↔ o = 0
-/
theorem cof_ne_zero {o} : cof o ≠ 0 ↔ o ≠ 0 :=
  cof_eq_zero.not

@[simp]
/-
**Ordinal.cof_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_pos {o} : 0 < cof o ↔ 0 < o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cof_pos {o} : 0 < cof o ↔ 0 < o := by
  simp [pos_iff_ne_zero]

@[simp]
/-
**Ordinal.cof_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_zero : cof 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.cof_eq_zero`：cof_eq_zero {o} : cof o = 0 ↔ o = 0
-/
theorem cof_zero : cof 0 = 0 :=
  cof_eq_zero.2 rfl
/-
**Ordinal.cof_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_eq_one_iff {o} : cof o = 1 ↔ o in range succ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOnWellOrder`：inductionOnWellOrder {motive : Ordinal -> 
Prop} (o : Ordinal) (type : forall (α) [LinearOrder α] [WellFoundedLT α], motive
 (typeLT α)) : mot…
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.cof_type`：cof_type (α : Type*) [LinearOrder α] [WellFoundedLT α]
 : (typeLT α).cof = Order.cof α
· 使用定理 `Order.cof_eq_one_iff`：cof_eq_one_iff : cof α = 1 ↔ exists x : α, IsTop x
· 使用定理 `Ordinal.type_lt_mem_range_succ_iff`：type_lt_mem_range_succ_iff [LinearOr
der α] [WellFoundedLT α] : typeLT α in range succ ↔ exists x : α, IsMax x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cof_eq_one_iff {o} : cof o = 1 ↔ o ∈ range succ := by
  cases o using inductionOnWellOrder with | type α
  rw [cof_type, Order.cof_eq_one_iff, type_lt_mem_range_succ_iff]
  simp_rw [isTop_iff_isMax]
/-
**Ordinal.cof_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_add_one (o) : cof (o + 1) = 1
参数：o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.cof_eq_one_iff`：cof_eq_one_iff {o} : cof o = 1 ↔ o in range succ
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem cof_add_one (o) : cof (o + 1) = 1 :=
  cof_eq_one_iff.2 (mem_range_self o)

@[simp]
/-
**Ordinal.cof_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_one : cof 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Ordinal.cof_add_one`：cof_add_one (o) : cof (o + 1) = 1
-/
theorem cof_one : cof 1 = 1 := by
  simpa using cof_add_one 0

@[deprecated cof_add_one (since := "2026-05-25")]
/-
**Ordinal.cof_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_succ (o) : cof (succ o) = 1
参数：o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.cof_add_one`：cof_add_one (o) : cof (o + 1) = 1
-/
theorem cof_succ (o) : cof (succ o) = 1 :=
  cof_add_one o
/-
**Ordinal.one_lt_cof_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：one_lt_cof_iff {o : Ordinal} : 1 < cof o ↔ IsSuccLimit o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Cardinal.le_one_iff`：∀ {c : Cardinal.{u_1}}, c ≤ 1 ↔ c = 0 ∨ c = 1
· 使用定理 `Ordinal.isSuccLimit_iff`：isSuccLimit_iff {o : Ordinal} : IsSuccLimit o ↔
 o != 0 ∧ IsSuccPrelimit o
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `Order.not_isSuccPrelimit_iff_mem_range_succ`：not_isSuccPrelimit_iff_mem_
range_succ : ¬ IsSuccPrelimit a ↔ a in range (succ : α -> α)
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.cof_eq_zero`：cof_eq_zero {o} : cof o = 0 ↔ o = 0
· 使用定理 `Ordinal.cof_eq_one_iff`：cof_eq_one_iff {o} : cof o = 1 ↔ o in range succ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_lt_cof_iff {o : Ordinal} : 1 < cof o ↔ IsSuccLimit o := by
  rw [← not_iff_not, not_lt, Cardinal.le_one_iff, isSuccLimit_iff,
    not_and_or, not_ne_iff, not_isSuccPrelimit_iff_mem_range_succ, cof_eq_zero, cof_eq_one_iff]

@[simp]
/-
**Ordinal.cof_lt_aleph0_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_lt_aleph0_iff {o : Ordinal} : cof o < ℵ₀ ↔ cof o <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.cof_toType`：cof_toType (o : Ordinal) : Order.cof o.ToType = o.co
f
· 使用定理 `Order.cof_lt_aleph0_iff`：cof_lt_aleph0_iff : cof α < ℵ₀ ↔ cof α <= 1
-/
theorem cof_lt_aleph0_iff {o : Ordinal} : cof o < ℵ₀ ↔ cof o ≤ 1 := by
  simpa using Order.cof_lt_aleph0_iff (α := o.ToType)

@[simp]
/-
**Ordinal.aleph0_le_cof_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：aleph0_le_cof_iff {o : Ordinal} : ℵ₀ <= cof o ↔ 1 < cof o
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
theorem aleph0_le_cof_iff {o : Ordinal} : ℵ₀ ≤ cof o ↔ 1 < cof o := by
  simp [← not_lt]

@[deprecated one_lt_cof_iff (since := "2026-03-22")]
/-
**Ordinal.aleph0_le_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：aleph0_le_cof {o} : ℵ₀ <= cof o ↔ IsSuccLimit o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.aleph0_le_cof_iff`：aleph0_le_cof_iff {o : Ordinal} : ℵ₀ <= cof o
 ↔ 1 < cof o
· 使用定理 `Ordinal.one_lt_cof_iff`：one_lt_cof_iff {o : Ordinal} : 1 < cof o ↔ IsSuc
cLimit o
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aleph0_le_cof {o} : ℵ₀ ≤ cof o ↔ IsSuccLimit o := by
  rw [aleph0_le_cof_iff, one_lt_cof_iff]

/-- A countable limit ordinal has cofinality `ℵ₀`. -/
/-
**Ordinal.cof_eq_aleph0_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_eq_aleph0_of_isSuccLimit {o : Ordinal} (ho : IsSuccLimit o) (ho' : o <
 ω₁) : cof o = ℵ₀
参数：ho : IsSuccLimit o；ho' : o < ω₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.cof_le_card`：cof_le_card (o : Ordinal) : cof o <= card o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.card_le_iff`：card_le_iff {o : Ordinal} {c : Cardinal} : o.card 
<= c ↔ o < (succ c).ord
· 使用定理 `Cardinal.succ_aleph0`：succ_aleph0 : succ ℵ₀ = ℵ₁
· 使用定理 `Cardinal.ord_aleph`：ord_aleph (o : Ordinal) : (ℵ_ o).ord = ω_ o
· 使用定理 `Ordinal.aleph0_le_cof_iff`：aleph0_le_cof_iff {o : Ordinal} : ℵ₀ <= cof o
 ↔ 1 < cof o
· 使用定理 `Ordinal.one_lt_cof_iff`：one_lt_cof_iff {o : Ordinal} : 1 < cof o ↔ IsSuc
cLimit o

--- 原说明 ---
A countable limit ordinal has cofinality `ℵ₀`.
-/
theorem cof_eq_aleph0_of_isSuccLimit {o : Ordinal} (ho : IsSuccLimit o) (ho' : o < ω₁) :
    cof o = ℵ₀ := by
  apply ((cof_le_card _).trans _).antisymm
  · rwa [aleph0_le_cof_iff, one_lt_cof_iff]
  · rwa [card_le_iff, succ_aleph0, ord_aleph]

@[simp]
/-
**Ordinal.cof_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_omega0 : cof ω = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.cof_eq_aleph0_of_isSuccLimit`：cof_eq_aleph0_of_isSuccLimit {o : 
Ordinal} (ho : IsSuccLimit o) (ho' : o < ω₁) : cof o = ℵ₀
· 使用定理 `Ordinal.isSuccLimit_omega0`：isSuccLimit_omega0 : IsSuccLimit ω
· 使用定理 `Ordinal.omega0_lt_omega_one`：omega0_lt_omega_one : ω < ω₁
-/
theorem cof_omega0 : cof ω = ℵ₀ :=
  cof_eq_aleph0_of_isSuccLimit isSuccLimit_omega0 omega0_lt_omega_one

@[deprecated (since := "2026-02-18")] alias cof_eq_one_iff_is_succ := cof_eq_one_iff

variable (α) in
/-- Every well-order has a cofinal subset of order type `(cof α).ord`. -/
/-
**Ordinal.exists_ord_cof_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：exists_ord_cof_eq [LinearOrder α] [WellFoundedLT α] : exists s : Set α, Is
Cofinal s ∧ typeLT s = (Order.cof α).ord
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Order.exists_cof_eq`：exists_cof_eq : exists s : Set α, IsCofinal s ∧ #s 
= cof α
· 使用定理 `Cardinal.exists_ord_eq`：exists_ord_eq (α) : exists (r : α -> α -> Prop) 
(_ : IsWellOrder α r), ord #α = type r
· 使用定理 `IsCofinal.trans`：IsCofinal.trans {s : Set α} {t : Set s} (hs : IsCofinal
 s) (ht : IsCofinal t) : IsCofinal (Subtype.val '' t)
· 使用定理 `isCofinal_setOfPred_imp_lt`：isCofinal_setOfPred_imp_lt (r : α -> α -> Pr
op) [h : IsWellFounded α r] : IsCofinal { a | forall b, r b a -> b < a }
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.ord_le`：ord_le {c o} : ord c <= o ↔ c <= o.card
· 使用定理 `Order.cof_le`：cof_le {s : Set α} (h : IsCofinal s) : cof α <= #s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_le_iff'`：type_le_iff' {α β} {r : α -> α -> Prop} {s : β -> 
β -> Prop} [IsWellOrder α r] [IsWellOrder β s] : type r <= type s ↔ Nonempty (r 
↪r s)
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `trichotomous_of`：trichotomous_of [Std.Trichotomous r] : forall a b : α, 
a ≺ b ∨ a = b ∨ b ≺ a
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `LT.lt.asymm`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b 
< a

--- 原说明 ---
Every well-order has a cofinal subset of order type `(cof α).ord`.
-/
theorem exists_ord_cof_eq [LinearOrder α] [WellFoundedLT α] :
    ∃ s : Set α, IsCofinal s ∧ typeLT s = (Order.cof α).ord := by
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  obtain ⟨r, hr, hr'⟩ := exists_ord_eq s
  have ht := hs.trans (isCofinal_setOfPred_imp_lt r)
  refine ⟨_, ht, (ord_le.2 (cof_le ht)).antisymm' ?_⟩
  rw [← hs', hr', type_le_iff']
  refine ⟨.ofMonotone (fun x ↦ ⟨x.1, ?_⟩) fun x y hxy ↦ ?_⟩
  · grind
  · apply (trichotomous_of r _ _).resolve_right
    rintro (_ | hxy')
    · simp_all [Subtype.coe_inj]
    · obtain ⟨x, z, hz, rfl⟩ := x
      exact (hz _ hxy').asymm hxy

@[deprecated (since := "2026-05-25")] alias ord_cof_eq := exists_ord_cof_eq

/-- Every cofinal set has a cofinal subset of order type `(cof α).ord`. -/
/-
**Ordinal.exists_ord_cof_eq_of_isCofinal** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：exists_ord_cof_eq_of_isCofinal [LinearOrder α] [WellFoundedLT α] {s : Set 
α} (hs : IsCofinal s) : exists t subseteq s, IsCofinal t ∧ typeLT t = (Order.cof
 α).ord
参数：hs : IsCofinal s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Ordinal.exists_ord_cof_eq`：exists_ord_cof_eq [LinearOrder α] [WellFounde
dLT α] : exists s : Set α, IsCofinal s ∧ typeLT s = (Order.cof α).ord
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `IsCofinal.trans`：IsCofinal.trans {s : Set α} {t : Set s} (hs : IsCofinal
 s) (ht : IsCofinal t) : IsCofinal (Subtype.val '' t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.cof_eq_of_isCofinal`：cof_eq_of_isCofinal {s : Set α} (hs : IsCofin
al s) : cof s = cof α
· 使用定理 `OrderIso.ordinalType_congr`：∀ {α β : Type u_1} [inst : LinearOrder α] [i
nst_1 : LinearOrder β] [inst_2 : WellFoundedLT α] [inst_3 : WellFoundedLT β]   (
h : α ≃o β), (Or…
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
· 使用定理 `Subtype.strictMono_coe`：Subtype.strictMono_coe [Preorder α] (p : α -> Pr
op) : StrictMono ((↑) : Subtype p -> α)

--- 原说明 ---
Every cofinal set has a cofinal subset of order type `(cof α).ord`.
-/
theorem exists_ord_cof_eq_of_isCofinal [LinearOrder α] [WellFoundedLT α]
    {s : Set α} (hs : IsCofinal s) : ∃ t ⊆ s, IsCofinal t ∧ typeLT t = (Order.cof α).ord := by
  obtain ⟨t, ht, ht'⟩ := exists_ord_cof_eq s
  rw [cof_eq_of_isCofinal hs] at ht'
  refine ⟨t, ?_, hs.trans ht, ?_⟩
  · simp
  · rw [← ht']
    exact ((Subtype.strictMono_coe _).strictMonoOn _).orderIso.ordinalType_congr.symm

@[simp]
/-
**Ordinal._root_.Order.cof_ord_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Order.cof_ord_cof (α : Type*) [LinearOrder α] [WellFoundedLT α] :
    (Order.cof α).ord.cof = Order.cof α := by
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq α
  rw [← hs', cof_type, cof_eq_of_isCofinal hs]

@[simp]
/-
**Ordinal.cof_ord_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_ord_cof (o : Ordinal) : o.cof.ord.cof = o.cof
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.cof_toType`：cof_toType (o : Ordinal) : Order.cof o.ToType = o.co
f
· 使用定理 `Order.cof_ord_cof`：∀ (α : Type u_1) [inst : LinearOrder α] [WellFoundedL
T α], (Order.cof α).ord.cof = Order.cof α
-/
theorem cof_ord_cof (o : Ordinal) : o.cof.ord.cof = o.cof := by
  simpa using Order.cof_ord_cof o.ToType

@[deprecated (since := "2026-03-21")] alias cof_cof := cof_ord_cof

/-! ### Cofinalities and suprema -/

section LinearOrder
variable [LinearOrder β] [LinearOrder γ]

/-
**Ordinal.lift_cof_iSup_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_cof_iSup_add_one [Small.{u} β] {f : β -> Ordinal} (hf : StrictMono f)
 : Cardinal.lift.{v} (cof (⨆ i, f i + 1)) = Cardinal.lift.{u} (Order.cof β)
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
· 使用定理 `Order.lift_cof_congr_of_strictMono`：lift_cof_congr_of_strictMono {f : α 
-> β} (hf : StrictMono f) (hf' : IsCofinal (range f)) : lift.{v} (cof α) = lift.
{u} (cof β)
· 使用定理 `Ordinal.lt_iSup_add_one_iff`：lt_iSup_add_one_iff {ι} {f : ι -> Ordinal.{
u}} {a} [Small.{u} ι] : a < ⨆ i, f i + 1 ↔ exists i, a <= f i
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ordinal.lift_cof`：lift_cof (o : Ordinal.{u}) : Cardinal.lift.{v} (cof o)
 = cof (Ordinal.lift.{v} o)
· 使用定理 `Ordinal.lift_lift`：lift_lift (a : Ordinal.{u}) : lift.{w} (lift.{v} a) =
 lift.{max v w} a
· 使用定理 `Ordinal.cof_Iio`：cof_Iio (o : Ordinal.{u}) : Order.cof (Iio o) = cof (li
ft.{u + 1} o)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_cof_iSup_add_one [Small.{u} β] {f : β → Ordinal} (hf : StrictMono f) :
    Cardinal.lift.{v} (cof (⨆ i, f i + 1)) = Cardinal.lift.{u} (Order.cof β) := by
  have : StrictMono (β := Iio (⨆ i, f i + 1)) (fun i ↦ ⟨f i, ?_⟩) := fun x y h ↦ hf h
  · have := lift_cof_congr_of_strictMono this ?_
    · rw [← Cardinal.lift_inj.{_, max (u + 1) v}, Cardinal.lift_lift.{_, _, v},
        Cardinal.lift_umax.{_, u + 1}, Cardinal.lift_umax.{_, u + 1}, this]
      simp
    · intro ⟨b, hb⟩
      rw [mem_Iio, Ordinal.lt_iSup_add_one_iff] at hb
      obtain ⟨i, hi⟩ := hb
      exact ⟨_, Set.mem_range_self i, hi⟩
  · rw [mem_Iio]
    exact (lt_add_one _).trans_le <| le_ciSup bddAbove_of_small _
/-
**Ordinal.cof_iSup_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_iSup_add_one {f : γ -> Ordinal} (hf : StrictMono f) : cof (⨆ i, f i + 
1) = Order.cof γ
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Ordinal.lift_cof_iSup_add_one`：lift_cof_iSup_add_one [Small.{u} β] {f : 
β -> Ordinal} (hf : StrictMono f) : Cardinal.lift.{v} (cof (⨆ i, f i + 1)) = Car
dinal.lift.{u} (Ord…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem cof_iSup_add_one {f : γ → Ordinal} (hf : StrictMono f) :
    cof (⨆ i, f i + 1) = Order.cof γ := by
  simpa using lift_cof_iSup_add_one hf
/-
**Ordinal.lift_cof_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_cof_iSup [Small.{u} β] [NoMaxOrder β] {f : β -> Ordinal} (hf : Strict
Mono f) : Cardinal.lift.{v} (cof (⨆ i, f i)) = Cardinal.lift.{u} (Order.cof β)
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_add_one`：iSup_add_one {β : Type*} [LinearOrder β] [NoMaxOrd
er β] {f : β -> Ordinal.{u}} (hf : StrictMono f) : ⨆ i, f i + 1 = ⨆ i, f i
· 使用定理 `Ordinal.lift_cof_iSup_add_one`：lift_cof_iSup_add_one [Small.{u} β] {f : 
β -> Ordinal} (hf : StrictMono f) : Cardinal.lift.{v} (cof (⨆ i, f i + 1)) = Car
dinal.lift.{u} (Ord…
-/
theorem lift_cof_iSup [Small.{u} β] [NoMaxOrder β] {f : β → Ordinal} (hf : StrictMono f) :
    Cardinal.lift.{v} (cof (⨆ i, f i)) = Cardinal.lift.{u} (Order.cof β) := by
  rw [← iSup_add_one hf, lift_cof_iSup_add_one hf]
/-
**Ordinal.cof_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_iSup [NoMaxOrder γ] {f : γ -> Ordinal} (hf : StrictMono f) : cof (⨆ i,
 f i) = Order.cof γ
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Ordinal.lift_cof_iSup`：lift_cof_iSup [Small.{u} β] [NoMaxOrder β] {f : β
 -> Ordinal} (hf : StrictMono f) : Cardinal.lift.{v} (cof (⨆ i, f i)) = Cardinal
.lift.{u} (…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem cof_iSup [NoMaxOrder γ] {f : γ → Ordinal} (hf : StrictMono f) :
    cof (⨆ i, f i) = Order.cof γ := by
  simpa using lift_cof_iSup hf

end LinearOrder

/-
**Ordinal.cof_iSup_Iio_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_iSup_Iio_add_one {a} {f : Iio a -> Ordinal} (hf : StrictMono f) : cof 
(⨆ i, f i + 1) = cof a
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.cof_Iio`：cof_Iio (o : Ordinal.{u}) : Order.cof (Iio o) = cof (li
ft.{u + 1} o)
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Ordinal.lift_cof_iSup_add_one`：lift_cof_iSup_add_one [Small.{u} β] {f : 
β -> Ordinal} (hf : StrictMono f) : Cardinal.lift.{v} (cof (⨆ i, f i + 1)) = Car
dinal.lift.{u} (Ord…
-/
theorem cof_iSup_Iio_add_one {a} {f : Iio a → Ordinal} (hf : StrictMono f) :
    cof (⨆ i, f i + 1) = cof a := by
  simpa [← lift_cof] using lift_cof_iSup_add_one hf
/-
**Ordinal.cof_iSup_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_iSup_Iio {a} {f : Iio a -> Ordinal} (hf : StrictMono f) (ha : IsSuccPr
elimit a) : cof (⨆ i, f i) = cof a
参数：hf : StrictMono f；ha : IsSuccPrelimit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_Iio_add_one`：iSup_Iio_add_one {a : Ordinal.{u}} {f : Iio a 
-> Ordinal.{u}} (hf : StrictMono f) (ha : IsSuccPrelimit a) : ⨆ i : Iio a, f i +
 1 = ⨆ i : Iio…
· 使用定理 `Ordinal.cof_iSup_Iio_add_one`：cof_iSup_Iio_add_one {a} {f : Iio a -> Ord
inal} (hf : StrictMono f) : cof (⨆ i, f i + 1) = cof a
-/
theorem cof_iSup_Iio {a} {f : Iio a → Ordinal} (hf : StrictMono f) (ha : IsSuccPrelimit a) :
    cof (⨆ i, f i) = cof a := by
  rw [← iSup_Iio_add_one hf ha, cof_iSup_Iio_add_one hf]
/-
**Ordinal.cof_map_of_isNormal** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_map_of_isNormal {f} (hf : IsNormal f) {a} (ha : IsSuccLimit a) : cof (
f a) = cof a
参数：hf : IsNormal f；ha : IsSuccLimit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.IsNormal.apply_of_isSuccLimit`：apply_of_isSuccLimit (hf : IsNormal
 f) (ha : IsSuccLimit a) : f a = ⨆ b : Iio a, f b
· 使用定理 `Ordinal.cof_iSup_Iio`：cof_iSup_Iio {a} {f : Iio a -> Ordinal} (hf : Stri
ctMono f) (ha : IsSuccPrelimit a) : cof (⨆ i, f i) = cof a
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Subtype.strictMono_coe`：Subtype.strictMono_coe [Preorder α] (p : α -> Pr
op) : StrictMono ((↑) : Subtype p -> α)
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem cof_map_of_isNormal {f} (hf : IsNormal f) {a} (ha : IsSuccLimit a) : cof (f a) = cof a := by
  rw [hf.apply_of_isSuccLimit ha, cof_iSup_Iio _ ha.isSuccPrelimit]
  exact hf.strictMono.comp <| Subtype.strictMono_coe _

@[deprecated (since := "2026-03-19")]
alias cof_eq_of_isNormal := cof_map_of_isNormal
/-
**Ordinal.le_cof_map_of_isNormal** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_cof_map_of_isNormal {f} (hf : IsNormal f) (a) : cof a <= cof (f a)
参数：hf : IsNormal f；a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.cof_zero`：cof_zero : cof 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.cof_add_one`：cof_add_one (o) : cof (o + 1) = 1
· 使用定理 `Cardinal.one_le_iff_ne_zero`：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ c ≠ 0
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Ordinal.cof_eq_zero`：cof_eq_zero {o} : cof o = 0 ↔ o = 0
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.cof_map_of_isNormal`：cof_map_of_isNormal {f} (hf : IsNormal f) {
a} (ha : IsSuccLimit a) : cof (f a) = cof a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem le_cof_map_of_isNormal {f} (hf : IsNormal f) (a) : cof a ≤ cof (f a) := by
  cases a using limitRecOn with
  | zero => simp
  | add_one a =>
    rw [cof_add_one, Cardinal.one_le_iff_ne_zero, cof_eq_zero.ne]
    exact (hf.strictMono (lt_succ a)).ne_zero
  | limit a ha => rw [cof_map_of_isNormal hf ha]

@[deprecated (since := "2026-03-19")]
alias cof_le_of_isNormal := le_cof_map_of_isNormal

set_option backward.isDefEq.respectTransparency false in
/-
**Ordinal.sSup_add_one_lt_of_lt_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sSup_add_one_lt_of_lt_cof {s : Set Ordinal.{u}} {a : Ordinal.{u}} (ha : #s
 < (lift.{u + 1} a).cof) (hs : forall i in s, i < a) : sSup ((· + 1) '' s) < a
参数：ha : #s < (lift.{u + 1} a).cof；hs : forall i in s, i < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp'`：range_comp' (g : α -> β) (f : ι -> α) : range (fun x =>
 g (f x)) = g '' range f
· 使用定理 `OrderIso.range_eq`：range_eq (e : α ≃o β) : Set.range e = Set.univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Ordinal.cof_type`：cof_type (α : Type*) [LinearOrder α] [WellFoundedLT α]
 : (typeLT α).cof = Order.cof α
· 使用定理 `Ordinal.lift_cof`：lift_cof (o : Ordinal.{u}) : Cardinal.lift.{v} (cof o)
 = cof (Ordinal.lift.{v} o)
· 使用定理 `Ordinal.cof_Iio`：cof_Iio (o : Ordinal.{u}) : Order.cof (Iio o) = cof (li
ft.{u + 1} o)
（共 32 条，此处仅展示前 30 条）
-/
theorem sSup_add_one_lt_of_lt_cof {s : Set Ordinal.{u}} {a : Ordinal.{u}}
    (ha : #s < (lift.{u + 1} a).cof) (hs : ∀ i ∈ s, i < a) : sSup ((· + 1) '' s) < a := by
  let f := OrderIso.ofRelIsoLT (enum (α := s) (· < ·))
  have : Small.{u} (Iio (typeLT s)) := by
    refine small_of_injective (β := Iio a) (f := fun x ↦ ⟨f x, hs _ (f x).2⟩) fun _ ↦ ?_
    simp [Subtype.val_inj]
  have : range (fun i ↦ (f i).1 + 1) = (· + 1) '' s := by
    convert! range_comp (· + 1) (fun i ↦ (f i).1)
    rw [range_comp', f.range_eq]
    simp
  rw [← this, sSup_range]
  apply lt_of_le_of_ne
  · simp [hs]
  · rintro rfl
    rw [← lift_cof, ← Cardinal.lift_lt.{_, u + 2}, Cardinal.lift_lift,
      lift_cof_iSup_add_one fun _ ↦ by simp, cof_Iio, ← lift_cof, cof_type,
      Cardinal.lift_lift, Cardinal.lift_lt] at ha
    exact ha.not_ge (cof_le_cardinalMk _)
/-
**Ordinal.sSup_lt_of_lt_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sSup_lt_of_lt_cof {s : Set Ordinal.{u}} {a : Ordinal.{u}} (ha : #s < (lift
.{u + 1} a).cof) (hs : forall i in s, i < a) : sSup s < a
参数：ha : #s < (lift.{u + 1} a).cof；hs : forall i in s, i < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ordinal.sSup_le_sSup_add_one`：sSup_le_sSup_add_one (s : Set Ordinal) : s
Sup s <= sSup ((· + 1) '' s)
· 使用定理 `Ordinal.sSup_add_one_lt_of_lt_cof`：sSup_add_one_lt_of_lt_cof {s : Set Or
dinal.{u}} {a : Ordinal.{u}} (ha : #s < (lift.{u + 1} a).cof) (hs : forall i in 
s, i < a) : sSup ((· + …
-/
theorem sSup_lt_of_lt_cof {s : Set Ordinal.{u}} {a : Ordinal.{u}}
    (ha : #s < (lift.{u + 1} a).cof) (hs : ∀ i ∈ s, i < a) : sSup s < a :=
  (sSup_le_sSup_add_one s).trans_lt (sSup_add_one_lt_of_lt_cof ha hs)
/-
**Ordinal.lift_iSup_add_one_lt_of_lt_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_iSup_add_one_lt_of_lt_cof {f : β -> Ordinal.{u}} {a : Ordinal.{u}} (h
a : Cardinal.lift.{u} #β < (lift.{v} a).cof) (hf : forall i, f i < a) : ⨆ i, f i
 + 1 < a
参数：ha : Cardinal.lift.{u} #β < (lift.{v} a).cof；hf : forall i, f i < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Set.range_comp'`：range_comp' (g : α -> β) (f : ι -> α) : range (fun x =>
 g (f x)) = g '' range f
· 使用定理 `Ordinal.sSup_add_one_lt_of_lt_cof`：sSup_add_one_lt_of_lt_cof {s : Set Or
dinal.{u}} {a : Ordinal.{u}} (ha : #s < (lift.{u + 1} a).cof) (hs : forall i in 
s, i < a) : sSup ((· + …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.mk_range_le_lift`：mk_range_le_lift {α : Type u} {β : Type v} {f
 : α -> β} : lift.{u} #(range f) <= lift.{v} #α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem lift_iSup_add_one_lt_of_lt_cof {f : β → Ordinal.{u}} {a : Ordinal.{u}}
    (ha : Cardinal.lift.{u} #β < (lift.{v} a).cof) (hf : ∀ i, f i < a) : ⨆ i, f i + 1 < a := by
  rw [iSup, range_comp' (· + 1)]
  apply sSup_add_one_lt_of_lt_cof _ (by simpa)
  rw [← Cardinal.lift_lt.{_, v}]
  apply mk_range_le_lift.trans_lt
  rw [← Cardinal.lift_lt.{_, u + 1}] at ha
  simpa [← lift_cof] using ha
/-
**Ordinal.iSup_add_one_lt_of_lt_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_add_one_lt_of_lt_cof {f : α -> Ordinal.{u}} {a : Ordinal.{u}} (ha : #
α < a.cof) (hf : forall i, f i < a) : ⨆ i, f i + 1 < a
参数：ha : #α < a.cof；hf : forall i, f i < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_iSup_add_one_lt_of_lt_cof`：lift_iSup_add_one_lt_of_lt_cof {
f : β -> Ordinal.{u}} {a : Ordinal.{u}} (ha : Cardinal.lift.{u} #β < (lift.{v} a
).cof) (hf : forall i, f i <…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lift_cof`：lift_cof (o : Ordinal.{u}) : Cardinal.lift.{v} (cof o)
 = cof (Ordinal.lift.{v} o)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
-/
theorem iSup_add_one_lt_of_lt_cof {f : α → Ordinal.{u}} {a : Ordinal.{u}}
    (ha : #α < a.cof) (hf : ∀ i, f i < a) : ⨆ i, f i + 1 < a := by
  rw [← Cardinal.lift_lt.{_, u}, lift_cof] at ha
  simpa using lift_iSup_add_one_lt_of_lt_cof ha hf
/-
**Ordinal.lift_iSup_lt_of_lt_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_iSup_lt_of_lt_cof {f : β -> Ordinal.{u}} {a : Ordinal.{u}} (ha : Card
inal.lift.{u} #β < (lift.{v} a).cof) (hf : forall i, f i < a) : ⨆ i, f i < a
参数：ha : Cardinal.lift.{u} #β < (lift.{v} a).cof；hf : forall i, f i < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ordinal.iSup_le_iSup_add_one`：iSup_le_iSup_add_one (f : β -> Ordinal) : 
⨆ i, f i <= ⨆ i, f i + 1
· 使用定理 `Ordinal.lift_iSup_add_one_lt_of_lt_cof`：lift_iSup_add_one_lt_of_lt_cof {
f : β -> Ordinal.{u}} {a : Ordinal.{u}} (ha : Cardinal.lift.{u} #β < (lift.{v} a
).cof) (hf : forall i, f i <…
-/
theorem lift_iSup_lt_of_lt_cof {f : β → Ordinal.{u}} {a : Ordinal.{u}}
    (ha : Cardinal.lift.{u} #β < (lift.{v} a).cof) (hf : ∀ i, f i < a) : ⨆ i, f i < a :=
  (iSup_le_iSup_add_one f).trans_lt (lift_iSup_add_one_lt_of_lt_cof ha hf)
/-
**Ordinal.iSup_lt_of_lt_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_lt_of_lt_cof {f : α -> Ordinal.{u}} {a : Ordinal.{u}} (ha : #α < a.co
f) (hf : forall i, f i < a) : ⨆ i, f i < a
参数：ha : #α < a.cof；hf : forall i, f i < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_iSup_lt_of_lt_cof`：lift_iSup_lt_of_lt_cof {f : β -> Ordinal
.{u}} {a : Ordinal.{u}} (ha : Cardinal.lift.{u} #β < (lift.{v} a).cof) (hf : for
all i, f i < a) : ⨆ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lift_cof`：lift_cof (o : Ordinal.{u}) : Cardinal.lift.{v} (cof o)
 = cof (Ordinal.lift.{v} o)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
-/
theorem iSup_lt_of_lt_cof {f : α → Ordinal.{u}} {a : Ordinal.{u}}
    (ha : #α < a.cof) (hf : ∀ i, f i < a) : ⨆ i, f i < a := by
  rw [← Cardinal.lift_lt.{_, u}, lift_cof] at ha
  simpa using lift_iSup_lt_of_lt_cof ha hf
/-
**Ordinal.cof_lift_iSup_add_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_lift_iSup_add_one_le [Small.{u} β] (f : β -> Ordinal.{u}) : cof (lift.
{v} (⨆ i, f i + 1)) <= Cardinal.lift.{u} (#β)
参数：f : β -> Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Ordinal.lift_iSup_add_one_lt_of_lt_cof`：lift_iSup_add_one_lt_of_lt_cof {
f : β -> Ordinal.{u}} {a : Ordinal.{u}} (ha : Cardinal.lift.{u} #β < (lift.{v} a
).cof) (hf : forall i, f i <…
· 使用定理 `Ordinal.lt_iSup_add_one`：lt_iSup_add_one {ι} (f : ι -> Ordinal.{u}) [Sma
ll.{u} ι] (i) : f i < ⨆ i, f i + 1
-/
theorem cof_lift_iSup_add_one_le [Small.{u} β] (f : β → Ordinal.{u}) :
    cof (lift.{v} (⨆ i, f i + 1)) ≤ Cardinal.lift.{u} (#β) := by
  by_contra! hf
  exact (lift_iSup_add_one_lt_of_lt_cof hf <| Ordinal.lt_iSup_add_one _).false
/-
**Ordinal.cof_iSup_add_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_iSup_add_one_le (f : α -> Ordinal.{u}) : cof (⨆ i, f i + 1) <= #α
参数：f : α -> Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lift_id`：lift_id : forall a, lift.{u, u} a = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Ordinal.cof_lift_iSup_add_one_le`：cof_lift_iSup_add_one_le [Small.{u} β]
 (f : β -> Ordinal.{u}) : cof (lift.{v} (⨆ i, f i + 1)) <= Cardinal.lift.{u} (#β
)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem cof_iSup_add_one_le (f : α → Ordinal.{u}) : cof (⨆ i, f i + 1) ≤ #α := by
  simpa using cof_lift_iSup_add_one_le f
/-
**Ordinal._root_.Cardinal.sSup_lt_of_lt_cof_ord** 是 Mathlib 中的一个定理，位于命名空间 `Ordin
al`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cardinal.sSup_lt_of_lt_cof_ord {s : Set Cardinal.{u}} {a : Cardinal.{u}}
    (ha : #s < (Cardinal.lift.{u + 1} a).ord.cof) (hs : ∀ i ∈ s, i < a) : sSup s < a := by
  rw [← ord_lt_ord, sSup_ord]
  apply Ordinal.sSup_lt_of_lt_cof
  · simpa [mk_image_eq ord_injective]
  · simpa
/-
**Ordinal._root_.Cardinal.lift_iSup_lt_of_lt_cof_ord** 是 Mathlib 中的一个定理，位于命名空间 `
Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cardinal.lift_iSup_lt_of_lt_cof_ord {f : β → Cardinal.{u}} {a : Cardinal.{u}}
    (ha : Cardinal.lift.{u} #β < a.lift.ord.cof) (hf : ∀ i, f i < a) : ⨆ i, f i < a := by
  rw [← ord_lt_ord, iSup_ord]
  apply Ordinal.lift_iSup_lt_of_lt_cof <;> simpa
/-
**Ordinal._root_.Cardinal.iSup_lt_of_lt_cof_ord** 是 Mathlib 中的一个定理，位于命名空间 `Ordin
al`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cardinal.iSup_lt_of_lt_cof_ord {f : α → Cardinal.{u}} {a : Cardinal.{u}}
    (ha : #α < a.ord.cof) (hf : ∀ i, f i < a) : ⨆ i, f i < a := by
  rw [← ord_lt_ord, iSup_ord]
  apply Ordinal.iSup_lt_of_lt_cof <;> simpa

/-- The set in the `lsub` characterization of `cof` is nonempty. -/
@[deprecated "to build an increasing function with limit o, use the fundamental sequence API."
(since := "2026-03-27")]
/-
**Ordinal.cof_lsub_def_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_lsub_def_nonempty (o) : { a : Cardinal | exists (ι : _) (f : ι -> Ordi
nal), lsub.{u, u} f = o ∧ #ι = a }.Nonempty
参数：o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Ordinal.lsub_typein`：lsub_typein (o : Ordinal) : lsub.{u, u} (typein (α
· 使用定理 `Cardinal.mk_toType`：∀ (o : Ordinal.{u_1}), Cardinal.mk o.ToType = o.card
-/
theorem cof_lsub_def_nonempty (o) :
    { a : Cardinal | ∃ (ι : _) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = a }.Nonempty :=
  ⟨_, ⟨_, _, lsub_typein o, mk_toType o⟩⟩

@[deprecated "to build an increasing function with limit o, use the fundamental sequence API."
(since := "2026-03-27")]
/-
**Ordinal.cof_eq_sInf_lsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_eq_sInf_lsub (o : Ordinal.{u}) : cof o = sInf { a : Cardinal | exists 
(ι : Type u) (f : ι -> Ordinal), lsub.{u, u} f = o ∧ #ι = a }
参数：o : Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Ordinal.cof_lsub_def_nonempty`：cof_lsub_def_nonempty (o) : { a : Cardina
l | exists (ι : _) (f : ι -> Ordinal), lsub.{u, u} f = o ∧ #ι = a }.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.cof_iSup_add_one_le`：cof_iSup_add_one_le (f : α -> Ordinal.{u}) 
: cof (⨆ i, f i + 1) <= #α
· 使用定理 `csInf_le'`：csInf_le' (h : a in s) : sInf s <= a
· 使用定理 `Order.cof_eq`：∀ (α : Type u) [inst : Preorder α], ∃ s, IsCofinal s ∧ Car
dinal.mk ↑s = Order.cof α
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Ordinal.lsub_le`：lsub_le {ι} {f : ι -> Ordinal} {a} : (forall i, f i < a
) -> lsub f <= a
· 使用定理 `Ordinal.typein_lt_self`：typein_lt_self {o : Ordinal} (i : o.ToType) : ty
pein (α
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ordinal.typein_enum`：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : typein r (enum r ⟨o, h⟩) = o
· 使用定理 `Ordinal.typein_le_typein`：typein_le_typein (r : α -> α -> Prop) [IsWellO
rder α r] {a b : α} : typein r a <= typein r b ↔ ¬r b a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Ordinal.lt_lsub`：lt_lsub {ι} (f : ι -> Ordinal) (i) : f i < lsub f
· 使用定理 `Ordinal.cof_toType`：cof_toType (o : Ordinal) : Order.cof o.ToType = o.co
f
-/
theorem cof_eq_sInf_lsub (o : Ordinal.{u}) : cof o =
    sInf { a : Cardinal | ∃ (ι : Type u) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = a } := by
  refine le_antisymm (le_csInf (cof_lsub_def_nonempty o) ?_) (csInf_le' ?_)
  · rintro a ⟨ι, f, hf, rfl⟩
    rw [← hf]
    exact cof_iSup_add_one_le f
  · rcases Order.cof_eq (α := o.ToType) with ⟨S, hS, hS'⟩
    let f : S → Ordinal := fun s => typein LT.lt s.val
    refine ⟨S, f, le_antisymm (lsub_le fun i => typein_lt_self (o := o) i)
      (le_of_forall_lt fun a ha => ?_), by rwa [cof_toType] at hS'⟩
    rw [← type_toType o] at ha
    rcases hS (enum (· < ·) ⟨a, ha⟩) with ⟨b, hb, hb'⟩
    rw [← not_lt, ← typein_le_typein, typein_enum] at hb'
    exact hb'.trans_lt (lt_lsub.{u, u} f ⟨b, hb⟩)

@[deprecated "to build an increasing function with limit o, use the fundamental sequence API."
(since := "2026-03-27")]
/-
**Ordinal.exists_lsub_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：exists_lsub_cof (o : Ordinal) : exists (ι : _) (f : ι -> Ordinal), lsub.{u
, u} f = o ∧ #ι = cof o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.cof_eq_sInf_lsub`：cof_eq_sInf_lsub (o : Ordinal.{u}) : cof o = s
Inf { a : Cardinal | exists (ι : Type u) (f : ι -> Ordinal), lsub.{u, u} f = o ∧
 #ι = a }
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
· 使用定理 `Ordinal.cof_lsub_def_nonempty`：cof_lsub_def_nonempty (o) : { a : Cardina
l | exists (ι : _) (f : ι -> Ordinal), lsub.{u, u} f = o ∧ #ι = a }.Nonempty
-/
theorem exists_lsub_cof (o : Ordinal) :
    ∃ (ι : _) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = cof o := by
  rw [cof_eq_sInf_lsub]
  exact csInf_mem (cof_lsub_def_nonempty o)

@[deprecated cof_iSup_add_one_le (since := "2026-03-22")]
/-
**Ordinal.cof_lsub_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_lsub_le {ι} (f : ι -> Ordinal) : cof (lsub.{u, u} f) <= #ι
参数：f : ι -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.cof_iSup_add_one_le`：cof_iSup_add_one_le (f : α -> Ordinal.{u}) 
: cof (⨆ i, f i + 1) <= #α
-/
theorem cof_lsub_le {ι} (f : ι → Ordinal) : cof (lsub.{u, u} f) ≤ #ι :=
  cof_iSup_add_one_le f

@[deprecated cof_lift_iSup_add_one_le (since := "2026-03-22")]
/-
**Ordinal.cof_lsub_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_lsub_le_lift {ι} (f : ι -> Ordinal) : cof (lsub.{u, v} f) <= Cardinal.
lift.{v, u} #ι
参数：f : ι -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lift_id'`：lift_id' (a : Ordinal) : lift a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Ordinal.cof_lift_iSup_add_one_le`：cof_lift_iSup_add_one_le [Small.{u} β]
 (f : β -> Ordinal.{u}) : cof (lift.{v} (⨆ i, f i + 1)) <= Cardinal.lift.{u} (#β
)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem cof_lsub_le_lift {ι} (f : ι → Ordinal) :
    cof (lsub.{u, v} f) ≤ Cardinal.lift.{v, u} #ι := by
  rw [← lift_id'.{u} (lsub f), ← Cardinal.lift_umax.{u, v}]
  exact cof_lift_iSup_add_one_le _

@[deprecated le_cof_iff (since := "2026-03-21")]
/-
**Ordinal.le_cof_iff_lsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_cof_iff_lsub {o : Ordinal} {a : Cardinal} : a <= cof o ↔ forall {ι} (f 
: ι -> Ordinal), lsub.{u, u} f = o -> a <= #ι
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.cof_eq_sInf_lsub`：cof_eq_sInf_lsub (o : Ordinal.{u}) : cof o = s
Inf { a : Cardinal | exists (ι : Type u) (f : ι -> Ordinal), lsub.{u, u} f = o ∧
 #ι = a }
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `le_csInf_iff''`：le_csInf_iff'' {s : Set α} {a : α} (ne : s.Nonempty) : a
 <= sInf s ↔ forall b : α, b in s -> a <= b
· 使用定理 `Ordinal.cof_lsub_def_nonempty`：cof_lsub_def_nonempty (o) : { a : Cardina
l | exists (ι : _) (f : ι -> Ordinal), lsub.{u, u} f = o ∧ #ι = a }.Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_cof_iff_lsub {o : Ordinal} {a : Cardinal} :
    a ≤ cof o ↔ ∀ {ι} (f : ι → Ordinal), lsub.{u, u} f = o → a ≤ #ι := by
  rw [cof_eq_sInf_lsub]
  exact
    (le_csInf_iff'' (cof_lsub_def_nonempty o)).trans
      ⟨fun H ι f hf => H _ ⟨ι, f, hf, rfl⟩, fun H b ⟨ι, f, hf, hb⟩ => by
        rw [← hb]
        exact H _ hf⟩

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/-
**Ordinal.lsub_lt_ord_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_lt_ord_lift {ι} {f : ι -> Ordinal} {c : Ordinal} (hι : Cardinal.lift.
{v, u} #ι < c.cof) (hf : forall i, f i < c) : lsub.{u, v} f < c
参数：hι : Cardinal.lift.{v, u} #ι < c.cof；hf : forall i, f i < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_iSup_add_one_lt_of_lt_cof`：lift_iSup_add_one_lt_of_lt_cof {
f : β -> Ordinal.{u}} {a : Ordinal.{u}} (ha : Cardinal.lift.{u} #β < (lift.{v} a
).cof) (hf : forall i, f i <…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Ordinal.lift_id'`：lift_id' (a : Ordinal) : lift a = a
-/
theorem lsub_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal}
    (hι : Cardinal.lift.{v, u} #ι < c.cof)
    (hf : ∀ i, f i < c) : lsub.{u, v} f < c := by
  apply lift_iSup_add_one_lt_of_lt_cof _ hf
  rwa [Cardinal.lift_umax, c.lift_id']

@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/-
**Ordinal.lsub_lt_ord** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lsub_lt_ord {ι} {f : ι -> Ordinal} {c : Ordinal} (hι : #ι < c.cof) : (fora
ll i, f i < c) -> lsub.{u, u} f < c
参数：hι : #ι < c.cof。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup_add_one_lt_of_lt_cof`：iSup_add_one_lt_of_lt_cof {f : α -> O
rdinal.{u}} {a : Ordinal.{u}} (ha : #α < a.cof) (hf : forall i, f i < a) : ⨆ i, 
f i + 1 < a
-/
theorem lsub_lt_ord {ι} {f : ι → Ordinal} {c : Ordinal} (hι : #ι < c.cof) :
    (∀ i, f i < c) → lsub.{u, u} f < c :=
  iSup_add_one_lt_of_lt_cof hι

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/-
**Ordinal.cof_iSup_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_iSup_le_lift {ι} {f : ι -> Ordinal} (H : forall i, f i < iSup f) : cof
 (iSup f) <= Cardinal.lift.{v, u} #ι
参数：H : forall i, f i < iSup f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Ordinal.lift_iSup_lt_of_lt_cof`：lift_iSup_lt_of_lt_cof {f : β -> Ordinal
.{u}} {a : Ordinal.{u}} (ha : Cardinal.lift.{u} #β < (lift.{v} a).cof) (hf : for
all i, f i < a) : ⨆ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Ordinal.lift_id'`：lift_id' (a : Ordinal) : lift a = a
-/
theorem cof_iSup_le_lift {ι} {f : ι → Ordinal} (H : ∀ i, f i < iSup f) :
    cof (iSup f) ≤ Cardinal.lift.{v, u} #ι := by
  by_contra! hf
  apply (lift_iSup_lt_of_lt_cof _ H).false
  rwa [Cardinal.lift_umax, lift_id']

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
/-
**Ordinal.cof_iSup_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_iSup_le {ι} {f : ι -> Ordinal} (H : forall i, f i < iSup f) : cof (iSu
p f) <= #ι
参数：H : forall i, f i < iSup f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Ordinal.iSup_lt_of_lt_cof`：iSup_lt_of_lt_cof {f : α -> Ordinal.{u}} {a :
 Ordinal.{u}} (ha : #α < a.cof) (hf : forall i, f i < a) : ⨆ i, f i < a
-/
theorem cof_iSup_le {ι} {f : ι → Ordinal} (H : ∀ i, f i < iSup f) :
    cof (iSup f) ≤ #ι := by
  by_contra! hf
  exact (iSup_lt_of_lt_cof hf H).false

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/-
**Ordinal.iSup_lt_ord_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_lt_ord_lift {ι} {f : ι -> Ordinal} {c : Ordinal} (hι : Cardinal.lift.
{v, u} #ι < c.cof) (hf : forall i, f i < c) : iSup f < c
参数：hι : Cardinal.lift.{v, u} #ι < c.cof；hf : forall i, f i < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_iSup_lt_of_lt_cof`：lift_iSup_lt_of_lt_cof {f : β -> Ordinal
.{u}} {a : Ordinal.{u}} (ha : Cardinal.lift.{u} #β < (lift.{v} a).cof) (hf : for
all i, f i < a) : ⨆ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Ordinal.lift_id'`：lift_id' (a : Ordinal) : lift a = a
-/
theorem iSup_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal} (hι : Cardinal.lift.{v, u} #ι < c.cof)
    (hf : ∀ i, f i < c) : iSup f < c := by
  apply lift_iSup_lt_of_lt_cof _ hf
  rwa [Cardinal.lift_umax, lift_id']

@[deprecated (since := "2026-03-22")]
alias iSup_lt_ord := iSup_lt_of_lt_cof

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/-
**Ordinal.iSup_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_lt_lift {ι} {f : ι -> Cardinal} {c : Cardinal} (hι : Cardinal.lift.{v
, u} #ι < c.ord.cof) (hf : forall i, f i < c) : iSup f < c
参数：hι : Cardinal.lift.{v, u} #ι < c.ord.cof；hf : forall i, f i < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_iSup_lt_of_lt_cof_ord`：∀ {β : Type v} {f : β → Cardinal.{u
}} {a : Cardinal.{u}},   Cardinal.lift.{u, v} (Cardinal.mk β) < (Cardinal.lift.{
v, u} a).ord.cof → (∀ (i …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
-/
theorem iSup_lt_lift {ι} {f : ι → Cardinal} {c : Cardinal}
    (hι : Cardinal.lift.{v, u} #ι < c.ord.cof)
    (hf : ∀ i, f i < c) : iSup f < c := by
  apply lift_iSup_lt_of_lt_cof_ord _ hf
  rwa [Cardinal.lift_umax, c.lift_id']

@[deprecated (since := "2026-03-22")]
alias iSup_lt := Cardinal.iSup_lt_of_lt_cof_ord
/-
**Ordinal.nfpFamily_lt_ord_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfpFamily_lt_ord_lift {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : ℵ₀ < cof
 c) (hc' : Cardinal.lift.{v, u} #ι < cof c) (hf : forall (i), forall b < c, f i 
b < c) {a} (ha : a < c) : nfpFamily f a < c
参数：hc : ℵ₀ < cof c；hc' : Cardinal.lift.{v, u} #ι < cof c；hf : forall (i), forall
 b < c, f i b < c；ha : a < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_iSup_lt_of_lt_cof`：lift_iSup_lt_of_lt_cof {f : β -> Ordinal
.{u}} {a : Ordinal.{u}} (ha : Cardinal.lift.{u} #β < (lift.{v} a).cof) (hf : for
all i, f i < a) : ⨆ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Ordinal.lift_id'`：lift_id' (a : Ordinal) : lift a = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Cardinal.mk_list_le_max`：mk_list_le_max (α : Type u) : #(List α) <= max 
ℵ₀ #α
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
-/
theorem nfpFamily_lt_ord_lift {ι} {f : ι → Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : Cardinal.lift.{v, u} #ι < cof c) (hf : ∀ (i), ∀ b < c, f i b < c) {a} (ha : a < c) :
    nfpFamily f a < c := by
  refine lift_iSup_lt_of_lt_cof ?_ (fun l ↦ ?_)
  · rw [Cardinal.lift_umax, c.lift_id']
    apply (Cardinal.lift_le.2 (mk_list_le_max _)).trans_lt
    rw [Cardinal.lift_max]
    apply max_lt <;> simpa
  · induction l with
    | nil => exact ha
    | cons i l H => exact hf _ _ H
/-
**Ordinal.nfpFamily_lt_ord** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfpFamily_lt_ord {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : ℵ₀ < cof c) (
hc' : #ι < cof c) (hf : forall (i), forall b < c, f i b < c) {a} : a < c -> nfpF
amily.{u, u} f a < c
参数：hc : ℵ₀ < cof c；hc' : #ι < cof c；hf : forall (i), forall b < c, f i b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.nfpFamily_lt_ord_lift`：nfpFamily_lt_ord_lift {ι} {f : ι -> Ordin
al -> Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : Cardinal.lift.{v, u} #ι < cof c) (hf
 : forall (i), fora…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem nfpFamily_lt_ord {ι} {f : ι → Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : #ι < cof c)
    (hf : ∀ (i), ∀ b < c, f i b < c) {a} : a < c → nfpFamily.{u, u} f a < c :=
  nfpFamily_lt_ord_lift hc (by rwa [(#ι).lift_id]) hf
/-
**Ordinal.nfp_lt_ord** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_lt_ord {f : Ordinal -> Ordinal} {c} (hc : ℵ₀ < cof c) (hf : forall i <
 c, f i < c) {a} : a < c -> nfp f a < c
参数：hc : ℵ₀ < cof c；hf : forall i < c, f i < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.nfpFamily_lt_ord_lift`：nfpFamily_lt_ord_lift {ι} {f : ι -> Ordin
al -> Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : Cardinal.lift.{v, u} #ι < cof c) (hf
 : forall (i), fora…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀
-/
theorem nfp_lt_ord {f : Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hf : ∀ i < c, f i < c) {a} :
    a < c → nfp f a < c :=
  nfpFamily_lt_ord_lift hc (by simpa using Cardinal.one_lt_aleph0.trans hc) fun _ => hf

@[deprecated exists_lsub_cof (since := "2026-03-21")]
/-
**Ordinal.exists_blsub_cof** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：exists_blsub_cof (o : Ordinal) : exists f : forall a < (cof o).ord, Ordina
l, blsub.{u, u} _ f = o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.exists_lsub_cof`：exists_lsub_cof (o : Ordinal) : exists (ι : _) 
(f : ι -> Ordinal), lsub.{u, u} f = o ∧ #ι = cof o
· 使用定理 `Cardinal.exists_ord_eq`：exists_ord_eq (α) : exists (r : α -> α -> Prop) 
(_ : IsWellOrder α r), ord #α = type r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.blsub_eq_lsub'`：blsub_eq_lsub' {ι : Type u} (r : ι -> ι -> Prop)
 [IsWellOrder ι r] (f : ι -> Ordinal.{max u v}) : blsub.{_, v} _ (bfamilyOfFamil
y' r f) = ls…
-/
theorem exists_blsub_cof (o : Ordinal) :
    ∃ f : ∀ a < (cof o).ord, Ordinal, blsub.{u, u} _ f = o := by
  rcases exists_lsub_cof o with ⟨ι, f, hf, hι⟩
  rcases Cardinal.exists_ord_eq ι with ⟨r, hr, hι'⟩
  rw [← @blsub_eq_lsub' ι r hr] at hf
  rw [← hι, hι']
  exact ⟨_, hf⟩

@[deprecated le_cof_iff (since := "2026-03-21")]
/-
**Ordinal.le_cof_iff_blsub** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_cof_iff_blsub {b : Ordinal} {a : Cardinal} : a <= cof b ↔ forall {o} (f
 : forall a < o, Ordinal), blsub.{u, u} o f = b -> a <= o.card
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Ordinal.le_cof_iff_lsub`：le_cof_iff_lsub {o : Ordinal} {a : Cardinal} : 
a <= cof o ↔ forall {ι} (f : ι -> Ordinal), lsub.{u, u} f = o -> a <= #ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_toType`：∀ (o : Ordinal.{u_1}), Cardinal.mk o.ToType = o.card
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `Cardinal.exists_ord_eq`：exists_ord_eq (α) : exists (r : α -> α -> Prop) 
(_ : IsWellOrder α r), ord #α = type r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.blsub_eq_lsub'`：blsub_eq_lsub' {ι : Type u} (r : ι -> ι -> Prop)
 [IsWellOrder ι r] (f : ι -> Ordinal.{max u v}) : blsub.{_, v} _ (bfamilyOfFamil
y' r f) = ls…
-/
theorem le_cof_iff_blsub {b : Ordinal} {a : Cardinal} :
    a ≤ cof b ↔ ∀ {o} (f : ∀ a < o, Ordinal), blsub.{u, u} o f = b → a ≤ o.card :=
  le_cof_iff_lsub.trans
    ⟨fun H o f hf => by simpa using H _ hf, fun H ι f hf => by
      rcases Cardinal.exists_ord_eq ι with ⟨r, hr, hι'⟩
      rw [← @blsub_eq_lsub' ι r hr] at hf
      simpa using H _ hf⟩

@[deprecated cof_lift_iSup_add_one_le (since := "2026-03-22")]
/-
**Ordinal.cof_blsub_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_blsub_le_lift {o} (f : forall a < o, Ordinal) : cof (blsub.{u, v} o f)
 <= Cardinal.lift.{v, u} o.card
参数：f : forall a < o, Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_toType`：∀ (o : Ordinal.{u_1}), Cardinal.mk o.ToType = o.card
· 使用定理 `Ordinal.cof_lsub_le_lift`：cof_lsub_le_lift {ι} (f : ι -> Ordinal) : cof 
(lsub.{u, v} f) <= Cardinal.lift.{v, u} #ι
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
-/
theorem cof_blsub_le_lift {o} (f : ∀ a < o, Ordinal) :
    cof (blsub.{u, v} o f) ≤ Cardinal.lift.{v, u} o.card := by
  rw [← mk_toType o]
  exact cof_lsub_le_lift _

@[deprecated cof_iSup_add_one_le (since := "2026-03-22")]
/-
**Ordinal.cof_blsub_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_blsub_le {o} (f : forall a < o, Ordinal) : cof (blsub.{u, u} o f) <= o
.card
参数：f : forall a < o, Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Ordinal.cof_blsub_le_lift`：cof_blsub_le_lift {o} (f : forall a < o, Ordi
nal) : cof (blsub.{u, v} o f) <= Cardinal.lift.{v, u} o.card
-/
theorem cof_blsub_le {o} (f : ∀ a < o, Ordinal) : cof (blsub.{u, u} o f) ≤ o.card := by
  rw [← o.card.lift_id]
  exact cof_blsub_le_lift f

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/-
**Ordinal.blsub_lt_ord_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_lt_ord_lift {o : Ordinal.{u}} {f : forall a < o, Ordinal} {c : Ordin
al} (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : forall i hi, f i hi < c) : 
blsub.{u, v} o f < c
参数：ho : Cardinal.lift.{v, u} o.card < c.cof；hf : forall i hi, f i hi < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ordinal.blsub_le`：blsub_le {o : Ordinal} {f : forall b < o, Ordinal} {a}
 : (forall i h, f i h < a) -> blsub o f <= a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lift_card`：lift_card (a) : Cardinal.lift.{u, v} (card a) = card 
(lift.{u} a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ordinal.cof_blsub_le_lift`：cof_blsub_le_lift {o} (f : forall a < o, Ordi
nal) : cof (blsub.{u, v} o f) <= Cardinal.lift.{v, u} o.card
-/
theorem blsub_lt_ord_lift {o : Ordinal.{u}} {f : ∀ a < o, Ordinal} {c : Ordinal}
    (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : ∀ i hi, f i hi < c) : blsub.{u, v} o f < c :=
  lt_of_le_of_ne (blsub_le hf) fun h =>
    ho.not_ge (by simpa [← iSup_ord, hf, h] using cof_blsub_le_lift.{u, v} f)

@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/-
**Ordinal.blsub_lt_ord** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：blsub_lt_ord {o : Ordinal} {f : forall a < o, Ordinal} {c : Ordinal} (ho :
 o.card < c.cof) (hf : forall i hi, f i hi < c) : blsub.{u, u} o f < c
参数：ho : o.card < c.cof；hf : forall i hi, f i hi < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.blsub_lt_ord_lift`：blsub_lt_ord_lift {o : Ordinal.{u}} {f : fora
ll a < o, Ordinal} {c : Ordinal} (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf 
: forall i hi, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem blsub_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof)
    (hf : ∀ i hi, f i hi < c) : blsub.{u, u} o f < c :=
  blsub_lt_ord_lift (by rwa [o.card.lift_id]) hf

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/-
**Ordinal.cof_bsup_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_bsup_le_lift {o : Ordinal} {f : forall a < o, Ordinal} (H : forall i h
, f i h < bsup.{u, v} o f) : cof (bsup.{u, v} o f) <= Cardinal.lift.{v, u} o.car
d
参数：H : forall i h, f i h < bsup.{u, v} o f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.bsup_eq_blsub_iff_lt_bsup`：bsup_eq_blsub_iff_lt_bsup {o : Ordina
l.{u}} (f : forall a < o, Ordinal.{max u v}) : bsup.{_, v} o f = blsub.{_, v} o 
f ↔ forall i hi, f i hi…
· 使用定理 `Ordinal.cof_blsub_le_lift`：cof_blsub_le_lift {o} (f : forall a < o, Ordi
nal) : cof (blsub.{u, v} o f) <= Cardinal.lift.{v, u} o.card
-/
theorem cof_bsup_le_lift {o : Ordinal} {f : ∀ a < o, Ordinal} (H : ∀ i h, f i h < bsup.{u, v} o f) :
    cof (bsup.{u, v} o f) ≤ Cardinal.lift.{v, u} o.card := by
  rw [← bsup_eq_blsub_iff_lt_bsup.{u, v}] at H
  rw [H]
  exact cof_blsub_le_lift.{u, v} f

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
/-
**Ordinal.cof_bsup_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_bsup_le {o : Ordinal} {f : forall a < o, Ordinal} : (forall i h, f i h
 < bsup.{u, u} o f) -> cof (bsup.{u, u} o f) <= o.card
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Ordinal.cof_bsup_le_lift`：cof_bsup_le_lift {o : Ordinal} {f : forall a <
 o, Ordinal} (H : forall i h, f i h < bsup.{u, v} o f) : cof (bsup.{u, v} o f) <
= Cardinal.lif…
-/
theorem cof_bsup_le {o : Ordinal} {f : ∀ a < o, Ordinal} :
    (∀ i h, f i h < bsup.{u, u} o f) → cof (bsup.{u, u} o f) ≤ o.card := by
  rw [← o.card.lift_id]
  exact cof_bsup_le_lift

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/-
**Ordinal.bsup_lt_ord_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_lt_ord_lift {o : Ordinal} {f : forall a < o, Ordinal} {c : Ordinal} (
ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : forall i hi, f i hi < c) : bsup.
{u, v} o f < c
参数：ho : Cardinal.lift.{v, u} o.card < c.cof；hf : forall i hi, f i hi < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ordinal.bsup_le_blsub`：bsup_le_blsub {o : Ordinal.{u}} (f : forall a < o
, Ordinal.{max u v}) : bsup.{_, v} o f <= blsub.{_, v} o f
· 使用定理 `Ordinal.blsub_lt_ord_lift`：blsub_lt_ord_lift {o : Ordinal.{u}} {f : fora
ll a < o, Ordinal} {c : Ordinal} (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf 
: forall i hi, …
-/
theorem bsup_lt_ord_lift {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal}
    (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : ∀ i hi, f i hi < c) : bsup.{u, v} o f < c :=
  (bsup_le_blsub f).trans_lt (blsub_lt_ord_lift ho hf)

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
/-
**Ordinal.bsup_lt_ord** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bsup_lt_ord {o : Ordinal} {f : forall a < o, Ordinal} {c : Ordinal} (ho : 
o.card < c.cof) : (forall i hi, f i hi < c) -> bsup.{u, u} o f < c
参数：ho : o.card < c.cof。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bsup_lt_ord_lift`：bsup_lt_ord_lift {o : Ordinal} {f : forall a <
 o, Ordinal} {c : Ordinal} (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : fora
ll i hi, f i h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem bsup_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof) :
    (∀ i hi, f i hi < c) → bsup.{u, u} o f < c :=
  bsup_lt_ord_lift (by rwa [o.card.lift_id])

/-! ### Cofinality arithmetic -/

@[simp]
/-
**Ordinal.cof_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_add (a : Ordinal) {b : Ordinal} (hb : b != 0) : cof (a + b) = cof b
参数：a : Ordinal；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.zero_or_succ_or_isSuccLimit`：zero_or_succ_or_isSuccLimit (o : Or
dinal) : o = 0 ∨ o in range succ ∨ IsSuccLimit o
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Ordinal.cof_add_one`：cof_add_one (o) : cof (o + 1) = 1
· 使用定理 `Ordinal.cof_map_of_isNormal`：cof_map_of_isNormal {f} (hf : IsNormal f) {
a} (ha : IsSuccLimit a) : cof (f a) = cof a
· 使用定理 `Ordinal.isNormal_add_right`：isNormal_add_right (a : Ordinal) : IsNormal 
(a + ·)

--- 原说明 ---
### Cofinality arithmetic
-/
theorem cof_add (a : Ordinal) {b : Ordinal} (hb : b ≠ 0) : cof (a + b) = cof b := by
  rcases zero_or_succ_or_isSuccLimit b with (rfl | ⟨c, rfl⟩ | hb)
  · contradiction
  · rw [succ_eq_add_one, ← add_assoc, cof_add_one, cof_add_one]
  · exact cof_map_of_isNormal (isNormal_add_right a) hb

@[simp]
/-
**Ordinal.cof_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_mul {a b : Ordinal} (ha : a != 0) (hb : IsSuccPrelimit b) : cof (a * b
) = cof b
参数：ha : a != 0；hb : IsSuccPrelimit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMin.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsMin a → a = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Ordinal.cof_zero`：cof_zero : cof 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ordinal.cof_map_of_isNormal`：cof_map_of_isNormal {f} (hf : IsNormal f) {
a} (ha : IsSuccLimit a) : cof (f a) = cof a
· 使用定理 `Ordinal.isNormal_mul_right`：isNormal_mul_right {a : Ordinal} (h : 0 < a)
 : IsNormal (a * ·)
· 使用定理 `Ne.pos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem cof_mul {a b : Ordinal} (ha : a ≠ 0) (hb : IsSuccPrelimit b) : cof (a * b) = cof b := by
  by_cases hb' : IsMin b
  · simp [hb'.eq_bot]
  · exact cof_map_of_isNormal (isNormal_mul_right ha.pos) ⟨hb', hb⟩

@[simp]
/-
**Ordinal.cof_preOmega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_preOmega {o : Ordinal} (ho : IsSuccPrelimit o) : (preOmega o).cof = o.
cof
参数：ho : IsSuccPrelimit o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMin.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsMin a → a = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Ordinal.preOmega_zero`：preOmega_zero : preOmega 0 = 0
· 使用定理 `Ordinal.cof_zero`：cof_zero : cof 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ordinal.cof_map_of_isNormal`：cof_map_of_isNormal {f} (hf : IsNormal f) {
a} (ha : IsSuccLimit a) : cof (f a) = cof a
· 使用定理 `Ordinal.isNormal_preOmega`：isNormal_preOmega : IsNormal preOmega
-/
theorem cof_preOmega {o : Ordinal} (ho : IsSuccPrelimit o) : (preOmega o).cof = o.cof := by
  by_cases h : IsMin o
  · simp [h.eq_bot]
  · exact cof_map_of_isNormal isNormal_preOmega ⟨h, ho⟩

@[simp]
/-
**Ordinal.cof_omega** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_omega {o : Ordinal} (ho : IsSuccLimit o) : (ω_ o).cof = o.cof
参数：ho : IsSuccLimit o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.cof_map_of_isNormal`：cof_map_of_isNormal {f} (hf : IsNormal f) {
a} (ha : IsSuccLimit a) : cof (f a) = cof a
· 使用定理 `Ordinal.isNormal_omega`：isNormal_omega : IsNormal omega
-/
theorem cof_omega {o : Ordinal} (ho : IsSuccLimit o) : (ω_ o).cof = o.cof :=
  cof_map_of_isNormal isNormal_omega ho

@[deprecated Order.cof_eq (since := "2026-03-20")]
/-
**Ordinal.cof_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_eq' (r : α -> α -> Prop) [H : IsWellOrder α r] (h : IsSuccLimit (type 
r)) : exists S : Set α, (forall a, exists b in S, r a b) ∧ #S = cof (type r)
参数：r : α -> α -> Prop；h : IsSuccLimit (type r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Ordinal.isSuccPrelimit_type_lt_iff`：isSuccPrelimit_type_lt_iff [LinearOr
der α] [WellFoundedLT α] : IsSuccPrelimit (typeLT α) ↔ NoMaxOrder α
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `Order.exists_cof_eq`：exists_cof_eq : exists s : Set α, IsCofinal s ∧ #s 
= cof α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_bddAbove_iff`：not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set 
α} : ¬BddAbove s ↔ forall x, exists y in s, x < y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_bddAbove_iff_isCofinal`：not_bddAbove_iff_isCofinal [NoMaxOrder α] {s
 : Set α} : ¬ BddAbove s ↔ IsCofinal s
-/
theorem cof_eq' (r : α → α → Prop) [H : IsWellOrder α r] (h : IsSuccLimit (type r)) :
    ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ #S = cof (type r) := by
  classical
  let := linearOrderOfSTO r
  have : WellFoundedLT α := H.toIsWellFounded
  have : NoMaxOrder α := isSuccPrelimit_type_lt_iff.1 h.isSuccPrelimit
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  refine ⟨s, ?_, hs'⟩
  rwa [← not_bddAbove_iff_isCofinal, not_bddAbove_iff] at hs

@[simp]
/-
**Ordinal.cof_univ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cof_univ : cof univ.{u, v} = Cardinal.univ.{u, v}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.univ.eq_1`：Ordinal.univ.{u, v} = Ordinal.lift.{v, u + 1} (Ordina
l.type fun x1 x2 => x1 < x2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lift_cof`：lift_cof (o : Ordinal.{u}) : Cardinal.lift.{v} (cof o)
 = cof (Ordinal.lift.{v} o)
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Ordinal.cof_type`：cof_type (α : Type*) [LinearOrder α] [WellFoundedLT α]
 : (typeLT α).cof = Order.cof α
· 使用定理 `Order.cof_ordinal`：cof_ordinal : cof Ordinal.{u} = Cardinal.univ.{u, u +
 1}
· 使用定理 `Cardinal.lift_univ`：lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w}
· 使用定理 `Cardinal.univ_umax`：univ_umax : univ.{u, max (u + 1) v} = univ.{u, v}
-/
theorem cof_univ : cof univ.{u, v} = Cardinal.univ.{u, v} := by
  rw [univ, ← lift_cof, cof_type, cof_ordinal, Cardinal.lift_univ, Cardinal.univ_umax.{u, v}]

end Ordinal

namespace Cardinal
open Ordinal

/-! ### Results on sets -/

-- TODO: re-state this for a bundled well-order
/-
**Cardinal.mk_bounded_subset** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_bounded_subset {α : Type*} (h : IsStrongPrelimit #α) {r : α -> α -> Pro
p} [IsWellOrder α r] (hr : (#α).ord = type r) : #{ s : Set α // Bounded r s } = 
#α
参数：h : IsStrongPrelimit #α；hr : (#α).ord = type r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.mk_eq_zero_iff`：mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty 
α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.not_unbounded_iff`：not_unbounded_iff {r : α -> α -> Prop} (s : Set α
) : ¬Unbounded r s ↔ Bounded r s
· 使用定理 `Set.unbounded_of_isEmpty`：unbounded_of_isEmpty [IsEmpty α] {r : α -> α -
> Prop} (s : Set α) : Unbounded r s
· 使用定理 `Cardinal.IsStrongLimit.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsStrongLimi
t → Cardinal.aleph0 ≤ c
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.coe_ofPred`：Set.coe_ofPred (p : α -> Prop) : ↥{ x | p x } = { x // p
 x }
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_iUnion_le_sum_mk`：mk_iUnion_le_sum_mk {α ι : Type u} {f : ι 
-> Set α} : #(⋃ i, f i) <= sum fun i => #(f i)
· 使用定理 `Cardinal.sum_le_mk_mul_iSup`：sum_le_mk_mul_iSup {ι : Type u} (f : ι -> C
ardinal.{u}) : sum f <= #ι * ⨆ i, f i
· 使用定理 `Cardinal.mul_le_max_of_aleph0_le_left`：mul_le_max_of_aleph0_le_left {a b
 : Cardinal} (h : ℵ₀ <= a) : a * b <= max a b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.mk_powerset`：mk_powerset {α : Type u} (s : Set α) : #(↥(𝒫 s)) =
 2 ^ #(↥s)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.card_typein_lt`：card_typein_lt {r : α -> α -> Prop} [IsWellOrde
r α r] (x : α) (h : ord #α = type r) : card (typein r x) < #α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Cardinal.mk_le_of_injective`：mk_le_of_injective {α β : Type u} {f : α ->
 β} (hf : Injective f) : #α <= #β
· 使用定理 `Ordinal.bounded_singleton`：bounded_singleton {r : α -> α -> Prop} [IsWel
lOrder α r] (hr : IsSuccLimit (type r)) (x) : Bounded r {x}
· 使用定理 `Cardinal.isSuccLimit_ord`：isSuccLimit_ord {c} (hc : ℵ₀ <= c) : IsSuccLim
it (ord c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
-/
theorem mk_bounded_subset {α : Type*} (h : IsStrongPrelimit #α) {r : α → α → Prop}
    [IsWellOrder α r] (hr : (#α).ord = type r) : #{ s : Set α // Bounded r s } = #α := by
  rcases eq_or_ne #α 0 with (ha | ha)
  · rw [ha]
    have := mk_eq_zero_iff.1 ha
    rw [mk_eq_zero_iff]
    constructor
    rintro ⟨s, hs⟩
    exact (not_unbounded_iff s).2 hs (unbounded_of_isEmpty s)
  have h' : IsStrongLimit #α := ⟨ha, @h⟩
  have ha := h'.aleph0_le
  apply le_antisymm
  · have : { s : Set α | Bounded r s } = ⋃ i, 𝒫 { j | r j i } := ofPred_exists _
    rw [← coe_ofPred, this]
    refine mk_iUnion_le_sum_mk.trans ((sum_le_mk_mul_iSup (fun i => #(𝒫 { j | r j i }))).trans
      ((mul_le_max_of_aleph0_le_left ha).trans ?_))
    rw [max_eq_left]
    apply ciSup_le' _
    intro i
    rw [mk_powerset]
    exact (h (card_typein_lt _ hr)).le
  · refine @mk_le_of_injective α _ (fun x => Subtype.mk {x} ?_) ?_
    · apply bounded_singleton
      rw [← hr]
      apply isSuccLimit_ord ha
    · intro a b hab
      simpa [singleton_eq_singleton_iff] using hab
/-
**Cardinal.mk_subset_mk_lt_cof** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_subset_mk_lt_cof {α : Type*} (h : IsStrongPrelimit #α) : #{ s : Set α /
/ #s < cof (#α).ord } = #α
参数：h : IsStrongPrelimit #α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.ord_zero`：ord_zero : ord 0 = 0
· 使用定理 `Ordinal.cof_zero`：cof_zero : cof 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Cardinal.exists_ord_eq`：exists_ord_eq (α) : exists (r : α -> α -> Prop) 
(_ : IsWellOrder α r), ord #α = type r
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_bounded_subset`：mk_bounded_subset {α : Type*} (h : IsStrongP
relimit #α) {r : α -> α -> Prop} [IsWellOrder α r] (hr : (#α).ord = type r) : #{
 s : Set α // Bo…
· 使用定理 `Cardinal.mk_subtype_le_of_subset`：mk_subtype_le_of_subset {α : Type u} {
p q : α -> Prop} (h : forall ⦃x⦄, p x -> q x) : #(Subtype p) <= #(Subtype q)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Order.cof_le`：cof_le {s : Set α} (h : IsCofinal s) : cof α <= #s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.not_bounded_iff`：not_bounded_iff {r : α -> α -> Prop} (s : Set α) : 
¬Bounded r s ↔ Unbounded r s
· 使用定理 `Cardinal.mk_le_of_injective`：mk_le_of_injective {α β : Type u} {f : α ->
 β} (hf : Injective f) : #α <= #β
· 使用定理 `Cardinal.mk_singleton`：mk_singleton {α : Type u} (x : α) : #({x} : Set α
) = 1
· 使用定理 `Ordinal.one_lt_cof_iff`：one_lt_cof_iff {o : Ordinal} : 1 < cof o ↔ IsSuc
cLimit o
· 使用定理 `Cardinal.isSuccLimit_ord`：isSuccLimit_ord {c} (hc : ℵ₀ <= c) : IsSuccLim
it (ord c)
· 使用定理 `Cardinal.IsStrongLimit.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsStrongLimi
t → Cardinal.aleph0 ≤ c
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
-/
theorem mk_subset_mk_lt_cof {α : Type*} (h : IsStrongPrelimit #α) :
    #{ s : Set α // #s < cof (#α).ord } = #α := by
  rcases eq_or_ne #α 0 with (ha | ha)
  · simp [ha]
  have h' : IsStrongLimit #α := ⟨ha, @h⟩
  rcases exists_ord_eq α with ⟨r, wo, hr⟩
  classical
  let := linearOrderOfSTO r
  apply le_antisymm
  · conv_rhs => rw [← mk_bounded_subset h hr]
    apply mk_subtype_le_of_subset
    intro s hs
    rw [hr] at hs
    contrapose! hs
    rw [not_bounded_iff] at hs
    apply cof_le
    simp_rw [IsCofinal, ← not_lt]
    exact hs
  · refine @mk_le_of_injective α _ (fun x => Subtype.mk {x} ?_) ?_
    · rw [mk_singleton, one_lt_cof_iff]
      exact isSuccLimit_ord h'.aleph0_le
    · intro a b hab
      simpa [singleton_eq_singleton_iff] using hab

@[deprecated (since := "2026-02-25")]
alias unbounded_of_unbounded_sUnion := isCofinal_of_isCofinal_sUnion
@[deprecated (since := "2026-02-25")]
alias unbounded_of_unbounded_iUnion := isCofinal_of_isCofinal_iUnion

/-! ### Consequences of König's lemma -/

/-
**Cardinal.lt_power_cof_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_power_cof_ord {c : Cardinal} (hc : ℵ₀ <= c) : c < c ^ c.ord.cof
参数：hc : ℵ₀ <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Cardinal.exists_ord_eq_type_lt`：exists_ord_eq_type_lt (α) : exists (_ : 
LinearOrder α) (_ : WellFoundedLT α), ord #α = typeLT α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.isSuccPrelimit_type_lt_iff`：isSuccPrelimit_type_lt_iff [LinearOr
der α] [WellFoundedLT α] : IsSuccPrelimit (typeLT α) ↔ NoMaxOrder α
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `Cardinal.isSuccLimit_ord`：isSuccLimit_ord {c} (hc : ℵ₀ <= c) : IsSuccLim
it (ord c)
· 使用定理 `Ordinal.exists_ord_cof_eq`：exists_ord_cof_eq [LinearOrder α] [WellFounde
dLT α] : exists s : Set α, IsCofinal s ∧ typeLT s = (Order.cof α).ord
· 使用定理 `Ordinal.cof_type`：cof_type (α : Type*) [LinearOrder α] [WellFoundedLT α]
 : (typeLT α).cof = Order.cof α
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `Ordinal.card_type`：card_type (r : α -> α -> Prop) [IsWellOrder α r] : ca
rd (type r) = #α
· 使用定理 `Cardinal.prod_const'`：prod_const' (ι : Type u) (a : Cardinal.{u}) : (pro
d fun _ : ι => a) = a ^ #ι
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `Cardinal.mk_iUnion_le_sum_mk`：mk_iUnion_le_sum_mk {α ι : Type u} {f : ι 
-> Set α} : #(⋃ i, f i) <= sum fun i => #(f i)
· 使用定理 `Cardinal.mk_univ`：mk_univ {α : Type u} : #(@univ α) = #α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCofinal_iff_iUnion_Iio_eq_univ`：isCofinal_iff_iUnion_Iio_eq_univ [NoMa
xOrder α] {s : Set α} : IsCofinal s ↔ ⋃ i in s, Iio i = univ where mpr hs
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Cardinal.sum_lt_prod`：sum_lt_prod {ι} (f g : ι -> Cardinal) (H : forall 
i, f i < g i) : sum f < prod g
· 使用定理 `Cardinal.mk_Iio_lt`：mk_Iio_lt [LinearOrder α] [WellFoundedLT α] (i : α) 
(h : ord #α = typeLT α) : #(Iio i) < #α

--- 原说明 ---
### Consequences of König's lemma
-/
theorem lt_power_cof_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : c < c ^ c.ord.cof := by
  induction c using Cardinal.inductionOn with | mk α
  obtain ⟨_, _, hα⟩ := exists_ord_eq_type_lt α
  have : NoMaxOrder α := by
    rw [← isSuccPrelimit_type_lt_iff, ← hα]
    exact (isSuccLimit_ord hc).isSuccPrelimit
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq α
  rw [hα, cof_type, ← card_ord (Order.cof _), ← hs', card_type, ← prod_const']
  refine (mk_iUnion_le_sum_mk.trans' ?_).trans_lt (sum_lt_prod _ _ fun i ↦ mk_Iio_lt i.1 hα)
  rw [← mk_univ, ← isCofinal_iff_iUnion_Iio_eq_univ.1 hs, iUnion_coe_set]

@[deprecated (since := "2026-03-30")]
alias lt_power_cof := lt_power_cof_ord
/-
**Cardinal.lt_cof_ord_power** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_cof_ord_power {a b : Cardinal} (ha : ℵ₀ <= a) (hb : 1 < b) : a < (b ^ a
).ord.cof
参数：ha : ℵ₀ <= a；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `Cardinal.power_le_power_left`：power_le_power_left : forall {a b c : Card
inal}, a != 0 -> b <= c -> a ^ b <= a ^ c
· 使用定理 `Cardinal.power_ne_zero`：power_ne_zero {a : Cardinal} (b : Cardinal) : a 
!= 0 -> a ^ b != 0
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.power_mul`：power_mul {a b c : Cardinal} : a ^ (b * c) = (a ^ b)
 ^ c
· 使用定理 `Cardinal.mul_eq_self`：mul_eq_self {c : Cardinal} (hc : ℵ₀ <= c) : c * c 
= c
· 使用定理 `Cardinal.lt_power_cof_ord`：lt_power_cof_ord {c : Cardinal} (hc : ℵ₀ <= c
) : c < c ^ c.ord.cof
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.cantor'`：cantor' (a) {b : Cardinal} (hb : 1 < b) : a < b ^ a
-/
theorem lt_cof_ord_power {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : 1 < b) : a < (b ^ a).ord.cof := by
  apply lt_imp_lt_of_le_imp_le (power_le_power_left <| power_ne_zero a hb.ne_bot)
  rw [← power_mul, mul_eq_self ha]
  exact lt_power_cof_ord (ha.trans <| (cantor' _ hb).le)

@[deprecated (since := "2026-03-30")]
alias lt_cof_power := lt_cof_ord_power

end Cardinal

