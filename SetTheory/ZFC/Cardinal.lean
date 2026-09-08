/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.ZFC.Basic

/-!
# Cardinalities of ZFC sets

In this file, we define the cardinalities of ZFC sets as `ZFSet.{u} → Cardinal.{u}`.

## Definitions

* `ZFSet.card`: Cardinality of a ZFC set.
-/

@[expose] public section

universe u v

open Cardinal

namespace ZFSet

/-- The cardinality of a ZFC set. -/
/-
**ZFSet.card** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：card (x : ZFSet.{u}) : Cardinal.{u}
参数：x : ZFSet.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cardinality of a ZFC set.
-/
def card (x : ZFSet.{u}) : Cardinal.{u} := #(Shrink x)

variable {x y : ZFSet.{u}}

/-- `ZFSet.card x` is equal to the cardinality of `x` as a set of `ZFSet`s. -/
/-
**ZFSet.cardinalMk_coe_sort** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：cardinalMk_coe_sort : #x = lift.{u + 1, u} (card x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.card.eq_1`：∀ (x : ZFSet.{u}), x.card = Cardinal.mk (Shrink.{u, u +
 1} ↥x)
· 使用定理 `Cardinal.lift_mk_shrink''`：lift_mk_shrink'' (α : Type max u v) [Small.{v
} α] : Cardinal.lift.{u} #(Shrink.{v} α) = #α

--- 原说明 ---
`ZFSet.card x` is equal to the cardinality of `x` as a set of `ZFSet`s.
-/
theorem cardinalMk_coe_sort : #x = lift.{u + 1, u} (card x) := by
  rw [card, lift_mk_shrink'']

@[gcongr]
/-
**ZFSet.card_mono** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：card_mono (h : x subseteq y) : card x <= card y
参数：h : x subseteq y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.cardinalMk_coe_sort`：cardinalMk_coe_sort : #x = lift.{u + 1, u} (c
ard x)
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ZFSet.coe_subset_coe`：coe_subset_coe : (x : Set ZFSet.{u}) subseteq y ↔ 
x subseteq y
-/
theorem card_mono (h : x ⊆ y) : card x ≤ card y := by
  simpa [cardinalMk_coe_sort] using mk_le_mk_of_subset (coe_subset_coe.2 h)

@[simp]
/-
**ZFSet.card_empty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：card_empty : card ∅ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `ZFSet.cardinalMk_coe_sort`：cardinalMk_coe_sort : #x = lift.{u + 1, u} (c
ard x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `Cardinal.lift_zero`：lift_zero : lift 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_empty : card ∅ = 0 := by
  rw [← lift_inj, ← cardinalMk_coe_sort]
  simp
/-
**ZFSet.card_insert_le** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：card_insert_le : card (insert x y) <= card y + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Cardinal.mk_insert_le`：mk_insert_le {α : Type u} {s : Set α} {a : α} : #
(insert a s : Set α) <= #s + 1
-/
theorem card_insert_le : card (insert x y) ≤ card y + 1 := by
  rw [← lift_le.{u + 1}]
  simpa [← cardinalMk_coe_sort] using! mk_insert_le
/-
**ZFSet.card_insert** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：card_insert (h : x ∉ y) : card (insert x y) = card y + 1
参数：h : x ∉ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Cardinal.mk_insert`：mk_insert {α : Type u} {s : Set α} {a : α} (h : a ∉ 
s) : #(insert a s : Set α) = #s + 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
-/
theorem card_insert (h : x ∉ y) : card (insert x y) = card y + 1 := by
  rw [← lift_inj.{u, u + 1}]
  simpa [← cardinalMk_coe_sort] using! mk_insert (SetLike.mem_coe.not.2 h)

@[simp]
/-
**ZFSet.card_singleton** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：card_singleton : card {x} = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `ZFSet.instLawfulSingleton`：LawfulSingleton ZFSet.{u_1} ZFSet.{u_1}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZFSet.card_empty`：card_empty : card ∅ = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ZFSet.card_insert`：card_insert (h : x ∉ y) : card (insert x y) = card y 
+ 1
· 使用定理 `ZFSet.notMem_empty`：notMem_empty (x) : x ∉ (∅ : ZFSet.{u})
-/
theorem card_singleton : card {x} = 1 := by
  simpa [notMem_singleton] using card_insert (notMem_empty x)
/-
**ZFSet.card_pair_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：card_pair_of_ne (h : x != y) : card {x, y} = 2
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.card_singleton`：card_singleton : card {x} = 1
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `ZFSet.card_insert`：card_insert (h : x ∉ y) : card (insert x y) = card y 
+ 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.notMem_singleton`：notMem_singleton {x y : ZFSet.{u}} : x ∉ ({y} : 
ZFSet.{u}) ↔ x != y
-/
theorem card_pair_of_ne (h : x ≠ y) : card {x, y} = 2 := by
  convert! card_insert (notMem_singleton.2 h)
  rw [card_singleton, one_add_one_eq_two]
/-
**ZFSet.card_union_le** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：card_union_le : card (x union y) <= card x + card y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `Cardinal.mk_union_le`：mk_union_le {α : Type u} (S T : Set α) : #(S union
 T : Set α) <= #S + #T
-/
theorem card_union_le : card (x ∪ y) ≤ card x + card y := by
  rw [← lift_le.{u + 1}]
  simpa [← cardinalMk_coe_sort] using! mk_union_le (x : Set ZFSet) y

@[simp]
/-
**ZFSet.card_powerset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：card_powerset (x : ZFSet.{u}) : card (powerset x) = 2 ^ card x
参数：x : ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.lift_power`：lift_power (a b : Cardinal.{u}) : lift.{v} (a ^ b) 
= lift.{v} a ^ lift.{v} b
· 使用定理 `Cardinal.lift_ofNat`：lift_ofNat (n : Nat) [n.AtLeastTwo] : lift.{u} (ofN
at(n) : Cardinal.{v}) = OfNat.ofNat n
· 使用定理 `Cardinal.mk_powerset`：mk_powerset {α : Type u} (s : Set α) : #(↥(𝒫 s)) =
 2 ^ #(↥s)
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
-/
theorem card_powerset (x : ZFSet.{u}) : card (powerset x) = 2 ^ card x := by
  rw [← lift_inj.{u, u + 1}]
  simpa [← cardinalMk_coe_sort] using mk_congr (powersetEquiv x)
/-
**ZFSet.card_image_le** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：card_image_le {f : ZFSet -> ZFSet} [Definable₁ f] : card (image f x) <= ca
rd x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.cardinalMk_coe_sort`：cardinalMk_coe_sort : #x = lift.{u + 1, u} (c
ard x)
· 使用定理 `Cardinal.mk_image_le`：mk_image_le {α β : Type u} {f : α -> β} {s : Set α
} : #(f '' s) <= #s
-/
theorem card_image_le {f : ZFSet → ZFSet} [Definable₁ f] :
    card (image f x) ≤ card x := by
  simpa [cardinalMk_coe_sort, ← coe_image, -mem_image] using mk_image_le (f := f) (s := x)
/-
**ZFSet.lift_card_range_le** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：lift_card_range_le {α} [Small.{v, u} α] {f : α -> ZFSet.{v}} : lift.{u} (c
ard (range f)) <= lift.{v} #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZFSet.cardinalMk_coe_sort`：cardinalMk_coe_sort : #x = lift.{u + 1, u} (c
ard x)
· 使用定理 `Cardinal.mk_range_le_lift`：mk_range_le_lift {α : Type u} {β : Type v} {f
 : α -> β} : lift.{u} #(range f) <= lift.{v} #α
-/
theorem lift_card_range_le {α} [Small.{v, u} α] {f : α → ZFSet.{v}} :
    lift.{u} (card (range f)) ≤ lift.{v} #α := by
  rw [← lift_le.{max u (v + 1)}, lift_lift.{v}, lift_umax.{u, v + 1}]
  simpa [cardinalMk_coe_sort, ← coe_range, -mem_range] using mk_range_le_lift (f := f)
/-
**ZFSet.iSup_card_le_card_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：iSup_card_le_card_iUnion {α} [Small.{v, u} α] {f : α -> ZFSet.{v}} : ⨆ i, 
card (f i) <= card (⋃ i, f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ZFSet.cardinalMk_coe_sort`：cardinalMk_coe_sort : #x = lift.{u + 1, u} (c
ard x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `Cardinal.iSup_mk_le_mk_iUnion`：iSup_mk_le_mk_iUnion {α : Type u} {ι : Ty
pe v} {f : ι -> Set α} : ⨆ i, #(f i) <= #(⋃ i, f i)
-/
theorem iSup_card_le_card_iUnion {α} [Small.{v, u} α] {f : α → ZFSet.{v}} :
    ⨆ i, card (f i) ≤ card (⋃ i, f i) := by
  simpa [cardinalMk_coe_sort, ← coe_iUnion, ← lift_iSup bddAbove_of_small, -mem_iUnion] using
    iSup_mk_le_mk_iUnion (f := SetLike.coe ∘ f)
/-
**ZFSet.lift_card_iUnion_le_sum_card** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：lift_card_iUnion_le_sum_card {α} [Small.{v, u} α] {f : α -> ZFSet.{v}} : l
ift (card (⋃ i, f i)) <= sum fun i => card (f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_sum`：lift_sum {ι : Type u} (f : ι -> Cardinal.{v}) : Cardi
nal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i)
· 使用定理 `ZFSet.cardinalMk_coe_sort`：cardinalMk_coe_sort : #x = lift.{u + 1, u} (c
ard x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.mk_iUnion_le_sum_mk_lift`：mk_iUnion_le_sum_mk_lift {α : Type u}
 {ι : Type v} {f : ι -> Set α} : lift.{v} #(⋃ i, f i) <= sum fun i => #(f i)
-/
theorem lift_card_iUnion_le_sum_card {α} [Small.{v, u} α] {f : α → ZFSet.{v}} :
    lift (card (⋃ i, f i)) ≤ sum fun i => card (f i) := by
  rw [← lift_le.{max u (v + 1)}, lift_umax.{max u v, v + 1}]
  simpa [cardinalMk_coe_sort, ← coe_iUnion, -mem_iUnion] using
    mk_iUnion_le_sum_mk_lift (f := SetLike.coe ∘ f)

end ZFSet

