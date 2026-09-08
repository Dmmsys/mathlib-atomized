/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Order.Interval.Finset.Basic

/-!
# Finite intervals of integers

This file proves that `ℤ` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as finsets and fintypes.
-/

public section

assert_not_exists Field

open Finset Int

namespace Int

/-
**Int.instLocallyFiniteOrder** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instLocallyFiniteOrder : LocallyFiniteOrder Int where finsetIcc a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder ℤ where
  finsetIcc a b :=
    (Finset.range (b + 1 - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding a
  finsetIco a b := (Finset.range (b - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding a
  finsetIoc a b :=
    (Finset.range (b - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)
  finsetIoo a b :=
    (Finset.range (b - a - 1).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)
  finset_mem_Icc a b x := by
    simp_rw [mem_map, mem_range, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    constructor
    · lia
    · intro
      use (x - a).toNat
      lia
  finset_mem_Ico a b x := by
    simp_rw [mem_map, mem_range, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    constructor
    · lia
    · intro
      use (x - a).toNat
      lia
  finset_mem_Ioc a b x := by
    simp_rw [mem_map, mem_range, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    constructor
    · lia
    · intro
      use (x - (a + 1)).toNat
      lia
  finset_mem_Ioo a b x := by
    simp_rw [mem_map, mem_range, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    constructor
    · lia
    · intro
      use (x - (a + 1)).toNat
      lia

variable (a b : ℤ)
/-
**Int.Icc_eq_finset_map** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：Icc_eq_finset_map : Icc a b = (Finset.range (b + 1 - a).toNat).map (Nat.ca
stEmbedding.trans <| addLeftEmbedding a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_eq_finset_map :
    Icc a b =
      (Finset.range (b + 1 - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl
/-
**Int.Ico_eq_finset_map** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：Ico_eq_finset_map : Ico a b = (Finset.range (b - a).toNat).map (Nat.castEm
bedding.trans <| addLeftEmbedding a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_eq_finset_map :
    Ico a b = (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl
/-
**Int.Ioc_eq_finset_map** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：Ioc_eq_finset_map : Ioc a b = (Finset.range (b - a).toNat).map (Nat.castEm
bedding.trans <| addLeftEmbedding (a + 1))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_eq_finset_map :
    Ioc a b =
      (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl
/-
**Int.Ioo_eq_finset_map** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：Ioo_eq_finset_map : Ioo a b = (Finset.range (b - a - 1).toNat).map (Nat.ca
stEmbedding.trans <| addLeftEmbedding (a + 1))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_eq_finset_map :
    Ioo a b =
      (Finset.range (b - a - 1).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl
/-
**Int.uIcc_eq_finset_map** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：uIcc_eq_finset_map : uIcc a b = (range (max a b + 1 - min a b).toNat).map 
(Nat.castEmbedding.trans <| addLeftEmbedding <| min a b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uIcc_eq_finset_map :
    uIcc a b = (range (max a b + 1 - min a b).toNat).map
      (Nat.castEmbedding.trans <| addLeftEmbedding <| min a b) := rfl

@[simp]
/-
**Int.card_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：card_Icc : #(Icc a b) = (b + 1 - a).toNat
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
-/
theorem card_Icc : #(Icc a b) = (b + 1 - a).toNat := (card_map _).trans <| card_range _

@[simp]
/-
**Int.card_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：card_Ico : #(Ico a b) = (b - a).toNat
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
-/
theorem card_Ico : #(Ico a b) = (b - a).toNat := (card_map _).trans <| card_range _

@[simp]
/-
**Int.card_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：card_Ioc : #(Ioc a b) = (b - a).toNat
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
-/
theorem card_Ioc : #(Ioc a b) = (b - a).toNat := (card_map _).trans <| card_range _

@[simp]
/-
**Int.card_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：card_Ioo : #(Ioo a b) = (b - a - 1).toNat
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
-/
theorem card_Ioo : #(Ioo a b) = (b - a - 1).toNat := (card_map _).trans <| card_range _

@[simp]
/-
**Int.card_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：card_uIcc : #(uIcc a b) = (b - a).natAbs + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.le_add_one`：∀ {a b : ℤ}, a ≤ b → a ≤ b + 1
· 使用定理 `min_le_max`：min_le_max : min a b <= max a b
· 使用定理 `Int.natCast_add`：∀ (n m : ℕ), ↑(n + m) = ↑n + ↑m
· 使用定理 `Int.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = |n|
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `max_sub_min_eq_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : Linea
rOrder α] [AddLeftMono α] [AddRightMono α] (a b : α),   max a b - min a b = |b -
 a|
· 使用定理 `Int.ofNat_one`：↑1 = 1
-/
theorem card_uIcc : #(uIcc a b) = (b - a).natAbs + 1 :=
  (card_map _).trans <|
    (Nat.cast_inj (R := ℤ)).mp <| by
      rw [card_range,
        Int.toNat_of_nonneg (sub_nonneg_of_le <| le_add_one min_le_max), Int.natCast_add,
        Int.natCast_natAbs, add_comm, add_sub_assoc, max_sub_min_eq_abs, add_comm, Int.ofNat_one]
/-
**Int.card_Icc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：card_Icc_of_le (h : a <= b + 1) : (#(Icc a b) : Int) = b + 1 - a
参数：h : a <= b + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.card_Icc`：card_Icc : #(Icc a b) = (b + 1 - a).toNat
· 使用定理 `Int.toNat_sub_of_le`：∀ {a b : ℤ}, b ≤ a → ↑(a - b).toNat = a - b
-/
theorem card_Icc_of_le (h : a ≤ b + 1) : (#(Icc a b) : ℤ) = b + 1 - a := by
  rw [card_Icc, toNat_sub_of_le h]
/-
**Int.card_Ico_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：card_Ico_of_le (h : a <= b) : (#(Ico a b) : Int) = b - a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.card_Ico`：card_Ico : #(Ico a b) = (b - a).toNat
· 使用定理 `Int.toNat_sub_of_le`：∀ {a b : ℤ}, b ≤ a → ↑(a - b).toNat = a - b
-/
theorem card_Ico_of_le (h : a ≤ b) : (#(Ico a b) : ℤ) = b - a := by
  rw [card_Ico, toNat_sub_of_le h]
/-
**Int.card_Ioc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：card_Ioc_of_le (h : a <= b) : (#(Ioc a b) : Int) = b - a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.card_Ioc`：card_Ioc : #(Ioc a b) = (b - a).toNat
· 使用定理 `Int.toNat_sub_of_le`：∀ {a b : ℤ}, b ≤ a → ↑(a - b).toNat = a - b
-/
theorem card_Ioc_of_le (h : a ≤ b) : (#(Ioc a b) : ℤ) = b - a := by
  rw [card_Ioc, toNat_sub_of_le h]
/-
**Int.card_Ioo_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：card_Ioo_of_lt (h : a < b) : (#(Ioo a b) : Int) = b - a - 1
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.card_Ioo`：card_Ioo : #(Ioo a b) = (b - a - 1).toNat
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `Int.toNat_sub_of_le`：∀ {a b : ℤ}, b ≤ a → ↑(a - b).toNat = a - b
-/
theorem card_Ioo_of_lt (h : a < b) : (#(Ioo a b) : ℤ) = b - a - 1 := by
  rw [card_Ioo, sub_sub, toNat_sub_of_le h]
/-
**Int.Icc_eq_pair** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：Icc_eq_pair : Finset.Icc a (a + 1) = {a, a + 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
theorem Icc_eq_pair : Finset.Icc a (a + 1) = {a, a + 1} := by
  ext
  simp
  omega
/-
**Int.card_fintype_Icc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：card_fintype_Icc_of_le (h : a <= b + 1) : (Fintype.card (Set.Icc a b) : In
t) = b + 1 - a
参数：h : a <= b + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `Int.card_Icc`：card_Icc : #(Icc a b) = (b + 1 - a).toNat
· 使用定理 `Int.ofNat_toNat`：∀ (a : ℤ), ↑a.toNat = max a 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_fintype_Icc_of_le (h : a ≤ b + 1) : (Fintype.card (Set.Icc a b) : ℤ) = b + 1 - a := by
  simp [h]
/-
**Int.card_fintype_Ico_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：card_fintype_Ico_of_le (h : a <= b) : (Fintype.card (Set.Ico a b) : Int) =
 b - a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `Int.card_Ico`：card_Ico : #(Ico a b) = (b - a).toNat
· 使用定理 `Int.ofNat_toNat`：∀ (a : ℤ), ↑a.toNat = max a 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_fintype_Ico_of_le (h : a ≤ b) : (Fintype.card (Set.Ico a b) : ℤ) = b - a := by
  simp [h]
/-
**Int.card_fintype_Ioc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：card_fintype_Ioc_of_le (h : a <= b) : (Fintype.card (Set.Ioc a b) : Int) =
 b - a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `Int.card_Ioc`：card_Ioc : #(Ioc a b) = (b - a).toNat
· 使用定理 `Int.ofNat_toNat`：∀ (a : ℤ), ↑a.toNat = max a 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_fintype_Ioc_of_le (h : a ≤ b) : (Fintype.card (Set.Ioc a b) : ℤ) = b - a := by
  simp [h]
/-
**Int.card_fintype_Ioo_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：card_fintype_Ioo_of_lt (h : a < b) : (Fintype.card (Set.Ioo a b) : Int) = 
b - a - 1
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `Int.card_Ioo`：card_Ioo : #(Ioo a b) = (b - a - 1).toNat
· 使用定理 `Int.pred_toNat`：∀ (i : ℤ), (i - 1).toNat = i.toNat - 1
· 使用引理 `Int.toNat_pred_coe_of_pos`：toNat_pred_coe_of_pos {i : Int} (h : 0 < i) :
 ((i.toNat - 1 : Nat) : Int) = i - 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_fintype_Ioo_of_lt (h : a < b) : (Fintype.card (Set.Ioo a b) : ℤ) = b - a - 1 := by
  simp [h]
/-
**Int.image_Ico_emod** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：image_Ico_emod (n a : Int) (h : 0 <= a) : (Ico n (n + a)).image (· % a) = 
Ico 0 a
参数：n a : Int；h : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Int.emod_zero`：∀ (a : ℤ), a % 0 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Int.emod_lt_of_pos`：∀ (a : ℤ) {b : ℤ}, 0 < b → a % b < b
· 使用定理 `Int.emod_add_mul_ediv`：∀ (a b : ℤ), a % b + b * (a / b) = a
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
（共 45 条，此处仅展示前 30 条）
-/
theorem image_Ico_emod (n a : ℤ) (h : 0 ≤ a) : (Ico n (n + a)).image (· % a) = Ico 0 a := by
  obtain rfl | ha := eq_or_lt_of_le h
  · simp
  ext i
  simp only [mem_image, mem_Ico]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨emod_nonneg i ha.ne', emod_lt_of_pos i ha⟩
  rintro ⟨hi₀, hia⟩
  have hn := Int.emod_add_mul_ediv n a
  obtain hi | hi := lt_or_ge i (n % a)
  · refine ⟨i + a * (n / a + 1), ⟨?_, ?_⟩, ?_⟩
    · calc
        n = 0 + n % a + a * (n / a) := by simp [hn]
        _ ≤ i + a + a * (n / a) := by gcongr; exact (Int.emod_lt_of_pos n ha).le
        _ = i + a * (n / a + 1) := by grind
    · calc
        i + a * (n / a + 1) < n % a + a * (n / a + 1) := by gcongr
        _ = n + a := by rw [mul_add, mul_one, ← add_assoc, hn]
    · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hi₀ hia]
  · refine ⟨i + a * (n / a), ⟨?_, ?_⟩, ?_⟩
    · exact hn.symm.le.trans (add_le_add_left hi _)
    · rw [add_comm n a]
      refine add_lt_add_of_lt_of_le hia (le_trans ?_ hn.le)
      simp only [le_add_iff_nonneg_left]
      exact Int.emod_nonneg n (ne_of_gt ha)
    · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hi₀ hia]

end Int

section Nat

/-
**Finset.Icc_succ_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.Icc_succ_succ (m n : Nat) : Icc (-(m + 1) : Int) (n + 1) = Icc (-m 
: Int) n union {(-(m + 1) : Int), (n + 1 : Int)}
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
· 使用引理 `Finset.union_singleton`：union_singleton (x : α) (s : Finset α) : s union
 {x} = insert x s
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
lemma Finset.Icc_succ_succ (m n : ℕ) :
    Icc (-(m + 1) : ℤ) (n + 1) = Icc (-m : ℤ) n ∪ {(-(m + 1) : ℤ), (n + 1 : ℤ)} := by
  ext
  simp only [mem_Icc, union_insert, union_singleton, mem_insert]
  omega
/-
**Finset.Ico_succ_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.Ico_succ_succ (m n : Nat) : Ico (-(m + 1) : Int) (n + 1) = Ico (-m 
: Int) n union {(-(m + 1) : Int), (n : Int)}
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
· 使用引理 `Finset.union_singleton`：union_singleton (x : α) (s : Finset α) : s union
 {x} = insert x s
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
lemma Finset.Ico_succ_succ (m n : ℕ) :
    Ico (-(m + 1) : ℤ) (n + 1) = Ico (-m : ℤ) n ∪ {(-(m + 1) : ℤ), (n : ℤ)} := by
  ext
  simp only [mem_Ico, union_insert, union_singleton, mem_insert]
  omega
/-
**Finset.Ioc_succ_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.Ioc_succ_succ (m n : Nat) : Ioc (-(m + 1) : Int) (n + 1) = Ioc (-m 
: Int) n union {-(m : Int), (n + 1 : Int)}
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
· 使用引理 `Finset.union_singleton`：union_singleton (x : α) (s : Finset α) : s union
 {x} = insert x s
-/
lemma Finset.Ioc_succ_succ (m n : ℕ) :
    Ioc (-(m + 1) : ℤ) (n + 1) = Ioc (-m : ℤ) n ∪ {-(m : ℤ), (n + 1 : ℤ)} := by
  ext
  simp only [mem_Ioc, union_insert, union_singleton, mem_insert]
  lia
/-
**Finset.Ioo_succ_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.Ioo_succ_succ (m n : Nat) : Ioo (-(m + 1) : Int) (n + 1) = Ioo (-m 
: Int) n union {-(m : Int), (n : Int)}
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
· 使用引理 `Finset.union_singleton`：union_singleton (x : α) (s : Finset α) : s union
 {x} = insert x s
-/
lemma Finset.Ioo_succ_succ (m n : ℕ) :
    Ioo (-(m + 1) : ℤ) (n + 1) = Ioo (-m : ℤ) n ∪ {-(m : ℤ), (n : ℤ)} := by
  ext
  simp only [mem_Ioo, union_insert, union_singleton, mem_insert]
  lia

end Nat

