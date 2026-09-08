/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting elements in an interval with given residue

The theorems in this file generalise `Nat.card_multiples` in
`Mathlib/Data/Nat/Factorization/Basic.lean` to all integer intervals and any fixed residue (not just
zero, which reduces to the multiples). Theorems are given for `Ico` and `Ioc` intervals.
-/

public section


open Finset Int

namespace Int

variable (a b : ℤ) {r : ℤ}


/-
**Int.Ico_filter_modEq_eq** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：Ico_filter_modEq_eq (v : Int) : {x in Ico a b | x ≡ v [ZMOD r]} = {x in Ic
o (a - v) (b - v) | r ∣ x}.map ⟨(· + v), add_left_injective v⟩
参数：v : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Ico_filter_modEq_eq (v : ℤ) :
    {x ∈ Ico a b | x ≡ v [ZMOD r]} =
    {x ∈ Ico (a - v) (b - v) | r ∣ x}.map ⟨(· + v), add_left_injective v⟩ := by
  ext x
  simp_rw [mem_map, mem_filter, mem_Ico, Function.Embedding.coeFn_mk, ← eq_sub_iff_add_eq,
    exists_eq_right, modEq_comm, modEq_iff_dvd, sub_lt_sub_iff_right, sub_le_sub_iff_right]
/-
**Int.Ioc_filter_modEq_eq** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：Ioc_filter_modEq_eq (v : Int) : {x in Ioc a b | x ≡ v [ZMOD r]} = {x in Io
c (a - v) (b - v) | r ∣ x}.map ⟨(· + v), add_left_injective v⟩
参数：v : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Ioc_filter_modEq_eq (v : ℤ) :
    {x ∈ Ioc a b | x ≡ v [ZMOD r]} =
    {x ∈ Ioc (a - v) (b - v) | r ∣ x}.map ⟨(· + v), add_left_injective v⟩ := by
  ext x
  simp_rw [mem_map, mem_filter, mem_Ioc, Function.Embedding.coeFn_mk, ← eq_sub_iff_add_eq,
    exists_eq_right, modEq_comm, modEq_iff_dvd, sub_lt_sub_iff_right, sub_le_sub_iff_right]

variable (hr : 0 < r)
include hr
/-
**Int.Ico_filter_dvd_eq** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：Ico_filter_dvd_eq : {x in Ico a b | r ∣ x} = (Ico ⌈a / (r : Rat)⌉ ⌈b / (r 
: Rat)⌉).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma Ico_filter_dvd_eq :
    {x ∈ Ico a b | r ∣ x} =
      (Ico ⌈a / (r : ℚ)⌉ ⌈b / (r : ℚ)⌉).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩ := by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, ceil_le, lt_ceil, div_le_iff₀, lt_div_iff₀,
    dvd_iff_exists_eq_mul_left, cast_pos.2 hr, ← cast_mul, cast_lt, cast_le]
  aesop
/-
**Int.Ioc_filter_dvd_eq** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：Ioc_filter_dvd_eq : {x in Ioc a b | r ∣ x} = (Ioc ⌊a / (r : Rat)⌋ ⌊b / (r 
: Rat)⌋).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma Ioc_filter_dvd_eq :
    {x ∈ Ioc a b | r ∣ x} =
      (Ioc ⌊a / (r : ℚ)⌋ ⌊b / (r : ℚ)⌋).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩ := by
  ext x
  simp only [mem_map, mem_filter, mem_Ioc, floor_lt, le_floor, div_lt_iff₀, le_div_iff₀,
    dvd_iff_exists_eq_mul_left, cast_pos.2 hr, ← cast_mul, cast_lt, cast_le]
  aesop

/-- There are `⌈b / r⌉ - ⌈a / r⌉` multiples of `r` in `[a, b)`, if `a ≤ b`. -/
/-
**Int.Ico_filter_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：Ico_filter_dvd_card : #{x in Ico a b | r ∣ x} = max (⌈b / (r : Rat)⌉ - ⌈a 
/ (r : Rat)⌉) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.Ico_filter_dvd_eq`：Ico_filter_dvd_eq : {x in Ico a b | r ∣ x} = (Ico
 ⌈a / (r : Rat)⌉ ⌈b / (r : Rat)⌉).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Int.card_Ico`：card_Ico : #(Ico a b) = (b - a).toNat
· 使用定理 `Int.toNat_eq_max`：∀ (a : ℤ), ↑a.toNat = max a 0

--- 原说明 ---
There are `⌈b / r⌉ - ⌈a / r⌉` multiples of `r` in `[a, b)`, if `a ≤ b`.
-/
theorem Ico_filter_dvd_card : #{x ∈ Ico a b | r ∣ x} = max (⌈b / (r : ℚ)⌉ - ⌈a / (r : ℚ)⌉) 0 := by
  rw [Ico_filter_dvd_eq _ _ hr, card_map, card_Ico, toNat_eq_max]

/-- There are `⌊b / r⌋ - ⌊a / r⌋` multiples of `r` in `(a, b]`, if `a ≤ b`. -/
/-
**Int.Ioc_filter_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：Ioc_filter_dvd_card : #{x in Ioc a b | r ∣ x} = max (⌊b / (r : Rat)⌋ - ⌊a 
/ (r : Rat)⌋) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.Ioc_filter_dvd_eq`：Ioc_filter_dvd_eq : {x in Ioc a b | r ∣ x} = (Ioc
 ⌊a / (r : Rat)⌋ ⌊b / (r : Rat)⌋).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Int.card_Ioc`：card_Ioc : #(Ioc a b) = (b - a).toNat
· 使用定理 `Int.toNat_eq_max`：∀ (a : ℤ), ↑a.toNat = max a 0

--- 原说明 ---
There are `⌊b / r⌋ - ⌊a / r⌋` multiples of `r` in `(a, b]`, if `a ≤ b`.
-/
theorem Ioc_filter_dvd_card : #{x ∈ Ioc a b | r ∣ x} = max (⌊b / (r : ℚ)⌋ - ⌊a / (r : ℚ)⌋) 0 := by
  rw [Ioc_filter_dvd_eq _ _ hr, card_map, card_Ioc, toNat_eq_max]

/-- There are `⌈(b - v) / r⌉ - ⌈(a - v) / r⌉` numbers congruent to `v` mod `r` in `[a, b)`,
if `a ≤ b`. -/
/-
**Int.Ico_filter_modEq_card** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：Ico_filter_modEq_card (v : Int) : #{x in Ico a b | x ≡ v [ZMOD r]} = max (
⌈(b - v) / (r : Rat)⌉ - ⌈(a - v) / (r : Rat)⌉) 0
参数：v : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `Int.Ico_filter_modEq_eq`：Ico_filter_modEq_eq (v : Int) : {x in Ico a b |
 x ≡ v [ZMOD r]} = {x in Ico (a - v) (b - v) | r ∣ x}.map ⟨(· + v), add_left_inj
ective v⟩
· 使用引理 `Int.Ico_filter_dvd_eq`：Ico_filter_dvd_eq : {x in Ico a b | r ∣ x} = (Ico
 ⌈a / (r : Rat)⌉ ⌈b / (r : Rat)⌉).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Int.card_Ico`：card_Ico : #(Ico a b) = (b - a).toNat
· 使用定理 `Int.ofNat_toNat`：∀ (a : ℤ), ↑a.toNat = max a 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
There are `⌈(b - v) / r⌉ - ⌈(a - v) / r⌉` numbers congruent to `v` mod `r` in `[
a, b)`,
if `a ≤ b`.
-/
theorem Ico_filter_modEq_card (v : ℤ) :
    #{x ∈ Ico a b | x ≡ v [ZMOD r]} = max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 := by
  simp [Ico_filter_modEq_eq, Ico_filter_dvd_eq, hr]

/-- There are `⌊(b - v) / r⌋ - ⌊(a - v) / r⌋` numbers congruent to `v` mod `r` in `(a, b]`,
if `a ≤ b`. -/
/-
**Int.Ioc_filter_modEq_card** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：Ioc_filter_modEq_card (v : Int) : #{x in Ioc a b | x ≡ v [ZMOD r]} = max (
⌊(b - v) / (r : Rat)⌋ - ⌊(a - v) / (r : Rat)⌋) 0
参数：v : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `Int.Ioc_filter_modEq_eq`：Ioc_filter_modEq_eq (v : Int) : {x in Ioc a b |
 x ≡ v [ZMOD r]} = {x in Ioc (a - v) (b - v) | r ∣ x}.map ⟨(· + v), add_left_inj
ective v⟩
· 使用引理 `Int.Ioc_filter_dvd_eq`：Ioc_filter_dvd_eq : {x in Ioc a b | r ∣ x} = (Ioc
 ⌊a / (r : Rat)⌋ ⌊b / (r : Rat)⌋).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Int.card_Ioc`：card_Ioc : #(Ioc a b) = (b - a).toNat
· 使用定理 `Int.ofNat_toNat`：∀ (a : ℤ), ↑a.toNat = max a 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
There are `⌊(b - v) / r⌋ - ⌊(a - v) / r⌋` numbers congruent to `v` mod `r` in `(
a, b]`,
if `a ≤ b`.
-/
theorem Ioc_filter_modEq_card (v : ℤ) :
    #{x ∈ Ioc a b | x ≡ v [ZMOD r]} = max (⌊(b - v) / (r : ℚ)⌋ - ⌊(a - v) / (r : ℚ)⌋) 0 := by
  simp [Ioc_filter_modEq_eq, Ioc_filter_dvd_eq, hr]

end Int

namespace Nat

variable (a b : ℕ) {r : ℕ}

/-
**Nat.Ico_filter_modEq_cast** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：Ico_filter_modEq_cast {v : Nat} : {x in Ico a b | x ≡ v [MOD r]}.map castE
mbedding = {x in Ico (a : Int) (b : Int) | x ≡ v [ZMOD r]}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.castEmbedding_apply`：∀ {R : Type u_2} [inst : AddMonoidWithOne R] [i
nst_1 : CharZero R] (a : ℕ), Nat.castEmbedding a = ↑a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ico_filter_modEq_cast {v : ℕ} :
    {x ∈ Ico a b | x ≡ v [MOD r]}.map castEmbedding =
      {x ∈ Ico (a : ℤ) (b : ℤ) | x ≡ v [ZMOD r]} := by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, castEmbedding_apply]
  constructor
  · simp_rw [forall_exists_index, ← natCast_modEq_iff]; intro y ⟨h, c⟩; subst c; exact_mod_cast h
  · intro h; lift x to ℕ using (by omega); exact ⟨x, by simp_all [natCast_modEq_iff]⟩
/-
**Nat.Ioc_filter_modEq_cast** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：Ioc_filter_modEq_cast {v : Nat} : {x in Ioc a b | x ≡ v [MOD r]}.map castE
mbedding = {x in Ioc (a : Int) (b : Int) | x ≡ v [ZMOD r]}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.castEmbedding_apply`：∀ {R : Type u_2} [inst : AddMonoidWithOne R] [i
nst_1 : CharZero R] (a : ℕ), Nat.castEmbedding a = ↑a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ioc_filter_modEq_cast {v : ℕ} :
    {x ∈ Ioc a b | x ≡ v [MOD r]}.map castEmbedding =
      {x ∈ Ioc (a : ℤ) (b : ℤ) | x ≡ v [ZMOD r]} := by
  ext x
  simp only [mem_map, mem_filter, mem_Ioc, castEmbedding_apply]
  constructor
  · simp_rw [forall_exists_index, ← natCast_modEq_iff]; intro y ⟨h, c⟩; subst c; exact_mod_cast h
  · intro h; lift x to ℕ using (by lia); exact ⟨x, by simp_all [natCast_modEq_iff]⟩

variable (hr : 0 < r)
include hr

/-- There are `⌈(b - v) / r⌉ - ⌈(a - v) / r⌉` numbers congruent to `v` mod `r` in `[a, b)`,
if `a ≤ b`. `Nat` version of `Int.Ico_filter_modEq_card`. -/
/-
**Nat.Ico_filter_modEq_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ico_filter_modEq_card (v : Nat) : #{x in Ico a b | x ≡ v [MOD r]} = max (⌈
(b - v) / (r : Rat)⌉ - ⌈(a - v) / (r : Rat)⌉) 0
参数：v : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用引理 `Nat.Ico_filter_modEq_cast`：Ico_filter_modEq_cast {v : Nat} : {x in Ico a
 b | x ≡ v [MOD r]}.map castEmbedding = {x in Ico (a : Int) (b : Int) | x ≡ v [Z
MOD r]}
· 使用定理 `Int.Ico_filter_modEq_card`：Ico_filter_modEq_card (v : Int) : #{x in Ico 
a b | x ≡ v [ZMOD r]} = max (⌈(b - v) / (r : Rat)⌉ - ⌈(a - v) / (r : Rat)⌉) 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
There are `⌈(b - v) / r⌉ - ⌈(a - v) / r⌉` numbers congruent to `v` mod `r` in `[
a, b)`,
if `a ≤ b`. `Nat` version of `Int.Ico_filter_modEq_card`.
-/
theorem Ico_filter_modEq_card (v : ℕ) :
    #{x ∈ Ico a b | x ≡ v [MOD r]} = max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 := by
  simp_rw [← Ico_filter_modEq_cast _ _ ▸ card_map _,
    Int.Ico_filter_modEq_card _ _ (cast_lt.mpr hr), Int.cast_natCast]

/-- There are `⌊(b - v) / r⌋ - ⌊(a - v) / r⌋` numbers congruent to `v` mod `r` in `(a, b]`,
if `a ≤ b`. `Nat` version of `Int.Ioc_filter_modEq_card`. -/
/-
**Nat.Ioc_filter_modEq_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ioc_filter_modEq_card (v : Nat) : #{x in Ioc a b | x ≡ v [MOD r]} = max (⌊
(b - v) / (r : Rat)⌋ - ⌊(a - v) / (r : Rat)⌋) 0
参数：v : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用引理 `Nat.Ioc_filter_modEq_cast`：Ioc_filter_modEq_cast {v : Nat} : {x in Ioc a
 b | x ≡ v [MOD r]}.map castEmbedding = {x in Ioc (a : Int) (b : Int) | x ≡ v [Z
MOD r]}
· 使用定理 `Int.Ioc_filter_modEq_card`：Ioc_filter_modEq_card (v : Int) : #{x in Ioc 
a b | x ≡ v [ZMOD r]} = max (⌊(b - v) / (r : Rat)⌋ - ⌊(a - v) / (r : Rat)⌋) 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
There are `⌊(b - v) / r⌋ - ⌊(a - v) / r⌋` numbers congruent to `v` mod `r` in `(
a, b]`,
if `a ≤ b`. `Nat` version of `Int.Ioc_filter_modEq_card`.
-/
theorem Ioc_filter_modEq_card (v : ℕ) :
    #{x ∈ Ioc a b | x ≡ v [MOD r]} = max (⌊(b - v) / (r : ℚ)⌋ - ⌊(a - v) / (r : ℚ)⌋) 0 := by
  simp_rw [← Ioc_filter_modEq_cast _ _ ▸ card_map _,
    Int.Ioc_filter_modEq_card _ _ (cast_lt.mpr hr), Int.cast_natCast]

/-- There are `⌈(b - v % r) / r⌉` numbers in `[0, b)` congruent to `v` mod `r`. -/
/-
**Nat.count_modEq_card_eq_ceil** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_modEq_card_eq_ceil (v : Nat) : b.count (· ≡ v [MOD r]) = ⌈(b - (v % 
r : Nat)) / (r : Rat)⌉
参数：v : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_eq_card_filter_range`：count_eq_card_filter_range (n : Nat) : c
ount p n = #{x in range n | p x}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用定理 `Nat.Ico_filter_modEq_card`：Ico_filter_modEq_card (v : Nat) : #{x in Ico 
a b | x ≡ v [MOD r]} = max (⌈(b - v) / (r : Rat)⌉ - ⌈(a - v) / (r : Rat)⌉) 0
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.ceil_le_ceil`：∀ {R : Type u_2} [inst : Ring R] [inst_1 : LinearOrder
 R] [inst_2 : FloorRing R] {a b : R}, a ≤ b → ⌈a⌉ ≤ ⌈b⌉
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `sub_le_sub_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, a ≤ b → ∀ (c : α), a - c ≤ b - c
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.div_add_mod`：∀ (m n : ℕ), n * (m / n) + m % n = m
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
There are `⌈(b - v % r) / r⌉` numbers in `[0, b)` congruent to `v` mod `r`.
-/
theorem count_modEq_card_eq_ceil (v : ℕ) :
    b.count (· ≡ v [MOD r]) = ⌈(b - (v % r : ℕ)) / (r : ℚ)⌉ := by
  have hr' : 0 < (r : ℚ) := by positivity
  rw [count_eq_card_filter_range, ← Ico_zero_eq_range, Ico_filter_modEq_card _ _ hr,
    max_eq_left (sub_nonneg.mpr <| by gcongr; positivity)]
  conv_lhs =>
    rw [← div_add_mod v r, cast_add, cast_mul, add_comm]
    tactic => simp_rw [← sub_sub, sub_div (_ - _), mul_div_cancel_left₀ _ hr'.ne',
      Int.ceil_sub_natCast]
    rw [sub_sub_sub_cancel_right, cast_zero, zero_sub]
  rw [sub_eq_self, ceil_eq_zero_iff, Set.mem_Ioc, div_le_iff₀ hr', lt_div_iff₀ hr', neg_one_mul,
    zero_mul, neg_lt_neg_iff, cast_lt]
  exact ⟨mod_lt _ hr, by simp⟩

/-- There are `b / r + [v % r < b % r]` numbers in `[0, b)` congruent to `v` mod `r`,
where `[·]` is the Iverson bracket. -/
/-
**Nat.count_modEq_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_modEq_card (v : Nat) : b.count (· ≡ v [MOD r]) = b / r + if v % r < 
b % r then 1 else 0
参数：v : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Nat.count_modEq_card_eq_ceil`：count_modEq_card_eq_ceil (v : Nat) : b.cou
nt (· ≡ v [MOD r]) = ⌈(b - (v % r : Nat)) / (r : Rat)⌉
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.div_add_mod`：∀ (m n : ℕ), n * (m / n) + m % n = m
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `add_sub`：∀ {G : Type u_3} [inst : SubNegMonoid G] (a b c : G), a + (b - 
c) = a + b - c
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Int.ceil_add_natCast`：ceil_add_natCast (a : R) (n : Nat) : ⌈a + n⌉ = ⌈a⌉
 + n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.ceil_eq_iff`：ceil_eq_iff : ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a <= z
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
There are `b / r + [v % r < b % r]` numbers in `[0, b)` congruent to `v` mod `r`
,
where `[·]` is the Iverson bracket.
-/
theorem count_modEq_card (v : ℕ) :
    b.count (· ≡ v [MOD r]) = b / r + if v % r < b % r then 1 else 0 := by
  have hr' : 0 < (r : ℚ) := by positivity
  rw [← ofNat_inj, count_modEq_card_eq_ceil _ hr, cast_add]
  conv_lhs => rw [← div_add_mod b r, cast_add, cast_mul, ← add_sub, _root_.add_div,
    mul_div_cancel_left₀ _ hr'.ne', add_comm, Int.ceil_add_natCast, add_comm]
  rw [add_right_inj]
  split_ifs with h
  · rw [← cast_sub h.le, Int.ceil_eq_iff, div_le_iff₀ hr', lt_div_iff₀ hr', cast_one, Int.cast_one,
      sub_self, zero_mul, cast_pos, tsub_pos_iff_lt, one_mul, cast_le, tsub_le_iff_right]
    exact ⟨h, ((mod_lt _ hr).trans_le (by simp)).le⟩
  · rw [cast_zero, ceil_eq_zero_iff, Set.mem_Ioc, div_le_iff₀ hr', lt_div_iff₀ hr', zero_mul,
      tsub_nonpos, ← neg_eq_neg_one_mul, neg_lt_sub_iff_lt_add, ← cast_add, cast_lt, cast_le]
    exact ⟨(mod_lt _ hr).trans_le (by simp), not_lt.mp h⟩

end Nat

